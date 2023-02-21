// See LICENSE.SiFive for license details.

package freechips.rocketchip.rocket

import chisel3._
import chisel3.util.{Cat, log2Ceil}
import Chisel.ImplicitConversions._
import freechips.rocketchip.config._
import freechips.rocketchip.tile._
import freechips.rocketchip.util._

class PMPConfig extends Bundle {
  val l = Bool()
  val res = UInt(2.W)
  val a = UInt(2.W)
  val x = Bool()
  val w = Bool()
  val r = Bool()
}

object PMP {
  def lgAlign = 2

  def apply(reg: PMPReg): PMP = {
    val pmp = Wire(new PMP()(reg.p))
    pmp.cfg := reg.cfg
    pmp.addr := reg.addr
    pmp.mask := pmp.computeMask
    pmp
  }
}

class PMPReg(implicit p: Parameters) extends CoreBundle()(p) {
  val cfg = new PMPConfig
  val addr = UInt((paddrBits - PMP.lgAlign).W)

  def reset(): Unit = {
    cfg.a := 0
    cfg.l := 0
  }

  def readAddr = if (pmpGranularity.log2 == PMP.lgAlign) addr else {
    val mask = ((BigInt(1) << (pmpGranularity.log2 - PMP.lgAlign)) - 1).U
    Mux(napot, addr | (mask >> 1), ~(~addr | mask))
  }
  def napot = cfg.a(1)
  def torNotNAPOT = cfg.a(0)
  def tor = !napot && torNotNAPOT
  def cfgLocked = cfg.l
  def addrLocked(next: PMPReg) = cfgLocked || next.cfgLocked && next.tor
}

class PMP(implicit p: Parameters) extends PMPReg {
  val mask = UInt(paddrBits.W)

  import PMP._
  def computeMask = {
    val base = Cat(addr, cfg.a(0)) | ((pmpGranularity - 1) >> lgAlign)
    Cat(base & ~(base + 1), ((1 << lgAlign) - 1).U)
  }
  private def comparand = ~(~(addr << lgAlign) | (pmpGranularity - 1))

  private def pow2Match(x: UInt, lgSize: UInt, lgMaxSize: Int) = {
    def eval(a: UInt, b: UInt, m: UInt) = ((a ^ b) & ~m) === 0
    if (lgMaxSize <= pmpGranularity.log2) {
      eval(x, comparand, mask)
    } else {
      // break up the circuit; the MSB part will be CSE'd
      val lsbMask = mask | UIntToOH1(lgSize, lgMaxSize)
      val msbMatch = eval(x >> lgMaxSize, comparand >> lgMaxSize, mask >> lgMaxSize)
      val lsbMatch = eval(x(lgMaxSize-1, 0), comparand(lgMaxSize-1, 0), lsbMask(lgMaxSize-1, 0))
      msbMatch && lsbMatch
    }
  }

  private def boundMatch(x: UInt, lsbMask: UInt, lgMaxSize: Int) = {
    if (lgMaxSize <= pmpGranularity.log2) {
      x < comparand
    } else {
      // break up the circuit; the MSB part will be CSE'd
      val msbsLess = (x >> lgMaxSize) < (comparand >> lgMaxSize)
      val msbsEqual = ((x >> lgMaxSize) ^ (comparand >> lgMaxSize)) === 0
      val lsbsLess =  (x(lgMaxSize-1, 0) | lsbMask) < comparand(lgMaxSize-1, 0)
      msbsLess || (msbsEqual && lsbsLess)
    }
  }

  private def lowerBoundMatch(x: UInt, lgSize: UInt, lgMaxSize: Int) =
    !boundMatch(x, UIntToOH1(lgSize, lgMaxSize), lgMaxSize)

  private def upperBoundMatch(x: UInt, lgMaxSize: Int) =
    boundMatch(x, 0.U, lgMaxSize)

  private def rangeMatch(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: PMP) =
    prev.lowerBoundMatch(x, lgSize, lgMaxSize) && upperBoundMatch(x, lgMaxSize)

  private def pow2Homogeneous(x: UInt, pgLevel: UInt) = {
    val maskHomogeneous = pgLevelMap { idxBits => if (idxBits > paddrBits) false.B else mask(idxBits - 1) } (pgLevel)
    maskHomogeneous || (pgLevelMap { idxBits => ((x ^ comparand) >> idxBits) =/= 0 } (pgLevel))
  }

  private def pgLevelMap[T](f: Int => T) = (0 until pgLevels).map { i =>
    f(pgIdxBits + (pgLevels - 1 - i) * pgLevelBits)
  }

  private def rangeHomogeneous(x: UInt, pgLevel: UInt, prev: PMP) = {
    val beginsAfterLower = !(x < prev.comparand)
    val beginsAfterUpper = !(x < comparand)

    val pgMask = pgLevelMap { idxBits => (((BigInt(1) << paddrBits) - (BigInt(1) << idxBits)) max 0).U } (pgLevel)
    val endsBeforeLower = (x & pgMask) < (prev.comparand & pgMask)
    val endsBeforeUpper = (x & pgMask) < (comparand & pgMask)

    endsBeforeLower || beginsAfterUpper || (beginsAfterLower && endsBeforeUpper)
  }

  // returns whether this PMP completely contains, or contains none of, a page
  def homogeneous(x: UInt, pgLevel: UInt, prev: PMP): Bool =
    Mux(napot, pow2Homogeneous(x, pgLevel), !torNotNAPOT || rangeHomogeneous(x, pgLevel, prev))

  // returns whether this matching PMP fully contains the access
  def aligned(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: PMP): Bool = if (lgMaxSize <= pmpGranularity.log2) true.B else {
    val lsbMask = UIntToOH1(lgSize, lgMaxSize)
    val straddlesLowerBound = ((x >> lgMaxSize) ^ (prev.comparand >> lgMaxSize)) === 0 && (prev.comparand(lgMaxSize-1, 0) & ~x(lgMaxSize-1, 0)) =/= 0
    val straddlesUpperBound = ((x >> lgMaxSize) ^ (comparand >> lgMaxSize)) === 0 && (comparand(lgMaxSize-1, 0) & (x(lgMaxSize-1, 0) | lsbMask)) =/= 0
    val rangeAligned = !(straddlesLowerBound || straddlesUpperBound)
    val pow2Aligned = (lsbMask & ~mask(lgMaxSize-1, 0)) === 0
    Mux(napot, pow2Aligned, rangeAligned)
  }

  // returns whether this PMP matches at least one byte of the access
  def hit(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: PMP): Bool =
    Mux(napot, pow2Match(x, lgSize, lgMaxSize), torNotNAPOT && rangeMatch(x, lgSize, lgMaxSize, prev))
}

// INFO(DD): this is used to check whether PMPs can cover the full range of a page
//           If you do not familiar with foldLeft and case, learn it from Scala
class PMPHomogeneityChecker(pmps: Seq[PMP])(implicit p: Parameters) {
  def apply(addr: UInt, pgLevel: UInt): Bool = {
    pmps.foldLeft((true.B, 0.U.asTypeOf(new PMP))) { case ((h, prev), pmp) =>
      (h && pmp.homogeneous(addr, pgLevel, prev), pmp)
    }._1
  }
}

// INFO(DD): The basic idea is simple here, find a hit PMP, and returns the
//           r/w/x permissios back
//           Missing parts: check the permissions according to the priv-level
//            I guess it's handled by the upper layer
class PMPChecker(lgMaxSize: Int)(implicit val p: Parameters) extends Module
    with HasCoreParameters {
  val io = IO(new Bundle {
    val prv = Input(UInt(PRV.SZ.W))
    val pmp = Input(Vec(nPMPs, new PMP))
    val addr = Input(UInt(paddrBits.W))
    val size = Input(UInt(log2Ceil(lgMaxSize + 1).W))
    val r = Output(Bool())
    val w = Output(Bool())
    val x = Output(Bool())
  })

  val default = if (io.pmp.isEmpty) true.B else io.prv > PRV.S
  val pmp0 = WireInit(0.U.asTypeOf(new PMP))
  pmp0.cfg.r := default
  pmp0.cfg.w := default
  pmp0.cfg.x := default

  val res = (io.pmp zip (pmp0 +: io.pmp)).reverse.foldLeft(pmp0) { case (prev, (pmp, prevPMP)) =>
    val hit = pmp.hit(io.addr, io.size, lgMaxSize, prevPMP)
    val ignore = default && !pmp.cfg.l
    val aligned = pmp.aligned(io.addr, io.size, lgMaxSize, prevPMP)

    for ((name, idx) <- Seq("no", "TOR", if (pmpGranularity <= 4) "NA4" else "", "NAPOT").zipWithIndex; if name.nonEmpty)
      property.cover(pmp.cfg.a === idx, s"The cfg access is set to ${name} access ", "Cover PMP access mode setting")

    property.cover(pmp.cfg.l === 0x1, s"The cfg lock is set to high ", "Cover PMP lock mode setting")
   
    // Not including Write and no Read permission as the combination is reserved
    for ((name, idx) <- Seq("no", "RO", "", "RW", "X", "RX", "", "RWX").zipWithIndex; if name.nonEmpty)
      property.cover((Cat(pmp.cfg.x, pmp.cfg.w, pmp.cfg.r) === idx), s"The permission is set to ${name} access ", "Cover PMP access permission setting")

    for ((name, idx) <- Seq("", "TOR", if (pmpGranularity <= 4) "NA4" else "", "NAPOT").zipWithIndex; if name.nonEmpty) {
      property.cover(!ignore && hit && aligned && pmp.cfg.a === idx, s"The access matches ${name} mode ", "Cover PMP access")
      property.cover(pmp.cfg.l && hit && aligned && pmp.cfg.a === idx, s"The access matches ${name} mode with lock bit high", "Cover PMP access with lock bit")
    }

    val cur = WireInit(pmp)
    cur.cfg.r := aligned && (pmp.cfg.r || ignore)
    cur.cfg.w := aligned && (pmp.cfg.w || ignore)
    cur.cfg.x := aligned && (pmp.cfg.x || ignore)
    Mux(hit, cur, prev)
  }

  io.r := res.cfg.r
  io.w := res.cfg.w
  io.x := res.cfg.x
}

/*
 * The following is the SMPU module
 * Info(DD): we can reuse most of PMP's logics for SMPU
 * */
class SMPUConfig extends Bundle {
  val l = Bool()
  val res = UInt(2.W)
  val a = UInt(2.W)
  val x = Bool()
  val w = Bool()
  val r = Bool()
}

object SMPU {
  def lgAlign = 2

  def apply(reg: SMPUReg): SMPU = {
    val smpu = Wire(new SMPU()(reg.p))
    smpu.cfg := reg.cfg
    smpu.off := reg.off
    smpu.addr := reg.addr
    smpu.mask := smpu.computeMask
    smpu
  }
}

class SMPUReg(implicit p: Parameters) extends CoreBundle()(p) {
  val cfg = new SMPUConfig
  val addr = UInt((paddrBits - SMPU.lgAlign).W)
  //val off = UInt((vaddrBits).W) // offset
  val off = UInt(64.W) // offset

  def reset(): Unit = {
    cfg.a := 0
    cfg.l := 0
    off   := 0
  }

  def readAddr = if (pmpGranularity.log2 == SMPU.lgAlign) addr else {
    val mask = ((BigInt(1) << (pmpGranularity.log2 - SMPU.lgAlign)) - 1).U
    Mux(napot, addr | (mask >> 1), ~(~addr | mask))
  }
  def readOff = off
  def napot = cfg.a(1)
  def torNotNAPOT = cfg.a(0)
  def tor = !napot && torNotNAPOT
  def cfgLocked = cfg.l
  def addrLocked(next: SMPUReg) = cfgLocked || next.cfgLocked && next.tor
}

class SMPU(implicit p: Parameters) extends SMPUReg {
  val mask = UInt(paddrBits.W)

  import SMPU._
  def computeMask = {
    val base = Cat(addr, cfg.a(0)) | ((pmpGranularity - 1) >> lgAlign)
    Cat(base & ~(base + 1), ((1 << lgAlign) - 1).U)
  }
  private def comparand = ~(~(addr << lgAlign) | (pmpGranularity - 1))

  private def pow2Match(x: UInt, lgSize: UInt, lgMaxSize: Int) = {
    def eval(a: UInt, b: UInt, m: UInt) = ((a ^ b) & ~m) === 0
    if (lgMaxSize <= pmpGranularity.log2) {
      eval(x, comparand, mask)
    } else {
      // break up the circuit; the MSB part will be CSE'd
      val lsbMask = mask | UIntToOH1(lgSize, lgMaxSize)
      val msbMatch = eval(x >> lgMaxSize, comparand >> lgMaxSize, mask >> lgMaxSize)
      val lsbMatch = eval(x(lgMaxSize-1, 0), comparand(lgMaxSize-1, 0), lsbMask(lgMaxSize-1, 0))
      msbMatch && lsbMatch
    }
  }

  private def boundMatch(x: UInt, lsbMask: UInt, lgMaxSize: Int) = {
    if (lgMaxSize <= pmpGranularity.log2) {
      x < comparand
    } else {
      // break up the circuit; the MSB part will be CSE'd
      val msbsLess = (x >> lgMaxSize) < (comparand >> lgMaxSize)
      val msbsEqual = ((x >> lgMaxSize) ^ (comparand >> lgMaxSize)) === 0
      val lsbsLess =  (x(lgMaxSize-1, 0) | lsbMask) < comparand(lgMaxSize-1, 0)
      msbsLess || (msbsEqual && lsbsLess)
    }
  }

  private def lowerBoundMatch(x: UInt, lgSize: UInt, lgMaxSize: Int) =
    !boundMatch(x, UIntToOH1(lgSize, lgMaxSize), lgMaxSize)

  private def upperBoundMatch(x: UInt, lgMaxSize: Int) =
    boundMatch(x, 0.U, lgMaxSize)

  private def rangeMatch(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: SMPU) =
    prev.lowerBoundMatch(x, lgSize, lgMaxSize) && upperBoundMatch(x, lgMaxSize)

  private def pow2Homogeneous(x: UInt, pgLevel: UInt) = {
    val maskHomogeneous = pgLevelMap { idxBits => if (idxBits > paddrBits) false.B else mask(idxBits - 1) } (pgLevel)
    maskHomogeneous || (pgLevelMap { idxBits => ((x ^ comparand) >> idxBits) =/= 0 } (pgLevel))
  }

  private def pgLevelMap[T](f: Int => T) = (0 until pgLevels).map { i =>
    f(pgIdxBits + (pgLevels - 1 - i) * pgLevelBits)
  }

  private def rangeHomogeneous(x: UInt, pgLevel: UInt, prev: SMPU) = {
    val beginsAfterLower = !(x < prev.comparand)
    val beginsAfterUpper = !(x < comparand)

    val pgMask = pgLevelMap { idxBits => (((BigInt(1) << paddrBits) - (BigInt(1) << idxBits)) max 0).U } (pgLevel)
    val endsBeforeLower = (x & pgMask) < (prev.comparand & pgMask)
    val endsBeforeUpper = (x & pgMask) < (comparand & pgMask)

    endsBeforeLower || beginsAfterUpper || (beginsAfterLower && endsBeforeUpper)
  }

  // returns whether this SMPU completely contains, or contains none of, a page
  def homogeneous(x: UInt, pgLevel: UInt, prev: SMPU): Bool =
    Mux(napot, pow2Homogeneous(x, pgLevel), !torNotNAPOT || rangeHomogeneous(x, pgLevel, prev))

  // returns whether this matching SMPU fully contains the access
  def aligned(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: SMPU): Bool = if (lgMaxSize <= pmpGranularity.log2) true.B else {
    val lsbMask = UIntToOH1(lgSize, lgMaxSize)
    val straddlesLowerBound = ((x >> lgMaxSize) ^ (prev.comparand >> lgMaxSize)) === 0 && (prev.comparand(lgMaxSize-1, 0) & ~x(lgMaxSize-1, 0)) =/= 0
    val straddlesUpperBound = ((x >> lgMaxSize) ^ (comparand >> lgMaxSize)) === 0 && (comparand(lgMaxSize-1, 0) & (x(lgMaxSize-1, 0) | lsbMask)) =/= 0
    val rangeAligned = !(straddlesLowerBound || straddlesUpperBound)
    val pow2Aligned = (lsbMask & ~mask(lgMaxSize-1, 0)) === 0
    Mux(napot, pow2Aligned, rangeAligned)
  }

  // returns whether this SMPU matches at least one byte of the access
  def hit(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: SMPU): Bool =
    Mux(napot, pow2Match(x, lgSize, lgMaxSize), torNotNAPOT && rangeMatch(x, lgSize, lgMaxSize, prev))
}

class SMPUChecker(lgMaxSize: Int)(implicit val p: Parameters) extends Module
    with HasCoreParameters {
  val io = IO(new Bundle {
    val prv = Input(UInt(PRV.SZ.W))
    val smpu = Input(Vec(nSMPUs, new SMPU))
    val addr = Input(UInt(vaddrBits.W))
    val size = Input(UInt(log2Ceil(lgMaxSize + 1).W))
    val r = Output(Bool())
    val w = Output(Bool())
    val x = Output(Bool())
    val paddr = Output(UInt(paddrBits.W))
  })

  val default = if (io.smpu.isEmpty) true.B else io.prv > PRV.U
  val smpu0 = WireInit(0.U.asTypeOf(new SMPU))
  smpu0.cfg.r := default
  smpu0.cfg.w := default
  smpu0.cfg.x := default
  smpu0.off := 0 // The default behavior of smpuoff is 0 (no translation here)

  // Here, we use some basic settings of PMP, e.g., lgMaxSize, granularity, etc.
  val res = (io.smpu zip (smpu0 +: io.smpu)).reverse.foldLeft(smpu0) { case (prev, (smpu, prevSMPU)) =>
    // Note(DD): here, we use (io.addr - smpu.off) to represent the real PA, i.e., PA = VA - Off
    val paddr = io.addr - smpu.off
    val hit = smpu.hit(paddr, io.size, lgMaxSize, prevSMPU)
    val ignore = default && !smpu.cfg.l
    val aligned = smpu.aligned(paddr, io.size, lgMaxSize, prevSMPU)

    for ((name, idx) <- Seq("no", "TOR", if (pmpGranularity <= 4) "NA4" else "", "NAPOT").zipWithIndex; if name.nonEmpty)
      property.cover(smpu.cfg.a === idx, s"The cfg access is set to ${name} access ", "Cover SMPU access mode setting")

    property.cover(smpu.cfg.l === 0x1, s"The cfg lock is set to high ", "Cover SMPU lock mode setting")

    // Not including Write and no Read permission as the combination is reserved
    for ((name, idx) <- Seq("no", "RO", "", "RW", "X", "RX", "", "RWX").zipWithIndex; if name.nonEmpty)
      property.cover((Cat(smpu.cfg.x, smpu.cfg.w, smpu.cfg.r) === idx), s"The permission is set to ${name} access ", "Cover SMPU access permission setting")

    for ((name, idx) <- Seq("", "TOR", if (pmpGranularity <= 4) "NA4" else "", "NAPOT").zipWithIndex; if name.nonEmpty) {
      property.cover(!ignore && hit && aligned && smpu.cfg.a === idx, s"The access matches ${name} mode ", "Cover SMPU access")
      property.cover(smpu.cfg.l && hit && aligned && smpu.cfg.a === idx, s"The access matches ${name} mode with lock bit high", "Cover SMPU access with lock bit")
    }


    val cur = WireInit(smpu)
    cur.cfg.r := aligned && (smpu.cfg.r || ignore)
    cur.cfg.w := aligned && (smpu.cfg.w || ignore)
    cur.cfg.x := aligned && (smpu.cfg.x || ignore)

//    printf("hit[%d], vaddr=[%x], paddr=[%x], off=[%x], r:%d, w:%d, x:%d\n",
//	hit, io.addr, io.addr-smpu.off, smpu.off, smpu.cfg.r, smpu.cfg.w, smpu.cfg.x)
    Mux(hit, cur, prev)
  }
  //    paddr, hit, ignore, aligned)
  // hit?[%b], ignore?[%b], aligned?[%b]\n

  io.r := res.cfg.r
  io.w := res.cfg.w
  io.x := res.cfg.x
  io.paddr := Mux(io.prv > PRV.S, io.addr, (io.addr - res.off))
}

/*
 * Note(DD): A temporal checker that merges PMP and SMPU
 * The output r,w,x means the access can not pass either SMPU and PMP.
 * The output paddr is translated paddr using SMPU
 *
 * For M/S mode, the Checker should be the same as PMPChecker,
 * For U mode, the Checker is a combination of PMP/SMPU checkers.
 * */
class PMPSMPUChecker(lgMaxSize: Int)(implicit val p: Parameters) extends Module
    with HasCoreParameters {
  val io = IO(new Bundle {
    val prv = Input(UInt(PRV.SZ.W))
    val pmp = Input(Vec(nPMPs, new PMP))
    val smpu = Input(Vec(nSMPUs, new SMPU))
    val addr = Input(UInt(vaddrBits.W))
    val size = Input(UInt(log2Ceil(lgMaxSize + 1).W))
    val r = Output(Bool())
    val w = Output(Bool())
    val x = Output(Bool())
    val paddr = Output(UInt(paddrBits.W))
  })

  val defaultSMPU = if (io.smpu.isEmpty) true.B else io.prv > PRV.U
  val defaultPMP = if (io.pmp.isEmpty) true.B else io.prv > PRV.S
  val smpu0 = WireInit(0.U.asTypeOf(new SMPU))
  smpu0.cfg.r := defaultSMPU
  smpu0.cfg.w := defaultSMPU
  smpu0.cfg.x := defaultSMPU
  smpu0.off := 0 // The default behavior of smpuoff is 0 (no translation here)

  val pmp0 = WireInit(0.U.asTypeOf(new PMP))
  pmp0.cfg.r := defaultPMP
  pmp0.cfg.w := defaultPMP
  pmp0.cfg.x := defaultPMP

  // Here, we use some basic settings of PMP, e.g., lgMaxSize, granularity, etc.
  val res = (io.smpu zip (smpu0 +: io.smpu)).reverse.foldLeft(smpu0) { case (prev, (smpu, prevSMPU)) =>
    // Note(DD): here, we use (io.addr - smpu.off) to represent the real PA, i.e., PA = VA - Off
    val paddr = Mux(io.prv > PRV.U, io.addr, io.addr - smpu.off)
    // Always hit when prv > PRV.U, which will enforce to use PMP's results
    val hit = (io.prv > PRV.U) || smpu.hit(paddr, io.size, lgMaxSize, prevSMPU)
    //val ignore = defaultSMPU && !smpu.cfg.l
    val ignore = defaultSMPU  // only enforce U-mode now
    // NOt perform alignment checking when S/M modes
    val aligned = (io.prv > PRV.U) || smpu.aligned(paddr, io.size, lgMaxSize, prevSMPU)

    // We check the PMP permission for each SMPU entry
    val resPMP = (io.pmp zip (pmp0 +: io.pmp)).reverse.foldLeft(pmp0) { case (prev2, (pmp, prevPMP)) =>
      val hitPMP = pmp.hit(paddr, io.size, lgMaxSize, prevPMP)
      val ignorePMP = defaultPMP && !pmp.cfg.l
      val alignedPMP = pmp.aligned(paddr, io.size, lgMaxSize, prevPMP)
      val curPMP = WireInit(pmp)
      curPMP.cfg.r := alignedPMP && (pmp.cfg.r || ignorePMP)
      curPMP.cfg.w := alignedPMP && (pmp.cfg.w || ignorePMP)
      curPMP.cfg.x := alignedPMP && (pmp.cfg.x || ignorePMP)
      Mux(hitPMP, curPMP, prev2)
    }

    val cur = WireInit(smpu)
    cur.cfg.r := aligned && (smpu.cfg.r || ignore) && resPMP.cfg.r 
    cur.cfg.w := aligned && (smpu.cfg.w || ignore) && resPMP.cfg.w
    cur.cfg.x := aligned && (smpu.cfg.x || ignore) && resPMP.cfg.x

    Mux(hit, cur, prev)
  }

  io.r := res.cfg.r
  io.w := res.cfg.w
  io.x := res.cfg.x
  io.paddr := Mux(io.prv > PRV.U, io.addr, (io.addr - res.off))
}
