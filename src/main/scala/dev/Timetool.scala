package spatial.tests.dev

object XGHelpers {
  def scalaIfElse[T](cond: scala.Boolean, ift: => T, iff: => T): T = {
    if (cond) ift else iff
  }
}

import argon.uconst
import emul.FixedPoint
import spatial.libdsl._
import utils.io.files._

sealed trait InterpType
object HypercubeInterp extends InterpType
object SimplexInterp extends InterpType

protected object LDefs {
  val lattice_rank = 5
  val lattice_size = 10
  val num_keypoints = 16

  val sizes = Array.fill(lattice_rank)(lattice_size)
  val dimensions = sizes.length
  val strides: Array[Int] = Array.fill(dimensions){1}

  (1 to (dimensions - 1)) foreach {
    d => {
      strides(d) = strides(d-1) * sizes(d-1)
    }
  }

  val size = sizes.product

  type Log2Size = _5 // ceil(log2(size))

  type indexBits = _3

  type intBits = _16
  val intBits = 16
  type mantissaBits = _16
  val mantissaBits = 16


  val totalBits = intBits + mantissaBits

  type T = FixPt[FALSE, intBits, mantissaBits]
  type CornerType = FixPt[FALSE, intBits, _0]
  type ResidualType = FixPt[FALSE, _1, mantissaBits]
  type AccumResidualType = FixPt[FALSE, _1, mantissaBits]

  type IndexType = FixPt[FALSE, indexBits, _0]

  type ParameterIndex = FixPt[FALSE, Log2Size, _0]
  def ParameterIndex(x: Int): ParameterIndex = uconst[ParameterIndex](FixedPoint.fromInt(x))

  type OutputType = FixPt[TRUE, _16, mantissaBits]
  type I = FixPt[TRUE, _32, _0]
}

protected object LUtils {
  import LDefs._

  def allCorners(maxes: Seq[scala.Int], partials: Seq[Seq[scala.Int]] = Seq(Seq.empty)): Seq[Seq[scala.Int]] = maxes match {
    case Nil => Nil
    case h::tail if tail.nonEmpty => (0 to h).flatMap{i => allCorners(tail, partials.map(_ ++ Seq(i)))}
    case h::tail if tail.isEmpty => (0 to h).flatMap{i => partials.map(_ ++ Seq(i))}
  }

  object CombinationTree {

    private def join[T](x1: Seq[T], x2: Seq[T], func: (T,T) => T): Seq[T] = x1.flatMap{a => x2.map{b => func(a,b)}}

    private def combine[T](xs: Seq[Seq[T]], func: (T,T) => T): Seq[Seq[T]] = xs.length match {
      case 0 => throw new Exception("Empty reduction level")
      case 1 => xs
      case len if len % 2 == 0 => combine(List.tabulate(len/2){i => join(xs(2*i), xs(2*i+1), func)}, func)
      case len => combine(List.tabulate(len/2){i => join(xs(2*i), xs(2*i+1), func) } :+ xs.last, func)
    }

    def apply[T](xs: Seq[T]*)(func: (T,T) => T): Seq[T] = combine(xs, func).head
  }


  def evaluate(input: (scala.Int => T),
               params: (I32 => OutputType),
               interpolation_type: InterpType
              )(implicit state: argon.State): OutputType = interpolation_type match {
      case SimplexInterp =>
        val simplex = new SimplexLattice[intBits, mantissaBits, Log2Size, intBits, FALSE](dimensions, strides.toArray)
        simplex.evaluate(input, params)

      case HypercubeInterp =>
        val hypercube = new HypercubeLattice[intBits, mantissaBits, Log2Size, intBits, FALSE](dimensions, strides.toArray)
        hypercube.evaluate(input, params)

  }
}


sealed trait BBoxModel

case object NN_32_32_RELU extends BBoxModel
case object NN_32_32_Leaky extends BBoxModel
case object NN_16_16_RELU extends BBoxModel
case object NN_16_16_Leaky extends BBoxModel
case object NN_64_RELU extends BBoxModel
case object NN_64_Leaky extends BBoxModel
case object NN_8_8_RELU extends BBoxModel
case object NN_4_4_RELU extends BBoxModel
case object NN_16_4_RELU extends BBoxModel
case object NN_8_4_RELU extends BBoxModel
case object XGBoost_10_5 extends BBoxModel
case object XGBoost_20_5 extends BBoxModel
case object XGBoost_25_5 extends BBoxModel
case object XGBoost_10_6 extends BBoxModel
case object XGBoost_20_6 extends BBoxModel
case object XGBoost_40_4 extends BBoxModel
case object XGBoost_64_4 extends BBoxModel
case object XGBoost_96_4 extends BBoxModel
case object XGBoost_128_4 extends BBoxModel
case object XGBoost_128_3 extends BBoxModel
case object Hypercube_4_2 extends BBoxModel
case object Hypercube_8_2 extends BBoxModel
case object Hypercube_16_2 extends BBoxModel
case object Hypercube_4_3 extends BBoxModel
case object Hypercube_4_4 extends BBoxModel
case object Hypercube_4_5 extends BBoxModel
case object Hypercube_8_3 extends BBoxModel
case object Hypercube_8_4 extends BBoxModel
case object Simplex_4_2 extends BBoxModel
case object Simplex_8_2 extends BBoxModel
case object Simplex_16_2 extends BBoxModel
case object Simplex_4_3 extends BBoxModel
case object Simplex_4_4 extends BBoxModel
case object Simplex_4_5 extends BBoxModel
case object Simplex_8_3 extends BBoxModel
case object Simplex_8_4 extends BBoxModel
case object Polyfit_2 extends BBoxModel
case object Polyfit_3 extends BBoxModel
case object Polyfit_4 extends BBoxModel


class Timetool_Primitive_NN_64_RELU extends Timetool_Primitive(NN_64_RELU)
class Timetool_Primitive_NN_64_Leaky extends Timetool_Primitive(NN_64_Leaky)
class Timetool_Primitive_NN_32_32_RELU extends Timetool_Primitive(NN_32_32_RELU)
class Timetool_Primitive_NN_32_32_Leaky extends Timetool_Primitive(NN_32_32_Leaky)
class Timetool_Primitive_NN_16_16_RELU extends Timetool_Primitive(NN_16_16_RELU)
class Timetool_Primitive_NN_16_16_Leaky extends Timetool_Primitive(NN_16_16_Leaky)
class Timetool_Primitive_NN_8_8_RELU extends Timetool_Primitive(NN_8_8_RELU)
class Timetool_Primitive_NN_4_4_RELU extends Timetool_Primitive(NN_4_4_RELU)
class Timetool_Primitive_NN_16_4_RELU extends Timetool_Primitive(NN_16_4_RELU)
class Timetool_Primitive_NN_8_4_RELU extends Timetool_Primitive(NN_8_4_RELU)
class Timetool_Primitive_XGBoost_10_5 extends Timetool_Primitive(XGBoost_10_5)
class Timetool_Primitive_XGBoost_10_6 extends Timetool_Primitive(XGBoost_10_6)
class Timetool_Primitive_XGBoost_20_5 extends Timetool_Primitive(XGBoost_20_5)
class Timetool_Primitive_XGBoost_25_5 extends Timetool_Primitive(XGBoost_25_5)
class Timetool_Primitive_XGBoost_20_6 extends Timetool_Primitive(XGBoost_20_6)
class Timetool_Primitive_XGBoost_40_4 extends Timetool_Primitive(XGBoost_40_4)
class Timetool_Primitive_XGBoost_64_4 extends Timetool_Primitive(XGBoost_64_4)
class Timetool_Primitive_XGBoost_96_4 extends Timetool_Primitive(XGBoost_96_4)
class Timetool_Primitive_XGBoost_128_4 extends Timetool_Primitive(XGBoost_128_4)
class Timetool_Primitive_XGBoost_128_3 extends Timetool_Primitive(XGBoost_128_3)
class Timetool_Primitive_Hypercube_4_2 extends Timetool_Primitive(Hypercube_4_2)
class Timetool_Primitive_Hypercube_8_2 extends Timetool_Primitive(Hypercube_8_2)
class Timetool_Primitive_Hypercube_16_2 extends Timetool_Primitive(Hypercube_16_2)
class Timetool_Primitive_Hypercube_4_3 extends Timetool_Primitive(Hypercube_4_3)
class Timetool_Primitive_Hypercube_4_4 extends Timetool_Primitive(Hypercube_4_4)
class Timetool_Primitive_Hypercube_4_5 extends Timetool_Primitive(Hypercube_4_5)
class Timetool_Primitive_Hypercube_8_3 extends Timetool_Primitive(Hypercube_8_3)
class Timetool_Primitive_Hypercube_8_4 extends Timetool_Primitive(Hypercube_8_4)
class Timetool_Primitive_Simplex_4_2 extends Timetool_Primitive(Simplex_4_2)
class Timetool_Primitive_Simplex_8_2 extends Timetool_Primitive(Simplex_8_2)
class Timetool_Primitive_Simplex_16_2 extends Timetool_Primitive(Simplex_16_2)
class Timetool_Primitive_Simplex_4_3 extends Timetool_Primitive(Simplex_4_3)
class Timetool_Primitive_Simplex_4_4 extends Timetool_Primitive(Simplex_4_4)
class Timetool_Primitive_Simplex_4_5 extends Timetool_Primitive(Simplex_4_5)
class Timetool_Primitive_Simplex_8_3 extends Timetool_Primitive(Simplex_8_3)
class Timetool_Primitive_Simplex_8_4 extends Timetool_Primitive(Simplex_8_4)
class Timetool_Primitive_Polyfit_2 extends Timetool_Primitive(Polyfit_2)
class Timetool_Primitive_Polyfit_3 extends Timetool_Primitive(Polyfit_3)
class Timetool_Primitive_Polyfit_4 extends Timetool_Primitive(Polyfit_4)

@spatial abstract class Timetool_Primitive(model: BBoxModel) extends SpatialTest {
//  override def runtimeArgs: Args = "0 157 341 35.2498 -28.1037 12039 12 0"
//  type T = FixPt[TRUE,_16,_16]
  @struct case class KEEP(shouldKeep: Bit)
  import spatial.dsl._

  def main(args: Array[String]): Unit = {
    val par = 1
    val TS = 8
    val bbox_factory = new Timetool_Boxes[_32, _16, _16]()

    assert(args(0).to[Int] == 5.to[Int])
    type I = bbox_factory.I
    type T = bbox_factory.T
    type FEATURES = bbox_factory.FEATURES
    type DELAY = bbox_factory.DELAY
    val row = Array.fill(8)(args(0).to[I])
    val rising_idx = Array.fill(8)(args(1).to[I])
    val falling_idx = Array.fill(8)(args(2).to[I])
    val volume = Array.fill(8)(args(3).to[I])
    val rising_v = Array.fill(8)(args(4).to[T])
    val falling_v = Array.fill(8)(args(5).to[T])
    val first_val = Array.fill(8)(args(6).to[T])
    val last_val = Array.fill(8)(args(7).to[T])

    val NUM_LINES = ArgIn[Int]
    val numel = rising_idx.length
    setArg(NUM_LINES, numel)

    val row_dram = DRAM[I](numel)
    val rising_idx_dram = DRAM[I](numel)
    val rising_v_dram = DRAM[T](numel)
    val falling_idx_dram = DRAM[I](numel)
    val falling_v_dram = DRAM[T](numel)
    val volume_dram = DRAM[I](numel)
    val first_val_dram = DRAM[T](numel)
    val last_val_dram = DRAM[T](numel)

    setMem(row_dram, row)
    setMem(rising_idx_dram, rising_idx)
    setMem(rising_v_dram, rising_v)
    setMem(falling_idx_dram, falling_idx)
    setMem(falling_v_dram, falling_v)
    setMem(volume_dram, volume)
    setMem(first_val_dram, first_val)
    setMem(last_val_dram, last_val)

    val delays_dram = DRAM[T](volume.length)

    val filter_box = bbox_factory.filter_unit
    val infer_box = model match {

      case NN_32_32_RELU => bbox_factory.NN_32_32_RELU
      case NN_32_32_Leaky => bbox_factory.NN_32_32_Leaky
      case NN_16_16_RELU => bbox_factory.NN_16_16_RELU
      case NN_16_16_Leaky => bbox_factory.NN_16_16_Leaky
      case NN_64_RELU => bbox_factory.NN_64_RELU
      case NN_64_Leaky => bbox_factory.NN_64_Leaky
      case NN_8_8_RELU => bbox_factory.NN_8_8_RELU
      case NN_4_4_RELU => bbox_factory.NN_4_4_RELU
      case NN_16_4_RELU => bbox_factory.NN_16_4_RELU
      case NN_8_4_RELU => bbox_factory.NN_8_4_RELU
      case XGBoost_10_5 => bbox_factory.XGBoost_10_5
      case XGBoost_20_5 => bbox_factory.XGBoost_20_5
      case XGBoost_25_5 => bbox_factory.XGBoost_25_5
      case XGBoost_10_6 => bbox_factory.XGBoost_10_6
      case XGBoost_20_6 => bbox_factory.XGBoost_20_6
      case XGBoost_40_4 => bbox_factory.XGBoost_40_4
      case XGBoost_64_4 => bbox_factory.XGBoost_64_4
      case XGBoost_96_4 => bbox_factory.XGBoost_96_4
      case XGBoost_128_4 => bbox_factory.XGBoost_128_4
      case XGBoost_128_3 => bbox_factory.XGBoost_128_3
      case Hypercube_4_2 => bbox_factory.Hypercube_4_2
      case Hypercube_8_2 => bbox_factory.Hypercube_8_2
      case Hypercube_16_2 => bbox_factory.Hypercube_16_2
      case Hypercube_4_3 => bbox_factory.Hypercube_4_3
      case Hypercube_4_4 => bbox_factory.Hypercube_4_4
      case Hypercube_4_5 => bbox_factory.Hypercube_4_5
      case Hypercube_8_3 => bbox_factory.Hypercube_8_3
      case Hypercube_8_4 => bbox_factory.Hypercube_8_4
      case Simplex_4_2 => bbox_factory.Simplex_4_2
      case Simplex_8_2 => bbox_factory.Simplex_8_2
      case Simplex_16_2 => bbox_factory.Simplex_16_2
      case Simplex_4_3 => bbox_factory.Simplex_4_3
      case Simplex_4_4 => bbox_factory.Simplex_4_4
      case Simplex_4_5 => bbox_factory.Simplex_4_5
      case Simplex_8_3 => bbox_factory.Simplex_8_3
      case Simplex_8_4 => bbox_factory.Simplex_8_4
      case Polyfit_2 => bbox_factory.Polyfit_2
      case Polyfit_3 => bbox_factory.Polyfit_3
      case Polyfit_4 => bbox_factory.Polyfit_4

    }


    Accel {
      val row_queue = FIFO[I](16)
      val rising_idx_queue = FIFO[I](16)
      val rising_v_queue = FIFO[T](16)
      val falling_idx_queue = FIFO[I](16)
      val falling_v_queue = FIFO[T](16)
      val volume_queue = FIFO[I](16)
      val first_val_queue = FIFO[T](16)
      val last_val_queue = FIFO[T](16)
      val delay_queue = FIFO[T](16)

      Stream.Foreach(NUM_LINES by 1){pt =>
        Pipe {
          if (pt % TS == 0) {
            row_queue load row_dram(pt :: pt + TS)
            rising_idx_queue load rising_idx_dram(pt :: pt + TS)
            rising_v_queue load rising_v_dram(pt :: pt + TS)
            falling_idx_queue load falling_idx_dram(pt :: pt + TS)
            falling_v_queue load falling_v_dram(pt :: pt + TS)
            volume_queue load volume_dram(pt :: pt + TS)
            first_val_queue load first_val_dram(pt :: pt + TS)
            last_val_queue load last_val_dram(pt :: pt + TS)
          }
        }

        Pipe {
          val row = row_queue.deq()
          val rising_idx = rising_idx_queue.deq()
          val falling_idx = falling_idx_queue.deq()
          val rising_v = rising_v_queue.deq()
          val falling_v = falling_v_queue.deq()
          val volume = volume_queue.deq()
          val first_val = first_val_queue.deq()
          val last_val = last_val_queue.deq()
          val fullfeatures = bbox_factory.FEATURES(row,rising_idx,falling_idx,volume,rising_v,falling_v,first_val,last_val)

          val filter = filter_box(fullfeatures)

//          val delayBox = if (filter.shouldKeep) bbox(fullfeatures) else DELAY(0)
          val delayBox = if (filter.shouldKeep) infer_box(fullfeatures) else bbox_factory.DELAY(0)

          delay_queue.enq(delayBox.delay)
        }

        Pipe{
          val out_queue = FIFO[T](16)
          out_queue.enq(delay_queue.deq())
          if (pt % TS == TS-1) {
            delays_dram(pt-TS+1::pt+1) store out_queue
          }
        }
      }
    }

    val delays_gold = Array.fill[T](8)(509.093.to[T]) //Array.tabulate(5){i => i}
    printArray(getMem(delays_dram), "got delays:" )
//    printArray(delays_gold, "wanted delays:")
    println("")
    println(r"label = 509.093")
//    println(r"OK: ${max_idx_gold == getMem(max_idx)}")
//    assert(max_idx_gold == getMem(max_idx))
  }
}

