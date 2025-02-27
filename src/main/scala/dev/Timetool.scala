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
          val delayBox = if (filter.shouldKeep) infer_box(fullfeatures) else bbox_factory.DELAY(fullfeatures.row, 0, Bit(false))

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


@spatial object Timetool_Aggregator extends SpatialApp {
//  override def runtimeArgs: Args = "0 157 341 35.2498 -28.1037 12039 12 0"
//  type T = FixPt[TRUE,_16,_16]
  import spatial.dsl._

  def main(args: Array[String]): Unit = {
    val bbox_factory = new Timetool_Boxes[_32, _16, _16]()
    type I = bbox_factory.I
    type T = bbox_factory.T
    type FEATURES = bbox_factory.FEATURES
    type DELAY = bbox_factory.DELAY
    type PRED = bbox_factory.PRED
    type DELAYPACKET = bbox_factory.DELAYPACKET

    val rows_per_image = 52
    assert(rows_per_image <= 52, "Only ripped the first 52 rows of a sample image for this app")
    val num_streams = 4
    val lines_per_image = rows_per_image / num_streams

    val aggregator_box = bbox_factory.Aggregator(rows_per_image, num_streams)

    val prediction_sample = Array[T](-716.3620.toUnchecked[T], -330.1214.toUnchecked[T], -519.684.toUnchecked[T], -896.4518.toUnchecked[T], -1077.711.toUnchecked[T], -890.712.toUnchecked[T], -513.6430.toUnchecked[T], 44.15193.toUnchecked[T], -323.927.toUnchecked[T], -1072.1175.toUnchecked[T], -1442.2030.toUnchecked[T], -1055.3090.toUnchecked[T], -305.31416.toUnchecked[T], -148.42493.toUnchecked[T], -710.4781.toUnchecked[T], -1265.2079.toUnchecked[T], -1259.7677.toUnchecked[T], -698.6960.toUnchecked[T], -142.08236.toUnchecked[T], 451.0909.toUnchecked[T], -129.38156.toUnchecked[T], -1248.8739.toUnchecked[T], -1791.3176.toUnchecked[T], -1153.378.toUnchecked[T], -91.15338.toUnchecked[T], 248.2987.toUnchecked[T], -507.59681.toUnchecked[T], -1431.6159.toUnchecked[T], -1603.9838.toUnchecked[T], -844.6271.toUnchecked[T], 70.19418.toUnchecked[T], 254.9741.toUnchecked[T], 50.654317.toUnchecked[T], -873.464.toUnchecked[T], -1614.2710.toUnchecked[T], -1410.3875.toUnchecked[T], -483.36309.toUnchecked[T], 876.7110.toUnchecked[T], 89.78333.toUnchecked[T], -1332.126.toUnchecked[T], -2058.3218.toUnchecked[T], -1326.2464.toUnchecked[T], 155.29917.toUnchecked[T], 645.245.toUnchecked[T], -286.6558.toUnchecked[T], -1524.68.toUnchecked[T], -1881.5067.toUnchecked[T], -959.0747.toUnchecked[T], 330.1995.toUnchecked[T], 694.3043.toUnchecked[T], 268.34211.toUnchecked[T], -1038.4596.toUnchecked[T])
    // Fill streams
    val stream0_rows = DRAM[I](lines_per_image)
    val stream0_delays = DRAM[T](lines_per_image)
    setMem(stream0_rows, Array.tabulate[I](lines_per_image){i => (i + 0).to[I]})
    setMem(stream0_delays, Array.tabulate[T](lines_per_image){i => prediction_sample(i)})
    val stream1_rows = DRAM[I](lines_per_image)
    val stream1_delays = DRAM[T](lines_per_image)
    setMem(stream1_rows, Array.tabulate[I](lines_per_image){i => (i + lines_per_image).to[I]})
    setMem(stream1_delays, Array.tabulate[T](lines_per_image){i => prediction_sample(i + lines_per_image)})
    val stream2_rows = DRAM[I](lines_per_image)
    val stream2_delays = DRAM[T](lines_per_image)
    setMem(stream2_rows, Array.tabulate[I](lines_per_image){i => (i + 2*lines_per_image).to[I]})
    setMem(stream2_delays, Array.tabulate[T](lines_per_image){i => prediction_sample(i + 2*lines_per_image)})
    val stream3_rows = DRAM[I](lines_per_image)
    val stream3_delays = DRAM[T](lines_per_image)
    setMem(stream3_rows, Array.tabulate[I](lines_per_image){i => (i + 3*lines_per_image).to[I]})
    setMem(stream3_delays, Array.tabulate[T](lines_per_image){i => prediction_sample(i + 3*lines_per_image)})

    val mean = ArgOut[T]
    val variance = ArgOut[T]

    Accel {

      Stream{
        // Stage 0: Load data
        val stream0_rows_fifo = FIFO[I](lines_per_image)
        val stream0_delays_fifo = FIFO[T](lines_per_image)
        stream0_rows_fifo load stream0_rows
        stream0_delays_fifo load stream0_delays
        val stream1_rows_fifo = FIFO[I](lines_per_image)
        val stream1_delays_fifo = FIFO[T](lines_per_image)
        stream1_rows_fifo load stream1_rows
        stream1_delays_fifo load stream1_delays
        val stream2_rows_fifo = FIFO[I](lines_per_image)
        val stream2_delays_fifo = FIFO[T](lines_per_image)
        stream2_rows_fifo load stream2_rows
        stream2_delays_fifo load stream2_delays
        val stream3_rows_fifo = FIFO[I](lines_per_image)
        val stream3_delays_fifo = FIFO[T](lines_per_image)
        stream3_rows_fifo load stream3_rows
        stream3_delays_fifo load stream3_delays

        // Stage 1: Pack data into structs
        val stream0 = FIFO[DELAY](lines_per_image)
        val stream1 = FIFO[DELAY](lines_per_image)
        val stream2 = FIFO[DELAY](lines_per_image)
        val stream3 = FIFO[DELAY](lines_per_image)
        Foreach(lines_per_image by 1){ i =>
          stream0.enq(bbox_factory.DELAY(stream0_rows_fifo.deq(), stream0_delays_fifo.deq(), Bit(true)))
          stream1.enq(bbox_factory.DELAY(stream1_rows_fifo.deq(), stream1_delays_fifo.deq(), Bit(true)))
          stream2.enq(bbox_factory.DELAY(stream2_rows_fifo.deq(), stream2_delays_fifo.deq(), Bit(true)))
          stream3.enq(bbox_factory.DELAY(stream3_rows_fifo.deq(), stream3_delays_fifo.deq(), Bit(true)))
        }

        // Stage 2: Aggregate
        val result = aggregator_box(bbox_factory.DELAYPACKET(stream0.deqInterface(), stream1.deqInterface(), stream2.deqInterface(), stream3.deqInterface()))

        // Stage 3: Report answer
        mean := result.mean
        variance := result.variance
      }
    }

    println(r"got: ${getArg(mean)}, ${getArg(variance)}")
    println(r"wanted: -665.62979, 1792.6974")

  }
}
