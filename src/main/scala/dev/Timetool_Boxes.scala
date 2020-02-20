package spatial.tests.dev

import spatial.libdsl._
import argon.{Cast}

object XGMeta {
  def scalaIfElse[T](cond: scala.Boolean, ift: => T, iff: => T): T = {
    if (cond) ift else iff
  }
}

class Timetool_Boxes[IDX <: INT[_], DEC <: INT[_], FRAC <: INT[_]]
()(implicit state: argon.State, ev1: argon.Type[FixPt[FALSE, IDX, _0]],
                                ev2: argon.Type[FixPt[TRUE, DEC, FRAC]],
                                ev3: spatial.lang.Bits[FixPt[TRUE, DEC, FRAC]],
                                c1: Cast[scala.Int, FixPt[FALSE, IDX, _0]],
                                c2: Cast[FixPt[FALSE, IDX, _0], FixPt[TRUE, DEC, FRAC]],
                                c3: Cast[scala.Int, FixPt[TRUE, DEC, FRAC]],
                                c4: Cast[scala.Double, FixPt[TRUE, DEC, FRAC]],
                                c5: Cast[scala.Double, FixPt[FALSE, IDX, _0]],
                                c6: Cast[FixPt[TRUE, DEC, FRAC], FixPt[FALSE, _3, _16]],
                                c7: Cast[FixPt[FALSE, _3, _16], FixPt[TRUE, DEC, FRAC]],
                                c8: Cast[FixPt[FALSE, _0, _16], FixPt[TRUE, DEC, FRAC]],
                                c9: Cast[FixPt[TRUE, DEC, FRAC], FixPt[TRUE, _32, _16]],
                                c10: Cast[FixPt[TRUE, _32, _16], FixPt[TRUE, DEC, FRAC]],
                                c11: Cast[FixPt[FALSE, IDX, _0], FixPt[TRUE, _32, _16]],
                                c12: Cast[FixPt[FALSE, IDX, _0], I32],
) {
  type I = FixPt[FALSE, IDX, _0]
  type T = FixPt[TRUE, DEC, FRAC]
  type H = FixPt[TRUE,_32,_16]
  type ResidualType = FixPt[FALSE, _0, _16]
  type AccumResidualType = FixPt[FALSE, _3, _16]
  type ParameterIndex = FixPt[FALSE, _10, _0]
  @struct case class FEATURES(row: I, rising_idx: I, falling_idx: I, volume: I, rising_weight: T, falling_weight: T, first_val: T, last_val: T)
  @struct case class DELAY(row: I, delay: T, valid: Bit)
  @streamstruct case class DELAYPACKET(stream0: DELAY, stream1: DELAY, stream2: DELAY, stream3: DELAY)
  @streamstruct case class PRED(mean: T, variance: T)

  @struct case class KEEP(shouldKeep: Bit)

  // Filter helpers
  def filter_unit = Blackbox.SpatialPrimitive[FEATURES, KEEP] { in: FEATURES =>
    val shouldNotKeep = in.rising_idx === 0 || in.falling_idx === 0 || (in.first_val > 30.to[T] && in.last_val > 30.to[T]) || (in.falling_idx - in.rising_idx < 100.to[I])
    KEEP(!shouldNotKeep)
  }

  def getField(ft: FEATURES, field: String): T = field match {
    case "row" => ft.row.to[T]
    case "rising_idx" => ft.rising_idx.to[T]
    case "falling_idx" => ft.falling_idx.to[T]
    case "volume" => (ft.volume / 4096.to[I]).to[T]
    case "rising_weight" => ft.rising_weight.to[T]
    case "falling_weight" => ft.falling_weight.to[T]
    case "first_val" => ft.first_val.to[T]
    case "last_val" => ft.last_val.to[T]
  }

  // Lattice helpers
  private def spatial_sort(dimensions: scala.Int, strides: Seq[scala.Int], inputs: (Int => ResidualType)): (Array[ResidualType], Array[ParameterIndex]) = {
    var values: Array[ParameterIndex] = null
    var keys: Array[ResidualType] = null
    SimplexHelper.sort(dimensions).zipWithIndex foreach { case (stage, stage_index) =>
      val new_indices = Array.fill[ParameterIndex](dimensions) { null }
      val new_values = Array.fill[ResidualType](dimensions) { null }

      SimplexHelper.compute_complement(stage, dimensions) foreach { pass =>
        if (stage_index == 0) {
          new_indices(pass) = strides(pass).to[ParameterIndex]
          new_values(pass) = inputs(pass)
        } else {
          new_indices(pass) = values(pass)
          new_values(pass) = keys(pass)
        }
      }
      stage foreach {
        pair => {
          val a = if (stage_index == 0) inputs(pair._1) else keys(pair._1)
          val b = if (stage_index == 0) inputs(pair._2) else keys(pair._2)
          val a_ind: ParameterIndex = if (stage_index == 0) strides(pair._1).to[ParameterIndex] else values(pair._1)
          val b_ind: ParameterIndex = if (stage_index == 0) strides(pair._2).to[ParameterIndex] else values(pair._2)

          val cmp = a > b

          new_values(pair._1) = spatial.dsl.mux(cmp, a, b)
          new_values(pair._2) = spatial.dsl.mux(cmp, b, a)
          new_indices(pair._1) = spatial.dsl.mux(cmp, a_ind, b_ind)
          new_indices(pair._2) = spatial.dsl.mux(cmp, b_ind, a_ind)
        }
      }
      keys = new_values
      values = new_indices
    }

    (keys, values)
  }

  private def PrefixSumHillisSteele(vals: Array[ParameterIndex]): Array[ParameterIndex] = {
    val current = vals.clone
    val log2_length = ((0 to (vals.length - 1)) find { 1 << _ >= vals.length }).get
    List.tabulate(log2_length, vals.length) { (i, j) =>
      if (!(j < (1 << i))) current(j) = current(j) + current(j - (1 << i))
    }
    current
  }

  private def allCorners(maxes: Seq[scala.Int], partials: Seq[Seq[scala.Int]] = Seq(Seq.empty)): Seq[Seq[scala.Int]] = maxes match {
    case Nil => Nil
    case h::tail if tail.nonEmpty => (0 to h).flatMap{i => allCorners(tail, partials.map(_ ++ Seq(i)))}
    case h::tail if tail.isEmpty => (0 to h).flatMap{i => partials.map(_ ++ Seq(i))}
  }
  class Calibrator(input_breakpoints: Seq[Double], output_values: Seq[Double]) {
    def evaluate(pt: T): AccumResidualType = {
      val ranges_bitvector = input_breakpoints.zipWithIndex.map{case (edge, i) =>
        if (i == 0) pt < edge.to[T]
        else if (i == input_breakpoints.length-1) pt >= edge.to[T]
        else pt >= input_breakpoints(i-1).to[T] && pt < edge.to[T]
      }
      val computed_values = input_breakpoints.zipWithIndex.map{case (edge, i) =>
        if (i == 0) output_values(0).to[T]
        else if (i == input_breakpoints.length-1) output_values.last.to[T]
        else (pt - input_breakpoints(i-1).to[T]) * ((output_values(i) - output_values(i-1)) / (edge - input_breakpoints(i-1))).to[T]
      }
      oneHotMux(ranges_bitvector, computed_values).to[AccumResidualType]
    }
  }
  abstract class Lattice_Model(calibs: Map[String,Calibrator], dimensions: scala.Int, size: scala.Int) {
    def strides: Seq[scala.Int] = {
      val strides: Array[Int] = Array.fill(dimensions){1}
      (1 to (dimensions - 1)) foreach {d => strides(d) = strides(d-1) * size }
      strides.toSeq
    }
    def calibrate(ft: FEATURES, field: String): AccumResidualType = calibs(field).evaluate(getField(ft,field))
    def evaluate(ft: FEATURES): T
  }
  class Simplex(val calibs: Map[String,Calibrator], val dimensions: scala.Int, val size: scala.Int, val params: Seq[Double]) extends Lattice_Model(calibs, dimensions, size) {
    def evaluate(in: FEATURES): T = {
      val input = calibs.map{case (k,v) => v.evaluate(getField(in,k))}.toSeq
      val corners = Array.tabulate(dimensions) {input(_).to[ParameterIndex]}

      // Extends residuals by 1 bit.
      val (sorted_residuals, sorted_strides) = spatial_sort(dimensions, strides, input(_).to[ResidualType])
      var lower_index = corners.map { corner => corner * size.to[ParameterIndex] }.reduce {_ + _}
      var upper_index = lower_index + (size * dimensions).to[ParameterIndex]
      // Compute Bidirectional Simplex Interpolation
      val weights: Seq[ResidualType] = (0.to[ResidualType] :: sorted_residuals.toList) zip (sorted_residuals.toList :+ 0.to[ResidualType]) map {case (a, b) => a - b}
      val midpoint = weights.size / 2
      var total_lower = 0.to[T]
      var total_upper = 0.to[T]

      (0 to midpoint - 1) foreach {dim =>
        Console.println(s"step $dim forward ${lower_index}")
        total_lower = total_lower + weights(dim).to[T] * oneHotMux(Seq.tabulate(params.length){j => j.toUnchecked[ParameterIndex] === lower_index}, params.map(_.to[T]))
        lower_index = lower_index + sorted_strides(dim)
      }

      (weights.size - 1 to midpoint by -1) foreach { dim =>
        Console.println(s"step $dim backward ${upper_index}")
        total_upper = total_upper + weights(dim).to[T] * oneHotMux(Seq.tabulate(params.length){j => j.toUnchecked[ParameterIndex] === upper_index}, params.map(_.to[T]))
        upper_index = upper_index - sorted_strides(dim - 1)
      }
      total_lower + total_upper
    }
  }
  class Hypercube(val calibs: Map[String,Calibrator], val dimensions: scala.Int, val size: scala.Int, val params: Seq[Double]) extends Lattice_Model(calibs, dimensions, size) {
    def evaluate(in: FEATURES): T = {
      val ft = calibs.map{case (k,v) => v.evaluate(getField(in,k))}.toSeq
      val residualPairs = ft.map{ x => Seq(x, 1.to[AccumResidualType] - x)}.toSeq
      // Compute all hypervolumes in binary counting order (000, 001, 010, 011, etc..)
      val hypervolumes: Seq[AccumResidualType] = utils.math.CombinationTree(residualPairs:_*)(_*_)
      // Compute hypercube origin
      val base: Seq[ParameterIndex] = ft.map {x => x.to[ParameterIndex]}
      // Get all vertices of hypercube and reverse so that these are opposite the hypervolumes (i.e. 0,0  0,1  1,0  1,1 for a 2d lattice).  These are used as offsets
      val corners: Seq[Seq[scala.Int]] = allCorners(Seq.fill(dimensions)(1)).reverse

      // Get flat index for each (corner + origin)
      val indices: Seq[ParameterIndex] = corners map { c =>
        val corner = (base zip c.map(_.to[ParameterIndex])) map {case (a,b) => a + b}
        corner.zip(strides)  map { case (cc,s) =>
          cc * s
        } reduce {_+_}
      }

      // Get weighted sum
      hypervolumes.map(_.to[T]).zip(indices).map{case (hv,i) => hv * oneHotMux(Seq.tabulate(params.length){j => j.to[ParameterIndex] === i}, params.map(_.to[T]))}.reduceTree {_+_}
    }

  }

  // FC-NN Helpers
  private def center(in: FEATURES, mean: FEATURES): Seq[T] = {
    val row = in.row - mean.row
    val rising_idx = in.rising_idx - mean.rising_idx
    val falling_idx = in.falling_idx - mean.falling_idx
    val rising_weight = in.rising_weight - mean.rising_weight
    val falling_weight = in.falling_weight - mean.falling_weight
    val volume = (in.volume - mean.volume) / 4096.to[I]
    val first_val = in.first_val - mean.first_val
    val last_val = in.last_val - mean.last_val
    Seq(row.to[T], rising_idx.to[T], falling_idx.to[T], volume.to[T], rising_weight.to[T], falling_weight.to[T], first_val.to[T], last_val.to[T])
  }
  private def forward_prop(features: Seq[T], lxDims: List[scala.Int], lxW: List[Seq[T]], lxB: List[Seq[T]], lxAct: List[T => T]): T = {
    val activations = scala.collection.mutable.ListBuffer.fill[Seq[T]](lxW.length)(Seq[T]())
    List.tabulate(lxDims.length) {i =>
      val input: Seq[T] = if (i == 0) features else activations(i-1)
      val cols = lxDims(i)
      val rows = lxW(i).length / cols
      println(s"$input")
      println(s"$rows $cols for ${lxDims(i)}, ${lxW(i)}")
      activations(i) = Seq.tabulate(cols) {ii =>
        val weights: Seq[T] = List.tabulate(rows) { jj => lxW(i)(jj * cols + ii) }
        lxAct(i)(weights.zip(input).map{case (a,b) => a * b}.reduceTree{_ + _} + lxB(i)(ii))
      }
    }
    activations.last.head
  }
  private def RELU(x: T): T = mux(x <= 0.to[T], 0.to[T], x)
  private def LeakyRELU(x: T): T = mux(x <= 0.to[T], x * 0.125.to[T], x)

  // XGBoost helpers
  private class TreeNode(field: java.lang.String, thresh: T, leftTree: Either[TreeNode, T], rightTree: Either[TreeNode, T]) {
    def evaluate(sample: FEATURES): T = {
      val point: T = getField(sample, field)
      mux(point < thresh,
        {
          leftTree match {
            case Left(tn) => tn.evaluate(sample)
            case Right(term) => term
          }
        },
        {
          rightTree match {
            case Left(tn) => tn.evaluate(sample)
            case Right(term) => term
          }
        }
      )
    }
  }

  private def buildTree(idx: scala.Int, params: scala.List[(java.lang.String, T)]): Either[TreeNode, T] = {
    XGMeta.scalaIfElse[Either[TreeNode, T]](params(idx)._1.equals(""),
      Right(params(idx)._2),
      {
        val leftIdx = idx * 2 + 1
        val rightIdx = idx * 2 + 2
        assert(leftIdx < params.length && rightIdx < params.length, "Your params are screwed up.  Is there an unterminated node?")
        val leftRoot = buildTree(leftIdx, params)
        val rightRoot = buildTree(rightIdx, params)

        Left(new TreeNode(params(idx)._1, params(idx)._2, leftRoot, rightRoot))
      }
    )
  }

  // Poly helpers
  private def compute(pt: T, model: Seq[T]): T = {
    model.reverse.zipWithIndex.map{case (m,i) =>
      val pow = if (i > 0) List.tabulate(i){k => pt/128.to[T]}.reduceTree(_*_)
                else 1.to[T]
      pow * m
    }.reduceTree{_+_}
  }


  // Blackbox Implementations
  def NN_64_RELU = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_64_RELU_Raw_Data.NN_64_RELU_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B) = NN_64_RELU_Raw_Data.NN_64_RELU_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(64,1), List(l1W, l2W), List(l1B, l2B), List(RELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_64_Leaky = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_64_Leaky_Raw_Data.NN_64_Leaky_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B) = NN_64_Leaky_Raw_Data.NN_64_Leaky_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(64,1), List(l1W, l2W), List(l1B, l2B), List(LeakyRELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_32_32_RELU = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_32_32_RELU_Raw_Data.NN_32_32_RELU_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B, l3W, l3B) = NN_32_32_RELU_Raw_Data.NN_32_32_RELU_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(32,32,1), List(l1W, l2W, l3W), List(l1B, l2B, l3B), List(RELU, RELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_32_32_Leaky = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_32_32_Leaky_Raw_Data.NN_32_32_Leaky_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B, l3W, l3B) = NN_32_32_Leaky_Raw_Data.NN_32_32_Leaky_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(32,32,1), List(l1W, l2W, l3W), List(l1B, l2B, l3B), List(LeakyRELU, LeakyRELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_16_16_RELU = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_16_16_RELU_Raw_Data.NN_16_16_RELU_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B, l3W, l3B) = NN_16_16_RELU_Raw_Data.NN_16_16_RELU_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(16,16,1), List(l1W, l2W, l3W), List(l1B, l2B, l3B), List(RELU, RELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_16_16_Leaky = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_16_16_Leaky_Raw_Data.NN_16_16_Leaky_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B, l3W, l3B) = NN_16_16_Leaky_Raw_Data.NN_16_16_Leaky_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(16,16,1), List(l1W, l2W, l3W), List(l1B, l2B, l3B), List(LeakyRELU, LeakyRELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_8_8_RELU = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_8_8_RELU_Raw_Data.NN_8_8_RELU_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B, l3W, l3B) = NN_8_8_RELU_Raw_Data.NN_8_8_RELU_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(8,8,1), List(l1W, l2W, l3W), List(l1B, l2B, l3B), List(RELU, RELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_4_4_RELU = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_4_4_RELU_Raw_Data.NN_4_4_RELU_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B, l3W, l3B) = NN_4_4_RELU_Raw_Data.NN_4_4_RELU_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(4,4,1), List(l1W, l2W, l3W), List(l1B, l2B, l3B), List(RELU, RELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_16_4_RELU = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_16_4_RELU_Raw_Data.NN_16_4_RELU_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B, l3W, l3B) = NN_16_4_RELU_Raw_Data.NN_16_4_RELU_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(16,4,1), List(l1W, l2W, l3W), List(l1B, l2B, l3B), List(RELU, RELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }
  def NN_8_4_RELU = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val mean_values = NN_8_4_RELU_Raw_Data.NN_8_4_RELU_mean[I,T]({x => x.to[I]}, {x => x.to[T]})
    val mean = FEATURES(mean_values._1,mean_values._2,mean_values._3,mean_values._4,mean_values._5,mean_values._6,mean_values._7,mean_values._8)
    val (l1W, l1B, l2W, l2B, l3W, l3B) = NN_8_4_RELU_Raw_Data.NN_8_4_RELU_layers[T](x => x.toSaturating[T])

    val features = center(in, mean)
    val result = forward_prop(features, List(8,4,1), List(l1W, l2W, l3W), List(l1B, l2B, l3B), List(RELU, RELU, {x => x}))

    DELAY(in.row, result, Bit(true))
  }

  def XGBoost_10_5 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_10s.XGBoost_10_5_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_20_5 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_20_5.XGBoost_20_5_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_25_5 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_25s.XGBoost_25_5_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_10_6 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_10s.XGBoost_10_6_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_20_6 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_20_6.XGBoost_20_6_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_40_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_40s.XGBoost_40_4_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_64_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_64_4.XGBoost_64_4_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_96_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_96_4.XGBoost_96_4_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_128_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_128_4.XGBoost_128_4_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }
  def XGBoost_128_3 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val trees = XGBoost_Raw_Data_128_3.XGBoost_128_3_trees[T](x => x.toSaturating[T])
    DELAY(in.row, trees.map { t =>
      val root = buildTree(0, t)
      root.left.get.evaluate(in)
    }.reduceTree {_ + _} + 0.5.to[T], Bit(true))
  }

  def Simplex_4_2 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 4
    val size = 2
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Simplex(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Simplex_8_2 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 8
    val size = 2
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Simplex(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Simplex_16_2 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 16
    val size = 2
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Simplex(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Simplex_4_3 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 4
    val size = 3
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Simplex(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Simplex_4_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 4
    val size = 4
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Simplex(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
    def Simplex_4_5 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 4
    val size = 5
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Simplex(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Simplex_8_3 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 8
    val size = 3
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Simplex(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))  }
  def Simplex_8_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 8
    val size = 4
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Simplex(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }

  def Hypercube_4_2 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 4
    val size = 2
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Hypercube(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Hypercube_8_2 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 8
    val size = 2
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Hypercube(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Hypercube_16_2 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 16
    val size = 2
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Hypercube(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Hypercube_4_3 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 4
    val size = 3
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Hypercube(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))  }
  def Hypercube_4_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 4
    val size = 4
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Hypercube(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
    def Hypercube_4_5 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 4
    val size = 5
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Hypercube(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }
  def Hypercube_8_3 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 8
    val size = 3
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Hypercube(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))  }
  def Hypercube_8_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val num_keypoints = 8
    val size = 4
    val calibs = Map(
      "rising_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "falling_idx" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "first_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
      "last_val" -> new Calibrator(Seq.tabulate(num_keypoints){i => 0.1 + i}, Seq.tabulate(num_keypoints){i => 0.1 + i}),
    )
    val network = new Hypercube(calibs, 4, size, Seq.tabulate(scala.math.pow(size,4).toInt){ i => 0.1 + i })
    DELAY(in.row, network.evaluate(in), Bit(true))
  }

  def Polyfit_2 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val (rising_model, falling_model) = Polyfit_Raw_Data.Polyfit_2_params[T](x => x.toSaturating[T])
    val rising_pred = compute(in.rising_idx.to[T], rising_model)
    val falling_pred = compute(in.falling_idx.to[T], falling_model)
    val full_pred = oneHotMux(Seq(in.first_val < 30.to[T] && in.last_val < 30.to[T], in.first_val < 30.to[T] && in.last_val >= 30.to[T], in.first_val >= 30.to[T] && in.last_val < 30.to[T]),
                              Seq((rising_pred + falling_pred)/2.to[T], rising_pred, falling_pred))
    DELAY(in.row, full_pred, Bit(true))
  }
  def Polyfit_3 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val (rising_model, falling_model) = Polyfit_Raw_Data.Polyfit_3_params[T](x => x.toSaturating[T])
    val rising_pred = compute(in.rising_idx.to[T], rising_model)
    val falling_pred = compute(in.falling_idx.to[T], falling_model)
    val full_pred = oneHotMux(Seq(in.first_val < 30.to[T] && in.last_val < 30.to[T], in.first_val < 30.to[T] && in.last_val >= 30.to[T], in.first_val >= 30.to[T] && in.last_val < 30.to[T]),
                              Seq((rising_pred + falling_pred)/2.to[T], rising_pred, falling_pred))
    DELAY(in.row, full_pred, Bit(true))
  }
  def Polyfit_4 = Blackbox.SpatialPrimitive[FEATURES, DELAY] { in: FEATURES =>
    val (rising_model, falling_model) = Polyfit_Raw_Data.Polyfit_4_params[T](x => x.toSaturating[T])
    val rising_pred = compute(in.rising_idx.to[T], rising_model)
    val falling_pred = compute(in.falling_idx.to[T], falling_model)
    val full_pred = oneHotMux(Seq(in.first_val < 30.to[T] && in.last_val < 30.to[T], in.first_val < 30.to[T] && in.last_val >= 30.to[T], in.first_val >= 30.to[T] && in.last_val < 30.to[T]),
                              Seq((rising_pred + falling_pred)/2.to[T], rising_pred, falling_pred))
    DELAY(in.row, full_pred, Bit(true))
  }

  def Aggregator(num_rows: scala.Int, num_streams: scala.Int) = Blackbox.SpatialController[DELAYPACKET, PRED] { in : DELAYPACKET =>
    @struct case class AGG(count: I, x: H, x2: H)
    implicit class AggHelp(a: AGG) {
      def +(b: AGG): AGG = AGG(a.count + b.count, a.x + b.x, a.x2 + b.x2)
    }
    val deltas = LUT[T](108)(0.0.toUnchecked[T], -366.63.toUnchecked[T], -183.32.toUnchecked[T], 183.31.toUnchecked[T], 366.63.toUnchecked[T], 183.31.toUnchecked[T], -183.32.toUnchecked[T], -733.26.toUnchecked[T], -366.63.toUnchecked[T],
      366.63.toUnchecked[T], 733.26.toUnchecked[T], 366.63.toUnchecked[T], -366.63.toUnchecked[T], -549.95.toUnchecked[T], 0.0.toUnchecked[T], 549.94.toUnchecked[T], 549.94.toUnchecked[T], 0.0.toUnchecked[T], -549.95.toUnchecked[T], -1099.895.toUnchecked[T],
      -549.95.toUnchecked[T], 549.94.toUnchecked[T], 1099.89.toUnchecked[T], 549.94.toUnchecked[T], -549.95.toUnchecked[T], -916.58.toUnchecked[T], -183.32.toUnchecked[T], 733.26.toUnchecked[T], 916.57.toUnchecked[T], 183.31.toUnchecked[T], -733.26.toUnchecked[T],
      -916.58.toUnchecked[T], -733.26.toUnchecked[T], 183.31.toUnchecked[T], 916.57.toUnchecked[T], 733.26.toUnchecked[T], -183.32.toUnchecked[T], -1466.525.toUnchecked[T], -733.26.toUnchecked[T], 733.26.toUnchecked[T], 1466.52.toUnchecked[T], 733.26.toUnchecked[T],
      -733.26.toUnchecked[T], -1283.21.toUnchecked[T], -366.63.toUnchecked[T], 916.57.toUnchecked[T], 1283.2.toUnchecked[T], 366.63.toUnchecked[T], -916.58.toUnchecked[T], -1283.21.toUnchecked[T], -916.58.toUnchecked[T], 366.63.toUnchecked[T], 1283.2.toUnchecked[T],
      916.57.toUnchecked[T], -366.63.toUnchecked[T], -1099.895.toUnchecked[T], 0.0.toUnchecked[T], 1099.89.toUnchecked[T], 1099.89.toUnchecked[T], 0.0.toUnchecked[T], -1099.895.toUnchecked[T], -1833.15477.toUnchecked[T], -916.58.toUnchecked[T], 916.57.toUnchecked[T],
      1833.15.toUnchecked[T], 916.57.toUnchecked[T], -916.58.toUnchecked[T], -1649.84.toUnchecked[T], -549.95.toUnchecked[T], 1099.89.toUnchecked[T], 1649.83.toUnchecked[T], 549.94.toUnchecked[T], -1099.895.toUnchecked[T], -1649.84.toUnchecked[T], -1099.895.toUnchecked[T],
      549.94.toUnchecked[T], 1649.83.toUnchecked[T], 1099.89.toUnchecked[T], -549.95.toUnchecked[T], -1283.21.toUnchecked[T], 183.31.toUnchecked[T], 1466.52.toUnchecked[T], 1283.2.toUnchecked[T], -183.32.toUnchecked[T], -1466.525.toUnchecked[T], -1283.21.toUnchecked[T],
      -1466.525.toUnchecked[T], -183.32.toUnchecked[T], 1283.2.toUnchecked[T], 1466.52.toUnchecked[T], 183.31.toUnchecked[T], -1649.84.toUnchecked[T], 0.0.toUnchecked[T], 1649.83.toUnchecked[T], 1649.83.toUnchecked[T], 0.0.toUnchecked[T], -1649.84.toUnchecked[T], -1833.15479.toUnchecked[T],
      -366.63.toUnchecked[T], 1466.52.toUnchecked[T], 1833.15.toUnchecked[T], 366.63.toUnchecked[T], -1466.525.toUnchecked[T], -1833.15475.toUnchecked[T], 1466.525.toUnchecked[T], 366.63.toUnchecked[T], 1833.15.toUnchecked[T], 1466.52.toUnchecked[T], -366.63.toUnchecked[T])
    def DELAY_TO_AGG(x: DELAY): AGG = mux(x.valid,
                          AGG(1.to[I], (deltas(x.row.to[I32]) + x.delay).to[H], (deltas(x.row.to[I32]) + x.delay).to[H] * (deltas(x.row.to[I32]) + x.delay).to[H]),
                          AGG(0.to[I], 0.to[H], 0.to[H]))
    val mean = FIFO[T](8)
    val variance = FIFO[T](8)
    Pipe{
      val aggregates = Reg[AGG](AGG(0.to[I],0.to[H],0.to[H]))
      Reduce(aggregates)(num_rows / num_streams by 1){i =>
        val pt0 = in.stream0
        val pt1 = in.stream1
        val pt2 = in.stream2
        val pt3 = in.stream3
        List(DELAY_TO_AGG(pt0), DELAY_TO_AGG(pt1), DELAY_TO_AGG(pt2), DELAY_TO_AGG(pt3)).reduceTree{_+_}
      }{case (a: AGG, b: AGG) => a + b}
      val agg = aggregates.value
      val m = agg.x / agg.count.to[H]
      val E2x = pow(m.to[H], 2)
      val Ex2 = agg.x2 / agg.count.to[H]
      mean.enq(m.to[T])
      variance.enq((Ex2 - E2x).to[T])
    }
    PRED(mean.deqInterface(), variance.deqInterface())
  }
}
