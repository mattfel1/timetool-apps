import spatial.dsl._

@spatial object GEMM_VILIM extends SpatialApp {

  // Feel free to tweak this. You're under no obligation whatsoever to keep precisions anywhere as long as your final
  // result satisfies the requirements in GEMM.md
  type HI = FixPt[TRUE, _10, _22]
  type LOW = FixPt[TRUE, _1, _15]

  val N = 128

  override def main(args: Array[String]): Unit = {

    // Compute C (MxK) = A (MxN) x B (NxK)
    // MxN matrix
    val A_data = loadCSV2D[LOW]("A.csv")

    val A_DRAM = DRAM[LOW](N, N)
    setMem(A_DRAM, A_data)

    // NxK matrix
    val B_data = loadCSV2D[LOW]("B.csv")

    val B_DRAM = DRAM[LOW](N, N)
    setMem(B_DRAM, B_data)

    val C_DRAM = DRAM[HI](N * N)

    Accel {
      val aTile = SRAM[LOW](N, N)
      val bTile = SRAM[LOW](N, N)
      val cTile = FIFO[HI](N*2)

      Parallel{
        aTile load A_DRAM(0::N, 0::N)
        bTile load B_DRAM(0::N, 0::N)
      }

      Stream {
        Foreach(N by 1 par 1){ ii =>
          Foreach(N by 1 par 1){ jj =>
            val o = Reduce(Reg[HI])(N by 1 par 1){ kk =>
              aTile(ii, kk).to[HI] * bTile(kk, jj).to[HI]
            }{_+_}
            cTile.enq(o)
          }
        }
        C_DRAM(0::N*N) store cTile
      }
    }

    val mat = getMem(C_DRAM)
    val mat2 = Matrix.tabulate(N, N) { (i ,j) =>
      mat(i * N + j)
    }
    writeCSV2D(mat2, "output.csv")
  }
}

import spatial.dsl._
@spatial object crash extends SpatialApp {

  // Feel free to tweak this. You're under no obligation whatsoever to keep precisions anywhere as long as your final
  // result satisfies the requirements in GEMM.md
  type T = FixPt[TRUE, _10, _22]
  val M = 128
  val N = 128
  val P = 128

  override def main(args: Array[String]): Unit = {

    // Compute C (MxK) = A (MxN) x B (NxK)
    // MxN matrix
    val m = M
    val n = N
    val p = P
    val A_data = loadCSV2D[T]("A.csv")

    val A_DRAM = DRAM[T](M, P)
    setMem(A_DRAM, A_data)

    // NxK matrix
    val B_data = loadCSV2D[T]("B.csv")

    val B_DRAM = DRAM[T](P, N)
    setMem(B_DRAM, B_data)

    val C_DRAM = DRAM[T](M, N)

    val n_r = 4
    val m_c = 16
    val k_c = 16
    val n_r_par = 1
    val c_init = (0::M, 0::N){(_,_) => 0.to[T] }

    setMem(C_DRAM, c_init)

    Accel {
      val tileC = SRAM[T](M, N).buffer
      tileC load C_DRAM(0::M, 0::N par 16)
      Foreach(P by k_c) { k =>
        val tileA = SRAM[T](M, k_c)
        val tileB = SRAM[T](k_c, N)
        Parallel {
          tileA load A_DRAM(0::M, k::k+k_c par min(16,k_c))
          tileB load B_DRAM(k::k+k_c, 0::N par min(16,k_c))
        }

        Foreach(M by m_c) { local_m =>
          val tileA_ip = SRAM[T](m_c, k_c)
          val tileB_pj = SRAM[T](k_c, n_r)

          Foreach(m_c by 1, k_c by 1 par min(16,k_c)) { (copy_m, copy_k) => tileA_ip(copy_m, copy_k) = tileA(local_m + copy_m, copy_k) }

          Foreach(N by n_r) { local_n =>
            Foreach(k_c by 1, n_r by 1) { (copy_k, copy_n) => tileB_pj(copy_k, copy_n) = tileB(copy_k, local_n + copy_n) }
            val tileC_acc = RegFile[T](n_r,n_r).buffer
            Foreach(m_c by n_r){ accum_m =>
              Foreach(n_r by 1, n_r by 1 par n_r) { (copy_m, copy_n) =>
                tileC_acc(copy_m, copy_n) = tileC(local_m + accum_m + copy_m, local_n + copy_n)
              }

              MemFold(tileC_acc)(k_c by 1) { compute_k =>
                val tileC_partial = RegFile[T](n_r,n_r)
                Foreach(n_r by 1, n_r by 1 par n_r) { (compute_m, compute_n) =>
                  tileC_partial(compute_m, compute_n) = tileA_ip(compute_m, compute_k) * tileB_pj(compute_k, compute_n)
                }
                tileC_partial
              }{_+_}

              Foreach(n_r by 1, n_r by 1 par n_r) { (copy_m, copy_n) =>
                tileC(local_m + accum_m + copy_m, local_n + copy_n) = tileC_acc(copy_m, copy_n)
              }
            }
          }
        }
      }
      C_DRAM(0::M, 0::N par 16) store tileC
    }

    //val PAR_K = 2
    //val PAR_J = 2

    //val m = 16
    //val n = 16
    //val p = 16

    //Accel {
      //// Produce C in M x N tiles
      //Foreach(M by m, K by n) { (ii, jj) =>
        //val tileC = SRAM[T](m, n).buffer
        //tileC load C_DRAM(ii::ii+m, jj::jj+n par PAR_J)
        //// Combine intermediates across common dimension
        //MemFold(tileC)(M by p) { kk =>
          //// Allocate on-chip scratchpads
          //val tileA = SRAM[T](m, p)
          //val tileB = SRAM[T](p, n)
          //val accum = SRAM[T](m, n)

          //// Load tiles of A and B from DRAM
          //tileA load A_DRAM(ii :: ii + m, kk :: kk + p) // M x P
          //tileB load B_DRAM(kk :: kk + p, jj :: jj + n) // P x N

          //// Combine intermediates across a chunk of P
          //MemReduce(accum)(p by 1 par PAR_K) { k =>
            //val partC = SRAM[T](m, n)
            //Foreach(m by 1, n by 1 par PAR_J) { (i, j) =>
              //partC(i, j) = tileA(i, k) * tileB(k, j)
            //}
            //partC
            //// Combine intermediates with element-wise add
          //}{(a,b)=>a+b}
        //}{(a,b)=>a+b}

        //// Store the tile of C to DRAM
        //C_DRAM(ii :: ii + m, jj :: jj + n) store tileC
      //}
    //}

    val result = getMatrix(C_DRAM)
    writeCSV2D(getMatrix(C_DRAM), "output.csv")
  }
}
