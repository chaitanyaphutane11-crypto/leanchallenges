import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Asymptotics Filter

------------------------------------------------------------------------
-- ⚙️ COMPUTABLE STRUCTURAL DEFINITIONS (100% COMPUTABLE OVER ℚ)
------------------------------------------------------------------------

def b (n : ℕ) : ℚ := (3 / 4 : ℚ) * (3 : ℚ)^n + (1 / 4 : ℚ) * (-1 : ℚ)^n

def b_dom (n : ℕ) : ℚ := (3 / 4 : ℚ) * (3 : ℚ)^n


------------------------------------------------------------------------
-- 🔬 ISOLATED BACKGROUND LEMMAS (PREVENTS WORKSPACE TIMEOUT CRASHES)
------------------------------------------------------------------------

lemma b_h1_helper (x : ℕ) : (-1 : ℝ)^x / (3 : ℝ)^x = (-1 / 3 : ℝ)^x := by
  exact (div_pow (-1 : ℝ) 3 x).symm

lemma b_h_body_helper (x : ℕ) : 
    (1 / 4 * (-1 : ℝ)^x) / (3 / 4 * (3 : ℝ)^x) = (-1 / 3 : ℝ)^x * (1 / 3) := by
  rw [← div_mul_div_comm, b_h1_helper]
  ring


------------------------------------------------------------------------
-- 📊 ASYMPTOTIC PROOF SECTION (EVALUATED OVER ℝ VIA COERCION CASTS)
------------------------------------------------------------------------

theorem structural_ceiling_asymptotic : 
    (fun n => (b n : ℝ) - (b_dom n : ℝ)) =o[atTop] (fun n => (b_dom n : ℝ)) := by
  -- Step A: Unfold sequence definitions
  unfold b b_dom
  
  -- Execute push_cast directly without redundant simp macros
  push_cast
  
  -- Step B: Cancel matching ring terms over the Real field
  have h_sub : (fun n => ((3 / 4 : ℝ) * (3 : ℝ)^n + (1 / 4 : ℝ) * (-1 : ℝ)^n) - (3 / 4 : ℝ) * (3 : ℝ)^n) = 
               (fun n => (1 / 4 : ℝ) * (-1 : ℝ)^n) := by
    ext n
    ring
  rw [h_sub]
  
  -- Step C: Convert the little-o filter into a quotient limit over ℝ
  rw [isLittleO_iff_tendsto]
  · have h_body : (fun x => (1 / 4 * (-1 : ℝ)^x) / (3 / 4 * (3 : ℝ)^x)) = (fun x => (-1 / 3 : ℝ)^x * (1 / 3)) := by
      ext x
      exact b_h_body_helper x
    rw [h_body]
    
    -- Invoke geometric sequence decay property over the Real field for base |-1/3| < 1
    have h_lim : Tendsto (fun x => ((-1 / 3 : ℝ)^x)) atTop (nhds 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      norm_num
      
    -- Multiply our decaying limit directly by a constant neighborhood limit
    have h_scalar := Tendsto.mul h_lim (tendsto_const_nhds : Tendsto (fun _ => (1 / 3 : ℝ)) atTop (nhds (1 / 3)))
    simp only [zero_mul] at h_scalar
    exact h_scalar

  -- Step D: Resolve the non-vanishing denominator implication
  · intro n h
    change (3 / 4 : ℝ) * (3 : ℝ)^n = 0 at h
    have h_nonzero : (3 / 4 : ℝ) * (3 : ℝ)^n ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact pow_ne_zero n (by norm_num)
    have h_false : False := h_nonzero h
    exact h_false.elim


------------------------------------------------------------------------
-- ⚙️ LIVE CONSOLE PRINTING (EXECUTED ON THE CPU)
------------------------------------------------------------------------

#eval b 0
#eval b 1
#eval b 2
#eval b 3
#eval b 4
#eval b 5

-- FIX: Explicitly supply the natural range list to evaluate the full functional map
#eval List.map (fun n => (n, b n, b_dom n)) [0, 1, 2, 3, 4, 5]
