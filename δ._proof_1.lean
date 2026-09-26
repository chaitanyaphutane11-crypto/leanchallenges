import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Asymptotics Filter

------------------------------------------------------------------------
-- ⚙️ CONFIGURATION BLOCK (IRRATIONAL SILVER RATIO FIELDS)
------------------------------------------------------------------------

noncomputable def δ : ℝ := 1 + Real.sqrt 2
noncomputable def ψ_s : ℝ := 1 - Real.sqrt 2

noncomputable def s_seq (n : ℕ) : ℝ := (1 / (2 * Real.sqrt 2)) * δ^n - (1 / (2 * Real.sqrt 2)) * ψ_s^n
noncomputable def s_dom (n : ℕ) : ℝ := (1 / (2 * Real.sqrt 2)) * δ^n


------------------------------------------------------------------------
-- 🔬 ISOLATED BACKGROUND LEMMAS (PREVENTS WORKSPACE TIMEOUT CRASHES)
------------------------------------------------------------------------

lemma s_h1_helper (x : ℕ) (_hδ : δ ≠ 0) : ψ_s^x / δ^x = (ψ_s / δ)^x := by
  exact (div_pow ψ_s δ x).symm

lemma s_h_body_helper (x : ℕ) (hδ : δ ≠ 0) : 
    (- (1 / (2 * Real.sqrt 2)) * ψ_s^x) / ((1 / (2 * Real.sqrt 2)) * δ^x) = (ψ_s / δ)^x * (-1) := by
  have h_div : (- (1 / (2 * Real.sqrt 2)) * ψ_s^x) / ((1 / (2 * Real.sqrt 2)) * δ^x) = - (ψ_s^x / δ^x) := by
    have h_sqrt : (1 / (2 * Real.sqrt 2) : ℝ) ≠ 0 := by
      intro h
      have h2 : (2 : ℝ) > 0 := by norm_num
      have h_sq : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr h2
      have h_denom : 2 * Real.sqrt 2 > 0 := mul_pos (by norm_num) h_sq
      exact (ne_of_gt (one_div_pos.mpr h_denom) h).elim
    have : (- (1 / (2 * Real.sqrt 2)) * ψ_s^x) = (1 / (2 * Real.sqrt 2)) * (- (ψ_s^x)) := by ring
    rw [this, mul_div_mul_left _ _ h_sqrt]
    ring
  rw [h_div, s_h1_helper x hδ]
  ring


------------------------------------------------------------------------
-- 📊 THE ASYMPTOTIC SILVER RATIO THEOREM RESOLUTION
------------------------------------------------------------------------

theorem silver_ratio_ceiling_asymptotic : 
    (fun n => s_seq n - s_dom n) =o[atTop] s_dom := by
  -- Step A: Strip structural definitions via unfold
  unfold s_seq s_dom
  
  -- Step B: Cancel matching ring terms over the Real field
  have h_sub : (fun n => ((1 / (2 * Real.sqrt 2)) * δ^n - (1 / (2 * Real.sqrt 2)) * ψ_s^n) - (1 / (2 * Real.sqrt 2)) * δ^n) = 
               (fun n => - (1 / (2 * Real.sqrt 2)) * ψ_s^n) := by
    ext n
    ring
  rw [h_sub]
  
  -- Step C: Establish basic non-zero conditions for our Silver base
  have h2 : (2 : ℝ) > 0 := by norm_num
  have h_sqrt_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr h2
  have hδ_pos : δ > 0 := by
    unfold δ
    have : Real.sqrt 2 > 0 := h_sqrt_pos
    linarith
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  
  -- Step D: Convert little-o filter into quotient limits
  rw [isLittleO_iff_tendsto]
  · have h_body : (fun x => (- (1 / (2 * Real.sqrt 2)) * ψ_s^x) / ((1 / (2 * Real.sqrt 2)) * δ^x)) = (fun x => (ψ_s / δ)^x * (-1)) := by
      ext x
      exact s_h_body_helper x hδ_ne
    rw [h_body]
    
    -- Evaluate the geometric decay limit for our new irrational ratio base vector |ψ_s / δ| < 1
    have h_lim : Tendsto (fun x => ((ψ_s / δ)^x)) atTop (nhds 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      unfold ψ_s δ
      
      -- Open the absolute value bound and clear denominators linearly
      rw [abs_lt]
      have h_denom : 0 < 1 + Real.sqrt 2 := by
        have : Real.sqrt 2 > 0 := h_sqrt_pos
        linarith
      constructor
      · rw [lt_div_iff₀ h_denom]
        ring_nf
        linarith
      · -- FIX: Swap 'div_lt_iff_of_pos' with the verified Mathlib 4 name 'div_lt_iff₀'
        rw [div_lt_iff₀ h_denom]
        ring_nf
        have : Real.sqrt 2 > 0 := h_sqrt_pos
        linarith
      
    -- Combine with continuous multiplier vector topology using Tendsto.mul
    have h_scalar := Tendsto.mul h_lim (tendsto_const_nhds : Tendsto (fun _ => (-1 : ℝ)) atTop (nhds (-1)))
    simp only [zero_mul] at h_scalar
    exact h_scalar

  -- Step E: Confirm the non-vanishing property of the dominant silver pole
  · intro n h
    have h_pow_ne : δ^n ≠ 0 := pow_ne_zero n hδ_ne
    have h_coeff_ne : (1 / (2 * Real.sqrt 2) : ℝ) ≠ 0 := by
      intro hc
      have h_denom : 2 * Real.sqrt 2 > 0 := mul_pos (by norm_num) h_sqrt_pos
      exact (ne_of_gt (one_div_pos.mpr h_denom) hc).elim
    have h_prod_ne : (1 / (2 * Real.sqrt 2)) * δ^n ≠ 0 := mul_ne_zero h_coeff_ne h_pow_ne
    exact (h_prod_ne h).elim
