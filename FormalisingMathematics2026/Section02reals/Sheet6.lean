/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2026.Solutions.Section02reals.Sheet5
-- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  unfold TendsTo at *
  intro ε hε
  specialize h (ε/37) (by linarith) 
  rcases h with ⟨b0, h'⟩
  use b0 
  intro n hn 
  change |37 * a n - 37 * t| < ε
  specialize h' n hn 
  calc |37 * a n - 37 * t| = |37*(a n - t)| := by rw[mul_sub]
              _             = |37| * |a n - t| := by exact abs_mul 37 (a n - t)
              _             = 37*|a n - t| := by rw [abs_of_pos (by positivity)]
              _             < 37* (ε/37) := by apply mul_lt_mul_of_pos_left h' (by positivity)
              _             = ε := by field_simp

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  unfold TendsTo at * 
  intro ε hε
  specialize h (ε/c) (by exact div_pos hε hc)
  rcases h with ⟨b, hb⟩
  use b
  intro n hn 
  specialize hb n hn
  change |c * a n - c*t| < ε
  calc |c * a n - c*t| = |c*(a n - t)| := by rw[mul_sub c _ _ ]
          _            = |c| * |a n - t| := by rw[abs_mul c _]
          _            = c * |a n - t| := by rw [abs_of_pos hc]
          _            < c * (ε/c) := by exact mul_lt_mul_of_pos_left hb hc
          _            = c* ε/c := by exact mul_div_assoc' c ε c
          _            = ε := by field_simp

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  unfold TendsTo at * 
  intro ε hε
  have hc': 0 < -c := by linarith
  specialize h (ε / (-c)) (div_pos hε hc')
  rcases h with ⟨b, hb⟩
  use b
  intro n hn 
  specialize hb n hn
  change |c * a n - c*t| < ε
  calc |c * a n - c*t| = |c*(a n - t)| := by rw[mul_sub c _ _ ]
          _            = |c| * |a n - t| := by rw[abs_mul c _]
          _            = -c * |a n - t| := by rw [abs_of_neg hc]
          _            < -c * (ε/(-c)) := by exact mul_lt_mul_of_pos_left hb hc'
          _            = ε := by
                              have h0 : c ≠ 0 := by exact hc.ne
                              field_simp

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · exact tendsTo_neg_const_mul h hc
  · subst hc
    simpa using tendsTo_const 0
  · exact tendsTo_pos_const_mul h hc

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
/- change TendsTo (fun n ↦ a n * c) (c * t) -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  have hc: t*c = c*t := by ring_nf 
  have h2 := tendsTo_const_mul c h 
  simp only [mul_comm c ] at h2 
  exact h2
  
-- alternatively we can also do this 
theorem tendsTo_mul_const_tw {a: ℕ→ℝ} {t: ℝ} (c: ℝ) (h: TendsTo a t):
    TendsTo (fun n ↦ a n * c) (t * c) := by 
    rw [mul_comm t _]
    have h': (fun n ↦ a n * c ) = (fun n ↦ c * a n) := by 
      funext n -- intro fo function binders
      rw [mul_comm (a n) _]
    rw [h']
    exact tendsTo_const_mul c h

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

theorem basic_triangle (a b: ℝ): |a + b| <= |a| + |b| := by 
  sorry

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  intro ε hε
  specialize h1 (ε/2) (by linarith)
  specialize h2 (ε/2) (by linarith)
  rcases h1 with ⟨b1, hb1⟩
  rcases h2 with ⟨b2, hb2⟩
  use max b1 b2
  intro n hn 
  rw [max_le_iff] at hn
  specialize hb1 n hn.1
  specialize hb2 n hn.2
  change (|a n - b n - t| < ε/2) at hb1
  calc |a n - (t + u)| = |a n + 0 - t - u| := by ring_nf
          _            = |(a n - b n - t) + (b n - u)| := by ring_nf
          _           <= |a n - b n - t| + |b n - u| := by 
                                      /- exact basic_triangle (a n - b n - t) (b n - u) -/
                                      exact basic_triangle _ _ 
          _           <  ε/2 + ε/2 := by gcongr 
          _           = ε := by linarith 

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  
  have h': TendsTo (fun n => t) t := by exact tendsTo_const t
  constructor
  · intro h 
    simpa using tendsTo_sub h h'
  · intro h 
    simpa using tendsTo_add h h'

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  unfold TendsTo
  intro ε hε
  specialize ha (√ε) (by exact Real.sqrt_pos.mpr hε)
  rcases ha with ⟨ba, hba⟩
  specialize hb (√ε) (by exact Real.sqrt_pos.mpr hε)
  rcases hb with ⟨bb, hbb⟩
  use max ba bb
  intro n hn 
  rw [max_le_iff] at hn 
  specialize hba n hn.1
  specialize hbb n hn.2
  simp only [sub_zero] at hba hbb
  change |a n * b n - 0| < ε
  calc |a n * b n - 0| = |a n * b n| := by simp only [sub_zero _ ]
          _            = |a n| * |b n| := by simp only [abs_mul (a n) _]
          _            < √ε*√ε := by gcongr
          _            = ε := by refine Real.mul_self_sqrt (hε.le)

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  unfold TendsTo
  intro ε hε
  specialize ha (√ε) (by exact Real.sqrt_pos.mpr hε)
  rcases ha with ⟨ba, hba⟩
  specialize hb (√ε) (by exact Real.sqrt_pos.mpr hε)
  rcases hb with ⟨bb, hbb⟩
  use max ba bb
  intro n hn 
  rw [max_le_iff] at hn 
  specialize hba n hn.1
  specialize hbb n hn.2
  change |a n * b n - t*u| < ε
  sorry

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  sorry

end Section2sheet6
