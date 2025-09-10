import Mathlib

open scoped LinearMap

example {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
    (h : ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖) :
    closure (T '' (Metric.ball (0 : α) 1)) ⊇ Metric.ball (0 : β) δ := fun y hy ↦ by
  have t1 : Convex ℝ (closure (T '' (Metric.ball (0 : α) 1))) :=
    Convex.is_linear_image (convex_ball 0 1) T.isBoundedLinearMap.toIsLinearMap |> .closure
  have t3 : Balanced ℝ (closure (⇑T '' Metric.ball 0 1)) := by
    refine Balanced.closure ?_
    intro _ ha _ ⟨_, ⟨_, hc, hd⟩, d⟩
    simp at d
    rw [← d, ← hd, ← ContinuousLinearMap.map_smul]
    exact Set.mem_image_of_mem (⇑T) (Balanced.smul_mem balanced_ball_zero ha hc)
  have t4 : (closure (⇑T '' Metric.ball 0 1)).Nonempty :=
    ⟨T 0, subset_closure ⟨0, by simp⟩⟩
  have : ∀ z ∉ closure (T '' (Metric.ball (0 : α) 1)), z ∉ Metric.ball (0 : β) δ := fun z hz ↦ by
    obtain ⟨f, hf1, hf2⟩ := RCLike.geometric_hahn_banach' t1 isClosed_closure t3 t4 z hz
    have ha : ∀ a ∈ Metric.closedBall (0 : α) 1, ‖f (T a)‖ < 1 := fun a ha ↦ by
      refine hf2 (T a) ((image_closure_subset_closure_image T.continuous) ?_)
      exact ⟨a, by simp [closure_ball (0 : α) (zero_ne_one' ℝ).symm, ha]⟩
    have : ‖((f : β →L[ℝ] ℝ).comp T)‖ ≤ 1 := by
      refine (f.comp T).opNorm_le_bound' (zero_le_one' ℝ) fun x hx ↦ ?_
      have xin : (1 / ‖x‖) • x ∈ Metric.closedBall 0 1 := by
        rw [mem_closedBall_zero_iff]
        simp [norm_smul_of_nonneg ?_ x, hx]
      refine le_of_lt (by calc
        _ = ‖(f.comp T) ((1 / ‖x‖) • x)‖ * ‖x‖ := by simp [field]
        _ < 1 * ‖x‖ := (mul_lt_mul_iff_of_pos_right (by positivity)).mpr (ha ((1 / ‖x‖) • x) xin))
    have : δ < ‖z‖ := by calc
      _ < δ * ‖f z‖ :=(lt_mul_iff_one_lt_right h0).mpr hf1
      _ ≤ δ * (‖f‖ * ‖z‖) := (mul_le_mul_iff_of_pos_left h0).mpr (f.le_opNorm z)
      _ ≤ ‖((f : β →L[ℝ] ℝ).comp T)‖ * ‖z‖ := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right (h f) (norm_nonneg z)
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right this (norm_nonneg z)
      _ = _ := by simp
    simp [le_of_lt this]
  by_contra! nh
  have := this y nh
  contradiction
