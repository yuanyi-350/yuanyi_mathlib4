/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# The equivalence of categories of sheaves of a dense subsite

If `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`, and `A` is
a category with suitable limits, then the functor
`G.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` is an equivalence
of categories. The equivalence of categories can be obtained as `sheafEquiv J K G A`
which is defined in the file `Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean`.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

@[expose] public section

universe w v u w'

namespace CategoryTheory.Functor.IsDenseSubsite

open CategoryTheory Opposite

variable {C D : Type*} [Category* C] [Category* D]
variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {A : Type w} [Category.{w'} A] [∀ X, Limits.HasLimitsOfShape (StructuredArrow X G.op) A]
variable [G.IsDenseSubsite J K]

set_option backward.isDefEq.respectTransparency false in
include K in
lemma isIso_ranCounit_app_of_isDenseSubsite (Y : Sheaf J A) (U X) :
    IsIso ((yoneda.map ((G.op.ranCounit.app Y.obj).app (op U))).app (op X)) := by
  rw [isIso_iff_bijective]
  constructor
  · intro f₁ f₂ e
    apply (isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).hom_ext
    rintro ⟨⟨⟨⟩⟩, ⟨W⟩, g⟩
    obtain ⟨g, rfl⟩ : ∃ g' : G.obj W ⟶ G.obj U, g = g'.op := ⟨g.unop, rfl⟩
    apply (Y.2 X _ (IsDenseSubsite.imageSieve_mem J K G g)).isSeparatedFor.ext
    dsimp
    rintro V iVW ⟨iVU, e'⟩
    have := congr($e ≫ Y.1.map iVU.op)
    simp only [comp_obj, yoneda_map_app, Category.assoc, comp_map,
      ← NatTrans.naturality, op_obj, op_map, Quiver.Hom.unop_op, ← map_comp_assoc,
      ← op_comp, ← e'] at this ⊢
    simpa [← NatTrans.naturality] using this
  · intro f
    let c : Limits.Cone (StructuredArrow.proj (op (G.obj U)) G.op ⋙ Y.obj) := by
      refine ⟨X, ⟨fun g ↦ ?_, ?_⟩⟩
      · exact f ≫ IsDenseSubsite.mapPreimage K G Y g.hom.unop
      · dsimp
        rintro ⟨⟨⟨⟩⟩, ⟨W₁⟩, g₁⟩ ⟨⟨⟨⟩⟩, ⟨W₂⟩, g₂⟩ ⟨⟨⟨⟨⟩⟩⟩, i, hi⟩
        dsimp at g₁ g₂ i hi
        -- See issue https://github.com/leanprover-community/mathlib4/pull/15781 for tracking performance regressions of `rintro` as here
        have h : g₂ = g₁ ≫ (G.map i.unop).op := by simpa only [Category.id_comp] using hi
        rcases h with ⟨rfl⟩
        have h : ∃ g' : G.obj W₁ ⟶ G.obj U, g₁ = g'.op := ⟨g₁.unop, rfl⟩
        rcases h with ⟨g, rfl⟩
        have h : ∃ i' : W₂ ⟶ W₁, i = i'.op := ⟨i.unop, rfl⟩
        rcases h with ⟨i, rfl⟩
        simp only [unop_comp, Quiver.Hom.unop_op, Category.id_comp]
        rw [Category.assoc, IsDenseSubsite.mapPreimage_comp_map]
    refine ⟨(isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).lift c, ?_⟩
    · have := (isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).fac c (.mk (𝟙 _))
      simp only [id_obj, comp_obj, StructuredArrow.proj_obj, StructuredArrow.mk_right,
        RightExtension.coneAt_pt, RightExtension.mk_left, RightExtension.coneAt_π_app,
        const_obj_obj, op_obj, StructuredArrow.mk_hom_eq_self, map_id, whiskeringLeft_obj_obj,
        RightExtension.mk_hom, Category.id_comp] at this
      simpa [c, yoneda_map_app] using this

instance (Y : Sheaf J A) : IsIso ((G.sheafAdjunctionCocontinuous A J K).counit.app Y) := by
  apply +allowSynthFailures ReflectsIsomorphisms.reflects (sheafToPresheaf J A)
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨U⟩
  apply +allowSynthFailures ReflectsIsomorphisms.reflects yoneda
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨X⟩
  simpa [sheafAdjunctionCocontinuous_counit_app_hom]
    using isIso_ranCounit_app_of_isDenseSubsite G J K Y U X

instance : (G.sheafPushforwardContinuous A J K).IsEquivalence :=
  (G.sheafAdjunctionCocontinuous A J K).toEquivalence.isEquivalence_functor

end IsDenseSubsite

end CategoryTheory.Functor
