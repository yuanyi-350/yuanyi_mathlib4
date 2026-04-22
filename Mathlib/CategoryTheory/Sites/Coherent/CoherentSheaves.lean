/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
/-!

# Sheaves for the coherent topology

This file characterises sheaves for the coherent topology

## Main result

* `isSheaf_coherent`: a presheaf of types is a sheaf for the coherent topology if and only
  if it satisfies the sheaf condition with respect to every presieve consisting of a finite
  effective epimorphic family.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Precoherent C]

universe w in
lemma isSheaf_coherent (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (coherentTopology C) P ↔
    (∀ (B : C) (α : Type) [Finite α] (X : α → C) (π : (a : α) → (X a ⟶ B)),
      EffectiveEpiFamily X π → (Presieve.ofArrows X π).IsSheafFor P) := by
  rw [coherentTopology, Presieve.isSheaf_coverage]
  simp only [coherentCoverage]
  grind

namespace coherentTopology

/-- Every Yoneda-presheaf is a sheaf for the coherent topology. -/
theorem isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (coherentTopology C) (yoneda.obj W) := by
  rw [isSheaf_coherent]
  exact fun X α _ Y π H ↦
    Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable
      ((Sieve.effectiveEpimorphic_family Y π).mpr H) _

variable (C) in
/-- The coherent topology on a precoherent category is subcanonical. -/
instance subcanonical : (coherentTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

end coherentTopology

end CategoryTheory
