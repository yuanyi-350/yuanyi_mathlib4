/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Preadditive structure on algebras over a monad

If `C` is a preadditive category and `T` is an additive monad on `C` then `Algebra T` is also
preadditive. Dually, if `U` is an additive comonad on `C` then `Coalgebra U` is preadditive as well.

-/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] (T : Monad C)
  [Functor.Additive (T : C ⥤ C)]

open CategoryTheory.Limits Preadditive

/-- The category of algebras over an additive monad on a preadditive category is preadditive. -/
@[simps!]
instance Monad.algebraPreadditive : Preadditive (Monad.Algebra T) where
  homGroup F G := by
    letI : Add (F ⟶ G) := ⟨fun α β =>
        { f := α.f + β.f
          h := by simp only [Functor.map_add, add_comp, Monad.Algebra.Hom.h, comp_add] }⟩
    letI : Zero (F ⟶ G) := ⟨
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }⟩
    letI : SMul ℕ (F ⟶ G) := ⟨fun n α =>
        { f := n • α.f
          h := by rw [Functor.map_nsmul, nsmul_comp, Monad.Algebra.Hom.h, comp_nsmul] }⟩
    letI : Neg (F ⟶ G) := ⟨fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Monad.Algebra.Hom.h, comp_neg] }⟩
    letI : Sub (F ⟶ G) := ⟨fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Monad.Algebra.Hom.h, comp_sub] }⟩
    letI : SMul ℤ (F ⟶ G) := ⟨fun r α =>
        { f := r • α.f
          h := by rw [Functor.map_zsmul, zsmul_comp, Monad.Algebra.Hom.h, comp_zsmul] }⟩
    exact
      (show Function.Injective (fun α : F ⟶ G => α.f) from by
        intro α β h
        ext
        exact h).addCommGroup (fun α => α.f) rfl (fun _ _ => rfl) (fun _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
  add_comp := by
    intros
    ext
    apply add_comp
  comp_add := by
    intros
    ext
    apply comp_add

instance Monad.forget_additive : (Monad.forget T).Additive where

variable (U : Comonad C) [Functor.Additive (U : C ⥤ C)]

/-- The category of coalgebras over an additive comonad on a preadditive category is preadditive. -/
@[simps!]
instance Comonad.coalgebraPreadditive : Preadditive (Comonad.Coalgebra U) where
  homGroup F G := by
    letI : Add (F ⟶ G) := ⟨fun α β =>
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Comonad.Coalgebra.Hom.h, add_comp] }⟩
    letI : Zero (F ⟶ G) := ⟨
        { f := 0
          h := by simp only [Functor.map_zero, comp_zero, zero_comp] }⟩
    letI : SMul ℕ (F ⟶ G) := ⟨fun n α =>
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Comonad.Coalgebra.Hom.h, nsmul_comp] }⟩
    letI : Neg (F ⟶ G) := ⟨fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Comonad.Coalgebra.Hom.h, neg_comp] }⟩
    letI : Sub (F ⟶ G) := ⟨fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Comonad.Coalgebra.Hom.h, sub_comp] }⟩
    letI : SMul ℤ (F ⟶ G) := ⟨fun r α =>
        { f := r • α.f
          h := by rw [Functor.map_zsmul, comp_zsmul, Comonad.Coalgebra.Hom.h, zsmul_comp] }⟩
    exact
      (show Function.Injective (fun α : F ⟶ G => α.f) from by
        intro α β h
        ext
        exact h).addCommGroup (fun α => α.f) rfl (fun _ _ => rfl) (fun _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
  add_comp := by
    intros
    ext
    apply add_comp
  comp_add := by
    intros
    ext
    apply comp_add

instance Comonad.forget_additive : (Comonad.forget U).Additive where

end CategoryTheory
