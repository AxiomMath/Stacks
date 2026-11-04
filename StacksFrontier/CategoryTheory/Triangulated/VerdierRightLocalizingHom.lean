module

public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
public import StacksFrontier.CategoryTheory.Functor.Derived.InitialResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms in a Verdier quotient out of an object orthogonal to a localizing part

Let `C` be a triangulated category, `B` a triangulated subcategory closed under isomorphisms and
`L : C ⥤ D` a localization functor for `B.trW`, the Verdier quotient `C/B`. Let `A` be a
triangulated subcategory of `C` which is right `B`-localizing in the sense of Verdier
(`CategoryTheory.ObjectProperty.IsVerdierRightLocalizing`). If `M` is an object of `C` with no
nonzero morphism into an object of `A ⊓ B`, then for every object `H` of `A`

`L : Hom_C(M, H) ⟶ Hom_{C/B}(L M, L H)`

is bijective. The object `M` itself is not assumed to lie in `A`.

## Main results

* `CategoryTheory.ObjectProperty.map_bijective_of_leftOrthogonal_inf`: the bijection above.

## References

* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The intersection of two shift-stable object properties is shift-stable. -/
theorem isStableUnderShift_inf (P Q : ObjectProperty C) [P.IsStableUnderShift ℤ]
    [Q.IsStableUnderShift ℤ] : (P ⊓ Q).IsStableUnderShift ℤ :=
  ⟨fun a => ⟨fun _ hX => ⟨P.le_shift a _ hX.1, Q.le_shift a _ hX.2⟩⟩⟩

variable [IsTriangulated C] (A B : ObjectProperty C) [A.IsTriangulated] [B.IsTriangulated]
  [B.IsClosedUnderIsomorphisms] [A.IsVerdierRightLocalizing B]

/-- **Morphisms out of an object orthogonal to `A ⊓ B` into an object of `A` are computed in the
Verdier quotient by `B`**, when `A` is right `B`-localizing. -/
@[sga "4½ Etat_0 2.5.3" "(b) ⇒ (a)", sga "4½ Etat_0 2.6.3" "Left clause of 6-3"]
theorem map_bijective_of_leftOrthogonal_inf (L : C ⥤ D) [L.IsLocalization B.trW] {M H : C}
    (hM : (A ⊓ B).leftOrthogonal M) (hH : A H) :
    Function.Bijective (L.map : (M ⟶ H) → (L.obj M ⟶ L.obj H)) := by
  have := isStableUnderShift_inf A B
  refine ⟨fun f₁ f₂ hf => ?_, fun g => ?_⟩
  · rw [MorphismProperty.map_eq_iff_postcomp L B.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    obtain ⟨Z', s', b, -, hs', fac⟩ := IsVerdierRightLocalizing.fac' s hH hs
    exact (A ⊓ B).leftOrthogonal_cancel_trW hM hs'
      (by rw [← fac, reassoc_of% eq])
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L B.trW g
    obtain ⟨Z, s', b, -, hs', fac⟩ := IsVerdierRightLocalizing.fac' φ.s hH φ.hs
    obtain ⟨Y, g', h', hT, hY⟩ := ((A ⊓ B).trW_iff s').1 hs'
    obtain ⟨m, hm⟩ := (Triangle.mk s' g' h').coyoneda_exact₂ hT (φ.f ≫ b) (hM _ hY)
    refine ⟨m, ?_⟩
    have hs'B : B.trW s' := trW_monotone inf_le_right _ hs'
    have : IsIso (L.map φ.s) := Localization.inverts L B.trW _ φ.hs
    have : IsIso (L.map s') := Localization.inverts L B.trW _ hs'B
    have : IsIso (L.map b) := by
      have : IsIso (L.map φ.s ≫ L.map b) := by rw [← L.map_comp, fac]; infer_instance
      exact IsIso.of_isIso_comp_left (L.map φ.s) (L.map b)
    rw [hφ, ← cancel_mono (L.map φ.s), MorphismProperty.LeftFraction.map_comp_map_s,
      ← cancel_mono (L.map b), ← L.map_comp, ← L.map_comp, ← L.map_comp, Category.assoc, fac]
    exact congrArg L.map hm.symm

end CategoryTheory.ObjectProperty
