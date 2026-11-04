module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.ImmersionOfRegularSchemes
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.RingTheory.Smooth.RegularRing

/-!
# A morphism of regular schemes is a local complete intersection morphism

A morphism of schemes which is locally of finite type and whose source and target are both
regular is a local complete intersection morphism in the sense of Stacks 069F: this is
**Stacks 0E9K**.

## Main results

* `AlgebraicGeometry.AffineSpace.smooth_over`: affine space over a base is smooth over it.
* `AlgebraicGeometry.isRegular_of_smooth`: regularity ascends along a smooth morphism.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_isRegular`: a morphism locally of
  finite type between regular schemes is a local complete intersection morphism.

## References

* [Stacks Project, Lemma 37.62.11 (Tag 0E9K)](https://stacks.math.columbia.edu/tag/0E9K)
* [Stacks Project, Lemma 31.22.12 (Tag 0E9J)](https://stacks.math.columbia.edu/tag/0E9J)
* [Stacks Project, Lemma 29.39.2 (Tag 04II)](https://stacks.math.columbia.edu/tag/04II)
* [Stacks Project, Lemma 10.163.10 (Tag 07NF)](https://stacks.math.columbia.edu/tag/07NF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- Affine space over a base is smooth over it. -/
theorem AffineSpace.smooth_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    Smooth (𝔸(n; S) ↘ S) := by
  let P := MvPolynomial n (ULift.{u} ℤ)
  have : Algebra.Smooth (ULift.{u} ℤ) P := ⟨inferInstance, inferInstance⟩
  let g := Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) P))
  have : Smooth g := (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    (RingHom.smooth_algebraMap.mpr inferInstance)
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
  have : Smooth (terminal.from (Spec (.of P))) := by
    simpa only [← terminalIsTerminal.hom_ext (g ≫ terminal.from _) (terminal.from _)]
      using smooth_comp g _
  change Smooth (pullback.fst (terminal.from S) (terminal.from (Spec (.of P))))
  infer_instance

/-- If `f : X ⟶ Y` is smooth and `Y` is regular, then `X` is regular. -/
@[ega "IV 17.5.8" "(iii)", sga "1 II 3.1" "regular case"]
theorem isRegular_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Smooth f)
    (hY : IsRegular Y) : IsRegular X := by
  have : Smooth f := hf
  intro x
  obtain ⟨U, hxU, hU⟩ := hY (f.base x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (by simpa using hxU) (f ⁻¹ᵁ U.1).2
  have : IsRegularRing Γ(Y, U) := hU
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U.1 V hVU).hom.toAlgebra
  have : Algebra.Smooth Γ(Y, U) Γ(X, V) := RingHom.smooth_algebraMap.mp
    (by simpa [RingHom.algebraMap_toAlgebra] using f.smooth_appLE U.2 hV hVU)
  exact ⟨⟨V, hV⟩, hxV, Algebra.isRegularRing_of_smooth Γ(Y, U) Γ(X, V)⟩

/-- A morphism of schemes which is locally of finite type and whose source and target are
regular is a local complete intersection morphism. -/
@[stacks 0E9K]
theorem isLocalCompleteIntersectionMorphism_of_isRegular {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hX : IsRegular X) (hY : IsRegular Y) :
    IsLocalCompleteIntersectionMorphism f := by
  intro x
  refine ⟨finiteTypeAt_of_locallyOfFiniteType f x, ?_⟩
  obtain ⟨W, hxW, -⟩ := hX x
  obtain ⟨n, i, hi, hcomp⟩ := exists_immersion_affineSpace (f := W.1.ι ≫ f)
  refine ⟨W.1, hxW, _, i, _, hi, ?_, AffineSpace.smooth_over (ULift.{u} (Fin n)) Y, hcomp.symm⟩
  exact isKoszulRegularImmersion_of_isRegularImmersion i
    (isRegularImmersion_of_isRegular i (hX.restrict W.1)
      (isRegular_of_smooth _ (AffineSpace.smooth_over _ Y) hY))

end AlgebraicGeometry

end
