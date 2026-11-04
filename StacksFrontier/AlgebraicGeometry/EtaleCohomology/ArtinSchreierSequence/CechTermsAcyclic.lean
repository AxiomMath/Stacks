module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AffineDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ZariskiCechResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.Homology.CompositeCollapseFiniteProducts

/-!
# The terms of the Zariski Čech resolution of `𝐆_a` are acyclic for the direct image

Let `f : X ⟶ S` be a separated morphism to an affine scheme and `V ⊆ X` an affine open. Then the
direct image `ι_{V,*} 𝐆_{a,V}` is acyclic for `f_*`. Consequently, for a finite open covering of
`X` whose finite intersections are affine, every term of the Čech resolution
`Stacks.ArtinSchreier.zariskiCechComplex` is acyclic for `f_*`.

## Main results

* `Stacks.ArtinSchreier.isAffineHom_ι_of_isAffineOpen`: an affine open of `X` is affine over `S`.
* `Stacks.ArtinSchreier.acyclic_openDirectImage`: `ι_{V,*} 𝐆_{a,V}` is acyclic for `f_*`.
* `Stacks.ArtinSchreier.acyclic_zariskiCechComplex_X`: the terms of the Zariski Čech resolution
  of `𝐆_a` are acyclic for `f_*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open Stacks.CategoryTheory.CechComplex

universe u

namespace Stacks.ArtinSchreier

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [IsSeparated f]

attribute [local instance] HasExt.standard

include f in
/-- An affine open subscheme of a scheme separated over an affine scheme is affine over it. -/
theorem isAffineHom_ι_of_isAffineOpen {V : X.Opens} (hV : IsAffineOpen V) :
    IsAffineHom V.ι := by
  have : IsAffine V.toScheme := hV
  exact MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) V.ι f
    inferInstance inferInstance

/-- `R^n g_* 𝐆_a = 0` for `n > 0` and `g` affine, in the form of positivity of `n`. -/
private theorem isZero_rightDerived_additiveSheaf_of_pos {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsAffineHom g] (n : ℕ) (hn : 0 < n) :
    IsZero (((etaleAbelianDirectImage.{u, 0} g).rightDerived n).obj
      (additiveSheaf.{u, u + 1} Y)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact isZero_rightDerived_etaleAbelianDirectImage_additiveSheaf g m

/-- **`ι_{V,*} 𝐆_{a,V}` is acyclic for `f_*`** for an affine open `V` of a scheme separated over an
affine scheme. -/
theorem acyclic_openDirectImage {V : X.Opens} (hV : IsAffineOpen V) :
    Stacks.RightDerivedComp.acyclic (etaleAbelianDirectImage.{u, 0} f) (openDirectImage X V) := by
  have : IsAffine V.toScheme := hV
  have : IsAffineHom V.ι := isAffineHom_ι_of_isAffineOpen f hV
  have : (etaleAbelianDirectImage.{u, 0} V.ι).PreservesInjectiveObjects :=
    smallEtalePushforwardAb_preservesInjectiveObjects V.ι
  intro n hn
  exact (isZero_rightDerived_additiveSheaf_of_pos (V.ι ≫ f) n hn).of_iso <|
    (Stacks.RightDerivedComp.objIso (etaleAbelianDirectImage.{u, 0} V.ι)
      (injectiveResolution (additiveSheaf.{u, u + 1} V))
      (isZero_rightDerived_additiveSheaf_of_pos V.ι)
      (etaleAbelianDirectImage.{u, 0} f) n).symm ≪≫
      (Stacks.DerivedFunctor.rightDerivedIso (etaleAbelianDirectImageCompIso.{u, 0} V.ι f)
        n).app _

variable {ι : Type} [Finite ι] (U : ι → X.Opens)

/-- **Every term of the Zariski Čech resolution of `𝐆_a` is acyclic for `f_*`**, for a finite
covering family whose finite intersections are affine. -/
theorem acyclic_zariskiCechComplex_X (hU : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
    IsAffineOpen (inter U x)) (n : ℕ) :
    Stacks.RightDerivedComp.acyclic (etaleAbelianDirectImage.{u, 0} f)
      ((zariskiCechComplex X U).X n) :=
  Stacks.RightDerivedComp.acyclic_of_isLimit_fan (ι := Fin (n + 1) → ι) _
    (isLimitFan U (openDirectImagePresheaf X) n) fun x ↦ acyclic_openDirectImage f (hU n x)

end Stacks.ArtinSchreier

end
