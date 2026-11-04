module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothDeRhamLocallyFree
public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.Setup
public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.CoefficientField

/-!
# Finite local freeness of de Rham cohomology over `ℚ`, from rigidity over Artinian bases

Let `A` be an Artinian local `ℚ`-algebra with residue field `k = A/𝔪`, and `f : X ⟶ Spec A` proper
and smooth. A coefficient field `σ : k → A` exists
(`IsArtinianRing.exists_residue_comp_eq_id_of_algebraRat`), and with it the trivial deformation
`X' = X₀ ×_k Spec A` of the special fibre `X₀`. Since `X'` comes by base change from the proper
smooth `X₀` over the field `k`, its de Rham cohomology `H^n_dR(X'/A) = H^n_dR(X₀/k) ⊗_k A` is a
free `A`-module ([Stacks, Tag 0FM0]). The rigidity statement `Rf_*Ω^•_{X/A} ≅ Rf'_*Ω^•_{X'/A}`
therefore makes every `H^n_dR(X/A)` free, which is the Artinian input of
`Stacks.DeRhamSmooth.isLocallyFree_deRhamCohomologySheaf_of_artinian`.

## Main results

* `Stacks.DeRhamRigidity.free_moduleSpecΓ_deRhamCohomologySheaf_trivialMap`: the de Rham
  cohomology of the trivial deformation is free.
* `Stacks.DeRhamRigidity.artinianDeRhamLocallyFree_of_rigidity`: the Artinian case of the finite
  local freeness, from rigidity.
* `Stacks.DeRhamRigidity.isLocallyFree_deRhamCohomologySheaf_of_rigidity`: for `f : X ⟶ Y` proper
  smooth over a `ℚ`-scheme every `ℋ^q_dR(X/Y)` is finite locally free, given rigidity.

## Implementation notes

The rigidity isomorphism is an explicit hypothesis `hrig` of the last two results; it is the part
of the argument not yet formalized. The derived categories are those of
`CategoryTheory.HasDerivedCategory.standard` at priority `10000`, as in
`StacksFrontier/AlgebraicGeometry/DeRham/ProperSmoothAffineDeRhamModel.lean`. No `@[stacks]`
attribute is carried.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Stacks.DeRhamDirectImage Stacks.DeRhamSmooth

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamRigidity

variable {A : CommRingCat.{u}} [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- **The de Rham cohomology of the trivial deformation is free.** For a local ring `A`, a ring
map `σ : A/𝔪 → A` and `f : X ⟶ Spec A` proper and smooth, every `Γ(Spec A, ℋ^n_dR(X'/A))` is a
free `A`-module, where `X' = X₀ ×_{A/𝔪} Spec A`: the model of `X'` is the derived base change
along `σ` of the perfect model of the special fibre over the field `A/𝔪` ([Stacks, Tag 0FM0]). -/
theorem free_moduleSpecΓ_deRhamCohomologySheaf_trivialMap (σ : A ⧸ maximalIdeal A →+* A)
    [IsProper f] [Smooth f] (n : ℤ) :
    Module.Free A ((moduleSpecΓFunctor (R := A)).obj
      (deRhamCohomologySheaf (trivialMap σ f) n)) := by
  let : Field (residueRing A) := Ideal.Quotient.field (maximalIdeal A)
  obtain ⟨hfree, -⟩ := StacksDraft.Perfect.free_homology_totalDerivedExtensionScalars_of_field
    (sectionMap σ).hom
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (sectionMap σ).hom)
    (affineDeRhamModel (specialMap f)) (isPerfect_affineDeRhamModel _) n
  exact Module.Free.of_equiv
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
      (affineDeRhamModelBaseChangeIso (specialMap f) (sectionMap σ)).symm ≪≫
      affineDeRhamModelHomologyIso (trivialMap σ f) n).toLinearEquiv

/-- **The Artinian case of the finite local freeness of de Rham cohomology over `ℚ`, from
rigidity.** Suppose that for every Artinian local `ℚ`-algebra `A`, every coefficient field
`σ : A/𝔪 → A` and every proper smooth `f : X ⟶ Spec A`, the derived direct image
`Rf_*Ω^•_{X/A}` is isomorphic to that of the trivial deformation `X' = X₀ ×_{A/𝔪} Spec A`. Then
every `ℋ^n_dR(X/A)` over such a base is finite locally free: its global sections are those of
`ℋ^n_dR(X'/A)`, which are free (`free_moduleSpecΓ_deRhamCohomologySheaf_trivialMap`).

The rigidity hypothesis `hrig` is not yet formalized. -/
theorem artinianDeRhamLocallyFree_of_rigidity
    (hrig : ∀ (A : CommRingCat.{u}) [IsArtinianRing A] [IsLocalRing A] [Algebra ℚ A]
      (σ : A ⧸ IsLocalRing.maximalIdeal A →+* A)
      (_hσ : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp σ = RingHom.id _)
      (X : Scheme.{u}) (f : X ⟶ Spec A) [IsProper f] [Smooth f],
      Nonempty (Stacks.DeRhamDirectImage.derivedDeRhamDirectImage f ≅
        Stacks.DeRhamDirectImage.derivedDeRhamDirectImage (trivialMap σ f))) :
    Stacks.DeRhamSmooth.ArtinianDeRhamLocallyFree.{u} := by
  intro A _ _ _ X f _ _ n
  obtain ⟨σ, hσ⟩ := IsArtinianRing.exists_residue_comp_eq_id_of_algebraRat A
  obtain ⟨e⟩ := hrig A σ hσ X f
  refine isFiniteLocallyFree_deRhamCohomologySheaf_of_free f (fun m => ?_) n
  exact Module.Free.of_equiv' (free_moduleSpecΓ_deRhamCohomologySheaf_trivialMap f σ m)
    ((moduleSpecΓFunctor (R := A)).mapIso
      ((DerivedCategory.Plus.homologyFunctor _ m).mapIso e)).toLinearEquiv.symm

/-- **The de Rham cohomology sheaves of a proper smooth morphism over `ℚ` are finite locally free,
from rigidity** ([Stacks, Tag 0FMN], the sentence the source defers to a future reference). Let
`f : X ⟶ Y` be proper and smooth, with `Y` over a scheme `S` over `Spec R` for a `ℚ`-algebra `R`.
Given the rigidity of `Rf_*Ω^•` over Artinian local `ℚ`-algebras (the hypothesis `hrig` of
`artinianDeRhamLocallyFree_of_rigidity`), every `ℋ^q_dR(X/Y)` is a finite locally free
`𝒪_Y`-module.

The rigidity hypothesis `hrig` is not yet formalized. -/
theorem isLocallyFree_deRhamCohomologySheaf_of_rigidity
    (hrig : ∀ (A : CommRingCat.{u}) [IsArtinianRing A] [IsLocalRing A] [Algebra ℚ A]
      (σ : A ⧸ IsLocalRing.maximalIdeal A →+* A)
      (_hσ : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp σ = RingHom.id _)
      (X : Scheme.{u}) (f : X ⟶ Spec A) [IsProper f] [Smooth f],
      Nonempty (Stacks.DeRhamDirectImage.derivedDeRhamDirectImage f ≅
        Stacks.DeRhamDirectImage.derivedDeRhamDirectImage (trivialMap σ f)))
    {X Y S : Scheme.{u}} {R : CommRingCat.{u}} [Algebra ℚ R] (f : X ⟶ Y) (g : Y ⟶ S)
    (σ : S ⟶ Spec R) [IsProper f] [Smooth f] (q : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (deRhamCohomologySheaf f q) :=
  isLocallyFree_deRhamCohomologySheaf_of_artinian (artinianDeRhamLocallyFree_of_rigidity hrig)
    f g σ q

end Stacks.DeRhamRigidity
