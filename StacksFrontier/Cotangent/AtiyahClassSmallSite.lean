module

public import StacksFrontier.Cotangent.AtiyahClass
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange
import StacksCore.Tactic.StacksAttribute

/-!
# The Atiyah triangle on the small model of `C_{B/A}`

Let `A → B` be a ring map and let `κ` be a cardinal. This file repeats the construction of
`StacksFrontier/Cotangent/AtiyahClass.lean` on the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the footnote-restricted site `C_{B/A}`, with
coefficients in `ModuleCat.{u} B` rather than `ModuleCat.{u + 1} (ULift B)`.

**Why a second construction.** `CommAlgCat.atiyahSite` is `AsSmall.{u}` of the *unrestricted*
site `CommAlgCat.polynomialSite A B`, whose objects live in `Type (u + 1)`; the triangle there is
formed in `D(ModuleCat.{u + 1} (ULift B))`. Every tool that computes `Lπ_!` on `C_{B/A}` —
[Stacks, Tag 08PT] and [Stacks, Tag 08PS] by a point resolution, [Stacks, Tag 08QE], the change
of coefficients of [Stacks, Tag 08QJ], and [Stacks, Tag 08PU] — is instead stated on the small
model at universe `u`. The two sites are *not* equivalent: the small model is equivalent to the
restricted site `CommAlgCat.boundedPolynomialSite A B κ`
(`CommAlgCat.boundedPolynomialSiteEquiv`) and only fully faithfully embedded in the unrestricted
one (`CommAlgCat.fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite`), and the unrestricted
site is not essentially small at `u` at all. So the identifications of the endpoints of the
Atiyah triangle cannot be transported to `CommAlgCat.atiyahSite`; the triangle has to be built
where the tools are.

## Main definitions

* `CommAlgCat.smallAtiyahStructureSheaf`: the tautological sheaf of commutative rings `𝒪` on the
  small model, with sections in `Type u`, and `CommAlgCat.smallAtiyahBaseSheaf`, the constant
  sheaf of rings `A`, with `CommAlgCat.smallAtiyahBaseHom` the map `A̲ ⟶ 𝒪` given by the
  `A`-algebra structures.
* `CommAlgCat.smallAtiyahPrincipalPartsSequence`: the sequence of first principal parts of the
  sheaves of `𝒪`-modules on the small model, relative to `A̲`.
* `CommAlgCat.smallAtiyahModuleSheaf`: a `B`-module read as a sheaf of `𝒪`-modules through the
  augmentations.
* `CommAlgCat.smallPolynomialAtiyahTriangle`: the image of the sequence of principal parts under
  `Lπ_! : D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ], and `CommAlgCat.smallPolynomialAtiyahClass` its
  last arrow.

## Main results

* `CommAlgCat.smallPolynomialAtiyahTriangle_distinguished`: the triangle is distinguished.
* `CommAlgCat.smallPolynomialAtiyahTriangle_obj₁`,
  `CommAlgCat.smallPolynomialAtiyahTriangle_obj₂` and
  `CommAlgCat.smallPolynomialAtiyahTriangle_obj₃`: its three terms are `Lπ_!` of the relative
  differentials tensored with the module, of the sheaf of first principal parts of the module,
  and of the module itself.

## Implementation notes

The structure sheaf is built so that the presheaf of rings underlying it is
`CommAlgCat.smallPolynomialStructurePresheaf` on the nose, and the coefficient map of derived
lower shriek is `CommAlgCat.smallPolynomialAugmentation` itself rather than a second copy of it:
that is what makes the change of coefficients of [Stacks, Tag 08QJ], which is stated for that
map, applicable to this triangle.

No universe lift occurs anywhere: the site, the rings `A` and `B`, the sections of `𝒪` and the
coefficient modules all live in `Type u`. This is the convention of [Stacks, Tag 09CZ] as it is
recorded in `Stacks.ChaoticSite.derivedColimitWithCoefficients`, and it is why the small model is
used.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD), the Atiyah-class
  triangle, and [Tag 09DE](https://stacks.math.columbia.edu/tag/09DE), the Atiyah class.
* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the sequence of
  principal parts, and [Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ), derived lower
  shriek with coefficients.
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR), the site `C_{B/A}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.SheafOfModules
  (moduleSheaves PrincipalPartsSequence principalPartsSequenceOfSite)

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### The two sheaves of rings on the small model -/

/-- The tautological presheaf of commutative rings `𝒪` on the small model of `C_{B/A}`, sending
an object `(P, α)` to the commutative ring `P`. Forgetting the commutativity gives
`CommAlgCat.smallPolynomialStructurePresheaf` on the nose. -/
def smallAtiyahStructurePresheaf :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ CommRingCat.{u} :=
  smallSiteToOver A B κ ⋙ Over.forget B ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u}

/-- **The structure sheaf `𝒪` of the small model of `C_{B/A}`.** The topology is chaotic, so
every presheaf is a sheaf. -/
def smallAtiyahStructureSheaf :
    Sheaf (⊥ : GrothendieckTopology (smallBoundedPolynomialSite A B κ)) CommRingCat.{u} :=
  ⟨smallAtiyahStructurePresheaf A B κ, Presheaf.isSheaf_bot _⟩

/-- **The constant sheaf of rings `A̲` on the small model of `C_{B/A}`**, over which the relative
differentials and the principal parts of `𝒪` are taken. No universe lift is needed: the sections
of `𝒪` live in the universe of `A`. -/
def smallAtiyahBaseSheaf :
    Sheaf (⊥ : GrothendieckTopology (smallBoundedPolynomialSite A B κ)) CommRingCat.{u} :=
  ⟨(Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj (CommRingCat.of A),
    Presheaf.isSheaf_bot _⟩

/-- **The map of sheaves of rings `A̲ ⟶ 𝒪`** given by the `A`-algebra structure of each object of
the small model of `C_{B/A}`. -/
def smallAtiyahBaseHom : smallAtiyahBaseSheaf A B κ ⟶ smallAtiyahStructureSheaf A B κ :=
  ⟨{ app X := CommRingCat.ofHom
        (algebraMap A ((((smallSiteToOver A B κ).obj X).left : CommAlgCat.{u} A) : Type u))
     naturality X Y f := by
       ext a
       exact (((smallSiteToOver A B κ).map f).left.hom.commutes a).symm }⟩

/-- The presheaf of rings underlying the structure sheaf of the small model is
`CommAlgCat.smallPolynomialStructurePresheaf`, on the nose: both are the passage from an object
of the model to the ring underlying the `A`-algebra it names. -/
theorem underlyingRingSheafOfSite_smallAtiyahStructureSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (smallAtiyahStructureSheaf A B κ)).obj =
      smallPolynomialStructurePresheaf A B κ :=
  rfl

/-! ### The sheaf of relative differentials on the small model -/

/-- The presheaf of relative differentials of `A̲ ⟶ 𝒪` on the small model of `C_{B/A}`, whose
value over `(P, α)` is `Ω[P⁄A]`. No universe lift intervenes, unlike on the unrestricted site. -/
def smallAtiyahRelativeDifferentialsPresheaf :
    PresheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (smallAtiyahStructureSheaf A B κ)).obj :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (smallAtiyahBaseHom A B κ).hom

/-- **The sheaf of relative differentials `Ω_{𝒪/A}` on the small model of `C_{B/A}`**, a sheaf of
`𝒪`-modules. It is the objectwise module of Kähler differentials, which is already a sheaf
because the topology is chaotic. -/
def smallAtiyahRelativeDifferentials :
    moduleSheaves.{u, u, u, u} (smallAtiyahStructureSheaf A B κ) where
  val := smallAtiyahRelativeDifferentialsPresheaf A B κ
  isSheaf := Presheaf.isSheaf_bot _

/-- The universal relative derivation of `𝒪` over `A̲` with values in `Ω_{𝒪/A}`. -/
def smallAtiyahUniversalDerivation :
    (smallAtiyahRelativeDifferentials A B κ).val.Derivation'
      (smallAtiyahBaseHom A B κ).hom :=
  PresheafOfModules.DifferentialsConstruction.derivation' (smallAtiyahBaseHom A B κ).hom

/-- **Tag 04BL for the small model of `C_{B/A}`.** `Ω_{𝒪/A}` corepresents the functor sending a
sheaf of `𝒪`-modules to the relative derivations of `𝒪` over `A̲` with values in it, so it is the
sheaf of differentials of `A̲ ⟶ 𝒪` in the sense the principal-parts sequence uses. Only the
presheaf-level universal property of Mathlib's `relativeDifferentials'` is needed: every presheaf
on a chaotic site is a sheaf, so a morphism of sheaves of modules is a morphism of the underlying
presheaves. -/
def smallAtiyahRelativeDifferentialsCorepresentableBy :
    (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u} (smallAtiyahBaseSheaf A B κ)
        (smallAtiyahStructureSheaf A B κ)
        (smallAtiyahBaseHom A B κ)).CorepresentableBy
      (smallAtiyahRelativeDifferentials A B κ) := by
  refine AlgebraicGeometry.SheafOfModules.universalDerivationCorepresentableBy.{u, u, u, u}
    _ _ _ (smallAtiyahUniversalDerivation A B κ) (fun F D => ?_)
  refine ⟨⟨(PresheafOfModules.DifferentialsConstruction.isUniversal'
    (smallAtiyahBaseHom A B κ).hom).desc D⟩, ?_, fun g hg => ?_⟩
  · exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (smallAtiyahBaseHom A B κ).hom).fac D
  · exact SheafOfModules.hom_ext
      ((PresheafOfModules.DifferentialsConstruction.isUniversal'
        (smallAtiyahBaseHom A B κ).hom).postcomp_injective _ _
          (hg.trans ((PresheafOfModules.DifferentialsConstruction.isUniversal'
            (smallAtiyahBaseHom A B κ).hom).fac D).symm))

/-- **The first vertex of the Atiyah triangle is formed with `Ω_{𝒪/A}`.** The corepresenting
object that the sequence of first principal parts is built from is identified with the objectwise
sheaf of Kähler differentials of the small model, by uniqueness of corepresenting objects. -/
def smallAtiyahDerivationsCoreprXIso :
    (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u} (smallAtiyahBaseSheaf A B κ)
        (smallAtiyahStructureSheaf A B κ) (smallAtiyahBaseHom A B κ)).coreprX ≅
      smallAtiyahRelativeDifferentials A B κ :=
  haveI := (smallAtiyahRelativeDifferentialsCorepresentableBy A B κ).isCorepresentable
  (smallAtiyahRelativeDifferentialsCorepresentableBy A B κ).isoCoreprX.symm

/-! ### The Atiyah triangle of a module on the small model -/

variable (M : ModuleCat.{u} (B : Type u))

/-- The sequence of first principal parts of the sheaves of `𝒪`-modules on the small model of
`C_{B/A}`, relative to the constant sheaf of rings `A`. -/
def smallAtiyahPrincipalPartsSequence :
    PrincipalPartsSequence.{u, u, u, u} (smallAtiyahBaseSheaf A B κ)
      (smallAtiyahStructureSheaf A B κ) (smallAtiyahBaseHom A B κ) :=
  principalPartsSequenceOfSite.{u, u, u, u} _ _ (smallAtiyahBaseHom A B κ)

/-- A `B`-module read as a sheaf of `𝒪`-modules on the small model of `C_{B/A}`: the constant
sheaf with value `M`, with `P` acting through the augmentation `α : P → B`. -/
def smallAtiyahModuleSheaf :
    moduleSheaves.{u, u, u, u} (smallAtiyahStructureSheaf A B κ) :=
  (Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (smallAtiyahStructureSheaf A B κ))).inverse.obj
    ((Stacks.ChaoticSite.coefficientRestriction (B : Type u)
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (smallAtiyahStructureSheaf A B κ)).obj
      (smallPolynomialAugmentation A B κ)).obj ((Functor.const _).obj M))

/-- **The Atiyah triangle of a `B`-module `M` on the small model of `C_{B/A}`**: the image under
`Lπ_! : D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ] of the sequence of first principal parts of `M`. -/
def smallPolynomialAtiyahTriangle :
    Triangle (DerivedCategory (ModuleCat.{u} (B : Type u))) :=
  Stacks.Atiyah.triangle (smallAtiyahPrincipalPartsSequence A B κ)
    (smallAtiyahModuleSheaf A B κ M) (B : Type u) (smallPolynomialAugmentation A B κ)

/-- **The Atiyah triangle on the small model is distinguished**: it is the image of a short exact
sequence of sheaves of `𝒪`-modules under the exact functor `Lπ_!` of [Stacks, Tag 09CZ]. -/
theorem smallPolynomialAtiyahTriangle_distinguished :
    smallPolynomialAtiyahTriangle A B κ M ∈ distinguishedTriangles :=
  Stacks.Atiyah.triangle_distinguished _ _ _ _

/-- The first term of the Atiyah triangle is `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M)`. -/
theorem smallPolynomialAtiyahTriangle_obj₁ :
    (smallPolynomialAtiyahTriangle A B κ M).obj₁ =
      (Stacks.Atiyah.lowerShriek (O₂ := smallAtiyahStructureSheaf A B κ) (B : Type u)
          (smallPolynomialAugmentation A B κ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (Stacks.Atiyah.chaoticModel.obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            (smallAtiyahStructureSheaf A B κ)).flip.obj
            (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u}
              (smallAtiyahBaseSheaf A B κ) (smallAtiyahStructureSheaf A B κ)
              (smallAtiyahBaseHom A B κ)).coreprX).obj (smallAtiyahModuleSheaf A B κ M)))) :=
  rfl

/-- The second term of the Atiyah triangle is `Lπ_!(P¹_{𝒪/A}(M))`. -/
theorem smallPolynomialAtiyahTriangle_obj₂ :
    (smallPolynomialAtiyahTriangle A B κ M).obj₂ =
      (Stacks.Atiyah.lowerShriek (O₂ := smallAtiyahStructureSheaf A B κ) (B : Type u)
          (smallPolynomialAugmentation A B κ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (Stacks.Atiyah.chaoticModel.obj
          ((smallAtiyahPrincipalPartsSequence A B κ).principalParts.obj
            (smallAtiyahModuleSheaf A B κ M)))) :=
  rfl

/-- The third term of the Atiyah triangle is `Lπ_!(M)`. -/
theorem smallPolynomialAtiyahTriangle_obj₃ :
    (smallPolynomialAtiyahTriangle A B κ M).obj₃ =
      (Stacks.Atiyah.lowerShriek (O₂ := smallAtiyahStructureSheaf A B κ) (B : Type u)
          (smallPolynomialAugmentation A B κ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Atiyah.chaoticModel.obj (smallAtiyahModuleSheaf A B κ M))) :=
  rfl

/-- **The Atiyah class of `M` on the small model of `C_{B/A}`**: the last arrow of the Atiyah
triangle. -/
def smallPolynomialAtiyahClass :
    (smallPolynomialAtiyahTriangle A B κ M).obj₃ ⟶
      (smallPolynomialAtiyahTriangle A B κ M).obj₁⟦(1 : ℤ)⟧ :=
  (smallPolynomialAtiyahTriangle A B κ M).mor₃

end CommAlgCat

end
