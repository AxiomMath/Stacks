module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedHomotopy
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentativeUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmple
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonBijective
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.Separated

/-!
# [Stacks, Tag 0F8H] where no hypothesis is left over

In `Stacks.Perfect.BoundedLocallyFreeComplexes`,
`exists_boundedFiniteLocallyFree_homotopy_of_exists_isAffineHom_isNoetherian_hasResolutionProperty`
is [Stacks, Tag 0F8H], and it carries the hypothesis `hmodel`: that `X` admits an affine morphism
to a Noetherian scheme with the resolution property.  That is the whole use [Stacks, Tag 0F8C]
makes of the converse of [Stacks, Tag 0F8B], which this library does not prove.

This file records the classes of schemes on which `hmodel` is discharged, so that the statement
is available with nothing assumed beyond the scheme: separated schemes, Noetherian schemes,
schemes with an ample invertible module, and affine schemes.  A separated scheme has affine
diagonal ([Stacks, Tag 0BDX]), so it bypasses Tag 0F8C entirely; a Noetherian scheme satisfies
`hmodel` with `Y = X` and `f = 𝟙`; and an ample invertible module gives quasi-compactness, the
resolution property ([Stacks, Tag 0F87]) and separatedness ([Stacks, Tag 09MP]) at once.

## Main results

All names are in the namespace `Stacks.Perfect.BoundedLocallyFreeComplexes`.

* `exists_affineNoetherianModel_of_isNoetherian`: a Noetherian scheme with the resolution
  property satisfies `hmodel`, by `Y = X` and `f = 𝟙`. This is what makes the hypothesis of the
  tagged statement satisfiable rather than merely true.
* `exists_boundedFiniteLocallyFree_homotopy_of_isSeparated` and `..._of_isNoetherian`,
  `..._of_isAmple`, `..._of_isAffine`: the conclusion of [Stacks, Tag 0F8H] on those schemes, with
  no hypothesis beyond the ones named.
* `exists_boundedFiniteLocallyFree_homotopy_unit_spec`, `..._twistingSheaf_projectiveSpace` and
  `..._twistingSheaf_projectiveSpaceOverIntegers`: the conclusion at three instances with every
  binder filled in — the structure sheaf on `Spec R`, the hyperplane sheaf on `ℙⁿ_S`, and the
  hyperplane sheaf on `ℙⁿ_ℤ`.  They assume nothing at all, so they are what shows the statement is
  not vacuous.  The last one goes through the *tagged* statement, with `hmodel` supplied; it is
  therefore a witness that the residual hypothesis of the tag is satisfiable.

## Implementation notes

The hypotheses of the four general forms are all *narrower* than those of [Stacks, Tag 0F8H]
itself, so none of them carries a `@[stacks]` attribute: the tag belongs on the statement with
the source's own hypotheses, which is in
`StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/DerivedHomotopy.lean`.

The three instantiated statements take `ℰ^• = ℱ^•` a single invertible module in degree zero and
`α = β` the identity.  Taking `α = β` is not a choice: at an instance where `ℰ^•` and `ℱ^•` are
single modules in degree zero the hypothesis `DerivedCategory.Q.map α = DerivedCategory.Q.map β`
*forces* `α = β`, since `Hom_{D(𝒪_X)}(ℰ^•, ℱ^•)` is then `Hom(ℰ^0, ℱ^0)`.  An instance with
`α ≠ β` therefore needs a complex with at least two nonzero terms — the mapping cone of an
identity is the cheapest — and that in turn needs finite local freeness of a biproduct of
modules, which this library does not have in either of its two `IsFiniteLocallyFree` spellings.
`ℙⁿ_S` and `ℙⁿ_ℤ` are among the instances because an affine scheme would leave every witness
inside the class of schemes on which the derived inclusion of the quasi-coherent modules is full
for trivial reasons.

Finite local freeness is recorded by two classes with the same single field, as the
implementation notes of `StacksFrontier/AlgebraicGeometry/ModuleLimits/FiniteLocallyFree.lean`
describe: `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, in which invertibility of rank
one is stated, and `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, in which
`boundedFiniteLocallyFreeComplex` is.  The one-field transfer between them is spelled out where
it is needed rather than through a bridge lemma of its own.

## References

* [Stacks Project, Tag 0F8H](https://stacks.math.columbia.edu/tag/0F8H)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 0F87](https://stacks.math.columbia.edu/tag/0F87)
* [Stacks Project, Tag 09MP](https://stacks.math.columbia.edu/tag/09MP)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AmpleProjectiveImmersion
open Stacks.Cohomology.PerfectComplexes
open Stacks.FiniteLocallyFree
open Stacks.ProjectiveSpace

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A Noetherian scheme with the resolution property is affine over a Noetherian scheme with
the resolution property**, namely over itself.  This is the hypothesis `hmodel` of the
formalized form of [Stacks, Tag 0F8H] and of [Stacks, Tag 0F8C]; the point of stating it is that it makes
that hypothesis satisfiable, so the tagged statement can be instantiated. -/
theorem exists_affineNoetherianModel_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    [HasResolutionProperty X] :
    ∃ (Y : Scheme.{u}) (f : X ⟶ Y),
      IsAffineHom f ∧ IsNoetherian Y ∧ HasResolutionProperty Y :=
  ⟨X, 𝟙 X, inferInstance, inferInstance, inferInstance⟩

/-- **[Stacks, Tag 0F8H] on a quasi-compact separated scheme with the resolution property.**  A
separated scheme has affine diagonal, so no form of [Stacks, Tag 0F8C] is needed. -/
theorem exists_boundedFiniteLocallyFree_homotopy_of_isSeparated (X : Scheme.{u})
    [CompactSpace X] [X.IsSeparated] [HasResolutionProperty X]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) :=
  exists_boundedFiniteLocallyFree_homotopy_of_affineDiagonal X E F hE hF α β h

/-- **[Stacks, Tag 0F8H] on a Noetherian scheme with the resolution property.**  The residual
hypothesis `hmodel` is satisfied by the identity of `X`, so nothing is assumed beyond the scheme
being Noetherian with the resolution property. -/
theorem exists_boundedFiniteLocallyFree_homotopy_of_isNoetherian (X : Scheme.{u})
    [IsNoetherian X] [HasResolutionProperty X]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) :=
  have _ : QuasiSeparatedSpace X := IsLocallyNoetherian.quasiSeparatedSpace
  exists_boundedFiniteLocallyFree_homotopy_of_exists_isAffineHom_isNoetherian_hasResolutionProperty
    X (exists_affineNoetherianModel_of_isNoetherian X) E F hE hF α β h

/-- **[Stacks, Tag 0F8H] on a scheme carrying an ample invertible module.**  Ampleness supplies
quasi-compactness, the resolution property ([Stacks, Tag 0F87]) and separatedness
([Stacks, Tag 09MP]), hence the affine diagonal. -/
theorem exists_boundedFiniteLocallyFree_homotopy_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) :=
  have _ : CompactSpace X := hL.1
  have _ : HasResolutionProperty X := hasResolutionProperty_of_isAmple L hL
  have _ : X.IsSeparated :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X L hL).isSeparated
  exists_boundedFiniteLocallyFree_homotopy_of_isSeparated X E F hE hF α β h

/-- **[Stacks, Tag 0F8H] on an affine scheme.**  The structure sheaf is ample on an affine
scheme. -/
theorem exists_boundedFiniteLocallyFree_homotopy_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) :=
  exists_boundedFiniteLocallyFree_homotopy_of_isAmple X (Stacks.Ample.unitModule X)
    (Stacks.Ample.isAmple_unitModule_of_isAffine X) E F hE hF α β h

/-- **[Stacks, Tag 0F8H] for the identity of the structure sheaf of `Spec R`.**  Every binder is
filled in: the identity of `𝒪_{Spec R}` in degree zero, compared with itself, becomes homotopic
after a quasi-isomorphism from a bounded complex of finite locally free modules. -/
theorem exists_boundedFiniteLocallyFree_homotopy_unit_spec (R : CommRingCat.{u}) :
    ∃ (G : CochainComplex (Spec R).Modules ℤ)
      (γ : G ⟶ (CochainComplex.singleFunctor (Spec R).Modules 0).obj
        (SheafOfModules.unit (Spec R).ringCatSheaf)) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex (Spec R) G ∧
        Nonempty (Homotopy (γ ≫ 𝟙 _) (γ ≫ 𝟙 _)) :=
  have hE := boundedFiniteLocallyFreeComplex_single (Spec R) _ (isFiniteLocallyFree_unit (Spec R))
  exists_boundedFiniteLocallyFree_homotopy_of_isAffine (Spec R) _ _ hE hE (𝟙 _) (𝟙 _) rfl

/-- Finite local freeness of the hyperplane sheaf of `ℙⁿ_S`, in the spelling
`boundedFiniteLocallyFreeComplex` uses.  It is invertible, hence finite locally free of rank
one. -/
private theorem isFiniteLocallyFree_projectiveSpaceTwistingSheaf (n : ℕ) (S : Scheme.{u})
    [IsAffine S] :
    IsFiniteLocallyFree.{u, u, u} (R := (projectiveSpaceOver n S).ringCatSheaf)
      (projectiveSpaceTwistingSheaf n S) := by
  have hrk := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
    (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S)
  constructor
  exact (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (M := projectiveSpaceTwistingSheaf n S) (r := 1)
    (hM := hrk)).exists_isFiniteLocallyFreeData

/-- **[Stacks, Tag 0F8H] for the identity of `𝒪(1)` on `ℙⁿ_S`, `S` affine.**  Every binder is
filled in, at a scheme that is not affine. -/
theorem exists_boundedFiniteLocallyFree_homotopy_twistingSheaf_projectiveSpace
    (n : ℕ) (S : Scheme.{u}) [IsAffine S] :
    ∃ (G : CochainComplex (projectiveSpaceOver n S).Modules ℤ)
      (γ : G ⟶ (CochainComplex.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (projectiveSpaceTwistingSheaf n S)) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex (projectiveSpaceOver n S) G ∧
        Nonempty (Homotopy (γ ≫ 𝟙 _) (γ ≫ 𝟙 _)) :=
  have hE := boundedFiniteLocallyFreeComplex_single _ _
    (isFiniteLocallyFree_projectiveSpaceTwistingSheaf n S)
  exists_boundedFiniteLocallyFree_homotopy_of_isAmple (projectiveSpaceOver n S)
    (projectiveSpaceTwistingSheaf n S) (isAmple_projectiveSpaceTwistingSheaf n S) _ _
    hE hE (𝟙 _) (𝟙 _) rfl

/-- `ℙⁿ` over the spectrum of the integers, the instance at which the residual hypothesis of
[Stacks, Tag 0F8H] is exhibited as satisfiable: it is Noetherian, which is what `hmodel` needs,
and it is not affine. -/
abbrev projectiveSpaceOverIntegers (n : ℕ) : Scheme.{u} :=
  projectiveSpaceOver n (Spec (CommRingCat.of (ULift.{u} ℤ)))

/-- `ℙⁿ_ℤ` is Noetherian: the integers are, and projective space over a Noetherian scheme is
Noetherian. -/
private theorem isNoetherian_projectiveSpaceOverIntegers (n : ℕ) :
    IsNoetherian (projectiveSpaceOverIntegers.{u} n) :=
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  projectiveSpaceOver_isNoetherian n (Spec (CommRingCat.of (ULift.{u} ℤ)))

/-- **[Stacks, Tag 0F8H] for the identity of `𝒪(1)` on `ℙⁿ_ℤ`, through the tagged statement
itself.**  Every binder of
`exists_boundedFiniteLocallyFree_homotopy_of_exists_isAffineHom_isNoetherian_hasResolutionProperty`
is filled in from declarations that assume nothing, the residual hypothesis `hmodel` included:
`ℙⁿ_ℤ` is Noetherian, so `hmodel` holds with `Y = ℙⁿ_ℤ` and `f = 𝟙`.  The scheme is not affine,
and the module is not the structure sheaf. -/
theorem exists_boundedFiniteLocallyFree_homotopy_twistingSheaf_projectiveSpaceOverIntegers
    (n : ℕ) :
    ∃ (G : CochainComplex (projectiveSpaceOverIntegers.{u} n).Modules ℤ)
      (γ : G ⟶ (CochainComplex.singleFunctor (projectiveSpaceOverIntegers.{u} n).Modules 0).obj
        (projectiveSpaceTwistingSheaf n (Spec (CommRingCat.of (ULift.{u} ℤ)))))
      (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex (projectiveSpaceOverIntegers.{u} n) G ∧
        Nonempty (Homotopy (γ ≫ 𝟙 _) (γ ≫ 𝟙 _)) :=
  have hN : IsNoetherian (projectiveSpaceOverIntegers.{u} n) :=
    isNoetherian_projectiveSpaceOverIntegers n
  have _ : CompactSpace (projectiveSpaceOverIntegers.{u} n) := hN.toCompactSpace
  have _ : IsLocallyNoetherian (projectiveSpaceOverIntegers.{u} n) := hN.toIsLocallyNoetherian
  have _ : QuasiSeparatedSpace (projectiveSpaceOverIntegers.{u} n) :=
    IsLocallyNoetherian.quasiSeparatedSpace
  have _ : HasResolutionProperty (projectiveSpaceOverIntegers.{u} n) :=
    hasResolutionProperty_of_isAmple (projectiveSpaceTwistingSheaf n _)
      (isAmple_projectiveSpaceTwistingSheaf n (Spec (CommRingCat.of (ULift.{u} ℤ))))
  have hE := boundedFiniteLocallyFreeComplex_single _ _
    (isFiniteLocallyFree_projectiveSpaceTwistingSheaf n (Spec (CommRingCat.of (ULift.{u} ℤ))))
  exists_boundedFiniteLocallyFree_homotopy_of_exists_isAffineHom_isNoetherian_hasResolutionProperty
    (projectiveSpaceOverIntegers.{u} n)
    (exists_affineNoetherianModel_of_isNoetherian (projectiveSpaceOverIntegers.{u} n)) _ _
    hE hE (𝟙 _) (𝟙 _) rfl

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
