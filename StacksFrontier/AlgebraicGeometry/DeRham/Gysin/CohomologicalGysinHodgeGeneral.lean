module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin map on cohomology, with its source read on the closed subscheme

`Stacks.DeRham.CohomologicalGysin.gysinCohomologyMap` builds the Gysin map of
[Stacks, Tag 0G8A] out of an arbitrary sheaf-level Gysin map `γ : 𝒜 ⟶ i_*ℋ ^c_Z(ℱ)` and
arbitrary `𝒪_X`-modules, but with every cohomology group read on `X`: its source is
`H^q(X, 𝒜)`.  The source of [Stacks, Tag 0G8A] writes the source of `γ^{p, q}` on the closed
subscheme instead,

`γ^{p, q} : H^q(Z, Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})`.

This file supplies that reading at the full generality of `gysinCohomologyMap`.  For `𝒜` the
direct image `i_*𝒜'` of a quasi-coherent module on the closed subscheme, the two sources are
identified by the affine-pushforward comparison of [Stacks, Tag 089W]: a closed immersion is an
affine morphism, so `H^q(Z, 𝒜') = H^q(X, i_*𝒜')`.

## Main definitions

* `gysinHodgeMapOfClosed`: the composite, for an arbitrary closed subset `T ⊆ X` carrying the
  local cohomology.
* `gysinHodgeMap`: **[Stacks, Tag 0G8A]** with `T` the image of the closed immersion, which is
  the source's situation — the map `H^q(Z, 𝒜') ⟶ H^{q + c}(X, ℱ)` induced by an arbitrary
  sheaf-level Gysin map `γ : i_*𝒜' ⟶ i_*ℋ ^c_Z(ℱ)`.
* `gysinHodgeFormsMap`: **[Stacks, Tag 0G8A]** at the source's own coefficient modules
  `𝒜' = Ω^p_{Z/S}` and `ℱ = Ω^{p + c}_{X/S}`, where the quasi-coherence the comparison needs is
  proved rather than assumed.

## Main results

* `equationGysinHodgeMap_eq`: `equationGysinHodgeMap` is `gysinHodgeMapOfClosed` at the Gysin
  map of the family of equations, by definition.

## Implementation notes

The sheaf-level `γ` is an input here, as it is in `gysinCohomologyMap`. Applied to the `γ^p` of
[Stacks, Tag 0G86] it gives the source's `γ^{p, q}`; that case is
`Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank`.

`gysinHodgeMapOfClosed` takes the closed subset `T` carrying the local cohomology separately from
the closed immersion `i`, so that `equationGysinHodgeMap_eq` holds by definition: there the
closed subset is the common zero locus `equationsClosedSet f` of the equations, which is `i(Z)`
only up to the propositional equality `Stacks.Gysin.equationsClosedSet_eq_range`.

## References

* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes

namespace Stacks.DeRham.CohomologicalGysin

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

/-- Sheaves of modules on a ringed space have a derived category. -/
local instance moduleSheavesHasDerivedCategory' (X : RingedSpace.{u, u}) :
    HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
  HasDerivedCategory.standard _

section HodgeGeneral

open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

variable {Z X S : Scheme.{u}}

/-- **The Gysin map on cohomology with its source read on the closed subscheme**, for the local
cohomology taken with supports in an arbitrary closed subset `T ⊆ X`.

The source `H^q(X, i_*𝒜')` of `gysinCohomologyMap` is rewritten as `H^q(Z, 𝒜')` by the
affine-pushforward comparison of [Stacks, Tag 089W]: a closed immersion is an affine morphism,
so `Stacks.AffineCohomologyResolution.cohomologyPushforwardIso` applies to the quasi-coherent
`𝒜'`. -/
def gysinHodgeMapOfClosed (i : Z ⟶ X) [IsClosedImmersion i]
    (T : Set X.carrier) (hT : IsClosed T) (c : ℕ)
    (A : Z.Modules) (hA : A.IsQuasicoherent) (F : X.Modules)
    (hvan : ∀ j : ℤ, j < (c : ℤ) → IsZero (localCohomologySheafOfComplex X.toRingedSpace T hT j
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (γ : (Scheme.Modules.pushforward i).obj A ⟶
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).obj
        (localCohomologySheafOfComplex X.toRingedSpace T hT (c : ℤ)
          ((singleFunctor _ (0 : ℤ)).obj F)))
    (q : ℕ) :
    Hgroup Z.ringCatSheaf ⊤ q A ⟶ Hgroup X.ringCatSheaf ⊤ (q + c) F :=
  ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i q).app ⟨A, hA⟩).hom ≫
    gysinCohomologyMap T hT c _ F hvan γ q

/-- **Stacks Project, Tag 0G8A: the Gysin map on cohomology, with the source written on the
closed subscheme.** Let `i : Z ⟶ X` be a closed immersion of schemes, let `c ≥ 0`, let `𝒜'` be a
quasi-coherent module on `Z`, let `ℱ` be an `𝒪_X`-module and assume

`ℋ ^j_{i(Z)}(ℱ) = 0` for `j = 0, …, c - 1`.

A sheaf-level Gysin map `γ : i_*𝒜' ⟶ i_*ℋ ^c_{i(Z)}(ℱ)` then induces

`γ^{p, q} : H^q(Z, 𝒜') ⟶ H^{q + c}(X, ℱ)`

for every `q`.  This is `gysinCohomologyMap`, whose source is `H^q(X, i_*𝒜')`, preceded by the
affine-pushforward comparison of [Stacks, Tag 089W]. -/
def gysinHodgeMap (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (A : Z.Modules) (hA : A.IsQuasicoherent) (F : X.Modules)
    (hvan : ∀ j : ℤ, j < (c : ℤ) → IsZero (localCohomologySheafOfComplex X.toRingedSpace
      (Set.range i.base) i.isClosedEmbedding.isClosed_range j
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (γ : (Scheme.Modules.pushforward i).obj A ⟶
      (modulePushforward (closedSubsetInclusion X.toRingedSpace (Set.range i.base))).obj
        (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
          i.isClosedEmbedding.isClosed_range (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F)))
    (q : ℕ) :
    Hgroup Z.ringCatSheaf ⊤ q A ⟶ Hgroup X.ringCatSheaf ⊤ (q + c) F :=
  gysinHodgeMapOfClosed i (Set.range i.base) i.isClosedEmbedding.isClosed_range c A hA F hvan γ q

/-- **Stacks Project, Tag 0G8A at the source's own coefficient modules.** This is
`gysinHodgeMap` read at `𝒜' = Ω^p_{Z/S}` and `ℱ = Ω^{p + c}_{X/S}`, so that it has exactly the
shape of the source's

`γ^{p, q} : H^q(Z, Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})`.

The quasi-coherence of `Ω^p_{Z/S}` needed by [Stacks, Tag 089W] is
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`. -/
def gysinHodgeFormsMap (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ)
    (hvan : ∀ j : ℤ, j < (c : ℤ) → IsZero (localCohomologySheafOfComplex X.toRingedSpace
      (Set.range i.base) i.isClosedEmbedding.isClosed_range j
      ((singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))
    (γ : (Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) (p : ℤ)) ⟶
      (modulePushforward (closedSubsetInclusion X.toRingedSpace (Set.range i.base))).obj
        (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
          i.isClosedEmbedding.isClosed_range (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj
            (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))
    (q : ℕ) :
    Hgroup Z.ringCatSheaf ⊤ q (relativeDifferentialForms (i ≫ π) (p : ℤ)) ⟶
      Hgroup X.ringCatSheaf ⊤ (q + c) (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) :=
  gysinHodgeMap i c (relativeDifferentialForms (i ≫ π) (p : ℤ))
    (isQuasicoherent_relativeDifferentialForms (i ≫ π) p)
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) hvan γ q

/-- **The Gysin map of a global family of equations on Hodge cohomology is the general
construction applied to that family's sheaf-level Gysin map**,
`AlgebraicGeometry.Scheme.Hom.gysinMapOfFormKernel`; the two sides are definitionally equal. -/
theorem equationGysinHodgeMap_eq (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ)
    [(relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent]
    (hcut : Stacks.Gysin.IsCutOutByEquations i f)
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace
        (Stacks.Perfect.CechDerivedSupport.equationsClosedSet f)
        (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet f) j
        ((singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))
    (q : ℕ) :
    equationGysinHodgeMap i π f p hcut hvan q =
      gysinHodgeMapOfClosed i (Stacks.Perfect.CechDerivedSupport.equationsClosedSet f)
        (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet f) c
        (relativeDifferentialForms (i ≫ π) (p : ℤ))
        (isQuasicoherent_relativeDifferentialForms (i ≫ π) p) _ hvan
        (gysinMapOfFormKernel i π f p
          (formKernelGeneratedByEquations_of_isCutOutByEquations i π hcut p)) q :=
  rfl

end HodgeGeneral

end Stacks.DeRham.CohomologicalGysin

end
