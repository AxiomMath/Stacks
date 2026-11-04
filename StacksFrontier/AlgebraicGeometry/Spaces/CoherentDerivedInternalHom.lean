module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentEtaleChartTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall
import StacksCore.Tactic.StacksAttribute

/-! # Derived internal Hom of coherent complexes on an algebraic space

Let `X` be a locally Noetherian algebraic space over a scheme `S`. For `K` in `D⁻_Coh(𝒪_X)` and
`L` in `D⁺_Coh(𝒪_X)`, Stacks 0D0S asserts that `RSheafHom(K, L)` lies in `D⁺_Coh(𝒪_X)`.

`RSheafHom(K, L)` is read, as the source reads it, on models: it is the internal Hom complex
`SheafHom(A, J)` of a complex `A` representing `K` and a K-injective complex `J` representing
`L`, and such a pair exists. Both clauses of the tag are then statements about that complex of
`𝒪_X`-modules on the small étale ringed site of `X`.

**The `D⁺` clause is proved here, unconditionally.** If `A` is
concentrated in degrees `≤ d` and `J` in degrees `≥ b` then `SheafHom(A, J)` is concentrated in
degrees `≥ b - d` (`AlgebraicGeometry.RingedSite.isStrictlyGE_sheafHomComplex`), so its class in
`D(𝒪_X)` is cohomologically bounded below; this needs neither local Noetherianity nor coherence.
Both clauses together, at the module universe of the structure rings, are
`AlgebraicGeometry.Space.derivedCategoryBPlus_isCoherentOnSite_sheafHomComplex` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedInternalHomCoherentCohomology`; the
implementation notes record why the coherent clause is out of reach at the module universe used
here.

Also proved: coherence of the cohomology modules of a complex of `𝒪_X`-modules is étale-local
(`AlgebraicGeometry.Space.isCoherentOnSite_homology_of_forall_affine_restrict`).

## Main results

* `AlgebraicGeometry.Space.isGE_sheafHomComplex`: the degree bound `b - d`.
* `AlgebraicGeometry.Space.isBoundedBelow_sheafHomComplex` and
  `AlgebraicGeometry.Space.isBoundedBelow_derivedSheafHomOnSpace`: **the bounded-below clause of
  Stacks 0D0S**, on a pair of models and for `K` and `L` themselves.
* `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_forall_affine_restrict`: coherence of the
  cohomology modules of a complex of `𝒪_X`-modules is étale-local.
* `AlgebraicGeometry.Space.exists_isStrictlyLE_isStrictlyGE_isKInjective_model`: the models on
  which the derived internal Hom is computed exist.

## Implementation notes

**Why the coherent clause is out of reach at the module universe `max (u + 1) m` used here.**
The source's proof is "coherence may be checked étale-locally (Stacks 07UB), so this follows
from the case of schemes (Stacks 0D0C)". The first
half is available and is `isCoherentOnSite_homology_of_forall_affine_restrict` below. The second
half is not, and assuming its conclusion on charts would assume the clause itself: coherence on
the small étale site is *equivalent* to coherence of the restrictions to the affine étale charts
(`AlgebraicGeometry.Space.isCoherentOnSite_iff_forall_affine_over`), and restriction to a slice
is exact, so "the cohomology of the restricted internal Hom complex is coherent on every affine
chart" and "the cohomology of the internal Hom complex is coherent" are the same statement.
Reaching the second half from Stacks 0D0C for schemes —
`AlgebraicGeometry.derivedCategoryBPlus_isCoherent_derivedSheafHom` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/SchemeCoherentDerivedHom.lean`, which is the
tag on an arbitrary locally Noetherian scheme — needs two constructions that are absent:

* identification of the sections of the internal Hom complex over an étale chart with morphisms
  in the derived category of the chart. This is Stacks 0A94, and the clause of it over an object
  of the site, `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom`, is
  stated only for a ringed site whose objects, morphisms and structure rings lie in one universe,
  because it needs the restriction of a K-injective complex to a slice to be K-injective
  (Stacks 08FI, `Stacks.Cohomology.Localization.isKInjective_over`), which rests on exactness of
  extension by zero (Stacks 03DJ,
  `Stacks.Sites.ExtensionByZero.extensionByZero_exact`) and through it on Grothendieck's axiom
  AB4 for `ModuleCat` with the index type and the modules in the same universe. The small étale
  ringed site of an algebraic space is `AlgebraicGeometry.RingedSite.{u + 1, u, u}`. The global
  clause of Stacks 0A94,
  `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom`, *is* available at
  these universes, but computes sections over the final object only;
* comparison of the derived category of `𝒪`-modules on the small étale site of an affine chart
  with the derived category of modules over its ring of functions, which is what turns those
  morphism groups into finite modules. Nothing in this development relates sheaves of modules on
  the small étale site of a scheme to sheaves of modules on its Zariski site, in either
  direction.

A third input would be needed even granted both. Passing from finiteness of the modules of
sections over the affine charts to `SheafOfModules.IsCoherentOnSite`, whose finite-type clause is
about local generation, goes through
`AlgebraicGeometry.Space.isCoherentOnSite_of_isCartesian`, whose cartesian hypothesis is supplied
by quasi-coherence — `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`
is Descent, Proposition 03DX(2), and it is proved, at the module universe `u` of the structure
rings. So that route additionally needs the cohomology of the internal Hom complex to be
quasi-coherent, which is clause (6) of Stacks 03M1; the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLocal` record that this clause is
not reached in this tree, and the module universe would have to be `u` as well.

**The derived internal Hom bifunctor is deliberately not used.**
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` is pinned to a ringed site with all three
universes equal, and the pin is load-bearing by the same chain as above: it needs Stacks 0A95
(`AlgebraicGeometry.RingedSite.homMap_quasiIso`), which needs Stacks 08FI, which needs Stacks
03DJ. Reading `RSheafHom(K, L)` on models uses only `AlgebraicGeometry.RingedSite.sheafHomComplex`
(Stacks 0A8Z), which is already polymorphic in the three site universes and in the module
universe, so none of that chain is required. For the same reason
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` (Stacks 0E8H on complexes), which is
pinned likewise, is not used: the étale-locality statement below is phrased on the restriction of
the internal Hom complex rather than on the internal Hom complex of the restrictions.

Coherence is `SheafOfModules.IsCoherentOnSite`, coherence on the small étale ringed site
(Stacks 01BW), and not `AlgebraicGeometry.Space.IsCoherent` (Stacks 07UA), which adds
quasi-coherence. The two agree by
`AlgebraicGeometry.Space.isCoherent_iff_isCoherentOnSite` at the module universe `u` of the
structure rings — and `u` is the one module universe at which these statements cannot be made:
the internal Hom complex of Stacks 0A8Z raises the module universe of a site with objects in
`Type (u + 1)` from `m` to `max (u + 1) m`, so `SheafHom(A, J)` lies in the same category as `A`
and `J` only for `m = max (u + 1) m`. Everything below is therefore at module universe
`max (u + 1) m`, where the local-to-global clause for coherence on the site holds at a free
module universe while the one for quasi-coherence
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`) binds the
module universe to the universe of the structure rings.

The two sheafification hypotheses that make `𝒪_X`-modules abelian are not assumed: at module
universe `max (u + 1) m` they follow from
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat`, since that universe
contains the universes of the site. Exactness of restriction to a slice is likewise not assumed:
at that module universe it follows from
`Stacks.SheafOfModules.overFunctor_preservesColimits` together with
`Stacks.SheafOfModules.preservesFiniteLimits_pushforward`, rather than from
`Stacks.Cohomology.Localization.restriction_exact`, which is pinned.

K-injectivity of `J` is what makes `SheafHom(A, J)` compute `RSheafHom(K, L)` rather than some
other object, so it belongs to the statement of the tag; it is not needed for the clause proved
here, which holds of the internal Hom complex of any pair of complexes with the stated bounds.

## References

* [Stacks Project, Tag 0D0S](https://stacks.math.columbia.edu/tag/0D0S)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.RingedSite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Sheafification of presheaves of abelian groups with sections in `max (u + 1) m` exists on the
small étale site, whose objects lie in `Type (u + 1)` and whose morphisms in `Type u`. -/
local instance hasSheafify_smallEtaleRingedSite :
    HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{max (u + 1) m} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) m, u, u + 1} _

/-- On the small étale site, sheafification of presheaves of abelian groups with sections in
`max (u + 1) m` inverts exactly the locally bijective morphisms. -/
local instance wEqualsLocallyBijective_smallEtaleRingedSite :
    (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{max (u + 1) m,
    u, u + 1} _

/-- Sheafification of presheaves of abelian groups with sections in `max (u + 1) m` exists on
every slice of the small étale site. -/
local instance hasSheafify_smallEtaleRingedSite_over (U : (smallEtaleRingedSite B S hS F hF).C) :
    HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over U)
      AddCommGrpCat.{max (u + 1) m} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) m, u, u + 1} _

/-- On every slice of the small étale site, sheafification of presheaves of abelian groups with
sections in `max (u + 1) m` inverts exactly the locally bijective morphisms. -/
local instance wEqualsLocallyBijective_smallEtaleRingedSite_over
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    ((smallEtaleRingedSite B S hS F hF).J.over U).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{max (u + 1) m,
    u, u + 1} _

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of `𝒪_X`-modules to a slice of the small étale site is additive: it reindexes
the components of a morphism along the forgetful functor of the slice. -/
local instance additive_overFunctor_smallEtaleRingedSite
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    (SheafOfModules.overFunctor.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O) U).Additive where
  map_add := by intros; rfl

/-- Restriction of `𝒪_X`-modules to a slice of the small étale site preserves finite limits:
it is the pushforward along the forgetful functor of the slice, and the pushforward of sheaves
of modules along a continuous functor is left exact. -/
local instance preservesFiniteLimits_overFunctor_smallEtaleRingedSite
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.pushforward.{max (u + 1) m}
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U) :
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U)))

/-- Restriction of `𝒪_X`-modules to a slice of the small étale site preserves finite colimits:
it is a left adjoint, by `Stacks.SheafOfModules.overFunctor_preservesColimits`. -/
local instance preservesFiniteColimits_overFunctor_smallEtaleRingedSite
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) :=
  have := Stacks.SheafOfModules.overFunctor_preservesColimits.{u + 1, u, u, m}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U
  inferInstance

/-- An exact functor commutes with the cohomology of a complex. -/
private def mapHomologyIsoOfExact {C₁ D₁ : Type*} [Category* C₁] [Category* D₁]
    [Abelian C₁] [Abelian D₁] (G : C₁ ⥤ D₁) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (M : CochainComplex C₁ ℤ) (n : ℤ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).homology n ≅ G.obj (M.homology n) :=
  (M.sc n).mapHomologyIso G

/-- **Coherence of the cohomology modules of a complex of `𝒪_X`-modules is étale-local.** If the
degree-`n` cohomology of the restriction of `M` to the slice at every affine étale chart is
coherent on that slice, then the degree-`n` cohomology of `M` is coherent.

The two halves are Stacks 07UB — coherence on the small étale site is tested on the affine étale
charts — and exactness of restriction to a slice, which makes it commute with cohomology. -/
public theorem isCoherentOnSite_homology_of_forall_affine_restrict
    (M : CochainComplex (Modules.{u, max (u + 1) m} B S hS F hF) ℤ) (n : ℤ)
    (h : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
      SheafOfModules.IsCoherentOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O))
        ((restrictComplex (smallEtaleRingedSite B S hS F hF) M U).homology n)) :
    SheafOfModules.IsCoherentOnSite (M.homology n) := by
  refine isCoherentOnSite_of_forall_affine_over B S hS F hF (M.homology n) fun U hU => ?_
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
    (mapHomologyIsoOfExact
      (SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) M n)
    (h U hU)

/-- **The internal Hom complex out of a bounded-above complex into a bounded-below complex is
cohomologically bounded below on an algebraic space.** If `A` is concentrated in degrees `≤ d`
and `J` in degrees `≥ b`, the class of `SheafHom(A, J)` in `D(𝒪_X)` is cohomologically
`≥ b - d`. -/
public theorem isGE_sheafHomComplex (d b : ℤ)
    (A J : CochainComplex (Modules.{u, max (u + 1) m} B S hS F hF) ℤ)
    [CochainComplex.IsStrictlyLE A d] [CochainComplex.IsStrictlyGE J b] :
    (DerivedCategory.Q.obj
      (sheafHomComplex (smallEtaleRingedSite B S hS F hF) A J).obj).IsGE (b - d) :=
  have := isStrictlyGE_sheafHomComplex (smallEtaleRingedSite B S hS F hF) A J d b
  inferInstance

/-- **Stacks 0D0S, the bounded-below clause, on a pair of models.** If `A` is concentrated in
degrees `≤ d` and `J` in degrees `≥ b`, the class of the internal Hom complex `SheafHom(A, J)`
in `D(𝒪_X)` is cohomologically bounded below.

For `A` a model of `K` and `J` a K-injective model of `L` this object is `RSheafHom(K, L)`, so
this is the `D⁺` half of the tag, with no hypothesis beyond the two bounds — neither local
Noetherianity nor coherence of the cohomology of `K` and `L`. -/
@[stacks 0D0S "the bounded-below clause, on a pair of models and with no Noetherian or coherence \
hypothesis"]
public theorem isBoundedBelow_sheafHomComplex
    (d b : ℤ) (A J : CochainComplex (Modules.{u, max (u + 1) m} B S hS F hF) ℤ)
    [CochainComplex.IsStrictlyLE A d] [CochainComplex.IsStrictlyGE J b] :
    DerivedCategoryB.IsBoundedBelow
      (DerivedCategory.Q.obj
        (sheafHomComplex (smallEtaleRingedSite B S hS F hF) A J).obj) :=
  ⟨b - d, fun i hi => (DerivedCategory.isGE_iff _ (b - d)).1
    (isGE_sheafHomComplex B S hS F hF d b A J) i hi⟩

/-- `𝒪_X`-modules with sections in `max (u + 1) m` form a Grothendieck abelian category: that
universe contains the universe of the objects of the small étale site, the universe of its
morphisms and the universe of the structure rings. -/
local instance isGrothendieckAbelian_smallEtaleModules :
    IsGrothendieckAbelian.{max (u + 1) m} (Modules.{u, max (u + 1) m} B S hS F hF) :=
  Stacks.SheafOfModules.Small.isGrothendieckAbelian_sheafOfModules.{u + 1, max (u + 1) m, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- **A bounded-above object of `D(𝒪_X)` and a bounded-below one are represented by a complex
concentrated in degrees `≤ d` and by a K-injective complex concentrated in degrees `≥ b`.**
These are the models on which the derived internal Hom is computed. -/
public theorem exists_isStrictlyLE_isStrictlyGE_isKInjective_model
    (K L : DerivedCategory (Modules.{u, max (u + 1) m} B S hS F hF)) (d b : ℤ)
    (hK : K.IsLE d) (hL : L.IsGE b) :
    ∃ A J : CochainComplex (Modules.{u, max (u + 1) m} B S hS F hF) ℤ,
      CochainComplex.IsStrictlyLE A d ∧ CochainComplex.IsStrictlyGE J b ∧
        CochainComplex.IsKInjective J ∧ Nonempty (DerivedCategory.Q.obj A ≅ K) ∧
        Nonempty (DerivedCategory.Q.obj J ≅ L) := by
  have := hK
  have := hL
  obtain ⟨A, hA, ⟨eA⟩⟩ := K.exists_iso_Q_obj_of_isLE d
  obtain ⟨C, hC, ⟨eC⟩⟩ := L.exists_iso_Q_obj_of_isGE b
  have := hC
  obtain ⟨R, -, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE b C
  exact ⟨A, R.cocomplex, hA, hR,
    CochainComplex.isKInjective_of_injective R.cocomplex b, ⟨eA.symm⟩,
    ⟨(asIso (DerivedCategory.Q.map R.ι)).symm ≪≫ eC.symm⟩⟩

/-- **Stacks 0D0S, the bounded-below clause.** Let `X` be an algebraic space over `S`. If `K` is
in `D⁻_Coh(𝒪_X)` and `L` is in `D⁺_Coh(𝒪_X)`, then `RSheafHom(K, L)` is cohomologically bounded
below.

`RSheafHom(K, L)` is the class of the internal Hom complex `SheafHom(A, J)` of a model `A` of
`K` and a K-injective model `J` of `L`; such a pair exists by
`AlgebraicGeometry.Space.exists_isStrictlyLE_isStrictlyGE_isKInjective_model`, and the
conclusion holds for it, by `AlgebraicGeometry.Space.isBoundedBelow_sheafHomComplex`.

Only the boundedness halves of `hK` and `hL` are used, and local Noetherianity of `X` is not
needed. -/
@[stacks 0D0S "the bounded-below clause, for K and L themselves and with no Noetherian \
hypothesis"]
public theorem isBoundedBelow_derivedSheafHomOnSpace
    (K L : DerivedCategory (Modules.{u, max (u + 1) m} B S hS F hF))
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun N : Modules.{u, max (u + 1) m} B S hS F hF =>
        SheafOfModules.IsCoherentOnSite N) K)
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (fun N : Modules.{u, max (u + 1) m} B S hS F hF =>
        SheafOfModules.IsCoherentOnSite N) L) :
    ∃ A J : CochainComplex (Modules.{u, max (u + 1) m} B S hS F hF) ℤ,
      CochainComplex.IsKInjective J ∧ Nonempty (DerivedCategory.Q.obj A ≅ K) ∧
        Nonempty (DerivedCategory.Q.obj J ≅ L) ∧
        DerivedCategoryB.IsBoundedBelow
          (DerivedCategory.Q.obj
            (sheafHomComplex (smallEtaleRingedSite B S hS F hF) A J).obj) := by
  obtain ⟨d, hd⟩ := hK.1
  obtain ⟨b, hb⟩ := hL.1
  have hKle : K.IsLE (d + 1) :=
    (DerivedCategory.isLE_iff K (d + 1)).mpr fun i hi => hd i (by omega)
  have hLge : L.IsGE b := (DerivedCategory.isGE_iff L b).mpr hb
  obtain ⟨A, J, hA, hJ, hJinj, ⟨eA⟩, ⟨eJ⟩⟩ :=
    exists_isStrictlyLE_isStrictlyGE_isKInjective_model B S hS F hF K L (d + 1) b hKle hLge
  have := hA
  have := hJ
  exact ⟨A, J, hJinj, ⟨eA⟩, ⟨eJ⟩, isBoundedBelow_sheafHomComplex B S hS F hF (d + 1) b A J⟩

end AlgebraicGeometry.Space

end
