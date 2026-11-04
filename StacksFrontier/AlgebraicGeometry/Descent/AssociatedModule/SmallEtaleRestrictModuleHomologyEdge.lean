module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictKInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorHomologyEdge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison `H^n(Rε_* E) ⟶ ε_*(H^n E)` on the small étale site

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of
Stacks 070R/08H7, so that `ε_*` is `AlgebraicGeometry.SmallEtale.restrictModule` and `Rε_*` is
`AlgebraicGeometry.SmallEtale.derivedRestrictModule` (Stacks 07A5 at `ε`).  The step of the proof
of Stacks 071Q that identifies the cohomology sheaves of `Rε_*` asserts

`H^n(Rε_* E) ≅ ε_*(H^n E)`

for an object `E` of `D(S_étale, 𝒪)` whose cohomology sheaves are quasi-coherent.  This file
constructs the canonical natural comparison underlying that identification, and proves it
invertible in the lowest degree.

## What this is and is not

It is **not** the clause of Stacks 0D6I on sections over an object, which is
`AlgebraicGeometry.SmallEtale.cohomologyOverObjectRestrictModuleIso`, the displayed
`H^i(ε(V), K) ≅ H^i(V, Rε_* K)`: that compares *hypercohomology over an object* on the two sites,
while the comparison here goes from a cohomology *sheaf* of `Rε_* E` to the direct image of a
cohomology sheaf of `E`.

Nor can it be obtained by moving `H^n` through `ε_*` formally.  `ε_*` carries no exactness
instance in this development — it is a right adjoint, so left exact and nothing more — and
`H^n ∘ Rε_* ≅ ε_* ∘ H^n` is false for a merely left exact functor.  What makes the comparison
exist at all is left t-exactness of `Rε_*` together with the degree-`n` agreement `R⁰ε_* ≅ ε_*`,
and that is exactly the input of `Stacks.DerivedFunctor.homologyEdge`, the edge transformation of
Stacks 0BKZ for an arbitrary right derived functor.

## Main results

* `AlgebraicGeometry.SmallEtale.homologyRestrictModuleEdge`: the canonical natural comparison
  `H^i(Rε_* E) ⟶ ε_*(H^i E)`.
* `AlgebraicGeometry.SmallEtale.isIso_homologyRestrictModuleEdge_app_of_isGE` and
  `AlgebraicGeometry.SmallEtale.homologyRestrictModuleIsoOfIsGE`: it is invertible at an object
  with no cohomology below degree `i`, with no quasi-coherence hypothesis — the lowest-degree
  identification `H^i ∘ Rε_* ≅ ε_* ∘ H^i` on `D^{≥ i}(S_étale, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.isGE_derivedRestrictModule_obj`: `Rε_*` is left t-exact.
* `AlgebraicGeometry.SmallEtale.restrictModuleDegreeNatIso`: `R⁰ε_* ≅ ε_*`, read in degree `i` on
  the objects placed in degree `i`.

## What is still owed for the quasi-coherent case

By `Stacks.DerivedFunctor.homologyEdge_app` the comparison factors as

`H^i(Rε_* E) ⟶ H^i(Rε_*(τ_{≥ i}E)) ≅ ε_*(H^i E)`,

the second factor being invertible always, so the quasi-coherent case of the identification is
exactly the statement

```lean
theorem isIso_homologyRestrictModuleEdge_app_of_isQuasicoherentOnSite (i : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) n).obj E).IsQuasicoherentOnSite) :
  IsIso ((homologyRestrictModuleEdge.{w} B S hS i).app E)
```

and, by the distinguished triangle `τ_{< i}E ⟶ E ⟶ τ_{≥ i}E`, is equivalent to the vanishing of
`H^i` and `H^{i + 1}` of `Rε_*(τ_{< i}E)`, that is to right t-exactness of `Rε_*` on the objects
with quasi-coherent cohomology.  Of the two things this needs, the first is proved and one
remains:

* **`R^p ε_* = 0` for `p > 0` on quasi-coherent `𝒪`-modules, in the module-valued spelling** —
  proved, as `AlgebraicGeometry.SmallEtale.isZero_rightDerived_restrictModuleOfSheaf`
  (`SmallEtaleModuleHigherDirectImageVanishing.lean` beside this module), with no hypothesis
  beyond `G.IsQuasicoherentOnSite` and `0 < p`.  It is *not* proved by comparing the two right
  derived functors across `SheafOfModules.toSheaf`, and that route is a dead end
  rather than a gap: the general-`p` comparison
  `Stacks.Cohomology.SiteModulePushforward.AnySite.rightDerivedPushforwardToSheafIso` forces its
  coefficient universe to dominate the universe of the objects of the sites, hence `u + 1` here
  where `u` is needed, and `SheafOfModules.toSheaf` cannot preserve injectives at all (an injective
  `𝒪`-module is not an injective abelian sheaf).  The route taken instead is Stacks 072W through
  the module-valued covering criterion
  `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`, the
  same instantiation clause (7) of Stacks 0DEW uses.  Its one new step is the transport of the
  affine vanishing from `CategoryTheory.Sheaf.H'` on
  `AlgebraicGeometry.Scheme.smallEtaleTopology` to
  `(SheafOfModules.evaluation _ _).rightDerived` on `AlgebraicGeometry.SmallEtale`, which is
  `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_associatedModule` in that same
  module.
* **The unbounded step**, which still blocks this, and *only* this.  Right t-exactness of `Rε_*`
  on the objects with quasi-coherent cohomology that are **bounded** is now proved, as
  `AlgebraicGeometry.SmallEtale.isLE_derivedRestrictModule_obj_of_isGE`, and with it the whole
  displayed statement for a bounded `E`, as
  `AlgebraicGeometry.SmallEtale.isIso_homologyRestrictModuleEdge_app_of_bounded`, both in
  `SmallEtaleRestrictModuleRightTExact.lean` beside this module.
  `τ_{< i}E` is bounded above by `i - 1` for every `E` but unbounded *below* unless `E` is, and
  the dévissage that carries the vanishing above from a single degree to a bounded object,
  `Stacks.SmallDerivedCategory.isLE_obj_of_isGE`, runs over a finite range.

  What drops the lower bound is the route of
  `AlgebraicGeometry.Space.isLE_rightDerived_obj_of_isLE` (Stacks 08F7 (3) with no lower
  endpoint): `E` is the derived limit of its truncation tower from below, `Rε_*` carries that to
  a derived limit, each term is bounded, and the Milnor sequence keeps the bound.

  Of those four steps the first three are available at `ε`.  The first, Stacks 0D6S at the
  small étale site, is proved as `AlgebraicGeometry.SmallEtale.isDerivedLimit_truncGETower`
  (`SmallEtaleTruncationTowerDerivedLimit.lean` beside this module); it needs no
  `Stacks.Cohomology.OlssonLaszloSituation` at all, being
  `Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic` — Stacks 0D6P
  with `d = 0`, universe-polymorphic — at the class of affine objects, which has enough objects
  by `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine` and over whose members a module
  quasi-coherent on the site is acyclic by
  `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`.  The
  cofinal system of coverings that an `OlssonLaszloSituation` would have asked for is available
  now too, generically, as `Stacks.Cohomology.CofinalCoveringSystem.ofHasEnoughObjects`; that
  route is simply longer.  The second step is
  `Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor` (Stacks 08U1) and the third is
  `AlgebraicGeometry.SmallEtale.isLE_derivedRestrictModule_obj_of_isGE` below.

  **What blocks it now is the fourth step, keeping the bound in the limit, and that is a gap in
  the general infrastructure rather than anything about `ε`.**
  `Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isMittagLeffler` does *not* apply here: it is
  stated only for a tower in `DerivedCategory AddCommGrpCat`, which is what the algebraic-space
  analogue needs, its functor being `Mod(𝒪_X) ⥤ Ab`.  `Rε_*` lands in
  `DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)` instead, and the only bound available for
  a derived limit there, `AlgebraicGeometry.isLE_of_isDerivedLimit`, both pays a degree and rests
  on exactness of countable products (Stacks 07KC (3)) through `AlgebraicGeometry.isLE_pi` — and
  countable products of sheaves are not exact.

  The *triangulated* half of the fourth step is now available with no exactness hypothesis at
  all, as `Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isZero_cokernel`
  (`StacksFrontier/Homology/DerivedCategory/InverseSystem/DerivedLimitAmplitude.lean`): a derived
  limit of a tower lying in degrees `≤ d` keeps that bound as soon as (a) the comparison
  `H^i(∏ₙ Kₙ) ⟶ ∏ₙ H^i(Kₙ)` is invertible for `i ≥ d`, and (b) the cokernel of the Milnor
  difference of the cohomology-sheaf system `n ↦ H^d(Kₙ)` vanishes.  It is proved from the long
  exact homology sequence of the defining triangle alone.  So what is owed is *not* a
  sheaf-valued Milnor short exact sequence, as an earlier reading of this note said — that
  sequence is not needed, and could not be had anyway, since
  `DerivedCategory.exists_milnor_shortExact_of_distTriang` itself carries the exact-products
  hypothesis.  What is owed is exactly (a) and (b) for the tower `n ↦ Rε_*(τ_{≥ -n}E)`.

  Of those, (a) is the real obstruction.  It is [Stacks, Tag 07KC] part (3) for a tower of
  modules on a site, and the library's only carrier of that clause,
  `Stacks.DerivedProducts.isIso_piComparison_homologyFunctor`, is stated under
  `CategoryTheory.Limits.HasExactLimitsOfShape (Discrete ℕ)`, which no `SheafOfModules` instance
  supplies and which is false for sheaves.  What makes it true nevertheless at `ε` is that every
  cohomology sheaf of every `Rε_*(τ_{≥ -n}E)` is quasi-coherent — this is
  `AlgebraicGeometry.SmallEtale.derivedRestrictModule_mem_of_bounded`, each term of the tower
  being bounded — so the product functor is exact on *those* families, affine opens being a
  basis over which a quasi-coherent module is acyclic and has exact sections.  The library has
  that argument only for a family of modules in a *single* degree, inside
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/InverseLimitOfAcyclicTower.lean`
  (Stacks 0BKY), as the `private` lemmas `preservesProduct_single_of_acyclic_cover` and
  `isZero_cohomology_product_on_cover`.  Carrying it from one degree to a tower of bounded
  objects with acyclic cohomology is what (a) needs; note that a dévissage over the amplitude of
  the terms will not do it, the amplitudes of the `τ_{≥ -n}E` growing with `n`, so the induction
  has to run over a degree window applied uniformly to the whole tower.

  (b) needs no new general infrastructure once (a) is in hand, but it does need its own input,
  and that input is *not* epimorphy of the transition maps by itself.  The transition maps are
  epi in the top degree from a finite stage on: the triangle
  `H^{-n-1}(E)[n+1] ⟶ τ_{≥ -n-1}E ⟶ τ_{≥ -n}E` of [Stacks, Tag 08J5] has its first vertex a
  quasi-coherent module in degree `-n-1`, so `Rε_*` of it lies in degrees `≤ -n-1` by
  `AlgebraicGeometry.SmallEtale.isLE_derivedRestrictModule_obj_single_of_isQuasicoherentOnSite`,
  and for `n` past `-d-2` that kills the obstruction `H^{d+1}` in the long exact sequence.  But a
  tower of *sheaves* with epi transitions can have `R¹lim ≠ 0`: solving `xₙ - tₙ(xₙ₊₁) = yₙ`
  recursively calls for a local lift at every stage, and the shrinkings need not stabilise.  The
  extra input is again quasi-coherence — over an affine open an epimorphism of quasi-coherent
  modules is surjective on sections, so the sections tower has eventually surjective transitions,
  hence is Mittag-Leffler (`Stacks.DerivedLimit.isMittagLeffler_of_eventually_surjective`) and
  its difference map is epi (`Stacks.DerivedLimit.epi_delta_of_isMittagLeffler`); epimorphy of
  the sheaf difference map then follows on a covering class exactly as in Stacks 0BKY.

  The `RingedSite.Hom`-shaped unbounded statements of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/` are still no help, and the reason
  is not the one an earlier reading of this note gave.  Stacks 0D6W,
  `Stacks.Cohomology.OlssonLaszlo.isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation`,
  *is* the unbounded truncation comparison for a sheaf-valued derived pushforward and would
  settle this directly; but it is stated for two `AlgebraicGeometry.RingedSite.{u, u, u}` and
  quantifies over `PreZeroHypercover.{u}`, and the objects of the small étale site lie in
  `Type (u + 1)`, so it does not typecheck at `ε`.

  The affine-chart route the source takes is also unblocked now: the 0BKZ step itself is
  `AlgebraicGeometry.SmallEtale.isIso_hypercohomologyEdge_app_of_isAffine` in that same module,
  with no boundedness hypothesis.  What that route still owes is the identification of the
  edge transformation used here, `Stacks.DerivedFunctor.homologyEdge`, with the sections-level
  comparison `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge` — two transformations of
  the same type which the library identifies nowhere — together with the passage from vanishing
  on the affine opens of `S` to vanishing of the cohomology sheaf.

## Implementation notes

The `CategoryTheory.HasDerivedCategory` instances are left free, as in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedPushforward.lean`;
nothing here is pinned to `CategoryTheory.HasDerivedCategory.standard`.

`AlgebraicGeometry.SmallEtale.commShift_derivedRestrictModule` and the two
`CategoryTheory.Functor.IsTriangulated` declarations are `local` instances: `Rε_*` is defined in a
module that does not carry them, so registering them globally here would risk a second,
independently built copy of the same datum appearing elsewhere.  A consumer activates them with
`attribute [local instance]`.

The composite instance for `(restrictModuleToDerived B S hS).IsTriangulated` is built by hand
rather than left to synthesis: the generic instance for a composite exists, but instance search
for it exceeds the default heartbeat allowance on this site.

No `@[stacks]` attribute is attached.  The edge transformation itself is
`Stacks.DerivedFunctor.homologyEdge`, where the relevant part of [Stacks, Tag 0BKZ] is carried;
the statement being approached, `H^n(Rε_* E) = ε_*(H^n E)`, is a step inside the proof of
[Stacks, Tag 071Q] rather than a tag of its own, and it is not proved here in the generality the
source uses it.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

universe w u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `ε_*` preserves limits, being the right adjoint of the associated-module functor of
Stacks 03DU (4).  In particular it is left exact, which is what makes `R⁰ε_* ≅ ε_*` hold. -/
instance preservesLimits_restrictModuleOfSheaf :
    PreservesLimits (restrictModuleOfSheaf B S hS) :=
  (associatedModuleAdjunction B S hS).rightAdjoint_preservesLimits

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- **`Rε_*` is left t-exact.**  An object of `D(S_étale, 𝒪)` with no cohomology below degree `n`
has derived direct image with no cohomology below degree `n`.

This is `Stacks.DerivedFunctor.isGE_totalRightDerived_obj` for the additive functor `ε_*`: the
`𝒪`-modules on `S_étale` are Grothendieck abelian at the universe of their sections
(`AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheafOfModules`), so an object with no
cohomology below `n` has an injective resolution whose terms vanish below `n` outright, and `ε_*`
applied degreewise carries that to a complex that again vanishes below `n`. -/
theorem isGE_derivedRestrictModule_obj
    (Z : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))) (n : ℤ) (hZ : Z.IsGE n) :
    ((derivedRestrictModule.{w, w} B S hS).obj Z).IsGE n :=
  have := hZ
  Stacks.DerivedFunctor.isGE_totalRightDerived_obj (restrictModuleOfSheaf B S hS) Z n

/-- The canonical commutation of `Rε_*` with the shift, the one produced from the comparison
`ε_* ⟶ Rε_*` by `CategoryTheory.Functor.IsRightDerivedFunctor.commShift`.  It is `local` so that
importing this module registers no second copy of this datum; see the implementation notes. -/
local instance commShift_derivedRestrictModule :
    (derivedRestrictModule.{w, w} B S hS).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedRestrictModule.{w, w} B S hS)
    (derivedRestrictModuleUnit.{w, w} B S hS)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B S hS))
      (ComplexShape.up ℤ)) ℤ

/-- Degreewise `ε_*` followed by the localization `K(𝒪_S) ⥤ D(𝒪_S)` is exact: an additive functor
induces an exact functor of unbounded homotopy categories (Stacks 014X) and the localization is
exact.  Built by hand rather than by instance search; see the implementation notes. -/
local instance isTriangulated_restrictModuleToDerived :
    (restrictModuleToDerived.{w} B S hS).IsTriangulated where
  map_distinguished T hT := by
    have : ((restrictModuleOfSheaf B S hS).mapHomotopyCategory
        (ComplexShape.up ℤ)).IsTriangulated :=
      HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory (restrictModuleOfSheaf B S hS)
    exact isomorphic_distinguished _
      (DerivedCategory.Qh.map_distinguished _
        (((restrictModuleOfSheaf B S hS).mapHomotopyCategory
          (ComplexShape.up ℤ)).map_distinguished T hT)) _
      ((Functor.mapTriangleCompIso
        ((restrictModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ))
        DerivedCategory.Qh).app T)

/-- **`Rε_*` is exact.**  A right derived functor of an exact functor out of the unbounded
homotopy category is exact (`Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor`,
Stacks 014A), the K-injective resolutions being
`Stacks.Cohomology.Localization.enoughKInjectives`. -/
local instance isTriangulated_derivedRestrictModule :
    (derivedRestrictModule.{w, w} B S hS).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    Stacks.Cohomology.Localization.enoughKInjectives
    (restrictModuleToDerived.{w} B S hS) (derivedRestrictModule.{w, w} B S hS)
    (derivedRestrictModuleUnit.{w, w} B S hS)

/-- **`R⁰ε_* ≅ ε_*`, read in degree `i`.**  For an `𝒪`-module `G` on `S_étale` placed in degree
`i`, the degree-`i` cohomology sheaf of `Rε_*(G[i])` is `ε_* G`, naturally in `G`.

This is `Stacks.DerivedFunctor.derivedDegreeNatIsoOfKInjective` for `ε_*`; left exactness of
`ε_*` is `AlgebraicGeometry.SmallEtale.preservesLimits_restrictModuleOfSheaf`, the left
t-exactness it needs is `isGE_derivedRestrictModule_obj`, and the K-injective resolutions are
`Stacks.Cohomology.Localization.enoughKInjectives`.  It is the one place where left exactness of
`ε_*` enters the construction of the comparison `H^i ∘ Rε_* ⟶ ε_* ∘ H^i`. -/
def restrictModuleDegreeNatIso (i : ℤ) :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheaf B S hS)) i ⋙
        derivedRestrictModule.{w, w} B S hS ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i ≅
      restrictModuleOfSheaf B S hS :=
  Stacks.DerivedFunctor.derivedDegreeNatIsoOfKInjective (restrictModuleOfSheaf B S hS)
    (derivedRestrictModule.{w, w} B S hS) (derivedRestrictModuleUnit.{w, w} B S hS)
    (fun _ => isGE_derivedRestrictModule_obj.{w} B S hS _ 0 inferInstance)
    Stacks.Cohomology.Localization.enoughKInjectives i

/-- **The comparison `H^i(Rε_* E) ⟶ ε_*(H^i E)`**, natural in the object `E` of
`D(S_étale, 𝒪)`.

It is the edge transformation of Stacks 0BKZ for the right derived functor `Rε_*`,
`Stacks.DerivedFunctor.homologyEdge`, whose two inputs are discharged at `ε`: left t-exactness is
`isGE_derivedRestrictModule_obj` and the degree-`i` agreement `R⁰ε_* ≅ ε_*` is
`restrictModuleDegreeNatIso`.  Concretely it is the truncation map `E ⟶ τ_{≥ i}E` read by
`H^i ∘ Rε_*`, followed by an isomorphism; see `Stacks.DerivedFunctor.homologyEdge_app`. -/
def homologyRestrictModuleEdge (i : ℤ) :
    derivedRestrictModule.{w, w} B S hS ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i ⟶
      DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheaf B S hS)) i ⋙
        restrictModuleOfSheaf B S hS :=
  Stacks.DerivedFunctor.homologyEdge (restrictModuleOfSheaf B S hS)
    (derivedRestrictModule.{w, w} B S hS) (isGE_derivedRestrictModule_obj.{w} B S hS) i
    (restrictModuleDegreeNatIso.{w} B S hS i)

/-- **The comparison is invertible at an object with no cohomology below degree `i`**, with no
quasi-coherence hypothesis: its only non-invertible factor is the truncation map `E ⟶ τ_{≥ i}E`,
which is itself invertible there. -/
theorem isIso_homologyRestrictModuleEdge_app_of_isGE (i : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))) [E.IsGE i] :
    IsIso ((homologyRestrictModuleEdge.{w} B S hS i).app E) :=
  Stacks.DerivedFunctor.isIso_homologyEdge_app_of_isGE (restrictModuleOfSheaf B S hS)
    (derivedRestrictModule.{w, w} B S hS) (isGE_derivedRestrictModule_obj.{w} B S hS) i
    (restrictModuleDegreeNatIso.{w} B S hS i) E

/-- **`H^i(Rε_* E) ≅ ε_*(H^i E)` on `D^{≥ i}(S_étale, 𝒪)`**, the lowest-degree case of the
identification of the cohomology sheaves of `Rε_*`, read as an isomorphism. -/
def homologyRestrictModuleIsoOfIsGE (i : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))) [E.IsGE i] :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).obj
        ((derivedRestrictModule.{w, w} B S hS).obj E) ≅
      (restrictModuleOfSheaf B S hS).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheaf B S hS)) i).obj E) :=
  @asIso _ _ _ _ _ (isIso_homologyRestrictModuleEdge_app_of_isGE.{w} B S hS i E)

end AlgebraicGeometry.SmallEtale

end
