module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleModuleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleHomologyEdge
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# `Rε_*` is right t-exact on bounded objects with quasi-coherent cohomology

Let `S` be a scheme contained in a big étale site `B` and let
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of [Stacks, Tag 070R], so that
`Rε_*` is `AlgebraicGeometry.SmallEtale.derivedRestrictModule`.  `Rε_*` is left t-exact with no
hypothesis at all (`AlgebraicGeometry.SmallEtale.isGE_derivedRestrictModule_obj`).  This file
proves that it is *right* t-exact on the objects of `D(S_étale, 𝒪)` which are bounded and whose
cohomology sheaves are quasi-coherent on the site, and deduces from that the obligation (iii) of
[Stacks, Tag 071Q] — invertibility of the comparison `H^i(Rε_* E) ⟶ ε_*(H^i E)` — for such `E`.

## The argument

The one input is the vanishing `R^pε_*𝒢 = 0` for `p > 0` and `𝒢` quasi-coherent on the site,
which is `AlgebraicGeometry.SmallEtale.isZero_rightDerived_restrictModuleOfSheaf`
([Stacks, Tag 03DW] at `ε`, in the module-valued spelling).  Read through the comparison
`H^m(Rε_*(𝒢[n])) ≅ R^{m-n}ε_*𝒢` of
`Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero` it says
that `Rε_*` carries an object concentrated in degree `n` into `D^{≤ n}`; the dévissage
`Stacks.SmallDerivedCategory.isLE_obj_of_isGE` then carries that from a single degree to any
bounded object with cohomology in the weak Serre subcategory of quasi-coherent modules.

Obligation (iii) follows for a bounded `E` because the edge transformation of [Stacks, Tag 0BKZ]
factors, by `Stacks.DerivedFunctor.homologyEdge_app`, as

`H^i(Rε_* E) ⟶ H^i(Rε_*(τ_{≥ i}E)) ≅ ε_*(H^i E)`,

the second factor being invertible always; and `τ_{< i}E` is bounded with quasi-coherent
cohomology, so `Rε_*(τ_{< i}E)` lies in `D^{≤ i - 1}` and the first factor is invertible by the
long exact sequence of the triangle `τ_{< i}E ⟶ E ⟶ τ_{≥ i}E`
(`DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁`).

## Main results

* `AlgebraicGeometry.SmallEtale.isLE_derivedRestrictModule_obj_single_of_isQuasicoherentOnSite`:
  `Rε_*` carries a quasi-coherent module placed in degree `n` into `D^{≤ n}`.
* `AlgebraicGeometry.SmallEtale.isLE_derivedRestrictModule_obj_of_isGE`: **right t-exactness of
  `Rε_*` on bounded objects with quasi-coherent cohomology.**
* `AlgebraicGeometry.SmallEtale.isIso_homologyRestrictModuleEdge_app_of_bounded`: **obligation
  (iii) of Stacks 071Q for a bounded object** — the comparison `H^i(Rε_* E) ⟶ ε_*(H^i E)` is
  invertible at an object with quasi-coherent cohomology which is bounded on both sides.
* `AlgebraicGeometry.SmallEtale.isQuasicoherent_homology_derivedRestrictModule_of_bounded` and
  `AlgebraicGeometry.SmallEtale.derivedRestrictModule_mem_of_bounded`: **obligation (ii) of
  Stacks 071Q for a bounded object** — `Rε_*` carries it into `D_QCoh(S_Zar, 𝒪_S)`.

## What is still owed, and what it needs

The unbounded case of obligations (iii) and (ii) — the statements written out in the module
documentation of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleHomologyEdge`
— is not proved here, and the boundedness hypothesis below is exactly where the gap sits:
`τ_{< i}E` is bounded above by `i - 1` for every `E`, but it is unbounded *below* unless `E` is,
and `Stacks.SmallDerivedCategory.isLE_obj_of_isGE` is a dévissage over a finite range.

Dropping the lower bound is the step `AlgebraicGeometry.Space.isLE_rightDerived_obj_of_isLE`
takes for an algebraic space ([Stacks, Tag 08F7] (3) with no lower endpoint): write `E` as the
derived limit of the tower of its truncations from below, push that forward (a right derived
functor of a functor commuting with countable products carries a derived limit to a derived
limit, `Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`, [Stacks, Tag 08U1]), bound
each bounded term by the result below, and keep the bound in the limit through the Milnor
sequence.

The first three of those four ingredients are now available at `ε`.  [Stacks, Tag 0D6S] at the
small étale site is `AlgebraicGeometry.SmallEtale.isDerivedLimit_truncGETower`, namely

```lean
theorem isDerivedLimit_truncGETower
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) q).obj E).IsQuasicoherentOnSite) :
  IsDerivedLimit (Stacks.DerivedLimit.truncGETower
    (SheafOfModules.{u} (structureSheaf B S hS)) E) E
```

at `CategoryTheory.HasDerivedCategory.standard`.  No
`Stacks.Cohomology.OlssonLaszloSituation` is involved: the convergence criterion
`Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic`, which is
[Stacks, Tag 0D6P] with `d = 0` at four independent universes, takes the covering class and the
vanishing directly — the affine objects
(`AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`) and
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`.  The
cofinal system of coverings an `OlssonLaszloSituation` would ask for is available too, generically
and for any class with enough objects, as
`Stacks.Cohomology.CofinalCoveringSystem.ofHasEnoughObjects`.

**What blocks the unbounded case now is the fourth ingredient.**
`Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isMittagLeffler` is stated only for a tower in
`DerivedCategory AddCommGrpCat`, which is what the algebraic-space analogue needs, its functor
being `Mod(𝒪_X) ⥤ Ab`; `Rε_*` lands in `DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)`
instead, and the sheaf-valued bound `AlgebraicGeometry.isLE_of_isDerivedLimit` both pays a degree
and rests on exactness of countable products, which fails for sheaves.

The triangulated content of that ingredient is now available with no exactness hypothesis, as
`Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isZero_cokernel`
(`StacksFrontier/Homology/DerivedCategory/InverseSystem/DerivedLimitAmplitude.lean`), proved from
the long exact homology sequence of the defining triangle alone.  It leaves two hypotheses to
discharge at `ε`: invertibility of the comparison `H^i(∏ₙ Kₙ) ⟶ ∏ₙ H^i(Kₙ)` in degrees `≥ d`,
which is [Stacks, Tag 07KC] part (3) for the tower and is the real obstruction, and vanishing of
the cokernel of the Milnor difference of the cohomology-sheaf system `n ↦ H^d(Kₙ)`.  Both are
true at `ε` because every term of the tower is bounded and so has quasi-coherent cohomology by
`AlgebraicGeometry.SmallEtale.derivedRestrictModule_mem_of_bounded`, making affine opens a basis
on which the product functor is exact; what the library does not yet have is that argument for
anything but a family of modules in a single degree (Stacks 0BKY, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/InverseLimitOfAcyclicTower.lean`).  The
full diagnosis, with the shapes the library does have, is in the module documentation of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleHomologyEdge`.
Because of this, the boundedness hypotheses of the results below are *not* removable yet, and
they are also what pins them to a free `CategoryTheory.HasDerivedCategory.{w}`: the
Tag 0D6S above is at the standard derived category only.

## Implementation notes

The `CategoryTheory.HasDerivedCategory` instances are left free, as in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedPushforward.lean`.

`AlgebraicGeometry.SmallEtale.commShift_derivedRestrictModule` and
`AlgebraicGeometry.SmallEtale.isTriangulated_derivedRestrictModule` are `local` instances of the
module that defines them and are activated here with `attribute [local instance]`, as that module
documents.

No `@[stacks]` attribute is attached.  Obligation (iii) of [Stacks, Tag 071Q] is proved here only
for a bounded object, so no clause of that tag is carried; the right t-exactness itself is the
instance at `ε` of no tag of its own.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 0D6S](https://stacks.math.columbia.edu/tag/0D6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
  (exists_quasiIso_isKInjective_sheafOfModules)

namespace AlgebraicGeometry.SmallEtale

universe w u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

attribute [local instance] commShift_derivedRestrictModule
  isTriangulated_derivedRestrictModule

/-- **`Rε_*` carries a quasi-coherent `𝒪`-module placed in degree `n` into `D^{≤ n}`.**

Above degree `n` the cohomology of `Rε_*(M[n])` is a higher direct image `R^pε_*M` with `p > 0`,
by `Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero`, and
those vanish on a module quasi-coherent on the site by
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_restrictModuleOfSheaf`, which is
[Stacks, Tag 03DW] at `ε`. -/
theorem isLE_derivedRestrictModule_obj_single_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (structureSheaf B S hS)) (hM : M.IsQuasicoherentOnSite) (n : ℤ) :
    ((derivedRestrictModule.{w, w} B S hS).obj
      ((DerivedCategory.singleFunctor _ n).obj M)).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro m hm
  exact Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero
    (restrictModuleOfSheaf B S hS) (derivedRestrictModule.{w, w} B S hS)
    (derivedRestrictModuleUnit.{w, w} B S hS)
    (exists_quasiIso_isKInjective_sheafOfModules _)
    M (fun p hp => isZero_rightDerived_restrictModuleOfSheaf B S hS M hM p hp) n m hm

/-- **`Rε_*` is right t-exact on bounded objects with quasi-coherent cohomology.**  An object of
`D(S_étale, 𝒪)` living in degrees `[a, b]` whose cohomology sheaves are all quasi-coherent on the
site has derived direct image living in degrees `≤ b`.

This is the dévissage `Stacks.SmallDerivedCategory.isLE_obj_of_isGE` over the weak Serre
subcategory `AlgebraicGeometry.SmallEtale.qcohOnSite`, whose single-degree input is
`isLE_derivedRestrictModule_obj_single_of_isQuasicoherentOnSite`.  Together with the
hypothesis-free left t-exactness `AlgebraicGeometry.SmallEtale.isGE_derivedRestrictModule_obj` it
says that `Rε_*` is t-exact there. -/
theorem isLE_derivedRestrictModule_obj_of_isGE
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) i).obj E).IsQuasicoherentOnSite)
    (a b : ℤ) (ha : E.IsGE a) (hb : E.IsLE b) :
    ((derivedRestrictModule.{w, w} B S hS).obj E).IsLE b := by
  have := ha
  have := hb
  have h := Stacks.SmallDerivedCategory.isLE_obj_of_isGE (qcohOnSite B S hS)
    (derivedRestrictModule.{w, w} B S hS) 0
    (fun M hM n => by
      simpa using isLE_derivedRestrictModule_obj_single_of_isQuasicoherentOnSite B S hS M hM n)
    E hE a b
  simpa using h

/-- **Obligation (iii) of [Stacks, Tag 071Q] for a bounded object.**  The comparison
`H^i(Rε_* E) ⟶ ε_*(H^i E)` of
`AlgebraicGeometry.SmallEtale.homologyRestrictModuleEdge` is invertible at an object `E` of
`D(S_étale, 𝒪)` whose cohomology sheaves are all quasi-coherent on the site and which lives in
degrees `[a, b]`.

By `Stacks.DerivedFunctor.homologyEdge_app` the comparison is the truncation map `E ⟶ τ_{≥ i}E`
read by `H^i ∘ Rε_*`, followed by an isomorphism.  The truncation `τ_{< i}E` is again bounded
with quasi-coherent cohomology, so `isLE_derivedRestrictModule_obj_of_isGE` puts
`Rε_*(τ_{< i}E)` in degrees `≤ i - 1`, and the long exact sequence of the image of the triangle
`τ_{< i}E ⟶ E ⟶ τ_{≥ i}E` then makes that first factor invertible, by
`DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁`.

The unbounded case is not proved; see the module documentation for the one step it needs. -/
theorem isIso_homologyRestrictModuleEdge_app_of_bounded (i : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) n).obj E).IsQuasicoherentOnSite)
    (a b : ℤ) (ha : E.IsGE a) (hb : E.IsLE b) :
    IsIso ((homologyRestrictModuleEdge.{w} B S hS i).app E) := by
  have := ha
  have := hb
  set F := (DerivedCategory.TStructure.t.truncLT i).obj E with hF
  have hFGE : F.IsGE a := inferInstanceAs (((DerivedCategory.TStructure.t.truncLT i).obj E).IsGE a)
  have hFLE : F.IsLE (i - 1) :=
    DerivedCategory.TStructure.t.isLE_of_le _ (i - 1) (i - 1) le_rfl
  have hFq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) n).obj F).IsQuasicoherentOnSite := by
    intro n
    by_cases hn : n < i
    · have := DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃
        ((DerivedCategory.TStructure.t.triangleLTGE i).obj E)
        (DerivedCategory.TStructure.t.triangleLTGE_distinguished i E) n i
        (inferInstanceAs (((DerivedCategory.TStructure.t.truncGE i).obj E).IsGE i)) hn
      exact (qcohOnSite B S hS).prop_of_iso
        (asIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheaf B S hS)) n).map
            ((DerivedCategory.TStructure.t.triangleLTGE i).obj E).mor₁)).symm (hE n)
    · exact (qcohOnSite B S hS).prop_of_isZero
        (DerivedCategory.isZero_of_isLE F (i - 1) n (by omega))
  have hRF : ((derivedRestrictModule.{w, w} B S hS).obj F).IsLE (i - 1) :=
    isLE_derivedRestrictModule_obj_of_isGE B S hS F hFq a (i - 1) hFGE hFLE
  have hiso : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).map
      ((derivedRestrictModule.{w, w} B S hS).map
        ((DerivedCategory.TStructure.t.truncGEπ i).app E))) :=
    DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁
      ((derivedRestrictModule.{w, w} B S hS).mapTriangle.obj
        ((DerivedCategory.TStructure.t.triangleLTGE i).obj E))
      ((derivedRestrictModule.{w, w} B S hS).map_distinguished _
        (DerivedCategory.TStructure.t.triangleLTGE_distinguished i E)) i (i - 1) hRF (by omega)
  have heq : (homologyRestrictModuleEdge.{w} B S hS i).app E =
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).map
        ((derivedRestrictModule.{w, w} B S hS).map
          ((DerivedCategory.TStructure.t.truncGEπ i).app E)) ≫
        (Stacks.DerivedFunctor.truncGEComparisonIso (restrictModuleOfSheaf B S hS)
          (derivedRestrictModule.{w, w} B S hS) (isGE_derivedRestrictModule_obj.{w} B S hS) i
          (restrictModuleDegreeNatIso.{w} B S hS i)).hom.app E :=
    Stacks.DerivedFunctor.homologyEdge_app _ _ _ i _ E
  rw [heq]
  have := hiso
  infer_instance

/-- **Obligation (ii) of [Stacks, Tag 071Q] for a bounded object**, degreewise: every cohomology
sheaf of `Rε_* E` is a quasi-coherent `𝒪_S`-module, for `E` bounded with cohomology
quasi-coherent on the site.

By `isIso_homologyRestrictModuleEdge_app_of_bounded` that cohomology sheaf is `ε_*(H^i E)`, and
the direct image along `ε` of a module quasi-coherent on the site is quasi-coherent, which is
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`. -/
theorem isQuasicoherent_homology_derivedRestrictModule_of_bounded (i : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) n).obj E).IsQuasicoherentOnSite)
    (a b : ℤ) (ha : E.IsGE a) (hb : E.IsLE b) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).obj
      ((derivedRestrictModule.{w, w} B S hS).obj E)).IsQuasicoherent := by
  have := isIso_homologyRestrictModuleEdge_app_of_bounded B S hS i E hE a b ha hb
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (asIso ((homologyRestrictModuleEdge.{w} B S hS i).app E)).symm
    (isQuasicoherent_restrictModule B S hS _ (hE i))

/-- **Obligation (ii) of [Stacks, Tag 071Q] for a bounded object.**  `Rε_*` carries an object of
`D_QCoh(S_étale, 𝒪)` which is bounded on both sides into `D_QCoh(S_Zar, 𝒪_S)`.

This is `isQuasicoherent_homology_derivedRestrictModule_of_bounded` read in every degree. -/
theorem derivedRestrictModule_mem_of_bounded
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) n).obj E).IsQuasicoherentOnSite)
    (a b : ℤ) (ha : E.IsGE a) (hb : E.IsLE b) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((derivedRestrictModule.{w, w} B S hS).obj E) :=
  fun i => isQuasicoherent_homology_derivedRestrictModule_of_bounded B S hS i E hE a b ha hb

end AlgebraicGeometry.SmallEtale

end
