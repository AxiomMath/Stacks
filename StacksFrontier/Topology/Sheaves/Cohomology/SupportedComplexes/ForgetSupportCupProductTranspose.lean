module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAdjunctionTranspose
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ForgetSupportAndCupProduct

/-!
# The compatibility of the corepresenting objects of [Stacks, Tag 0G77], transposed

`Stacks.Cohomology.SupportedComplexes.forgetSupport_supportedCupProductOfClasses` derives the
square of [Stacks, Tag 0G77] at the source's own corepresenting objects from
`Stacks.Cohomology.SupportedComplexes.ShiftedUnitCorepresentingCompatible`: a closed equation
between named canonical maps, in which the *inverse* of the projection-formula map of
[Stacks, Tag 0B53] at the pair of shifted structure sheaves occurs, together with the comparison
of [Stacks, Tag 0E2K] in both directions.

That equation is an equation between morphisms **into** `i_*(-)`, and the projection-formula map
of [Stacks, Tag 0B53] is by construction an adjoint transpose
(`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_eq`). So the whole equation may
be transposed under `Li^* ⊣ Ri_*` of [Stacks, Tag 079W], and transposing removes from it

* the inverse of the projection-formula map — the projection-formula map itself is replaced by
  the comparison of [Stacks, Tag 079U] that it is the transpose of, with no inverse taken;
* the comparison of [Stacks, Tag 0E2K], which cancels against itself;
* the right adjoint `Ri_*` in every position but one.

What is left is a statement about the derived pullback, the derived tensor product and the
comparison of [Stacks, Tag 079U].  This is the same manoeuvre that discharges the corresponding
hypothesis of [Stacks, Tag 0G79] in
`Stacks.Cohomology.SupportedComplexes.hunit_of_derivedPullbackCompatible`, carried out for the
cup product instead of for the base-change map.

## Main results

* `Stacks.Cohomology.SupportedComplexes.corepresentingCompatible_of_transpose` is the
  transposition, for an abstract adjunction, abstract bifunctors, abstract commutativity
  constraints and an abstract projection-formula map presented as an adjoint transpose.  The
  comparison of [Stacks, Tag 079U] enters only through the transposed form `w` of the
  projection-formula map, so the lemma mentions no comparison of bifunctors at all.
* `Stacks.Cohomology.SupportedComplexes.shiftedUnitCorepresentingCompatible_of_transpose` is that
  lemma at the data of Tag 0G77: it proves `ShiftedUnitCorepresentingCompatible`, hence Tag 0G77
  at the canonical corepresenting objects, from the transposed equation.
* `Stacks.Cohomology.SupportedComplexes.transposeCompatible_of_braidedComparison` reduces the
  transposed equation further, to one in which neither the right adjoint, nor the counit, nor the
  hom-equivalence occurs: the comparison of [Stacks, Tag 079U] read at the two shifted structure
  sheaves themselves, against the degree identifications of [Stacks, Tag 0FNH] on the two spaces
  and the comparison `Li^*(𝒪_X[-p]) ≅ 𝒪_Z[-p]` of [Stacks, Tag 01CD].

## References

* [Stacks Project, Lemma 20.34.11 (Tag 0G77)](https://stacks.math.columbia.edu/tag/0G77)
* [Stacks Project, Lemma 20.34.13 (Tag 0G79)](https://stacks.math.columbia.edu/tag/0G79)
* [Stacks Project, Lemma 20.28.6 (Tag 0B53)](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Lemma 20.28.8 (Tag 0B55)](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FNH](https://stacks.math.columbia.edu/tag/0FNH)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite
open Stacks.ClosedImmersion (mapDerivedCategoryIsoTotalRightDerived)
open Stacks.RingedSpace (shiftedUnitObject shiftedUnitTensorIso
  derivedPullbackShiftedUnitTensorIso derivedPullbackShiftedUnitIso)
open scoped CategoryTheory.Prod

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Cohomology.SupportedComplexes

section Abstract

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **The remaining hypothesis of [Stacks, Tag 0G77], transposed under the adjunction.**

Let `adj : L ⊣ R` be an adjunction, `cmp : P ≅ R` a comparison of two models of the right
adjoint, `TC`, `TD` bifunctors with commutativity constraints `bC`, `bD`, and let
`pf : TC (R V) U ⟶ R (TD V (L U))` be invertible and present a transposed morphism `w` as in
`hpf` — which is the defining equation of the projection-formula map of [Stacks, Tag 0B53],
`CategoryTheory.map_adjunctionTensorMap_comp_counit`.

Then the compatibility of two identifications `χ`, `χX` with the comparisons `ρ`, `ρV` obtained
by transposing `u`, `uV` — the hypothesis `hbk` of
`Stacks.Cohomology.SupportedComplexes.forgetSupport_supportedCupProduct` — follows from the
equation `hcompat` between the transposes, in which no inverse of `pf` occurs and `cmp` does
not occur at all. -/
theorem corepresentingCompatible_of_transpose
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {P : D ⥤ C} (cmp : P ≅ R)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (bC : ∀ A₁ A₂ : C, (TC.obj A₁).obj A₂ ≅ (TC.obj A₂).obj A₁)
    (bD : ∀ B₁ B₂ : D, (TD.obj B₁).obj B₂ ≅ (TD.obj B₂).obj B₁)
    {U VX WX : C} {V W : D}
    (χ : W ⟶ (TD.obj (L.obj U)).obj V) (χX : WX ⟶ (TC.obj U).obj VX)
    (u : L.obj WX ⟶ W) (uV : L.obj VX ⟶ V)
    (pf : (TC.obj (R.obj V)).obj U ⟶ R.obj ((TD.obj V).obj (L.obj U)))
    (hpfVU : IsIso pf)
    (w : L.obj ((TC.obj (R.obj V)).obj U) ⟶ (TD.obj V).obj (L.obj U))
    (hpf : L.map pf ≫ adj.counit.app ((TD.obj V).obj (L.obj U)) = w)
    (hcompat : u ≫ χ ≫ (bD (L.obj U) V).hom =
      L.map (χX ≫ (TC.obj U).map (adj.homEquiv VX V uV) ≫ (bC (R.obj V) U).inv) ≫ w) :
    (adj.homEquiv WX W u ≫ cmp.inv.app W) ≫ P.map χ ≫ P.map (bD (L.obj U) V).hom ≫
        cmp.hom.app ((TD.obj V).obj (L.obj U)) ≫
        CategoryTheory.inv (I := hpfVU) pf ≫
        (bC (R.obj V) U).hom ≫ (TC.obj U).map (cmp.inv.app V) =
      χX ≫ (TC.obj U).map (adj.homEquiv VX V uV ≫ cmp.inv.app V) := by
  have := hpfVU
  have key : adj.homEquiv WX ((TD.obj V).obj (L.obj U)) (u ≫ χ ≫ (bD (L.obj U) V).hom) =
      χX ≫ (TC.obj U).map (adj.homEquiv VX V uV) ≫ (bC (R.obj V) U).inv ≫ pf := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    simp only [Functor.map_comp, Category.assoc]
    rw [hpf]
    simpa only [Functor.map_comp, Category.assoc] using hcompat
  have hnat := cmp.inv.naturality (χ ≫ (bD (L.obj U) V).hom)
  have hleft : cmp.inv.app W ≫ P.map (χ ≫ (bD (L.obj U) V).hom) ≫
      cmp.hom.app ((TD.obj V).obj (L.obj U)) =
      R.map (χ ≫ (bD (L.obj U) V).hom) := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hP : P.map χ ≫ P.map (bD (L.obj U) V).hom = P.map (χ ≫ (bD (L.obj U) V).hom) :=
    (P.map_comp _ _).symm
  have hR : adj.homEquiv WX W u ≫ R.map (χ ≫ (bD (L.obj U) V).hom) =
      adj.homEquiv WX ((TD.obj V).obj (L.obj U)) (u ≫ χ ≫ (bD (L.obj U) V).hom) :=
    (adj.homEquiv_naturality_right u _).symm
  simp only [Category.assoc]
  rw [reassoc_of% hP, reassoc_of% hleft, reassoc_of% hR, key]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]

section Uncurry

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {E : Type*} [Category* E]

/-- An uncurried bifunctor on a morphism whose second component is an identity. -/
private theorem uncurryMap_prodIdRight (T : A ⥤ B ⥤ E) {Z Z' : A} (u : Z ⟶ Z') (W : B) :
    (Functor.uncurry.obj T).map (u ×ₘ 𝟙 W) = (T.map u).app W := by
  change (T.map u).app W ≫ (T.obj Z').map (𝟙 W) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- An uncurried bifunctor on a morphism whose first component is an identity. -/
private theorem uncurryMap_idProdLeft (T : A ⥤ B ⥤ E) (Z : A) {W W' : B} (v : W ⟶ W') :
    (Functor.uncurry.obj T).map (𝟙 Z ×ₘ v) = (T.obj Z).map v := by
  change (T.map (𝟙 Z)).app W ≫ (T.obj Z).map v = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

end Uncurry

/-- **The transposed equation, with the right adjoint removed.**

If the comparison `α` of bifunctors — the comparison of [Stacks, Tag 079U] in the application —
is compatible with the two commutativity constraints as in `hαb`, and the constraint on the
target is natural in both variables as in `hbD`, then the transposed equation `hcompat` of
`Stacks.Cohomology.SupportedComplexes.corepresentingCompatible_of_transpose` follows from
`hclean`, in which the right adjoint, the counit and the hom-equivalence no longer occur: it is
an equation between `α` read at `(U, VX)` and the identifications `χ`, `χX`, `u`, `uV`. -/
theorem transposeCompatible_of_braidedComparison
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (α : Functor.uncurry.obj TC ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TD)
    (bC : ∀ A₁ A₂ : C, (TC.obj A₁).obj A₂ ≅ (TC.obj A₂).obj A₁)
    (bD : ∀ B₁ B₂ : D, (TD.obj B₁).obj B₂ ≅ (TD.obj B₂).obj B₁)
    (hαb : ∀ A₁ A₂ : C, L.map (bC A₁ A₂).hom ≫ α.app (A₂, A₁) =
      α.app (A₁, A₂) ≫ (bD (L.obj A₁) (L.obj A₂)).hom)
    (hbD : ∀ {B₁ B₁' B₂ B₂' : D} (a : B₁ ⟶ B₁') (b : B₂ ⟶ B₂'),
      ((TD.map a).app B₂ ≫ (TD.obj B₁').map b) ≫ (bD B₁' B₂').hom =
        (bD B₁ B₂).hom ≫ ((TD.map b).app B₁ ≫ (TD.obj B₂').map a))
    {U VX WX : C} {V W : D}
    (χ : W ⟶ (TD.obj (L.obj U)).obj V) (χX : WX ⟶ (TC.obj U).obj VX)
    (u : L.obj WX ⟶ W) (uV : L.obj VX ⟶ V)
    (hclean : u ≫ χ ≫ (bD (L.obj U) V).hom =
      L.map χX ≫ α.app (U, VX) ≫ (bD (L.obj VX) (L.obj U)).inv ≫
        (TD.map uV).app (L.obj U)) :
    u ≫ χ ≫ (bD (L.obj U) V).hom =
      L.map (χX ≫ (TC.obj U).map (adj.homEquiv VX V uV) ≫ (bC (R.obj V) U).inv) ≫
        α.app (R.obj V, U) ≫
          (Functor.uncurry.obj TD).map (adj.counit.app V ×ₘ 𝟙 (L.obj U)) := by
  set h := adj.homEquiv VX V uV with hh
  have htri : L.map h ≫ adj.counit.app V = uV := by
    have h0 := (adj.homEquiv VX V).symm_apply_apply uV
    rw [Adjunction.homEquiv_counit] at h0
    rw [hh]
    exact h0
  have hc : (Functor.uncurry.obj TD).map (adj.counit.app V ×ₘ 𝟙 (L.obj U)) =
      (TD.map (adj.counit.app V)).app (L.obj U) :=
    uncurryMap_prodIdRight TD _ _
  have hb : L.map (bC (R.obj V) U).inv ≫ α.app (R.obj V, U) =
      α.app (U, R.obj V) ≫ (bD (L.obj (R.obj V)) (L.obj U)).inv := by
    have h₁ := hαb (R.obj V) U
    have h₂ : α.app (R.obj V, U) =
        L.map (bC (R.obj V) U).hom ≫ α.app (U, R.obj V) ≫
          (bD (L.obj (R.obj V)) (L.obj U)).inv := by
      rw [← Category.assoc, h₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h₂, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hn : L.map ((TC.obj U).map h) ≫ α.app (U, R.obj V) =
      α.app (U, VX) ≫ (TD.obj (L.obj U)).map (L.map h) := by
    have h₁ := α.naturality ((𝟙 U) ×ₘ h)
    rw [Functor.comp_map, Functor.comp_map, uncurryMap_idProdLeft TC U h] at h₁
    have h₂ : (L.prod L).map ((𝟙 U) ×ₘ h) = (𝟙 (L.obj U)) ×ₘ L.map h := by
      refine Prod.ext ?_ ?_
      · exact L.map_id U
      · rfl
    rw [h₂, uncurryMap_idProdLeft TD (L.obj U) (L.map h)] at h₁
    exact h₁
  have hbn : (TD.obj (L.obj U)).map (L.map h) ≫ (bD (L.obj (R.obj V)) (L.obj U)).inv =
      (bD (L.obj VX) (L.obj U)).inv ≫ (TD.map (L.map h)).app (L.obj U) := by
    have h₁ := hbD (L.map h) (𝟙 (L.obj U))
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, NatTrans.id_app,
      Category.id_comp] at h₁
    rw [Iso.comp_inv_eq, Category.assoc, h₁, Iso.inv_hom_id_assoc]
  rw [hclean, hc, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hb, reassoc_of% hn, reassoc_of% hbn]
  simp only [← NatTrans.comp_app, ← Functor.map_comp, htri]

end Abstract

section AtTheCanonicalObjects

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (a b : ℤ)

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- **The remaining hypothesis of [Stacks, Tag 0G77] at the canonical corepresenting objects,
transposed.**

`Stacks.Cohomology.SupportedComplexes.ShiftedUnitCorepresentingCompatible` — the hypothesis of
`Stacks.Cohomology.SupportedComplexes.forgetSupport_supportedCupProductOfClasses` — follows from
the equation `hbk` below, which is its transpose under `Li^* ⊣ Ri_*` of [Stacks, Tag 079W]. In
it the projection-formula map of [Stacks, Tag 0B53] is replaced by the comparison of
[Stacks, Tag 079U] that it is the transpose of, and the comparison of [Stacks, Tag 0E2K] does not
occur. -/
theorem shiftedUnitCorepresentingCompatible_of_transpose
    (hbk : (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) (a + b)).hom ≫
        (derivedPullbackShiftedUnitTensorIso (closedSubsetInclusion X Z) a b).hom ≫
          ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
            ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedUnitObject X a))
            (shiftedUnitObject (closedSubsetRingedSpace X Z) b)).hom =
      (derivedPullback (closedSubsetInclusion X Z)).map
          ((shiftedUnitTensorIso X a b).hom ≫
            ((derivedTensorProductFunctor X.sheaf).obj (shiftedUnitObject X a)).map
                ((derivedAdjunction (closedSubsetInclusion X Z)).homEquiv
                  (shiftedUnitObject X b) (shiftedUnitObject (closedSubsetRingedSpace X Z) b)
                  (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) b).hom) ≫
              ((canonicalDerivedTensorProduct X.sheaf).braidingIso
                (AlgebraicGeometry.RingedSpace.ringedSite X)
                ((derivedPushforward (closedSubsetInclusion X Z)).obj
                  (shiftedUnitObject (closedSubsetRingedSpace X Z) b))
                (shiftedUnitObject X a)).inv) ≫
        (pullbackTensorComparison (closedSubsetInclusion X Z)).app
            ((derivedPushforward (closedSubsetInclusion X Z)).obj
              (shiftedUnitObject (closedSubsetRingedSpace X Z) b), shiftedUnitObject X a) ≫
          (Functor.uncurry.obj
              (derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf)).map
            ((derivedAdjunction (closedSubsetInclusion X Z)).counit.app
                (shiftedUnitObject (closedSubsetRingedSpace X Z) b) ×ₘ
              𝟙 ((derivedPullback (closedSubsetInclusion X Z)).obj
                (shiftedUnitObject X a)))) :
    ShiftedUnitCorepresentingCompatible X Z hZ a b := by
  refine corepresentingCompatible_of_transpose (derivedAdjunction (closedSubsetInclusion X Z))
    (mapDerivedCategoryIsoTotalRightDerived (modulePushforward (closedSubsetInclusion X Z)))
    (derivedTensorProductFunctor X.sheaf)
    (derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf)
    ((canonicalDerivedTensorProduct X.sheaf).braidingIso
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
      (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z)))
    (derivedPullbackShiftedUnitTensorIso (closedSubsetInclusion X Z) a b).hom
    (shiftedUnitTensorIso X a b).hom
    (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) (a + b)).hom
    (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) b).hom
    (projectionFormulaMap (closedSubsetInclusion X Z)
      (shiftedUnitObject (closedSubsetRingedSpace X Z) b) (shiftedUnitObject X a))
    (isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed X Z hZ _ _)
    _ (CategoryTheory.map_adjunctionTensorMap_comp_counit
      (derivedAdjunction (closedSubsetInclusion X Z)) _ _
      (pullbackTensorComparison (closedSubsetInclusion X Z)) _ _) hbk

end AtTheCanonicalObjects

end Stacks.Cohomology.SupportedComplexes

end
