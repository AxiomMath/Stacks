module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PerfectStageNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.RetractOfAPerfectObject

/-!
# Base change of the perfect stage of [Stacks, Tag 08IF] (B), given a base-change map

Let `f : X ⟶ S`, `g : S' ⟶ S`, `f' : X' ⟶ S'`, `g' : X' ⟶ X` be morphisms of ringed spaces,
`𝒢` a complex on `X` and `𝒢'` a complex on `X'`, and suppose given maps

`bc_E : Lg^*Rf_*(E ⊗^L 𝒢) ⟶ Rf'_*(L(g')^*E ⊗^L 𝒢')`

natural in `E`, invertible at the duals of perfect objects. For the cartesian squares of
[Stacks, Tag 0DJS] this is the base-change map of [Stacks, Tag 0A1D] with `𝒢' = (g')^*𝒢`. Then
for perfect `P` on `X`, with `K(P) = Rf_*(P^∨ ⊗ 𝒢)`, `L(P) = K(P)^∨` and `K'`, `L'` likewise on
`X'`,

`Lg^*K(P) ≅ K'(L(g')^*P)` and `Lg^*L(P) ≅ L'(L(g')^*P)`,

and these are natural in `P` for the maps `K(p)` and `L(p)` of
`Stacks.Cohomology.RelativeExtCanonical.stageKMap` and `stageLMap`.

## Main definitions

* `Stacks.Cohomology.RelativeExtCanonical.stageKBaseChangeIso`
* `Stacks.Cohomology.RelativeExtCanonical.stageLBaseChangeIso`

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.derivedPullback_map_dualMate_comp`: the comparison
  `Lg^*(K^∨) ≅ (Lg^*K)^∨` is natural for duals of morphisms.
* `Stacks.Cohomology.RelativeExtCanonical.stageKBaseChangeIso_naturality` and
  `Stacks.Cohomology.RelativeExtCanonical.stageLBaseChangeIso_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The standard model, named

The two abbreviations below are elaborated here, where the standard model is the only
`HasDerivedCategory` instance in scope, so they carry it. Files that also see the locally small
global instance of `StacksFrontier.Homology.DerivedCategory.LocallySmall` state their results
through
them, and so stay at the standard model of everything above without any instance declaration. -/

/-- `D(𝒪)` at the standard model, in the spelling of the derived monoidal structure. -/
abbrev StdDerivedModules {T : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} T) :=
  Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc

/-- The derived pullback at the standard model. -/
abbrev stdPullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    StdDerivedModules Y.sheaf ⥤ StdDerivedModules X.sheaf :=
  derivedPullback f

/-- Perfectness at the standard model. -/
abbrev IsPerfectStd {T : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} T}
    (P : StdDerivedModules Rc) : Prop :=
  (Stacks.SheafOfModules.ringedSite Rc).IsPerfect P

section DualIso

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {T : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} T)
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The dual of a composite is the composite of the duals, in the opposite order. -/
theorem dualMate_comp {A B E : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc}
    (hA : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect A)
    (hB : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect B)
    (hE : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect E) (a : A ⟶ B) (b : B ⟶ E) :
    dualMate Rc hA hE (a ≫ b) = dualMate Rc hB hE b ≫ dualMate Rc hA hB a := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  exact ExactPairing.mate_comp _ _ _ a b

/-- The dual of an identity is the identity. -/
theorem dualMate_id {A : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc}
    (hA : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect A) :
    dualMate Rc hA hA (𝟙 A) = 𝟙 _ := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  exact @rightAdjointMate_id _ _ _ A
    (ExactPairing.hasRightDual (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc A hA))

/-- **The dual of an isomorphism of perfect objects**, `A ≅ B` giving `A^∨ ≅ B^∨` (with
`hom` the dual of the inverse). -/
def dualIsoOfIso {A B : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc}
    (hA : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect A)
    (hB : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect B) (e : A ≅ B) :
    Stacks.SheafOfModules.derivedDual Rc A ≅ Stacks.SheafOfModules.derivedDual Rc B where
  hom := dualMate Rc hB hA e.inv
  inv := dualMate Rc hA hB e.hom
  hom_inv_id := by rw [← dualMate_comp, e.hom_inv_id, dualMate_id]
  inv_hom_id := by rw [← dualMate_comp, e.inv_hom_id, dualMate_id]

end DualIso

section DualPullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`Lf^*(K^∨) ≅ (Lf^*K)^∨` is natural for duals of morphisms.** For `k : K₁ ⟶ K₂` between
perfect objects with perfect pullbacks, `Lf^*(k^∨)` corresponds to `(Lf^*k)^∨` under the
comparison isomorphisms `Stacks.SheafOfModules.derivedPullbackDerivedDualIso`. -/
theorem derivedPullback_map_dualMate_comp
    {K₁ K₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Y.sheaf}
    (hK₁ : (Stacks.SheafOfModules.ringedSite Y.sheaf).IsPerfect K₁)
    (hK₂ : (Stacks.SheafOfModules.ringedSite Y.sheaf).IsPerfect K₂)
    (hfK₁ : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect ((derivedPullback f).obj K₁))
    (hfK₂ : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect ((derivedPullback f).obj K₂))
    (k : K₁ ⟶ K₂) :
    (derivedPullback f).map (dualMate Y.sheaf hK₁ hK₂ k) ≫
        (Stacks.SheafOfModules.derivedPullbackDerivedDualIso f K₁ hK₁ hfK₁).hom =
      (Stacks.SheafOfModules.derivedPullbackDerivedDualIso f K₂ hK₂ hfK₂).hom ≫
        dualMate X.sheaf hfK₁ hfK₂ ((derivedPullback f).map k) :=
  @ExactPairing.map_mate_comp_rightDualIso _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf) (derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal f) _ _ _ _ _ _
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Y.sheaf K₁ hK₁)
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Y.sheaf K₂ hK₂)
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical X.sheaf _ hfK₁)
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical X.sheaf _ hfK₂) k

end DualPullback

section BaseChange

variable {X S S' X' : RingedSpace.{u, u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology S'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
  {G' : CochainComplex (SheafOfModules.{u} (structureSheafRing X')) ℤ}

variable (G G') in
/-- **A family of base-change maps** `Lg^*Rf_*(E ⊗^L 𝒢) ⟶ Rf'_*(L(g')^*E ⊗^L 𝒢')`, one for each
`E` in `D(𝒪_X)`. -/
abbrev BaseChangeFamily : Type _ :=
  ∀ E : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf,
    (derivedPullback g).obj ((derivedPushforward f).obj
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj E).obj
        (DerivedCategory.Q.obj G))) ⟶
    (derivedPushforward f').obj
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g').obj E)).obj (DerivedCategory.Q.obj G'))

/-- **Naturality of a family of base-change maps in `E`.** -/
def BaseChangeFamily.IsNatural (bc : BaseChangeFamily f g f' g' G G') : Prop :=
  ∀ {E₁ E₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf} (e : E₁ ⟶ E₂),
    (derivedPullback g).map ((derivedPushforward f).map
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map e).app
        (DerivedCategory.Q.obj G))) ≫ bc E₂ =
    bc E₁ ≫ (derivedPushforward f').map
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).map
        ((derivedPullback g').map e)).app (DerivedCategory.Q.obj G'))

variable (bc : BaseChangeFamily f g f' g' G G') (hbc : bc.IsNatural)

/-- **`Lg^*K(P) ≅ K'(L(g')^*P)`**: the base-change map at `P^∨`, followed by
`Rf'_*(L(g')^*(P^∨) ⊗ 𝒢') ≅ Rf'_*((L(g')^*P)^∨ ⊗ 𝒢')`. -/
def stageKBaseChangeIso (P : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf)
    (hP : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P)
    (hP' : (Stacks.SheafOfModules.ringedSite X'.sheaf).IsPerfect ((derivedPullback g').obj P))
    [IsIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P))] :
    (derivedPullback g).obj (stageK f (G := G) P) ≅
      stageK f' (G := G') ((derivedPullback g').obj P) :=
  asIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P)) ≪≫
    (derivedPushforward f').mapIso
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).mapIso
        (Stacks.SheafOfModules.derivedPullbackDerivedDualIso g' P hP hP')).app
          (DerivedCategory.Q.obj G'))

include hbc in
/-- **`Lg^*K(P) ≅ K'(L(g')^*P)` is natural in `P`**: it carries `Lg^*K(p)` to
`K'(L(g')^*p)`. -/
theorem stageKBaseChangeIso_naturality
    {P₁ P₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf}
    (hP₁ : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P₁)
    (hP₂ : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P₂)
    (hP₁' : (Stacks.SheafOfModules.ringedSite X'.sheaf).IsPerfect ((derivedPullback g').obj P₁))
    (hP₂' : (Stacks.SheafOfModules.ringedSite X'.sheaf).IsPerfect ((derivedPullback g').obj P₂))
    [IsIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P₁))]
    [IsIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P₂))] (p : P₁ ⟶ P₂) :
    (derivedPullback g).map (stageKMap f (G := G) hP₁ hP₂ p) ≫
        (stageKBaseChangeIso f g f' g' bc P₁ hP₁ hP₁').hom =
      (stageKBaseChangeIso f g f' g' bc P₂ hP₂ hP₂').hom ≫
        stageKMap f' (G := G') hP₁' hP₂' ((derivedPullback g').map p) := by
  have h := derivedPullback_map_dualMate_comp g' hP₁ hP₂ hP₁' hP₂' p
  simp only [stageKBaseChangeIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.app_hom]
  have h1 := hbc (dualMate X.sheaf hP₁ hP₂ p)
  have h2 : (derivedPushforward f').map
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).map
          ((derivedPullback g').map (dualMate X.sheaf hP₁ hP₂ p))).app
            (DerivedCategory.Q.obj G')) ≫
        (derivedPushforward f').map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).map
            (Stacks.SheafOfModules.derivedPullbackDerivedDualIso g' P₁ hP₁ hP₁').hom).app
              (DerivedCategory.Q.obj G')) =
      (derivedPushforward f').map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).map
            (Stacks.SheafOfModules.derivedPullbackDerivedDualIso g' P₂ hP₂ hP₂').hom).app
              (DerivedCategory.Q.obj G')) ≫
        stageKMap f' (G := G') hP₁' hP₂' ((derivedPullback g').map p) := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp, h, Functor.map_comp,
      NatTrans.comp_app, Functor.map_comp]
    rfl
  calc _ = ((derivedPullback g).map ((derivedPushforward f).map
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          (dualMate X.sheaf hP₁ hP₂ p)).app (DerivedCategory.Q.obj G))) ≫
          bc (Stacks.SheafOfModules.derivedDual X.sheaf P₁)) ≫ _ := (Category.assoc _ _ _).symm
    _ = _ := by rw [h1, Category.assoc, h2, ← Category.assoc]

/-- **`Lg^*L(P) ≅ L'(L(g')^*P)`**: `Lg^*(K(P)^∨) ≅ (Lg^*K(P))^∨`, followed by the dual of
`Lg^*K(P) ≅ K'(L(g')^*P)`. -/
def stageLBaseChangeIso (P : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf)
    (hP : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P)
    (hP' : (Stacks.SheafOfModules.ringedSite X'.sheaf).IsPerfect ((derivedPullback g').obj P))
    [IsIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P))]
    (hK : (Stacks.SheafOfModules.ringedSite S.sheaf).IsPerfect (stageK f (G := G) P))
    (hgK : (Stacks.SheafOfModules.ringedSite S'.sheaf).IsPerfect
      ((derivedPullback g).obj (stageK f (G := G) P)))
    (hK' : (Stacks.SheafOfModules.ringedSite S'.sheaf).IsPerfect
      (stageK f' (G := G') ((derivedPullback g').obj P))) :
    (derivedPullback g).obj (stageL f (G := G) P) ≅
      stageL f' (G := G') ((derivedPullback g').obj P) :=
  Stacks.SheafOfModules.derivedPullbackDerivedDualIso g (stageK f (G := G) P) hK hgK ≪≫
    dualIsoOfIso S'.sheaf hgK hK' (stageKBaseChangeIso f g f' g' bc P hP hP')

include hbc in
/-- **`Lg^*L(P) ≅ L'(L(g')^*P)` is natural in `P`**: it carries `Lg^*L(p)` to `L'(L(g')^*p)`. -/
theorem stageLBaseChangeIso_naturality
    {P₁ P₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf}
    (hP₁ : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P₁)
    (hP₂ : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P₂)
    (hP₁' : (Stacks.SheafOfModules.ringedSite X'.sheaf).IsPerfect ((derivedPullback g').obj P₁))
    (hP₂' : (Stacks.SheafOfModules.ringedSite X'.sheaf).IsPerfect ((derivedPullback g').obj P₂))
    [IsIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P₁))]
    [IsIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P₂))]
    (hK₁ : (Stacks.SheafOfModules.ringedSite S.sheaf).IsPerfect (stageK f (G := G) P₁))
    (hK₂ : (Stacks.SheafOfModules.ringedSite S.sheaf).IsPerfect (stageK f (G := G) P₂))
    (hgK₁ : (Stacks.SheafOfModules.ringedSite S'.sheaf).IsPerfect
      ((derivedPullback g).obj (stageK f (G := G) P₁)))
    (hgK₂ : (Stacks.SheafOfModules.ringedSite S'.sheaf).IsPerfect
      ((derivedPullback g).obj (stageK f (G := G) P₂)))
    (hK₁' : (Stacks.SheafOfModules.ringedSite S'.sheaf).IsPerfect
      (stageK f' (G := G') ((derivedPullback g').obj P₁)))
    (hK₂' : (Stacks.SheafOfModules.ringedSite S'.sheaf).IsPerfect
      (stageK f' (G := G') ((derivedPullback g').obj P₂))) (p : P₁ ⟶ P₂) :
    (derivedPullback g).map (stageLMap f (G := G) hP₁ hP₂ p hK₁ hK₂) ≫
        (stageLBaseChangeIso f g f' g' bc P₂ hP₂ hP₂' hK₂ hgK₂ hK₂').hom =
      (stageLBaseChangeIso f g f' g' bc P₁ hP₁ hP₁' hK₁ hgK₁ hK₁').hom ≫
        stageLMap f' (G := G') hP₁' hP₂' ((derivedPullback g').map p) hK₁' hK₂' := by
  have hK := stageKBaseChangeIso_naturality f g f' g' bc hbc hP₁ hP₂ hP₁' hP₂' p
  have h1 := derivedPullback_map_dualMate_comp g hK₂ hK₁ hgK₂ hgK₁ (stageKMap f (G := G) hP₁ hP₂ p)
  set e₁ := stageKBaseChangeIso f g f' g' bc P₁ hP₁ hP₁'
  set e₂ := stageKBaseChangeIso f g f' g' bc P₂ hP₂ hP₂'
  have hK' : e₂.inv ≫ (derivedPullback g).map (stageKMap f (G := G) hP₁ hP₂ p) =
      stageKMap f' (G := G') hP₁' hP₂' ((derivedPullback g').map p) ≫ e₁.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hK, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : dualMate S'.sheaf hgK₂ hgK₁ ((derivedPullback g).map (stageKMap f hP₁ hP₂ p)) ≫
      dualMate S'.sheaf hK₂' hgK₂ e₂.inv =
      dualMate S'.sheaf hK₁' hgK₁ e₁.inv ≫
        dualMate S'.sheaf hK₂' hK₁' (stageKMap f' (G := G') hP₁' hP₂' ((derivedPullback g').map p))
      := by
    rw [← dualMate_comp, ← dualMate_comp, hK']
  change (derivedPullback g).map (dualMate S.sheaf hK₂ hK₁ (stageKMap f hP₁ hP₂ p)) ≫
      (Stacks.SheafOfModules.derivedPullbackDerivedDualIso g _ hK₂ hgK₂).hom ≫
        dualMate S'.sheaf hK₂' hgK₂ e₂.inv =
    ((Stacks.SheafOfModules.derivedPullbackDerivedDualIso g _ hK₁ hgK₁).hom ≫
        dualMate S'.sheaf hK₁' hgK₁ e₁.inv) ≫
      dualMate S'.sheaf hK₂' hK₁' (stageKMap f' hP₁' hP₂' ((derivedPullback g').map p))
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm))

/-- `K'(L(g')^*P)` is perfect as soon as `Lg^*K(P)` is, being isomorphic to it. -/
theorem isPerfectStd_stageK_of_baseChange
    (P : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf)
    (hP : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P)
    (hP' : (Stacks.SheafOfModules.ringedSite X'.sheaf).IsPerfect ((derivedPullback g').obj P))
    [IsIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P))]
    (hgK : (Stacks.SheafOfModules.ringedSite S'.sheaf).IsPerfect
      ((derivedPullback g).obj (stageK f (G := G) P))) :
    (Stacks.SheafOfModules.ringedSite S'.sheaf).IsPerfect
      (stageK f' (G := G') ((derivedPullback g').obj P)) :=
  RingedSite.isPerfect_of_iso _ hgK (stageKBaseChangeIso f g f' g' bc P hP hP')

end BaseChange

end Stacks.Cohomology.RelativeExtCanonical

end
