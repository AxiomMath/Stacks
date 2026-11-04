module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QuasiAffineQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestriction

/-!
# Base change of the twisted inverse image along an open immersion

For a cartesian square
```
U --j'--> X
|         |
f'        f
v         v
V --j---> Y
```
of schemes with `j` an open immersion, the transformation `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` between the
twisted inverse images is an isomorphism. This is the open-immersion case of [Stacks, Tag 0A9K].

## Main results

* `Stacks.Duality.derivedPushforwardDerivedRestrictIso` — [Stacks, Tag 08FE],
  `Stacks.Cohomology.derivedPushforwardRestrictIso`, read in the spelling of
  `Stacks.Duality.derivedPushforward`.
* `Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion` — `ξ` is
  invertible for an open immersion `j`; it is an instance, so it supplies the invertibility
  that `Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap` asks for.

The proof writes `ξ` as the conjugate of the base change map `Rf_* ⋙ j^* ⟶ (j')^* ⋙ Rf'_*`
(Mathlib's `iterated_mateEquiv_conjugateEquiv`), which is invertible because the counit of
`j^* ⊣ Rj_*` is and because `Rf_* ⋙ j^* ≅ (j')^* ⋙ Rf'_*` carries the unit of `(j')^* ⊣ Rj'_*`
to `Rf'_*` of an isomorphism.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### Invertibility of a mate -/

section Mates

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- The mate `G ⋙ L₂ ⟶ L₁ ⋙ H` of an invertible 2-square `R₁ ⋙ G ⟶ H ⋙ R₂` is invertible when
the counit of `L₂ ⊣ R₂` is invertible and `L₂ ⋙ G` inverts the unit of `L₁ ⊣ R₁`: its component
at `c` is `L₂(G(η c))`, then `L₂(α)`, then the counit. -/
theorem isIso_mateEquiv_symm_natTrans (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare R₁ H G R₂) [IsIso α.natTrans] [IsIso adj₂.counit]
    (h : ∀ c : C, IsIso (L₂.map (G.map (adj₁.unit.app c)))) :
    IsIso ((mateEquiv adj₁ adj₂).symm α).natTrans := by
  have (c : C) : IsIso (((mateEquiv adj₁ adj₂).symm α).natTrans.app c) := by
    have hc : ((mateEquiv adj₁ adj₂).symm α).natTrans.app c =
        L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (α.natTrans.app (L₁.obj c)) ≫
          adj₂.counit.app (H.obj (L₁.obj c)) := by
      simp
    rw [hc]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Mates

/-! ### The unit and counit of `j^* ⊣ Rj_*` on full subcategories -/

section Lift

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  (A : ObjectProperty (DerivedCategory Y.Modules))
  (B : ObjectProperty (DerivedCategory X.Modules))
  (hres : ∀ K : A.FullSubcategory, B ((OpenImmersion.derivedRestrict j).obj K.obj))
  (hpush : ∀ L : B.FullSubcategory, A ((derivedPushforward j).obj L.obj))

/-- The unit of `j^* ⊣ Rj_*` between full subcategories is the unit of the ambient adjunction. -/
theorem map_liftDerivedRestrictPushforwardAdjunction_unit_app (E : A.FullSubcategory) :
    A.ι.map ((OpenImmersion.liftDerivedRestrictPushforwardAdjunction j A B hres hpush).unit.app
      E) = (OpenImmersion.derivedRestrictPushforwardAdjunction j).unit.app E.obj := by
  unfold OpenImmersion.liftDerivedRestrictPushforwardAdjunction
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [ObjectProperty.liftCompιIso]

/-- The counit of `j^* ⊣ Rj_*` between full subcategories is the counit of the ambient
adjunction. -/
theorem map_liftDerivedRestrictPushforwardAdjunction_counit_app (E : B.FullSubcategory) :
    B.ι.map ((OpenImmersion.liftDerivedRestrictPushforwardAdjunction j A B hres hpush).counit.app
      E) = (OpenImmersion.derivedRestrictPushforwardAdjunction j).counit.app E.obj := by
  unfold OpenImmersion.liftDerivedRestrictPushforwardAdjunction
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  simp [ObjectProperty.liftCompιIso]

/-- The counit of `j^* ⊣ Rj_*` between full subcategories is invertible: `Rj_*` is fully
faithful. -/
instance isIso_liftDerivedRestrictPushforwardAdjunction_counit :
    IsIso (OpenImmersion.liftDerivedRestrictPushforwardAdjunction j A B hres hpush).counit := by
  have (E : B.FullSubcategory) : IsIso
      ((OpenImmersion.liftDerivedRestrictPushforwardAdjunction j A B hres hpush).counit.app E) := by
    have : IsIso (B.ι.map
        ((OpenImmersion.liftDerivedRestrictPushforwardAdjunction j A B hres hpush).counit.app
          E)) := by
      rw [map_liftDerivedRestrictPushforwardAdjunction_counit_app]
      infer_instance
    exact isIso_of_reflects_iso _ B.ι
  exact NatIso.isIso_of_isIso_app _

end Lift

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

section Restrict

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j]

/-- **Derived direct image commutes with restriction to opens**, [Stacks, Tag 08FE], for a
cartesian square of schemes whose vertical sides are open immersions, in the spelling
`Rf_* ⋙ j^* ≅ (j')^* ⋙ Rf'_*` of `Stacks.Duality.derivedPushforward` and
`Stacks.Duality.OpenImmersion.derivedRestrict`, at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
def derivedPushforwardDerivedRestrictIso (sq : IsPullback j' f' f j) :
    derivedPushforward f ⋙ OpenImmersion.derivedRestrict j ≅
      OpenImmersion.derivedRestrict j' ⋙ derivedPushforward f' :=
  have hiR : (Scheme.Modules.pullback j').mapDerivedCategory.IsRightDerivedFunctor
      (Scheme.Modules.pullback j').mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (Scheme.Modules.pullback j').mapDerivedCategoryFactorsh
  have hjR : (Scheme.Modules.pullback j).mapDerivedCategory.IsRightDerivedFunctor
      (Scheme.Modules.pullback j).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (Scheme.Modules.pullback j).mapDerivedCategoryFactorsh
  have hfR : (derivedPushforward f).IsRightDerivedFunctor (derivedPushforwardUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := inferInstance
  have hf'R : (derivedPushforward f').IsRightDerivedFunctor (derivedPushforwardUnit f')
      (HomotopyCategory.quasiIso U.Modules (ComplexShape.up ℤ)) := inferInstance
  let e : derivedPushforward f ⋙ (Scheme.Modules.pullback j).mapDerivedCategory ≅
      (Scheme.Modules.pullback j').mapDerivedCategory ⋙ derivedPushforward f' :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
      f.toLRSHom.toShHom j'.toLRSHom.toShHom j.toLRSHom.toShHom f'.toLRSHom.toShHom
      _ _ (isPullback_toShHom j' f' f j sq) _ _ _ _
      (derivedPushforward f) (derivedPushforward f')
      (Scheme.Modules.pullback j').mapDerivedCategory
      (Scheme.Modules.pullback j).mapDerivedCategory
      (derivedPushforwardUnit f) (derivedPushforwardUnit f')
      (Scheme.Modules.pullback j').mapDerivedCategoryFactorsh.inv
      (Scheme.Modules.pullback j).mapDerivedCategoryFactorsh.inv hfR hf'R hiR hjR
  Functor.isoWhiskerLeft _
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorIsoPullback j)) ≪≫ e ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorIsoPullback j')).symm _

/-- After restriction to `V`, the derived direct image inverts the unit `K ⟶ Rj'_*((j')^*K)` of
the derived adjunction `(j')^* ⊣ Rj'_*`: its cone is supported away from `U`. -/
theorem isIso_derivedRestrict_map_derivedPushforward_map_unit (sq : IsPullback j' f' f j)
    (K : DerivedCategory X.Modules) :
    IsIso ((OpenImmersion.derivedRestrict j).map ((derivedPushforward f).map
      ((OpenImmersion.derivedRestrictPushforwardAdjunction j').unit.app K))) := by
  have h₁ : IsIso ((OpenImmersion.derivedRestrict j').map
      ((OpenImmersion.derivedRestrictPushforwardAdjunction j').unit.app K)) := by
    have h := (OpenImmersion.derivedRestrictPushforwardAdjunction j').left_triangle_components K
    rw [IsIso.eq_inv_of_inv_hom_id h]
    infer_instance
  have e := (derivedPushforwardDerivedRestrictIso j' f' f j sq).hom.naturality
    ((OpenImmersion.derivedRestrictPushforwardAdjunction j').unit.app K)
  dsimp only [Functor.comp_map] at e
  rw [← cancel_mono ((derivedPushforwardDerivedRestrictIso j' f' f j sq).inv.app _),
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at e
  rw [e]
  infer_instance

end Restrict

section BaseChange

open OpenImmersion

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j]
  (hpushj' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward j').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushj : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward j).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]

/-- **The open-immersion case of [Stacks, Tag 0A9K].** For a cartesian square of schemes whose
vertical sides `j : V ⟶ Y` and `j' : U ⟶ X` are open immersions, the transformation
`ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` between the twisted inverse images of `f` and `f'` is an isomorphism.

`ξ` is the conjugate, under the composite adjunctions `(j')^* ⋙ Rf'_* ⊣ a' ⋙ Rj'_*` and
`Rf_* ⋙ j^* ⊣ Rj_* ⋙ a`, of the base change map `Rf_* ⋙ j^* ⟶ (j')^* ⋙ Rf'_*`. That map is the
unit of `(j')^* ⊣ Rj'_*`, followed by the comparison of pushforwards around the square and the
counit of `j^* ⊣ Rj_*`; the counit is invertible, and after restriction to `V` the derived direct
image inverts the unit (`isIso_derivedRestrict_map_derivedPushforward_map_unit`). -/
theorem isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion
    (sq : IsPullback j' f' f j) :
    IsIso (twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf hpushf' hpushj
      sq) := by
  let hresj := isQuasicoherent_homology_derivedRestrict j
  let hresj' := isQuasicoherent_homology_derivedRestrict j'
  let adjL := quasiCoherentDerivedRestrictAdjunction j hresj hpushj
  let adjL' := quasiCoherentDerivedRestrictAdjunction j' hresj' hpushj'
  let α := quasiCoherentDerivedPushforwardSquareIso j' f' f j hpushj' hpushf hpushf' hpushj sq.w
  have hu (K : quasiCoherentDerivedCategory X) :
      IsIso ((quasiCoherentDerivedRestrict j hresj).map
        ((quasiCoherentDerivedPushforward f hpushf).map (adjL'.unit.app K))) := by
    have : IsIso ((derivedRestrict j).map ((derivedPushforward f).map
        ((ObjectProperty.ι _).map (adjL'.unit.app K)))) := by
      rw [map_liftDerivedRestrictPushforwardAdjunction_unit_app j' _ _ hresj' hpushj' K]
      exact isIso_derivedRestrict_map_derivedPushforward_map_unit j' f' f j sq K.obj
    exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (ObjectProperty.ι _) this _
  have : IsIso adjL.counit := isIso_liftDerivedRestrictPushforwardAdjunction_counit j _ _ _ _
  have hβ := isIso_mateEquiv_symm_natTrans adjL' adjL α.hom hu
  have hξ : twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf hpushf' hpushj sq =
      conjugateEquiv (adjL'.comp (twistedInverseImageAdjunction f' hpushf'))
        ((twistedInverseImageAdjunction f hpushf).comp adjL)
          ((mateEquiv adjL' adjL).symm α.hom).natTrans := by
    rw [← iterated_mateEquiv_conjugateEquiv]
    exact (congrArg (fun γ => (mateEquiv (twistedInverseImageAdjunction f' hpushf')
      (twistedInverseImageAdjunction f hpushf) γ).natTrans)
        ((mateEquiv adjL' adjL).apply_symm_apply α.hom)).symm
  rw [hξ]
  infer_instance

attribute [instance] isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion

end BaseChange

end Stacks.Duality

end
