module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor

/-!
# The comparison map of Stacks 0761 read on a slice

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `φ : x ⟶ y` an arrow of `𝒳`
lying over a morphism of schemes `a : U ⟶ V`. The comparison map
`c_φ : a_{small}^*(M|_{V_ét}) ⟶ M|_{U_ét}` of **Stacks 0761**, for an étale sheaf of modules `M`
on `𝒳` (`AlgebraicGeometry.Stack.restrictSheafPullbackComparison`), only depends on the
restriction of `M` to the slice `𝒳/y`: both restrictions are read through objects lying over `y`.
This file makes that precise by constructing the comparison map for an arbitrary étale sheaf of
modules `N` on the slice `𝒳/y`, natural in `N`, and identifying it with `c_φ` when `N` is the
restriction of a sheaf on `𝒳`.

Naturality in `N` is the point: the morphisms that come from a local computation — for instance
the presentation of an internal Hom over `y` as a kernel of a map of finite products, which is a
map of sheaves on `𝒳/y` and not on `𝒳` — act on the comparison maps.

## Main definitions

* `AlgebraicGeometry.Stack.sliceComparisonLift`: the arrow of `𝒳/y` along which the comparison of
  **Stacks 06W2** restricts sections, characterized by
  `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_eq_sliceComparisonLift`.
* `AlgebraicGeometry.Stack.slicePushforwardComparison` and
  `AlgebraicGeometry.Stack.slicePullbackComparison`: the comparison of **Stacks 06WC** for a
  presheaf of modules on `𝒳/y`, in its direct-image form and as its mate.
* `AlgebraicGeometry.Stack.sliceRestrictSheaf`, `AlgebraicGeometry.Stack.sliceRestrictAlongSheaf`:
  the restrictions to the small étale sites below `y` and `x`, read on `𝒳/y`, as functors of
  sheaves of modules.
* `AlgebraicGeometry.Stack.sliceSheafComparison` and
  `AlgebraicGeometry.Stack.sliceSheafComparisonNatTrans`: the comparison map `c_φ` read on
  `𝒳/y`, with `a_{small}^*` the inverse image of sheaves of modules.
* `AlgebraicGeometry.Stack.sliceOver`: the restriction of a sheaf of modules on `𝒳` to `𝒳/y` by
  reindexing, isomorphic to `M.over y` by `AlgebraicGeometry.Stack.overIsoSliceOver`.

## Main results

* `AlgebraicGeometry.Stack.slicePullbackComparison_over`: the slice comparison at the restriction
  of a sheaf on `𝒳` is the comparison map of **Stacks 06WC** of that sheaf.
* `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_iff_sliceSheafComparison`: `c_φ`
  is invertible exactly when the slice comparison at the restriction of the sheaf is.
* `AlgebraicGeometry.Stack.sliceSheafComparison_naturality`: the slice comparison is natural.
* The two restriction functors of sheaves on `𝒳/y` preserve finite limits.

## Implementation notes

The slice lifts are chosen with `exists_restrictionComparisonLift`, and their naturality in the
small étale object is read off from the naturality of the comparison of **Stacks 06W2** for the
represented presheaf `yoneda.obj _`, whose component the lift computes.

The restriction of `M` to `𝒳/y` is used in the reindexed spelling
`AlgebraicGeometry.Stack.sliceOver` for the identification with `c_φ`: `M.over y` carries in
addition a change of scalars along the identity, and the elaborator does not see through it
within its heartbeat budget when comparing the two adjunction transposes. For the same reason,
`AlgebraicGeometry.smallEtaleBaseChange`, `CategoryTheory.Over.post`,
`AlgebraicGeometry.Stack.baseStructureSheaf` and `AlgebraicGeometry.Stack.baseRingStructureSheaf`
are made locally irreducible.

## References

* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- The functor from the small étale site of the scheme below `x` to the slice `𝒳/x` along which
the restriction of Stacks 06WJ is read on the slice. -/
noncomputable def smallEtaleToSlice (x : 𝒳) :
    SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) ⥤ Over x :=
  letI := isEquivalence_overPost B S hS p hp x
  smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv

/-- The restriction of an étale sheaf of modules on `𝒳` to the slice `𝒳/y`, spelled as the
reindexing of its underlying presheaf of modules along `𝒳/y ⥤ 𝒳`. It is the restriction
`M.over y` up to the identity change of scalars (`AlgebraicGeometry.Stack.overIsoSliceOver`);
this spelling makes the restrictions to small étale sites of the slice agree with those of `𝒳`
without unfolding a change of scalars. -/
noncomputable def sliceOver (y : 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y) :=
  ⟨(PresheafOfModules.pushforward₀ (Over.forget y)
      (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj).obj M.val,
    (Over.forget y).op_comp_isSheaf_of_isSheaf
      ((associatedTopology B S hS p (etaleTopology B)).over y)
      (associatedTopology B S hS p (etaleTopology B)) _ M.isSheaf⟩

/-- The two spellings of the restriction of an étale sheaf of modules to the slice `𝒳/y` are
isomorphic, by the identity on sections. -/
noncomputable def overIsoSliceOver (y : 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    M.over y ≅ sliceOver B S hS p hp y M :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _))

variable {x y : 𝒳} (φ : x ⟶ y)

/-- The lift computing the comparison map of Stacks 06W2 below `φ`, as a morphism of the slice
`𝒳/y`. -/
noncomputable def sliceComparisonLift
    (W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :
    (Over.map φ).obj ((smallEtaleToSlice B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W)) ⟶
      (smallEtaleToSlice B E h S hS p hp y).obj W :=
  Over.homMk (exists_restrictionComparisonLift B E h S hS p hp φ W).choose
    (exists_restrictionComparisonLift B E h S hS p hp φ W).choose_spec.1

/-- The comparison map of Stacks 06W2 is restriction along the slice lift. -/
theorem restrictionPushforwardComparison_app_eq_sliceComparisonLift {A : Type*} [Category A]
    (F : 𝒳ᵒᵖ ⥤ A) (W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :
    (restrictionPushforwardComparison B E h S hS p hp φ F).app (Opposite.op W) =
      F.map (sliceComparisonLift B E h S hS p hp φ W).left.op :=
  restrictionPushforwardComparison_app B E h S hS p hp φ F W _
    (exists_restrictionComparisonLift B E h S hS p hp φ W).choose_spec.1
    (exists_restrictionComparisonLift B E h S hS p hp φ W).choose_spec.2

/-- The slice lifts are natural in the small étale object. -/
theorem sliceComparisonLift_naturality
    {W W' : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)} (g : W ⟶ W') :
    (Over.map φ).map ((smallEtaleToSlice B E h S hS p hp x).map
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).map g)) ≫
        sliceComparisonLift B E h S hS p hp φ W' =
      sliceComparisonLift B E h S hS p hp φ W ≫ (smallEtaleToSlice B E h S hS p hp y).map g := by
  apply Over.OverMorphism.ext
  let T := ((smallEtaleToSlice B E h S hS p hp y).obj W').left
  have hnat := ConcreteCategory.congr_hom ((restrictionPushforwardComparison B E h S hS p hp φ
    (yoneda.obj T)).naturality g.op) (𝟙 T)
  rw [restrictionPushforwardComparison_app_eq_sliceComparisonLift,
    restrictionPushforwardComparison_app_eq_sliceComparisonLift] at hnat
  have h₂ : ((Over.map φ).map ((smallEtaleToSlice B E h S hS p hp x).map
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).map g))).left ≫
        (sliceComparisonLift B E h S hS p hp φ W').left ≫ 𝟙 _ =
      (sliceComparisonLift B E h S hS p hp φ W).left ≫
        ((smallEtaleToSlice B E h S hS p hp y).map g).left ≫ 𝟙 _ := hnat.symm
  simpa using h₂

/-- The slice lifts, as a natural transformation of functors from the small étale site of the
scheme below `y` to the slice `𝒳/y`. -/
noncomputable def sliceComparisonLiftNatTrans :
    smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ) ⋙
        smallEtaleToSlice B E h S hS p hp x ⋙ Over.map φ ⟶
      smallEtaleToSlice B E h S hS p hp y where
  app W := sliceComparisonLift B E h S hS p hp φ W
  naturality _ _ g := sliceComparisonLift_naturality B E h S hS p hp φ g

section Modules

/-- The restriction of Stacks 06WJ at the source `x` of `φ : x ⟶ y`, read on the slice `𝒳/y`: a
presheaf of modules on `𝒳/y` is restricted along `𝒳/x ⟶ 𝒳/y` and the localization functor of
Stacks 06W0 at `x`, and its scalars are moved by
`AlgebraicGeometry.Stack.localStructurePresheafIso`. -/
noncomputable def sliceRestrictAlong :
    PresheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y).obj ⥤
      PresheafOfModules.{u}
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
  PresheafOfModules.pushforward₀ (smallEtaleToSlice B E h S hS p hp x ⋙ Over.map φ)
      ((ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).over y).obj ⋙
    PresheafOfModules.restrictScalars
      (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)).hom

/-- The scalar half of the slice comparison: the map `a_{small}^♯` of structure sheaves is
restriction along the slice lift. -/
theorem smallEtaleStructureComparison_app_eq_sliceComparisonLift
    (W : (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))ᵒᵖ)
    (r : (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)).obj.obj W) :
    (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj W)
        ((smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B)).app W r) =
      ((ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).over y).obj.map
        (sliceComparisonLift B E h S hS p hp φ W.unop).op
        ((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
          (etaleTopology_le_topology B)).hom.app W r) := by
  have hring := restrictionPushforwardComparison_app_eq_sliceComparisonLift B E h S hS p hp φ
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
    W.unop
  have hcancel := ConcreteCategory.congr_hom
    ((localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).inv_hom_id_app
      ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj W))
    ((restrictionPushforwardComparison B E h S hS p hp φ
        (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)).obj).app W
      ((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app W r))
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hcancel
  have happ : (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B)).app W r =
      (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)).inv.app
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj W)
        ((restrictionPushforwardComparison B E h S hS p hp φ
            (ringStructureSheafCore B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)).obj).app W
          ((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
            (etaleTopology_le_topology B)).hom.app W r)) :=
    rfl
  rw [happ, hcancel, hring]
  rfl

/-- **The comparison of Stacks 06WC read on the slice `𝒳/y`**, in its direct-image form: for a
presheaf of modules `N` on `𝒳/y`, the restriction at `y` maps to the direct image of the
restriction at `x` by restriction of `N` along the slice lifts. -/
noncomputable def slicePushforwardComparison
    (N : PresheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y).obj) :
    (sliceRestrictToSmallEtale B E h S hS p hp y).obj N ⟶
      (PresheafOfModules.pushforward.{u}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).obj
        ((sliceRestrictAlong B E h S hS p hp φ).obj N) :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (NatTrans.op (sliceComparisonLiftNatTrans B E h S hS p hp φ))
      N.presheaf)
    (by
      intro W r n
      refine (PresheafOfModules.map_smul N (sliceComparisonLift B E h S hS p hp φ W.unop).op
        ((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
          (etaleTopology_le_topology B)).hom.app W r) n).trans ?_
      rw [← smallEtaleStructureComparison_app_eq_sliceComparisonLift B E h S hS p hp φ W r]
      rfl)

/-- The slice comparison at the restriction of an étale sheaf of modules on `𝒳` to `𝒳/y` is the
comparison of Stacks 06WC of that sheaf. -/
theorem slicePushforwardComparison_over
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    slicePushforwardComparison B E h S hS p hp φ (sliceOver B S hS p hp y M).val =
      restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) M.val := by
  refine PresheafOfModules.hom_ext fun W => ?_
  ext n
  exact (ConcreteCategory.congr_hom (restrictionPushforwardComparison_app_eq_sliceComparisonLift
    B E h S hS p hp φ M.val.presheaf W.unop) n).symm

/-- The slice comparison in its direct-image form is natural in the presheaf of modules. -/
theorem slicePushforwardComparison_naturality
    {N N' : PresheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y).obj} (α : N ⟶ N') :
    (sliceRestrictToSmallEtale B E h S hS p hp y).map α ≫
        slicePushforwardComparison B E h S hS p hp φ N' =
      slicePushforwardComparison B E h S hS p hp φ N ≫
        (PresheafOfModules.pushforward.{u}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).map ((sliceRestrictAlong B E h S hS p hp φ).map α) := by
  refine PresheafOfModules.hom_ext fun W => ?_
  ext n
  exact (PresheafOfModules.naturality_apply α
    (sliceComparisonLift B E h S hS p hp φ W.unop).op n).symm

/-- **The comparison of Stacks 06WC read on the slice `𝒳/y`**: the mate of
`AlgebraicGeometry.Stack.slicePushforwardComparison` under the pullback–direct image adjunction
along `a_{small}^♯`. -/
noncomputable def slicePullbackComparison
    (N : PresheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y).obj) :
    (PresheafOfModules.pullback.{u}
        (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
        (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B))).obj
        ((sliceRestrictToSmallEtale B E h S hS p hp y).obj N) ⟶
      (sliceRestrictAlong B E h S hS p hp φ).obj N :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B))).homEquiv _ _).symm
      (slicePushforwardComparison B E h S hS p hp φ N)

/- The restrictions of `sliceOver y M` are the restrictions of `M`, and the adjunction
bijections at the two spellings agree. These are stated, and used, in the direction in which the
elaborator checks them within its budget. -/
private theorem homEquiv_restrict_eq_slice
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B))).homEquiv
      (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
        (etaleTopology_le_topology B) M.val)
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) M.val) =
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B))).homEquiv ((sliceRestrictToSmallEtale B E h S hS p hp y).obj
        (sliceOver B S hS p hp y M).val)
      ((sliceRestrictAlong B E h S hS p hp φ).obj
        (sliceOver B S hS p hp y M).val) := rfl

/-- The slice comparison at the restriction of an étale sheaf of modules to `𝒳/y` is the
comparison map of Stacks 06WC of that sheaf. -/
theorem slicePullbackComparison_over
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    slicePullbackComparison B E h S hS p hp φ (sliceOver B S hS p hp y M).val =
      restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) M.val := by
  rw [slicePullbackComparison, slicePushforwardComparison_over]
  exact (congrArg (fun e => e.symm (restrictModulePushforwardComparison B E h S hS p hp φ
    (etaleTopology B) (etaleTopology_le_topology B) M.val))
      (homEquiv_restrict_eq_slice B E h S hS p hp φ M)).symm

/-- The slice comparison is natural in the presheaf of modules. -/
theorem slicePullbackComparison_naturality
    {N N' : PresheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y).obj} (α : N ⟶ N') :
    (PresheafOfModules.pullback.{u}
        (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
        (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B))).map
        ((sliceRestrictToSmallEtale B E h S hS p hp y).map α) ≫
        slicePullbackComparison B E h S hS p hp φ N' =
      slicePullbackComparison B E h S hS p hp φ N ≫
        (sliceRestrictAlong B E h S hS p hp φ).map α := by
  apply ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    slicePullbackComparison, slicePullbackComparison, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact slicePushforwardComparison_naturality B E h S hS p hp φ α

end Modules

section Sheaves

/-- The functor from the small étale site of the scheme below `x` to the slice `𝒳/x` is
continuous for the small étale topology and the localized associated étale topology. -/
theorem isContinuous_smallEtaleToSlice (x : 𝒳) :
    (smallEtaleToSlice B E h S hS p hp x).IsContinuous
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      ((associatedTopology B S hS p (etaleTopology B)).over x) := by
  let := isEquivalence_overPost B S hS p hp x
  let hU : E.Contains (p.obj x).left.1 := contains_base B E h S hS p x
  let i := smallEtaleInclusion B E h (p.obj x).left.1 hU
  let b := Over.post (X := x) (p ⋙ Over.forget (B.obj hS))
  let J := SmallEtale.topology E (p.obj x).left.1 hU
  let K := associatedTopology B S hS p (etaleTopology B)
  let L := (etaleTopology B).over (p.obj x).left
  have h₁ : i.IsContinuous J L :=
    (isContinuous_and_isCocontinuous_smallEtaleInclusion B E h (p.obj x).left.1 hU).1
  have h₂ : b.inv.IsDenseSubsite L (K.over x) := by
    rw [← inducedTopology_overPost B S hS p hp (etaleTopology B) x]
    exact (inferInstance : b.asEquivalence.symm.functor.IsDenseSubsite L
      (b.asEquivalence.symm.inverse.inducedTopology L))
  exact Functor.isContinuous_comp i b.inv J L (K.over x)

/-- The functor from the small étale site of the scheme below `x` to the slice `𝒳/y` along
`φ : x ⟶ y` is continuous. -/
theorem isContinuous_smallEtaleToSlice_comp_map :
    (smallEtaleToSlice B E h S hS p hp x ⋙ Over.map φ).IsContinuous
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      ((associatedTopology B S hS p (etaleTopology B)).over y) := by
  have := isContinuous_smallEtaleToSlice B E h S hS p hp x
  exact Functor.isContinuous_comp _ _ _
    ((associatedTopology B S hS p (etaleTopology B)).over x) _

/-- The restriction of Stacks 06WJ at `y`, read on the slice `𝒳/y`, as a functor of sheaves of
modules. -/
@[reducible] noncomputable def sliceRestrictSheaf (y : 𝒳) :
    SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y) ⥤
      SheafOfModules.{u}
        (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)) where
  obj N := ⟨(sliceRestrictToSmallEtale B E h S hS p hp y).obj N.val, by
    have := isContinuous_smallEtaleToSlice B E h S hS p hp y
    exact (smallEtaleToSlice B E h S hS p hp y).op_comp_isSheaf_of_isSheaf _ _ _ N.isSheaf⟩
  map f := ⟨(sliceRestrictToSmallEtale B E h S hS p hp y).map f.val⟩
  map_id N := SheafOfModules.hom_ext
    ((sliceRestrictToSmallEtale B E h S hS p hp y).map_id N.val)
  map_comp f g := SheafOfModules.hom_ext
    ((sliceRestrictToSmallEtale B E h S hS p hp y).map_comp f.val g.val)

/-- The restriction of Stacks 06WJ at the source of `φ : x ⟶ y`, read on the slice `𝒳/y`, as a
functor of sheaves of modules. -/
@[reducible] noncomputable def sliceRestrictAlongSheaf :
    SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y) ⥤
      SheafOfModules.{u}
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)) where
  obj N := ⟨(sliceRestrictAlong B E h S hS p hp φ).obj N.val, by
    have := isContinuous_smallEtaleToSlice_comp_map B E h S hS p hp φ
    exact (smallEtaleToSlice B E h S hS p hp x ⋙ Over.map φ).op_comp_isSheaf_of_isSheaf _ _ _
      N.isSheaf⟩
  map f := ⟨(sliceRestrictAlong B E h S hS p hp φ).map f.val⟩
  map_id N := SheafOfModules.hom_ext
    ((sliceRestrictAlong B E h S hS p hp φ).map_id N.val)
  map_comp f g := SheafOfModules.hom_ext
    ((sliceRestrictAlong B E h S hS p hp φ).map_comp f.val g.val)

/-- **The comparison map `c_φ` of Stacks 0761 read on the slice `𝒳/y`**, for étale sheaves of
modules on `𝒳/y`: the adjunct, across the sheafification adjunction of the small étale site
below `x`, of `AlgebraicGeometry.Stack.slicePullbackComparison`. -/
noncomputable def sliceSheafComparison
    (N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y)) :
    (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).obj ((sliceRestrictSheaf B E h S hS p hp y).obj N) ⟶
      (sliceRestrictAlongSheaf B E h S hS p hp φ).obj N :=
  ((smallEtaleSheafificationAdjunction B E h S hS p x).homEquiv
    ((PresheafOfModules.pullback.{u}
        (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
        (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B))).obj ((sliceRestrictSheaf B E h S hS p hp y).obj N).val)
    ((sliceRestrictAlongSheaf B E h S hS p hp φ).obj N)).symm
      (slicePullbackComparison B E h S hS p hp φ N.val)

/-- A morphism out of a sheafification into a sheaf is invertible exactly when its transpose
becomes invertible after sheafification: the transpose of `g` is the sheafification of `g`
followed by the counit, which is invertible on a sheaf. -/
theorem isIso_smallEtaleSheafificationAdjunction_homEquiv_symm_iff (z : 𝒳)
    {P : PresheafOfModules.{u}
      (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj}
    {T : SheafOfModules.{u}
      (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))}
    (g : P ⟶ (SheafOfModules.forget _).obj T) :
    IsIso (((smallEtaleSheafificationAdjunction B E h S hS p z).homEquiv P T).symm g) ↔
      IsIso ((smallEtaleSheafification B E h S hS p z).map g) := by
  rw [Adjunction.homEquiv_counit]
  have : IsIso ((smallEtaleSheafificationAdjunction B E h S hS p z).counit.app T) :=
    NatIso.isIso_app_of_isIso _ _
  exact ⟨fun _ => IsIso.of_isIso_comp_right _
    ((smallEtaleSheafificationAdjunction B E h S hS p z).counit.app T), fun _ => inferInstance⟩

/-- The comparison map `c_φ` of Stacks 0761 at an étale sheaf of modules `M` on `𝒳` is
invertible exactly when the slice comparison at the restriction of `M` to `𝒳/y` is. -/
theorem isIso_restrictSheafPullbackComparison_iff_sliceSheafComparison
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ M) ↔
      IsIso (sliceSheafComparison B E h S hS p hp φ (sliceOver B S hS p hp y M)) := by
  have h₁ : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ M) ↔
      IsIso ((smallEtaleSheafification B E h S hS p x).map
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) M.val)) :=
    isIso_smallEtaleSheafificationAdjunction_homEquiv_symm_iff B E h S hS p x
      (T := (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj M) _
  have h₂ : IsIso (sliceSheafComparison B E h S hS p hp φ (sliceOver B S hS p hp y M)) ↔
      IsIso ((smallEtaleSheafification B E h S hS p x).map
        (slicePullbackComparison B E h S hS p hp φ (sliceOver B S hS p hp y M).val)) :=
    isIso_smallEtaleSheafificationAdjunction_homEquiv_symm_iff B E h S hS p x
      (T := (sliceRestrictAlongSheaf B E h S hS p hp φ).obj (sliceOver B S hS p hp y M)) _
  rw [h₁, h₂, slicePullbackComparison_over]
  exact Iff.rfl

/-- The sheaf comparison read on the slice `𝒳/y` is natural in the sheaf of modules. -/
theorem sliceSheafComparison_naturality
    {N N' : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y)} (α : N ⟶ N') :
    (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ).map
        ((sliceRestrictSheaf B E h S hS p hp y).map α) ≫
          sliceSheafComparison B E h S hS p hp φ N' =
      sliceSheafComparison B E h S hS p hp φ N ≫
        (sliceRestrictAlongSheaf B E h S hS p hp φ).map α := by
  let adj := smallEtaleSheafificationAdjunction B E h S hS p x
  have hleft := adj.homEquiv_naturality_left_symm
    (Y := (sliceRestrictAlongSheaf B E h S hS p hp φ).obj N')
    ((PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B))).map
      ((sliceRestrictToSmallEtale B E h S hS p hp y).map α.val))
    (slicePullbackComparison B E h S hS p hp φ N'.val)
  have hright := adj.homEquiv_naturality_right_symm
    (Y := (sliceRestrictAlongSheaf B E h S hS p hp φ).obj N)
    (slicePullbackComparison B E h S hS p hp φ N.val)
    ((sliceRestrictAlongSheaf B E h S hS p hp φ).map α)
  exact hleft.symm.trans ((congrArg (adj.homEquiv _
    ((sliceRestrictAlongSheaf B E h S hS p hp φ).obj N')).symm
      (slicePullbackComparison_naturality B E h S hS p hp φ α.val)).trans hright)

/-- The sheaf comparison read on the slice `𝒳/y`, as a natural transformation. -/
noncomputable def sliceSheafComparisonNatTrans :
    sliceRestrictSheaf B E h S hS p hp y ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ ⟶
      sliceRestrictAlongSheaf B E h S hS p hp φ where
  app N := sliceSheafComparison B E h S hS p hp φ N
  naturality _ _ α := sliceSheafComparison_naturality B E h S hS p hp φ α

/-- The slice comparison is invertible together with its value at an isomorphic sheaf. -/
theorem isIso_sliceSheafComparison_of_iso
    {N N' : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y)} (e : N ≅ N')
    (hN : IsIso (sliceSheafComparison B E h S hS p hp φ N)) :
    IsIso (sliceSheafComparison B E h S hS p hp φ N') := by
  have hcomp : IsIso ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).map ((sliceRestrictSheaf B E h S hS p hp y).map e.inv) ≫
        sliceSheafComparison B E h S hS p hp φ N) := by
    rw [show (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).map ((sliceRestrictSheaf B E h S hS p hp y).map e.inv) =
      ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).mapIso
        ((sliceRestrictSheaf B E h S hS p hp y).mapIso e.symm)).hom from rfl]
    infer_instance
  rw [sliceSheafComparison_naturality] at hcomp
  have h₁ : IsIso ((sliceRestrictAlongSheaf B E h S hS p hp φ).map e.inv) :=
    ((sliceRestrictAlongSheaf B E h S hS p hp φ).mapIso e.symm).isIso_hom
  exact IsIso.of_isIso_comp_right _ ((sliceRestrictAlongSheaf B E h S hS p hp φ).map e.inv)

section Limits

variable (K : Type) [SmallCategory K] [HasLimitsOfShape K (Type u)]

/-- The restriction along `𝒳/x ⥤ 𝒳/y` and the small étale site at `x` preserves limits: on
sections it is a reindexing followed by a change of scalars. -/
instance preservesLimitsOfShape_sliceRestrictAlong :
    PreservesLimitsOfShape K (sliceRestrictAlong B E h S hS p hp φ) := by
  refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
  have hsmall' : ∀ Y, Small.{u} ((D ⋙ PresheafOfModules.evaluation _ Y) ⋙ forget _).sections :=
    fun Y => (Types.hasLimit_iff_small_sections _).mp inferInstance
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X => ?_⟩
  let q := smallEtaleToSlice B E h S hS p hp x ⋙ Over.map φ
  have := hsmall' (q.op.obj X)
  have : PreservesLimit (D ⋙ PresheafOfModules.evaluation ((ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)).over y).obj (q.op.obj X))
      (ModuleCat.restrictScalars ((localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app X).hom) :=
    ModuleCat.preservesLimit_restrictScalars _ _
  exact (this.preserves (isLimitOfPreserves (PresheafOfModules.evaluation ((ringStructureSheafCore
    B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).over y).obj (q.op.obj X))
      hc)).some

/-- The restriction of sheaves of modules on `𝒳/y` to the small étale site below `y` preserves
limits, which are computed on underlying presheaves of modules. -/
instance preservesLimitsOfShape_sliceRestrictSheaf :
    PreservesLimitsOfShape K (sliceRestrictSheaf B E h S hS p hp y) := by
  have : PreservesLimitsOfShape K (sliceRestrictSheaf B E h S hS p hp y ⋙
      SheafOfModules.forget _) :=
    inferInstanceAs (PreservesLimitsOfShape K
      (SheafOfModules.forget _ ⋙ sliceRestrictToSmallEtale B E h S hS p hp y))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.forget _)

/-- The restriction of sheaves of modules on `𝒳/y` to the small étale site below the source of
`φ` preserves limits, which are computed on underlying presheaves of modules. -/
instance preservesLimitsOfShape_sliceRestrictAlongSheaf :
    PreservesLimitsOfShape K (sliceRestrictAlongSheaf B E h S hS p hp φ) := by
  have : PreservesLimitsOfShape K (sliceRestrictAlongSheaf B E h S hS p hp φ ⋙
      SheafOfModules.forget _) :=
    inferInstanceAs (PreservesLimitsOfShape K
      (SheafOfModules.forget _ ⋙ sliceRestrictAlong B E h S hS p hp φ))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.forget _)

end Limits

/-- The restriction of sheaves of modules on `𝒳/y` to the small étale site below `y` is left
exact. -/
instance preservesFiniteLimits_sliceRestrictSheaf :
    PreservesFiniteLimits (sliceRestrictSheaf B E h S hS p hp y) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- The restriction of sheaves of modules on `𝒳/y` to the small étale site below the source of
`φ` is left exact. -/
instance preservesFiniteLimits_sliceRestrictAlongSheaf :
    PreservesFiniteLimits (sliceRestrictAlongSheaf B E h S hS p hp φ) :=
  ⟨fun _ _ _ => inferInstance⟩

end Sheaves

end AlgebraicGeometry.Stack

end
