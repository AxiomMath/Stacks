module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The Picard group of the small étale site of a scheme

Let `S` be a scheme of a big étale site `B`. The associated-module functor `𝓕 ↦ 𝓕^a` from
`𝒪_S`-modules to `𝒪`-modules on the small étale site of `S` induces an isomorphism from the
Picard group of `S` onto the Picard group of the small étale ringed site of `S`.

This is the module-theoretic half of the identification `H¹_étale(S, 𝐆_m) = Pic(S)` of
[Stacks, Tag 03P8]: invertible modules on `S_étale` are quasi-coherent, hence by
[Stacks, Tag 03DX] (2) at `τ = étale` associated modules of quasi-coherent `𝒪_S`-modules, and
the equivalence of Tag 03DX (2) restricts to invertible objects because `𝓕 ↦ 𝓕^a` is monoidal
([Stacks, Tag 03EL] at `ε`).

## Main results

* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isInvertible`: an invertible
  `𝒪`-module on the small étale site of a scheme is quasi-coherent.
* `AlgebraicGeometry.SmallEtale.isInvertible_ringSheaf_associatedModule`: `𝓕 ↦ 𝓕^a` preserves
  invertibility.
* `AlgebraicGeometry.SmallEtale.exists_isInvertible_associatedModule_iso`: every invertible
  module on the small étale site is `𝓕^a` for an invertible `𝒪_S`-module `𝓕`.
* `AlgebraicGeometry.SmallEtale.picardGroupAssociatedModuleAddEquiv`: **`Pic(S)` is the Picard
  group of the small étale ringed site of `S`**, and
  `AlgebraicGeometry.SmallEtale.picardGroupAssociatedModuleEquiv_picardClass` pins it: it sends
  the class of `𝓕` to the class of `𝓕^a`.

## Implementation notes

No `@[stacks]` attribute is carried: this is a step of the proof of Tag 03P8, not a statement of
the source.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0B8Q on the small étale site of a scheme.** An invertible `𝒪`-module on the small
étale site of `S` is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
    (h : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property M) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS) M 1 := by
  have h₁ : HasWeakSheafify (smallEtaleRingedSite B S hS).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u})
  have h₂ : (smallEtaleRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u})
  exact RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible' (smallEtaleRingedSite B S hS) M
    (smallEtaleRingedSite_isLocallyRinged B S hS)

/-- **An invertible `𝒪`-module on the small étale site of a scheme is quasi-coherent.** It is
finite locally free of rank one, hence of finite presentation, hence quasi-coherent. -/
theorem isQuasicoherentOnSite_of_isInvertible
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
    (h : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property M) :
    M.IsQuasicoherentOnSite := by
  have hfree : SheafOfModules.IsFiniteLocallyFreeOnSite M :=
    (isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS M h).isFiniteLocallyFreeOnSite
  have : M.IsFinitePresentationOnSite :=
    _root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hfree
  infer_instance

/-! ### The associated module of an invertible module -/

open Stacks.SheafOfModules

/-- The associated module of the structure sheaf of `S` is the structure sheaf of the small étale
site: the pullback of the unit object is the unit object, the inclusion of the small Zariski site
being final. -/
noncomputable def associatedModuleObjUnitIso :
    (associatedModule B S hS).obj (_root_.SheafOfModules.unit S.ringCatSheaf) ≅
      _root_.SheafOfModules.unit (structureSheaf B S hS) :=
  @asIso _ _ _ _ (_root_.SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS))
    (_root_.SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _)

/-- **The associated module of an invertible `𝒪_S`-module is invertible**: the associated module
of a tensor inverse is a tensor inverse, `𝓕 ↦ 𝓕^a` being monoidal (Stacks 03EL at `ε`). -/
theorem isInvertible_ringSheaf_associatedModule (L : S.Modules)
    (hL : IsInvertible S.presheaf (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L) :
    IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property
      ((associatedModule B S hS).obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit (O := S.presheaf)
    (hO := Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L).mp hL
  refine (isInvertible_iff_exists_tensor_iso_unit _).mpr
    ⟨(associatedModule B S hS).obj N, ⟨?_⟩⟩
  exact (associatedModuleTensorIso B S hS L N).symm ≪≫ (associatedModule B S hS).mapIso e ≪≫
    associatedModuleObjUnitIso B S hS

/-- **`𝓕 ↦ 𝓕^a` on invertible modules.** -/
noncomputable def invertibleAssociatedModule :
    InvertibleModules S.presheaf (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) ⥤
      InvertibleModules (smallEtaleRingedSite B S hS).O.obj
        (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ associatedModule B S hS)
    fun L => isInvertible_ringSheaf_associatedModule B S hS L.obj L.property

/-- An invertible `𝒪_S`-module is quasi-coherent. -/
theorem isQuasicoherent_of_mem_invertibleModules
    (L : InvertibleModules S.presheaf (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace)) :
    L.obj.IsQuasicoherent :=
  Stacks.Picard.isQuasicoherent_of_isInvertible L.obj L.property

/-- `𝓕 ↦ 𝓕^a` is full on invertible modules, being full on quasi-coherent ones. -/
instance full_invertibleAssociatedModule : (invertibleAssociatedModule B S hS).Full where
  map_surjective {L₁ L₂} f := by
    let X₁ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
      ⟨L₁.obj, isQuasicoherent_of_mem_invertibleModules S L₁⟩
    let X₂ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
      ⟨L₂.obj, isQuasicoherent_of_mem_invertibleModules S L₂⟩
    let g : X₁ ⟶ X₂ := (fullyFaithfulAssociatedModuleQcoh' B S hS).preimage (X := X₁) (Y := X₂)
      f.hom
    refine ⟨ObjectProperty.homMk g.hom, ?_⟩
    ext1
    exact (fullyFaithfulAssociatedModuleQcoh' B S hS).map_preimage (X := X₁) (Y := X₂) f.hom

/-- `𝓕 ↦ 𝓕^a` is faithful on invertible modules, being faithful on quasi-coherent ones. -/
instance faithful_invertibleAssociatedModule : (invertibleAssociatedModule B S hS).Faithful where
  map_injective {L₁ L₂} f g h := by
    let X₁ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
      ⟨L₁.obj, isQuasicoherent_of_mem_invertibleModules S L₁⟩
    let X₂ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
      ⟨L₂.obj, isQuasicoherent_of_mem_invertibleModules S L₂⟩
    have h' : (associatedModuleQcoh B S hS).map (X := X₁) (Y := X₂) (ObjectProperty.homMk f.hom) =
        (associatedModuleQcoh B S hS).map (X := X₁) (Y := X₂) (ObjectProperty.homMk g.hom) :=
      congrArg (fun φ => φ.hom) h
    have := (fullyFaithfulAssociatedModuleQcoh' B S hS).map_injective h'
    ext1
    exact congrArg (fun φ => φ.hom) this

/-- **Every invertible module on the small étale site of `S` is the associated module of an
invertible `𝒪_S`-module.** It is quasi-coherent, hence by Stacks 03DX (2) the associated module
of a quasi-coherent `𝒪_S`-module `𝓕`; and the same applies to a tensor inverse, giving a
quasi-coherent `𝓖` with `(𝓕 ⊗ 𝓖)^a ≅ 𝒪 ≅ 𝒪_S^a`, so that `𝓕 ⊗ 𝓖 ≅ 𝒪_S` by full faithfulness of
`𝓕 ↦ 𝓕^a` on quasi-coherent modules. -/
theorem exists_isInvertible_associatedModule_iso
    (N : InvertibleModules (smallEtaleRingedSite B S hS).O.obj
      (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property) :
    ∃ (L : S.Modules) (_ : IsInvertible S.presheaf
      (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L),
      Nonempty ((associatedModule B S hS).obj L ≅ N.obj) := by
  have hq : ∀ M : InvertibleModules (smallEtaleRingedSite B S hS).O.obj
      (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property,
      ∃ X : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
        Nonempty ((associatedModule B S hS).obj X.obj ≅ M.obj) := fun M => by
    obtain ⟨X, ⟨e⟩⟩ := quasicoherentIsEssImageAssociatedModule B S hS M.obj
      (isQuasicoherentOnSite_of_isInvertible B S hS M.obj M.property)
    exact ⟨X, ⟨e⟩⟩
  obtain ⟨X, ⟨e⟩⟩ := hq N
  obtain ⟨Y, ⟨e'⟩⟩ := hq (picardInvObj _ _ N)
  have hXY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S.zariskiRingedSite.toRingedTopos.O).obj X.obj).obj Y.obj).IsQuasicoherent :=
    isQuasicoherent_tensorSheaf_of_isQuasicoherent S X.obj Y.obj X.property Y.property
  let XY : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory := ⟨_, hXY⟩
  let U : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨_root_.SheafOfModules.unit S.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S⟩
  let φ : (associatedModuleQcoh B S hS).obj XY ≅ (associatedModuleQcoh B S hS).obj U :=
    associatedModuleTensorIso B S hS X.obj Y.obj ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((smallEtaleRingedSite B S hS).toRingedTopos.O)).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((smallEtaleRingedSite B S hS).toRingedTopos.O)).obj N.obj).mapIso e' ≪≫
      (ObjectProperty.ι _).mapIso (picardTensorComm _ _ N (picardInvObj _ _ N)) ≪≫
      (ObjectProperty.ι _).mapIso (picardInvTensorIso _ _ N) ≪≫
      (associatedModuleObjUnitIso B S hS).symm
  let ψ : XY ≅ U := (fullyFaithfulAssociatedModuleQcoh' B S hS).preimageIso φ
  refine ⟨X.obj, ?_, ⟨e⟩⟩
  exact (isInvertible_iff_exists_tensor_iso_unit _).mpr
    ⟨Y.obj, ⟨(SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.mapIso ψ⟩⟩

/-- `𝓕 ↦ 𝓕^a` is essentially surjective on invertible modules. -/
instance essSurj_invertibleAssociatedModule : (invertibleAssociatedModule B S hS).EssSurj where
  mem_essImage N := by
    obtain ⟨L, hL, ⟨e⟩⟩ := exists_isInvertible_associatedModule_iso B S hS N
    exact ⟨⟨L, hL⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Sheafification of abelian presheaves on the small étale site, at the spelling
`(smallEtaleRingedSite B S hS).J`, which instance search does not unfold to `topology B S hS`. -/
instance hasWeakSheafify_smallEtaleRingedSite_J :
    HasWeakSheafify (smallEtaleRingedSite B S hS).J AddCommGrpCat.{u} :=
  (inferInstance : HasWeakSheafify (topology B S hS) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences on the small étale site, at the spelling
`(smallEtaleRingedSite B S hS).J`. -/
instance wEqualsLocallyBijective_smallEtaleRingedSite_J :
    (smallEtaleRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  (inferInstance : (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u})

/-- The group structure of the Picard group of the small étale ringed site, at the spelling
`(smallEtaleRingedSite B S hS).O.obj`, where instance search does not find it on its own. -/
noncomputable instance addCommGroupPicardGroupSmallEtaleRingedSite :
    AddCommGroup (PicardGroup (smallEtaleRingedSite B S hS).O.obj
      (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property) :=
  @instAddCommGroupPicardGroup _ _ (smallEtaleRingedSite B S hS).J _ _ inferInstance inferInstance

/-- `𝓕 ↦ 𝓕^a` is a bijection on isomorphism classes of invertible modules. -/
noncomputable def invertibleAssociatedModuleSkeletonEquiv :
    Skeleton (InvertibleModules S.presheaf (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace)) ≃
      Skeleton (InvertibleModules (smallEtaleRingedSite B S hS).O.obj
        (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property) :=
  Equiv.ofBijective (invertibleAssociatedModule B S hS).mapSkeleton.obj
    ⟨Functor.mapSkeleton_injective _, Functor.mapSkeleton_surjective _⟩

/-- The comparison of Picard groups induced by `𝓕 ↦ 𝓕^a`, as a bijection. -/
noncomputable def picardGroupAssociatedModuleEquiv :
    Stacks.Picard.ofScheme S ≃
      PicardGroup (smallEtaleRingedSite B S hS).O.obj
        (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property :=
  ((picardClassEquiv _ _).symm.trans (invertibleAssociatedModuleSkeletonEquiv B S hS)).trans
    (picardClassEquiv _ _)

/-- The comparison sends the class of `𝓕` to the class of `𝓕^a`. -/
theorem picardGroupAssociatedModuleEquiv_picardClass (L : S.Modules)
    (hL : IsInvertible S.presheaf (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L) :
    picardGroupAssociatedModuleEquiv B S hS
        (picardClass S.presheaf (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L hL) =
      picardClass (smallEtaleRingedSite B S hS).O.obj
        (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property
        ((associatedModule B S hS).obj L)
        (isInvertible_ringSheaf_associatedModule B S hS L hL) := by
  show picardClassEquiv _ _ ((invertibleAssociatedModule B S hS).mapSkeleton.obj
    ((picardClassEquiv _ _).symm (picardClassEquiv _ _ (toSkeleton ⟨L, hL⟩)))) = _
  rw [Equiv.symm_apply_apply, Functor.mapSkeleton_obj_toSkeleton]
  rfl

/-- **The Picard group of a scheme is the Picard group of its small étale ringed site**, through
`𝓕 ↦ 𝓕^a`. -/
noncomputable def picardGroupAssociatedModuleAddEquiv :
    Stacks.Picard.ofScheme S ≃+
      PicardGroup (smallEtaleRingedSite B S hS).O.obj
        (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property where
  toEquiv := picardGroupAssociatedModuleEquiv B S hS
  map_add' x y := by
    obtain ⟨L, hL, rfl⟩ := exists_picardClass_eq _ _ x
    obtain ⟨N, hN, rfl⟩ := exists_picardClass_eq _ _ y
    haveI := hL
    haveI := hN
    have hLN := isInvertible_tensorSheaf S.presheaf
      (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L N
    have hLa := isInvertible_ringSheaf_associatedModule B S hS L hL
    have hNa := isInvertible_ringSheaf_associatedModule B S hS N hN
    haveI := hLa
    haveI := hNa
    have hLNa := isInvertible_tensorSheaf (smallEtaleRingedSite B S hS).O.obj
      (Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property
      ((associatedModule B S hS).obj L) ((associatedModule B S hS).obj N)
    change picardGroupAssociatedModuleEquiv B S hS (picardClass _ _ L hL + picardClass _ _ N hN) =
      picardGroupAssociatedModuleEquiv B S hS (picardClass _ _ L hL) +
        picardGroupAssociatedModuleEquiv B S hS (picardClass _ _ N hN)
    rw [picardClass_tensorSheaf _ _ L N hL hN hLN]
    refine (picardGroupAssociatedModuleEquiv_picardClass B S hS _ hLN).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· + ·)
      (picardGroupAssociatedModuleEquiv_picardClass B S hS L hL).symm
      (picardGroupAssociatedModuleEquiv_picardClass B S hS N hN).symm)
    refine Eq.trans ?_ (picardClass_tensorSheaf _ _ _ _ hLa hNa hLNa).symm
    exact (picardClass_eq_iff _ _ _ _ _ _).2 ⟨associatedModuleTensorIso B S hS L N⟩

end AlgebraicGeometry.SmallEtale
