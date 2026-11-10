module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.PullbackOpen
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Injectivity of the pullback-pushforward unit at a point, and the criterion that assembles it

Let `g : X' ⟶ X` be a flat morphism of schemes and let `F` be an `𝒪_X`-module. At a point of
`X` which is the image of a point of `X'`, the stalk of the canonical map
`F ⟶ g_* g^* F` is injective: the stalk map `𝒪_{X, g x'} ⟶ 𝒪_{X', x'}` is a flat local
homomorphism, hence faithfully flat, and the stalk of the map in question is the base change
`F_x ⟶ F_x ⊗_{𝒪_{X, x}} 𝒪_{X', x'}`, which is injective by Stacks tag 05CK.

Separately, this file records the criterion that turns pointwise stalk injectivity at the
weakly associated points of the source into a monomorphism, *without* assuming anything of the
target. This is needed because the target of the map above is a pushforward, which is not
quasi-coherent unless the morphism is quasi-compact and quasi-separated.

## Main results

* `AlgebraicGeometry.stalk_pullbackPushforwardUnit_injective_of_flat`: injectivity of the
  stalk of `F ⟶ g_* g^* F` at a point in the image of a flat `g`.
* `AlgebraicGeometry.mono_of_stalk_injective_on_weaklyAssociatedPoints_of_source_quasicoherent`:
  a map out of a quasi-coherent module whose stalk maps are injective at every weakly
  associated point of the source is a monomorphism. The target is arbitrary.

## Implementation notes

The criterion of `AlgebraicGeometry.mono_of_stalk_injective_on_weaklyAssociatedPoints` asks for
the target to be quasi-coherent as well, because it argues with the kernel. Here the target is
`g_* g^* F`, for which quasi-coherence is unavailable, so the argument is run instead on the
*image* of a map `𝒪_X ⟶ F` presenting a section over an affine open: that image is a
quasi-coherent submodule of `F`, it has no weakly associated point by Stacks tag 05AN, hence
vanishes by Stacks tag 05AP, and so the section is zero. Monomorphy is then injectivity on
sections over every open, checked on an affine basis.

The faithful flatness of the stalk map is `Module.FaithfullyFlat.of_flat_of_isLocalHom`, and
the identification of the stalk of a pullback with a base change is
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`.

## References

* [Stacks Project, Tag 05CK](https://stacks.math.columbia.edu/tag/05CK)
* [Stacks Project, Tag 05AN](https://stacks.math.columbia.edu/tag/05AN)
* [Stacks Project, Tag 05AP](https://stacks.math.columbia.edu/tag/05AP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For a flat morphism `g : X' ⟶ X` and an `𝒪_X`-module `F`, the stalk at `g x'` of the
canonical map `F ⟶ g_* g^* F` is injective.

The stalk map `𝒪_{X, g x'} ⟶ 𝒪_{X', x'}` is a flat local homomorphism of local rings, hence
faithfully flat, and the composite of the stalk of the unit with the comparison of the stalk of
a pushforward is the base change `F_{g x'} ⟶ F_{g x'} ⊗_{𝒪_{X, g x'}} 𝒪_{X', x'}`, injective by
Stacks tag 05CK. -/
theorem stalk_pullbackPushforwardUnit_injective_of_flat
    {X' X : Scheme.{u}} (g : X' ⟶ X) [Flat g] (F : X.Modules) (x' : X') :
    Function.Injective
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (g x')).map
        ((Scheme.Modules.toPresheaf X).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F))).hom) := by
  let P := (Scheme.Modules.pullback g).obj F
  let fbase := (g.toLRSHom.toShHom).hom.base
  let b := fbase x'
  let R := X.presheaf.stalk b
  let S := X'.presheaf.stalk x'
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf b
  let φ := ((g.toLRSHom.toShHom).hom.stalkMap x').hom
  let : Algebra R S := φ.toAlgebra
  let : Module R M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val b
  have hff : φ.FaithfullyFlat := by
    have : Module.Flat R S := Flat.stalkMap g x'
    have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (g.stalkMap x').hom)
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  let eData := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    g.toLRSHom.toShHom F x'
  let e := eData.choose
  let unitStalk := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} b).map
    ((Scheme.Modules.toPresheaf X).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F))
  let pushStalk := TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
    fbase P.val.presheaf x'
  let k := unitStalk ≫ pushStalk
  let eMap : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.val.presheaf x' ⟶
      AddCommGrpCat.of (TensorProduct R S M) := AddCommGrpCat.ofHom e.toAddMonoidHom
  let tensorMap : M ⟶ AddCommGrpCat.of (TensorProduct R S M) :=
    AddCommGrpCat.ofHom (TensorProduct.mk R S M (1 : S)).toAddMonoidHom
  have hpush : ((Scheme.Modules.pushforward g).obj P).presheaf =
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} fbase).obj P.presheaf := rfl
  cases hpush
  have hcomp : k ≫ eMap = tensorMap := by
    refine TopCat.Presheaf.stalk_hom_ext
      ((Scheme.Modules.toPresheaf X).obj ((𝟭 X.Modules).obj F)) fun U hxU => ?_
    ext s
    simp only [k, unitStalk]
    have hunit := TopCat.Presheaf.stalkFunctor_map_germ_apply
      (C := AddCommGrpCat.{u}) U b hxU
      ((Scheme.Modules.toPresheaf X).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)) s
    have hpush := congrArg (fun k => k.hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app U) s))
      (TopCat.Presheaf.stalkPushforward_germ (C := AddCommGrpCat.{u}) fbase P.presheaf U x' hxU)
    exact (congrArg (fun z => eMap.hom (pushStalk.hom z)) hunit).trans
      ((congrArg eMap.hom hpush).trans (eData.choose_spec U hxU s))
  refine Function.Injective.of_comp (f := fun z => eMap.hom (pushStalk.hom z)) ?_
  change Function.Injective (k ≫ eMap).hom
  rw [hcomp]
  exact faithfullyFlat_tensor_mk_injective φ hff M

/-- **Stacks Project, Tags 05AN and 05AP.** On an affine scheme, a map `q : F ⟶ G` out of a
quasi-coherent module whose stalk maps are injective at every weakly associated point of `F`
kills no nonzero global section of `F`.

Nothing is assumed of `G`. The section is presented as a map `i : 𝒪_X ⟶ F`; its image is a
quasi-coherent submodule of `F` on which `q` vanishes, so by Stacks tag 05AN it has no weakly
associated point, hence vanishes by Stacks tag 05AP. -/
theorem image_eq_zero_of_stalk_injective_on_weaklyAssociatedPoints
    {X : Scheme.{u}} [IsAffine X] {A F G : X.Modules}
    [A.IsQuasicoherent] [F.IsQuasicoherent]
    (i : A ⟶ F) (q : F ⟶ G)
    (hiq : i ≫ q = 0)
    (hinj : ∀ x : X, x ∈ Stacks.Divisors.weaklyAssociatedPoints F →
      Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((Scheme.Modules.toPresheaf X).map q)).hom) :
    i = 0 := by
  classical
  let I := Abelian.image i
  let ι : I ⟶ F := Abelian.image.ι i
  have : I.IsQuasicoherent := inferInstance
  let T := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hT : T.ShortExact := {
    exact := ShortComplex.exact_cokernel ι
    mono_f := inferInstance
    epi_g := inferInstance }
  have hsub : Stacks.Divisors.weaklyAssociatedPoints I ⊆
      Stacks.Divisors.weaklyAssociatedPoints F :=
    AlgebraicGeometry.weaklyAssociatedPoints_subset_of_shortExact T hT
  have hιq : ι ≫ q = 0 := by
    apply (cancel_epi (Abelian.factorThruImage i)).1
    rw [← Category.assoc, Abelian.image.fac i, hiq]
    simp
  have hempty : Stacks.Divisors.weaklyAssociatedPoints I = ∅ := by
    ext x
    refine ⟨fun hx => ?_, by simp⟩
    have hqinj := hinj x (hsub hx)
    let St := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let Q := Scheme.Modules.toPresheaf X
    let tι := St.map (Q.map ι)
    have hmonoTι : Mono ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map ι.val) :=
      @OXModule.mono_val_of_mono _ I F ι (inferInstanceAs (Mono (Abelian.image.ι i)))
    have hinjι : Function.Injective tι.hom := OXModule.inj_of_mono_val I F ι hmonoTι x
    have hz : St.map (Q.map ι) ≫ St.map (Q.map q) = 0 := by
      rw [← St.map_comp, ← Q.map_comp, hιq]
      simp
    have hzeroι (a : St.obj I.val.presheaf) : tι.hom a = 0 := by
      apply hqinj
      rw [map_zero]
      exact congrArg (fun k => k.hom a) hz
    have hsubsingleton : Subsingleton (St.obj I.val.presheaf) :=
      ⟨fun a b => hinjι (by rw [hzeroι a, hzeroι b])⟩
    exact not_nontrivial_iff_subsingleton.mpr hsubsingleton
      (Stacks.Divisors.IsWeaklyAssociatedPoint.nontrivial hx)
  have hιzero : ι = 0 :=
    ((AlgebraicGeometry.isZero_iff_weaklyAssociatedPoints_eq_empty I).2 hempty).eq_of_src _ _
  calc
    i = Abelian.factorThruImage i ≫ ι := (Abelian.image.fac i).symm
    _ = 0 := by rw [hιzero, comp_zero]

/-- A map of `𝒪_X`-modules commutes with restriction of sections to a smaller open. -/
private theorem app_map_restrict {X : Scheme.{u}} {F G : X.Modules} (q : F ⟶ G) {U V : X.Opens}
    (h : U ≤ V) (s : F.presheaf.obj (Opposite.op V)) :
    (q.app U).hom (F.presheaf.map (homOfLE h).op s) =
      G.presheaf.map (homOfLE h).op ((q.app V).hom s) :=
  ConcreteCategory.congr_hom (q.mapPresheaf.naturality (homOfLE h).op) s

/-- On an affine scheme, a map `q : F ⟶ G` out of a quasi-coherent module whose stalk maps are
injective at every weakly associated point of `F` is injective on global sections. Nothing is
assumed of `G`. -/
theorem appTop_injective_of_stalk_injective_on_weaklyAssociatedPoints
    {X : Scheme.{u}} [IsAffine X] {F G : X.Modules} [F.IsQuasicoherent]
    (q : F ⟶ G)
    (hinj : ∀ x : X, x ∈ Stacks.Divisors.weaklyAssociatedPoints F →
      Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((Scheme.Modules.toPresheaf X).map q)).hom) :
    Function.Injective (q.app ⊤).hom := by
  refine (injective_iff_map_eq_zero (q.app ⊤).hom).mpr fun s hs => ?_
  let t : F.sections := F.val.sectionsMk
    (fun U ↦ F.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (fun U V k ↦ by
      refine Eq.trans (PresheafOfModules.map_comp_apply F.val
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op k s).symm ?_
      congr 1)
  let i : structureSheafModule X ⟶ F := F.unitHomEquiv.symm t
  have hit : F.unitHomEquiv i = t := F.unitHomEquiv.apply_symm_apply t
  have hiq : i ≫ q = 0 := by
    apply G.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    change q.val.app U ((F.unitHomEquiv i).val U) = 0
    rw [hit]
    exact (app_map_restrict q le_top s).trans (by rw [hs]; exact map_zero _)
  have he := congrArg (fun a ↦ (F.unitHomEquiv a).val (Opposite.op ⊤))
    (image_eq_zero_of_stalk_injective_on_weaklyAssociatedPoints i q hiq hinj)
  change (F.unitHomEquiv i).val (Opposite.op ⊤) = 0 at he
  rw [hit] at he
  change F.presheaf.map (𝟙 (Opposite.op ⊤)) s = 0 at he
  simpa using he

/-- Injectivity of a stalk map is inherited by the restriction of a map of modules to an open
subscheme. -/
theorem stalk_injective_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {F G : Y.Modules} (q : F ⟶ G) (x : X)
    (hq : Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j x)).map
      ((Scheme.Modules.toPresheaf Y).map q)).hom) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map ((Scheme.Modules.restrictFunctor j).map q))).hom := by
  let e := Scheme.Modules.restrictStalkNatIso j x
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app F)).1
  apply hq
  have hn' (a) := ConcreteCategory.congr_hom (e.hom.naturality q) a
  exact (hn' a).symm.trans ((congrArg (e.hom.app G).hom hab).trans (hn' b))

/-- **Stacks Project, Tags 05AN and 05AP.** A map `q : F ⟶ G` out of a quasi-coherent module on
a scheme is a monomorphism as soon as its stalk maps are injective at every weakly associated
point of `F`. Nothing is assumed of `G`.

This is `AlgebraicGeometry.mono_of_stalk_injective_on_weaklyAssociatedPoints` with the
quasi-coherence hypothesis on the target removed; the argument runs on the image of a section
rather than on the kernel of `q`. -/
theorem mono_of_stalk_injective_on_weaklyAssociatedPoints_of_source_quasicoherent
    {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent]
    (q : F ⟶ G)
    (hinj : ∀ x : X, x ∈ Stacks.Divisors.weaklyAssociatedPoints F →
      Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((Scheme.Modules.toPresheaf X).map q)).hom) :
    Mono q := by
  have happ (U : X.Opens) : Function.Injective (q.app U).hom := by
    apply (injective_iff_map_eq_zero (q.app U).hom).mpr
    intro s hs
    apply TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U s 0
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    let j := Scheme.Opens.ι (X := X) V
    let qV := (Scheme.Modules.restrictFunctor j).map q
    have : IsAffine (Scheme.Opens.toScheme (X := X) V) := hV
    have hinjV : Function.Injective (qV.app ⊤).hom :=
      appTop_injective_of_stalk_injective_on_weaklyAssociatedPoints qV (fun y hy ↦
        stalk_injective_restrict j q y (hinj (j y)
          ((isWeaklyAssociatedPoint_restrict_iff j F y).mp hy)))
    have hImage : j ''ᵁ (⊤ : (Scheme.Opens.toScheme (X := X) V).Opens) = V := by simp [j]
    have hqV : Function.Injective (q.app (j ''ᵁ ⊤)).hom := hinjV
    rw [hImage] at hqV
    have hzero : F.presheaf.map (homOfLE hVU).op s = 0 := by
      apply hqV
      rw [app_map_restrict q hVU s, hs, map_zero, map_zero]
    rw [← F.presheaf.germ_res_apply (homOfLE hVU) x hxV s, hzero, map_zero, map_zero]
  exact (Scheme.Modules.toPresheaf X).mono_of_mono_map
    ((NatTrans.mono_iff_mono_app _).mpr fun U ↦ ConcreteCategory.mono_of_injective _ (happ U.unop))

end AlgebraicGeometry

end
