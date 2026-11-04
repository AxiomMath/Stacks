module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleCoproducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ProetaleTestingFamily
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SmallSiteSheafificationSections
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective

/-!
# Inverse image along a closed immersion at a w-contractible object

Let `i : Z ⟶ X` be a closed immersion of affine schemes, `u : X_app ⥤ Z_app`, `U ↦ U ×_X Z`,
base change on the sites of affine ind-étale objects (Stacks 098X) and `v` its fully faithful
left adjoint (Stacks 09BK). For a sheaf `𝓕` of `Λ`-modules on the small pro-étale site of `X`
and an object `V` of `Z_app` whose ring of global sections is w-contractible, the sections of
the inverse image `i⁻¹𝓕` over `V` are the sections of `𝓕` over `v(V)`, naturally in `𝓕`
(Stacks 09BL (2)).

The inverse image is first read on the sites of affine ind-étale objects, through the
restriction equivalences of Stacks 098X: there it is the sheafification of the presheaf
`V ↦ 𝓕(v(V))`, as both are left adjoint to restriction along `u`. That presheaf takes finite
disjoint unions to products, `v` preserving coproducts and `𝓕` being a sheaf. At an object `V`
with w-contractible ring of global sections sheafification does not change the sections of such
a presheaf: every covering sieve of `V` contains a finite jointly surjective family, whose total
map from the disjoint union then has a section.

Since limits of sheaves are computed on sections, and objects with w-contractible ring of global
sections cover `Z_app`, the inverse image along `i` preserves all limits.

## Main results

* `AlgebraicGeometry.ProEtale.AppProetale.bijective_app_of_isWContractible`: a locally
  bijective morphism into a sheaf, out of a presheaf taking finite coproducts to products, is
  bijective at an object with w-contractible ring of global sections.
* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImageSectionsIso`: Stacks 09BL (2) for
  sheaves of modules.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace AlgebraicGeometry.ProEtale

namespace AppProetale

variable {S : Scheme.{u}} [IsAffine S]

/-- A covering sieve of an object of `S_app` with w-contractible ring of global sections
contains a finite family which is jointly surjective on underlying schemes. -/
theorem exists_finite_jointlySurjective_of_mem {W : AppProetale S}
    (hW : ProetaleWContractible.IsWContractible.{u, u} Γ(W.obj.left, ⊤)) {R : Sieve W}
    (hR : R ∈ (inclusion S).inducedTopology (Scheme.ProEt.topology S) W) :
    ∃ (n : ℕ) (T : ULift.{u} (Fin n) → AppProetale S) (f : ∀ k, T k ⟶ W),
      (∀ k, R (f k)) ∧ ∀ x : W.obj.left, ∃ k y, (f k).hom.left y = x := by
  have := appInclusion_isDenseSubsite S (hasAppCover S)
  have hR' := ((inclusion S).functorPushforward_mem_iff _ (Scheme.ProEt.topology S)).mpr hR
  have : IsAffine W.obj.left := W.property.1
  obtain ⟨n, U, f, hdec, hf, hR''⟩ :=
    Scheme.ProEt.exists_clopenDecomposition_of_isWContractible W.obj hW _ hR'
  choose T g h hg hfac using hR''
  refine ⟨n, fun k ↦ T k.down, fun k ↦ g k.down, fun k ↦ hg k.down, fun x ↦ ?_⟩
  have hx : x ∈ ⋃ i, Set.range (f i).base := by
    rw [hdec.cover]
    trivial
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
  refine ⟨⟨i⟩, (h i).left y, ?_⟩
  exact (congrArg (fun q ↦ q.left y) (hfac i)).symm

/-- Restricting along `f` and then along `g` is restricting along `f ≫ g`. -/
private theorem map_op_map_op_eq {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type t} {X Y Z : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h) (z : F.obj (op Z)) :
    F.map f.op (F.map g.op z) = F.map h.op z := by
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, hfg]

variable (t) in
/-- **Sections at a w-contractible object are not changed by a locally bijective map into a
sheaf.** Let `φ : P ⟶ Q` be a locally injective and locally surjective morphism of presheaves of
sets on `S_app`, with `Q` a sheaf and `P` taking finite coproducts to products. Then `φ` is
bijective on sections over every object whose ring of global sections is w-contractible. -/
theorem bijective_app_of_isWContractible {P Q : (AppProetale S)ᵒᵖ ⥤ Type t} (φ : P ⟶ Q)
    [Presheaf.IsLocallyInjective ((inclusion S).inducedTopology (Scheme.ProEt.topology S)) φ]
    [Presheaf.IsLocallySurjective ((inclusion S).inducedTopology (Scheme.ProEt.topology S)) φ]
    (hQ : Presieve.IsSheaf ((inclusion S).inducedTopology (Scheme.ProEt.topology S)) Q)
    (hP : ∀ {ι : Type u} [Finite ι] {T : ι → AppProetale S} {V : AppProetale S}
      {g : ∀ k, T k ⟶ V}, IsColimit (Cofan.mk V g) →
      Function.Bijective (fun x : P.obj (op V) ↦ fun k ↦ P.map (g k).op x))
    {W : AppProetale S} (hW : ProetaleWContractible.IsWContractible.{u, u} Γ(W.obj.left, ⊤)) :
    Function.Bijective (φ.app (op W)) := by
  let J := (inclusion S).inducedTopology (Scheme.ProEt.topology S)
  constructor
  · intro x y hxy
    obtain ⟨n, T, f, hfE, hsurj⟩ := exists_finite_jointlySurjective_of_mem hW
      (Presheaf.equalizerSieve_mem J φ x y hxy)
    obtain ⟨σ, hσ⟩ := exists_comp_sigmaDesc_eq_id hW f hsurj
    have heq : P.map (sigmaDesc T f).op x = P.map (sigmaDesc T f).op y := by
      apply (hP (isColimitSigmaCofan T)).injective
      funext k
      simp only [map_op_map_op_eq (sigmaι_sigmaDesc T f k)]
      exact hfE k
    simpa only [map_op_map_op_eq hσ, op_id, FunctorToTypes.map_id_apply] using
      congrArg (P.map σ.op) heq
  · intro s
    obtain ⟨n, T, f, hfI, hsurj⟩ := exists_finite_jointlySurjective_of_mem hW
      (Presheaf.imageSieve_mem J φ (U := op W) s)
    obtain ⟨σ, hσ⟩ := exists_comp_sigmaDesc_eq_id hW f hsurj
    choose y hy using hfI
    obtain ⟨r, hr⟩ := (hP (isColimitSigmaCofan T)).surjective y
    have hr' (k : _) : P.map (sigmaι T k).op r = y k := congrFun hr k
    have heq : φ.app (op (sigmaObj T)) r = Q.map (sigmaDesc T f).op s := by
      apply (bijective_map_cofan_inj_of_isSheaf Q hQ (isColimitSigmaCofan T)).injective
      funext k
      show Q.map (sigmaι T k).op (φ.app _ r) = Q.map (sigmaι T k).op (Q.map _ s)
      rw [← φ.naturality_apply (sigmaι T k).op r, hr' k, hy k,
        map_op_map_op_eq (sigmaι_sigmaDesc T f k)]
    exact ⟨P.map σ.op r, by
      rw [φ.naturality_apply σ.op r, heq, map_op_map_op_eq hσ, op_id,
        FunctorToTypes.map_id_apply]⟩

/-- **Objects with w-contractible ring of global sections cover `S_app`.** Every object `A` of
`S_app` is covered by a single object `V` whose ring of global sections is w-contractible: the
spectrum of a faithfully flat ind-étale w-contractible `Γ(A, ⊤)`-algebra (Stacks 0983), which
is ind-étale over `Γ(S, ⊤)` as a composite of ind-étale maps. -/
theorem exists_isWContractible_cover (A : AppProetale S) :
    ∃ (V : AppProetale S) (p : V ⟶ A),
      ProetaleWContractible.IsWContractible.{u, u} Γ(V.obj.left, ⊤) ∧
        Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ V) (fun _ ↦ p) ∈
          (inclusion S).inducedTopology (Scheme.ProEt.topology S) A := by
  classical
  obtain ⟨D, _, f, hff, hind, hwd⟩ := exists_faithfullyFlat_ind_etale_wContractible Γ(A.obj.left, ⊤)
  let r : Γ(A.obj.left, ⊤) ⟶ CommRingCat.of D := CommRingCat.ofHom f
  have hr : MorphismProperty.ind.{u} CommRingCat.etale.{u} r :=
    (MorphismProperty.ind_iff_ind_underMk r).mpr hind
  have hA : MorphismProperty.ind.{u} CommRingCat.etale.{u} A.obj.hom.appTop :=
    (MorphismProperty.ind_iff_ind_underMk _).mpr A.property.2
  let B : IndEtaleAlgebra ↥Γ(S, ⊤) := ⟨Under.mk (A.obj.hom.appTop ≫ r),
    (MorphismProperty.ind_iff_ind_underMk _).mp (CommRingCat.ind_etale_comp _ _ hA hr)⟩
  let V := appOfIndEtaleAlgebra S B
  let g : (appGamma S).obj (op A) ⟶ (appGamma S).obj (op V) :=
    ObjectProperty.homMk (Under.homMk (U := ((appGamma S).obj (op A)).obj) (V := B.obj) r rfl) ≫
      (appGammaObjIso S B).inv
  let p : V ⟶ A := (appGammaPreimage S g).unop
  have : IsAffine A.obj.left := A.property.1
  have : IsAffine V.obj.left := V.property.1
  have hp : p.hom.left.appTop = g.hom.right :=
    Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply _
  have hbij : Function.Bijective (appGammaObjIso S B).inv.hom.right.hom :=
    ConcreteCategory.bijective_of_isIso
      ((ObjectProperty.ι _ ⋙ Under.forget _).mapIso (appGammaObjIso S B)).inv
  have hffp : p.hom.left.appTop.hom.FaithfullyFlat := by
    rw [hp]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hff
      (RingHom.FaithfullyFlat.of_bijective hbij)
  have hsurj : Surjective p.hom.left :=
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine p.hom.left).mpr hffp).2
  refine ⟨V, p, ProetaleWContractible.isWContractible_of_isWeaklyContractible
    (Spec (CommRingCat.of D)) (((ProetaleWContractible.main_theorem D).out 1 2).mp hwd), ?_⟩
  have := appInclusion_isDenseSubsite S (hasAppCover S)
  refine ((inclusion S).functorPushforward_mem_iff _ (Scheme.ProEt.topology S)).mp ?_
  rw [Sieve.functorPushforward_ofArrows]
  refine Scheme.ProEt.ofArrows_mem_topology_of_isAffine (fun _ : PUnit.{u + 1} ↦ V.obj)
    (fun _ ↦ p.hom) 1 (fun _ ↦ PUnit.unit) (fun _ ↦ ⊤) (fun _ ↦ by
      simpa using isCompact_univ) ?_
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨0, ?_⟩
  obtain ⟨y, hy⟩ := hsurj.surj x
  exact ⟨y, trivial, hy⟩

/-- `S_app` has enough objects with w-contractible ring of global sections. -/
theorem hasEnoughObjects_isWContractible :
    ((inclusion S).inducedTopology (Scheme.ProEt.topology S)).HasEnoughObjects
      (fun V : AppProetale S ↦ ProetaleWContractible.IsWContractible.{u, u} Γ(V.obj.left, ⊤)) :=
  fun A ↦ by
    obtain ⟨V, p, hV, hp⟩ := exists_isWContractible_cover A
    exact ⟨PUnit, fun _ ↦ V, fun _ ↦ p, hp, fun _ ↦ hV⟩

end AppProetale

section Limits

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {B : ObjectProperty C}

/-- **Limits of sheaves are detected on enough objects.** On a site with enough objects
satisfying `B`, a cone of sheaves of a concrete category is a limit cone as soon as its sections
over every object satisfying `B` form a limit cone. -/
theorem isLimit_of_isLimit_mapCone_sheafSections {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [(forget A).ReflectsIsomorphisms] [J.HasSheafCompose (forget A)]
    (hB : J.HasEnoughObjects B) {K : Type*}
    [Category* K] [HasLimitsOfShape K A] {F : K ⥤ Sheaf J A} (c : Cone F)
    (hc : ∀ U : C, B U → Nonempty (IsLimit (((sheafSections J A).obj (op U)).mapCone c))) :
    Nonempty (IsLimit c) := by
  let L := limit.isLimit F
  let φ : c.pt ⟶ limit F := L.lift c
  have hφ (U : C) (hU : B U) : IsIso (φ.hom.app (op U)) := by
    have hL : IsLimit (((sheafSections J A).obj (op U)).mapCone (limit.cone F)) :=
      isLimitOfPreserves (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op U)) L
    let m := ((sheafSections J A).obj (op U)).mapConeMorphism (L.liftConeMorphism c)
    have := IsLimit.hom_isIso (hc U hU).some hL m
    exact Functor.map_isIso (Cones.forget _) m
  have hbij (U : C) (hU : B U) :
      Function.Bijective (ConcreteCategory.hom (φ.hom.app (op U))) := by
    have := hφ U hU
    exact ConcreteCategory.bijective_of_isIso _
  have : Sheaf.IsLocallyInjective φ :=
    Presheaf.isLocallyInjective_of_hasEnoughObjects_injective J φ.hom hB
      fun U hU ↦ (hbij U hU).injective
  have : Sheaf.IsLocallySurjective φ :=
    Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective J φ.hom hB
      fun U hU ↦ (hbij U hU).surjective
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨inferInstance, inferInstance⟩
  exact ⟨IsLimit.ofPointIso L⟩

end Limits

/-! ### The inverse image along a closed immersion of affine schemes -/

section ClosedImmersion

variable {Z X : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X) [IsClosedImmersion i]
  (Λ : Type v) [CommRing Λ]

/-- The inverse image along a closed immersion of affine schemes on the sites of affine
ind-étale objects: the sheafification of the presheaf `V ↦ 𝓕(v(V))`, for `v` the lift of
Stacks 09BK. -/
def appInverseImage :
    Sheaf ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
        (ModuleCat.{max (u + 1) v w} Λ) ⥤
      Sheaf ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
        (ModuleCat.{max (u + 1) v w} Λ) :=
  sheafToPresheaf ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)) _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (appLift i).op ⋙
    presheafToSheaf ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
      (ModuleCat.{max (u + 1) v w} Λ)

/-- Base change along `i` is continuous for the induced topologies on the sites of affine
ind-étale objects of `X` and `Z`. -/
instance : (appBaseChange i).IsContinuous
    ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
    ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) :=
  appBaseChange_isContinuous i _ _ (appInclusion_isDenseSubsite X (hasAppCover X))
    (appInclusion_isDenseSubsite Z (hasAppCover Z))

/-- The inverse image on the sites of affine ind-étale objects is left adjoint to restriction
along base change. -/
def appInverseImageAdjunction :
    appInverseImage.{w} i Λ ⊣
      (appBaseChange i).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v w} Λ)
        ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
        ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) :=
  Adjunction.restrictFullyFaithful
    (((appLiftAdjunction i).op.whiskerLeft (ModuleCat.{max (u + 1) v w} Λ)).comp
      (sheafificationAdjunction
        ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
        (ModuleCat.{max (u + 1) v w} Λ)))
    (fullyFaithfulSheafToPresheaf
      ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)) _)
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

attribute [local instance] ModuleCat.hasLimitsOfSize in
/-- **The inverse image along a closed immersion of affine schemes, read on the sites of affine
ind-étale objects.** Restricting the inverse image of a sheaf on the small pro-étale site to
`Z_app` is the inverse image of `AlgebraicGeometry.ProEtale.appInverseImage` applied to the
restriction of the sheaf to `X_app`: both are left adjoint to the same functor, since
restriction to `Z_app` followed by restriction along base change is restriction along base
change followed by restriction to `X_app`. -/
def proetaleModuleInverseImageCompRestrictionIso :
    proetaleModuleInverseImage.{u, v, w} i Λ ⋙
        (AppProetale.inclusion Z).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v w} Λ)
          ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
          (Scheme.ProEt.topology Z) ≅
      (AppProetale.inclusion X).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v w} Λ)
          ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
          (Scheme.ProEt.topology X) ⋙ appInverseImage.{w} i Λ := by
  have := appInclusion_isDenseSubsite X (hasAppCover X)
  have := appInclusion_isDenseSubsite Z (hasAppCover Z)
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{max (u + 1) v w} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, max (u + 1) v w, v}
  let A := ModuleCat.{max (u + 1) v w} Λ
  let RX := (AppProetale.inclusion X).sheafPushforwardContinuous A
    ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
  let RZ := (AppProetale.inclusion Z).sheafPushforwardContinuous A
    ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) (Scheme.ProEt.topology Z)
  let eX := RX.asEquivalence
  let eZ := RZ.asEquivalence
  let SG := (Scheme.proetaleBaseChange i).sheafPushforwardContinuous A
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
  let Su := (appBaseChange i).sheafPushforwardContinuous A
    ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
    ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
  have : (AppProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).IsContinuous
      ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
      (Scheme.ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
  let PFG := (AppProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).sheafPushforwardContinuous
    A ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
    (Scheme.ProEt.topology Z)
  have c1 : SG ⋙ RX ≅ PFG :=
    Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _) (A := A)
      (J := ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)))
      (K := Scheme.ProEt.topology X) (L := Scheme.ProEt.topology Z)
  have c2 : RZ ⋙ Su ≅ PFG :=
    Functor.sheafPushforwardContinuousComp' (eFG := eqToIso (appBaseChange_comp_inclusion i))
      (A := A) (J := ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)))
      (K := ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)))
      (L := Scheme.ProEt.topology Z)
  -- the right adjoint of the left side is `eZ.inverse ⋙ SG`, that of the right side
  -- `Su ⋙ eX.inverse`
  have key : eZ.inverse ⋙ SG ≅ Su ⋙ eX.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ eX.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _) ≪≫
        Functor.isoWhiskerLeft _ (c1 ≪≫ c2.symm) ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eZ.counitIso _ ≪≫ Functor.leftUnitor _) eX.inverse
  exact ((proetaleModuleInverseImageAdjunction.{u, v, w} Λ i).comp eZ.toAdjunction).leftAdjointUniq
    ((eX.toAdjunction.comp (appInverseImageAdjunction.{w} i Λ)).ofNatIsoRight key.symm)

/-- **Stacks 09BL (2) on the sites of affine ind-étale objects.** At an object `W` of `Z_app`
with w-contractible ring of global sections, the sections of `appInverseImage i Λ 𝓖` over `W`
are the sections of `𝓖` over the lift `v(W)`, naturally in `𝓖`: sheafification does not change
the sections over `W` of the presheaf `V ↦ 𝓖(v(V))`, which takes finite coproducts to products
since `v` preserves them and `𝓖` is a sheaf. -/
def appInverseImageSectionsIso (W : AppProetale Z)
    (hW : ProetaleWContractible.IsWContractible.{u, u} Γ(W.obj.left, ⊤)) :
    (sheafSections ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
        (ModuleCat.{max (u + 1) v w} Λ)).obj (op ((appLift i).obj W)) ≅
      appInverseImage.{w} i Λ ⋙
        (sheafSections ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
          (ModuleCat.{max (u + 1) v w} Λ)).obj (op W) := by
  let A := ModuleCat.{max (u + 1) v w} Λ
  let τ : (sheafSections ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
        A).obj (op ((appLift i).obj W)) ⟶
      appInverseImage.{w} i Λ ⋙
        (sheafSections ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
          A).obj (op W) :=
    { app G := (toSheafify ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
        ((appLift i).op ⋙ G.obj)).app (op W)
      naturality G G' f := congrArg (fun η ↦ η.app (op W))
        (toSheafify_naturality ((AppProetale.inclusion Z).inducedTopology
          (Scheme.ProEt.topology Z)) (Functor.whiskerLeft (appLift i).op f.hom)) }
  have : ∀ G, IsIso (τ.app G) := fun G ↦ by
    let P := (appLift i).op ⋙ G.obj
    have hinj := Stacks.ConstantSheaf.isLocallyInjective_toSheafify_moduleCat.{u, u + 1, max v w, v}
      ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) Λ P
    have hsurj :=
      Stacks.ConstantSheaf.isLocallySurjective_toSheafify_moduleCat.{u, u + 1, max v w, v}
        ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) Λ P
    have : Presheaf.IsLocallyInjective
        ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
        (Functor.whiskerRight (toSheafify
          ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) P) (forget A)) :=
      (Presheaf.isLocallyInjective_forget_iff _ _).mpr hinj
    have : Presheaf.IsLocallySurjective
        ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
        (Functor.whiskerRight (toSheafify
          ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) P) (forget A)) :=
      (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mp hsurj
    have hQ : Presieve.IsSheaf
        ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
        (sheafify ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) P ⋙
          forget A) :=
      (isSheaf_iff_isSheaf_of_type _ _).mp
        ((sheafCompose ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
          (forget A)).obj ((presheafToSheaf
            ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) A).obj
              P)).property
    have hG : Presieve.IsSheaf
        ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)) (G.obj ⋙ forget A) :=
      (isSheaf_iff_isSheaf_of_type _ _).mp ((sheafCompose
        ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)) (forget A)).obj
          G).property
    have := (appLiftAdjunction i).leftAdjoint_preservesColimits
    have hb := AppProetale.bijective_app_of_isWContractible.{max (u + 1) v w}
      (Functor.whiskerRight (toSheafify
        ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) P) (forget A)) hQ
      (fun {ι} _ {T} {V} {g} hc ↦ AppProetale.bijective_map_cofan_inj_of_isSheaf (G.obj ⋙ forget A)
        hG ((isColimitMapCoconeCofanMkEquiv (appLift i) T g) (isColimitOfPreserves _ hc))) hW
    have : IsIso ((forget A).map (τ.app G)) := (isIso_iff_bijective _).mpr hb
    exact isIso_of_reflects_iso (τ.app G) (forget A)
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- The inverse image along a closed immersion of affine schemes, on the sites of affine
ind-étale objects, preserves limits: limits of sheaves are computed on sections, and on sections
over an object with w-contractible ring of global sections the inverse image is evaluation at
the lift (`AlgebraicGeometry.ProEtale.appInverseImageSectionsIso`). -/
theorem preservesLimitsOfShape_appInverseImage (K : Type*) [Category* K]
    [HasLimitsOfShape K (ModuleCat.{max (u + 1) v w} Λ)] :
    PreservesLimitsOfShape K (appInverseImage.{w} i Λ) := by
  let A := ModuleCat.{max (u + 1) v w} Λ
  constructor
  intro F
  refine preservesLimit_of_preserves_limit_cone (limit.isLimit F) ?_
  refine (isLimit_of_isLimit_mapCone_sheafSections
    (AppProetale.hasEnoughObjects_isWContractible (S := Z)) _ fun W hW ↦ ?_).some
  have h1 : IsLimit (((sheafSections
      ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)) A).obj
        (op ((appLift i).obj W))).mapCone (limit.cone F)) :=
    isLimitOfPreserves (sheafToPresheaf
      ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)) A ⋙
        (evaluation _ A).obj (op ((appLift i).obj W)))
      (limit.isLimit F)
  exact ⟨IsLimit.mapConeEquiv (appInverseImageSectionsIso.{w} i Λ W hW) h1⟩

/-- **The inverse image along a closed immersion of affine schemes preserves limits** of
pro-étale sheaves of modules: on the sites of affine ind-étale objects it is
`AlgebraicGeometry.ProEtale.appInverseImage`, which does, and the restriction functors to those
sites are equivalences. -/
theorem preservesLimitsOfShape_proetaleModuleInverseImage_of_isClosedImmersion (K : Type*)
    [Category* K] [HasLimitsOfShape K (ModuleCat.{max (u + 1) v w} Λ)] :
    PreservesLimitsOfShape K (proetaleModuleInverseImage.{u, v, w} i Λ) := by
  have := appInclusion_isDenseSubsite X (hasAppCover X)
  have := appInclusion_isDenseSubsite Z (hasAppCover Z)
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{max (u + 1) v w} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, max (u + 1) v w, v}
  have := preservesLimitsOfShape_appInverseImage.{w} i Λ K
  let RZ := (AppProetale.inclusion Z).sheafPushforwardContinuous
    (ModuleCat.{max (u + 1) v w} Λ)
    ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) (Scheme.ProEt.topology Z)
  have : PreservesLimitsOfShape K (proetaleModuleInverseImage.{u, v, w} i Λ ⋙ RZ) :=
    preservesLimitsOfShape_of_natIso (proetaleModuleInverseImageCompRestrictionIso.{w} i Λ).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ RZ

end ClosedImmersion

end AlgebraicGeometry.ProEtale

end
