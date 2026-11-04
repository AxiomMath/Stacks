module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.LiftsOfObjects.Action.FreeTransitive
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.TangentSpace.Predeformation

/-!
# Functoriality of the action on lifts

A morphism `φ : 𝓕 ⟶ 𝓖` of deformation categories over `𝒞_Λ` carries lifts to lifts, hence
classes of lifts to classes of lifts, and the resulting map intertwines the two free
transitive actions of Tag 06JI: the map on the acting vector spaces is the differential of
`φ` tensored with the identity of the kernel.

## Main definitions

* `Deformation.linearOfNatural`: a natural family of maps between the values of two additive
  `k`-linear functors into `ModuleCat k` is `k`-linear at every object.
* `Deformation.linearLiftMap`: the same for a natural family between two set-valued functors
  carrying linear lifts.
* `Deformation.squareZeroLinearMap`: that linear map for the associated functors of
  isomorphism classes of `𝓕` and `𝓖`.

## Main results

* `Deformation.squareZeroLinearMap_tensor`: on a tensor `t ⊗ v`, the linear map above is the
  differential of `φ` tensored with the identity.
* `Deformation.mapLiftClasses_vadd`: the commutative square of actions.

## Implementation notes

The linearity of a natural family at `V` is read off from the two projections and the sum of
the two projections of `V × V`: additivity of a natural transformation is naturality applied
to `fst + snd`, and homogeneity is naturality applied to `r • 𝟙`. This is why
`linearOfNatural` needs both functors additive and `k`-linear but needs no hypothesis at all
on the family beyond naturality.

Transport across the defining equation of a linear lift is packaged as
`Deformation.linearFunctorLiftEquiv`, an `Equiv` ascribed at the folded type
`(L.functor.obj V : Type _) ≃ F.obj V`. Stating it that way, rather than as a bare `cast`,
is what keeps the goals of this file type-correct at `implicit` transparency, so that
`rw` can traverse them.

The proof of `mapLiftClasses_vadd` runs through
`Deformation.map_vadd_of_natural_difference`: it suffices that `φ` intertwine the two
difference maps, and that is checked on representatives using
`Deformation.liftDifference_isPushforward` on both sides. The comparison of the two
pushforwards needs the fibre product of the `𝓖`-side representatives to receive the image of
the `𝓕`-side one over the identity of `A' ×_A A'`, which is `hjLift` below.

## References

* [Stacks Project, Tag 06JJ](https://stacks.math.columbia.edu/tag/06JJ)
-/

@[expose] public section

namespace Deformation

/-! ### Linearity of a natural family -/

section
open CategoryTheory
universe uk vM uM uM'

/-- A natural family of maps between two additive `k`-linear functors into module categories
is `k`-linear at every object: additivity is naturality applied to the sum of the two
projections of `V × V`, and homogeneity is naturality applied to `r • 𝟙 V`. -/
public def linearOfNatural
    {k : Type uk} [CommRing k]
    (L : FGModuleCat.{vM} k ⥤ ModuleCat.{uM} k)
    (M : FGModuleCat.{vM} k ⥤ ModuleCat.{uM'} k)
    [L.Additive] [M.Additive] [L.Linear k] [M.Linear k]
    (η : ∀ V, L.obj V → M.obj V)
    (hη : ∀ {V W} (f : V ⟶ W) (x : L.obj V), η W (L.map f x) = M.map f (η V x))
    (V : FGModuleCat.{vM} k) : L.obj V →ₗ[k] M.obj V where
  toFun := η V
  map_add' x y := by
    let W := FGModuleCat.of k (V × V)
    let i₁ : V ⟶ W := FGModuleCat.ofHom (LinearMap.inl k V V)
    let i₂ : V ⟶ W := FGModuleCat.ofHom (LinearMap.inr k V V)
    let p₁ : W ⟶ V := FGModuleCat.ofHom (LinearMap.fst k V V)
    let p₂ : W ⟶ V := FGModuleCat.ofHom (LinearMap.snd k V V)
    have h11 : i₁ ≫ p₁ = 𝟙 V := by ext; rfl
    have h12 : i₁ ≫ p₂ = 0 := by ext; rfl
    have h21 : i₂ ≫ p₁ = 0 := by ext; rfl
    have h22 : i₂ ≫ p₂ = 𝟙 V := by ext; rfl
    let z := L.map i₁ x + L.map i₂ y
    have hz₁ : L.map p₁ z = x := by
      dsimp only [z]
      simp only [map_add, ← ModuleCat.comp_apply, ← L.map_comp, h11, h21,
        L.map_id, L.map_zero]
      simp
    have hz₂ : L.map p₂ z = y := by
      dsimp only [z]
      simp only [map_add, ← ModuleCat.comp_apply, ← L.map_comp, h12, h22,
        L.map_id, L.map_zero]
      simp
    have h := hη (p₁ + p₂) z
    rw [L.map_add, M.map_add] at h
    change η V (L.map p₁ z + L.map p₂ z) = M.map p₁ (η W z) + M.map p₂ (η W z) at h
    rwa [hz₁, hz₂, ← hη p₁ z, ← hη p₂ z, hz₁, hz₂] at h
  map_smul' r x := by
    have h := hη (r • 𝟙 V) x
    rwa [L.map_smul, M.map_smul, L.map_id, M.map_id] at h

end

/-! ### Transport across the defining equation of a linear lift -/

section
open CategoryTheory
universe uk uC vC uM

/-- Transport between the values of a linear lift and the values of the set-valued functor it
lifts. Ascribed at the folded type, so that goals mentioning it stay type-correct at
`implicit` transparency. -/
public noncomputable def linearFunctorLiftEquiv
    {k : Type uk} [CommRing k]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [CategoryTheory.Linear k C]
    {F : C ⥤ Type uM} (L : LinearFunctorLift k F) (V : C) :
    ((L.functor.obj V : ModuleCat.{uM} k) : Type uM) ≃ F.obj V :=
  Equiv.cast (congrArg (fun H : C ⥤ Type uM => H.obj V) L.forget_comp)

/-- The transport is natural. -/
public lemma linearFunctorLiftEquiv_map
    {k : Type uk} [CommRing k]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [CategoryTheory.Linear k C]
    {F : C ⥤ Type uM} (L : LinearFunctorLift k F) {V W : C} (f : V ⟶ W)
    (x : ((L.functor.obj V : ModuleCat.{uM} k) : Type uM)) :
    linearFunctorLiftEquiv L W ((L.functor.map f).hom x) =
      F.map f (linearFunctorLiftEquiv L V x) :=
  functor_map_cast (R := k) L.forget_comp.symm f x

end

/-! ### Linear maps between linear lifts -/

section
open CategoryTheory
universe uk vM uM uM'

/-- A natural family of maps between two set-valued functors carrying linear lifts induces a
`k`-linear map between the values of the lifts. -/
public noncomputable def linearLiftMap
    {k : Type uk} [CommRing k]
    {F : FGModuleCat.{vM} k ⥤ Type uM} {G : FGModuleCat.{vM} k ⥤ Type uM'}
    (L : LinearFunctorLift k F) (M : LinearFunctorLift k G)
    (η : ∀ V, F.obj V → G.obj V)
    (hη : ∀ {V W} (f : V ⟶ W) (x : F.obj V), η W (F.map f x) = G.map f (η V x))
    (V : FGModuleCat.{vM} k) : L.functor.obj V →ₗ[k] M.functor.obj V :=
  linearOfNatural L.functor M.functor
    (fun V x => (linearFunctorLiftEquiv M V).symm (η V (linearFunctorLiftEquiv L V x)))
    (by
      intro V W f x
      apply (linearFunctorLiftEquiv M W).injective
      rw [linearFunctorLiftEquiv_map M f, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        linearFunctorLiftEquiv_map L f]
      exact hη f _) V

/-- The induced linear map is natural. -/
public lemma linearLiftMap_naturality
    {k : Type uk} [CommRing k]
    {F : FGModuleCat.{vM} k ⥤ Type uM} {G : FGModuleCat.{vM} k ⥤ Type uM'}
    (L : LinearFunctorLift k F) (M : LinearFunctorLift k G)
    (η : ∀ V, F.obj V → G.obj V)
    (hη : ∀ {V W} (f : V ⟶ W) (x : F.obj V), η W (F.map f x) = G.map f (η V x))
    {V W : FGModuleCat.{vM} k} (f : V ⟶ W) (x : L.functor.obj V) :
    linearLiftMap L M η hη W ((L.functor.map f).hom x) =
      (M.functor.map f).hom (linearLiftMap L M η hη V x) := by
  change (linearFunctorLiftEquiv M W).symm
      (η W (linearFunctorLiftEquiv L W ((L.functor.map f).hom x))) =
    (M.functor.map f).hom ((linearFunctorLiftEquiv M V).symm
      (η V (linearFunctorLiftEquiv L V x)))
  apply (linearFunctorLiftEquiv M W).injective
  rw [linearFunctorLiftEquiv_map M f, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    linearFunctorLiftEquiv_map L f]
  exact hη f _

end

/-! ### The transport and the tangent coordinate -/

section
open CategoryTheory
universe u w uF vF

/-- The transport of a linear lift and `Deformation.tangentLiftCoord` are mutually inverse. -/
public lemma linearFunctorLiftEquiv_tangentLiftCoord
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)))
    (V : FGModuleCat.{w} k)
    (y : (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).obj
      ((squareZeroExtensionArtinian Λ k).obj V)) :
    linearFunctorLiftEquiv
        (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕.predeformation hS2) V
        (tangentLiftCoord 𝓕 h𝓕 hS2 V y) = y :=
  Equiv.apply_symm_apply _ y

end

/-! ### The linear map on associated tangent spaces -/

section
open CategoryTheory
universe u w uF vF uG vG

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    [h𝓕 : Fact (IsPredeformationCategory 𝓕.p)]
    [h𝓖 : Fact (IsPredeformationCategory 𝓖.p)]
    [hS2𝓕 : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.out.cofibered)))]
    [hS2𝓖 : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.out.cofibered)))]
    (φ : BasedFunctor 𝓕 𝓖)

/-- The map induced by `φ` on the canonical linear structures of the associated functors at
the square-zero extensions. -/
public noncomputable abbrev squareZeroLinearMap (V : FGModuleCat.{w} k) :=
  linearLiftMap
    (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕.out hS2𝓕.out)
    (associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖.out hS2𝓖.out)
    (fun V => mapIsomorphismClasses h𝓕.out.cofibered h𝓖.out.cofibered φ
      ((artinianSquareZeroExtensionFunctor Λ k).obj V))
    (fun f z => mapIsomorphismClasses_naturality
      h𝓕.out.cofibered h𝓖.out.cofibered φ
      ((artinianSquareZeroExtensionFunctor Λ k).map f) z) V

/-- On a pure tensor, the map induced by `φ` is its differential tensored with the identity. -/
public theorem squareZeroLinearMap_tensor
    (V : FGModuleCat.{w} k)
    (t : TensorProduct k (artinianTangentSpace Λ k
      (isomorphismClasses 𝓕 h𝓕.out.cofibered)) V) :
    let dφ := IsLinearMap.mk' (differential h𝓕.out.cofibered h𝓖.out.cofibered φ)
      (differential_isLinearMap 𝓕 𝓖 h𝓕.out h𝓖.out hS2𝓕.out hS2𝓖.out φ)
    squareZeroLinearMap 𝓕 𝓖 φ V
        (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓕 h𝓕.out hS2𝓕.out V t) =
      associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓖 h𝓖.out hS2𝓖.out V
        (TensorProduct.map dφ (LinearMap.id : V →ₗ[k] V) t) := by
  intro dφ
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t v =>
    rw [associatedTangentSpaceFunctor_iso_tensorLeft_pureUnlifted,
      TensorProduct.map_tmul, LinearMap.id_apply,
      associatedTangentSpaceFunctor_iso_tensorLeft_pureUnlifted,
      linearLiftMap_naturality _ _ _
        (fun f z => mapIsomorphismClasses_naturality
          h𝓕.out.cofibered h𝓖.out.cofibered φ
          ((artinianSquareZeroExtensionFunctor Λ k).map f) z)]
    congr 1
    let eF := associatedTangentSpaceModuleStructure_carrierUnlifted 𝓕 h𝓕.out hS2𝓕.out
    let eG := associatedTangentSpaceModuleStructure_carrierUnlifted 𝓖 h𝓖.out hS2𝓖.out
    change cast eG.symm (dφ (cast eF (cast eF.symm t))) = cast eG.symm (dφ t)
    rw [cast_cast, cast_eq]

end

/-! ### The action is functorial -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w uF vF uG vG

/-- On a representative, the map on classes of lifts is the class of the image lift. -/
public lemma mapLiftClasses_mk
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : A' ⟶ A)
    (x : 𝓕.p.Fiber A) (a : Lift 𝓕.p f x) :
    mapLiftClasses φ f x (ThinSkeleton.mk a) =
      ThinSkeleton.mk ((liftFunctor φ f x).obj a) := rfl

attribute [local implicit_reducible] liftFunctor

/-- **Stacks Project, Tag 06JJ.** The map on lift classes commutes with the torsor actions,
with tangent vectors mapped by the differential tensored with the identity of the kernel. -/
@[stacks 06JJ]
public theorem mapLiftClasses_vadd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (h𝓖 : IsDeformationCategory 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    let hS2𝓕 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 h𝓕.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
      (.inl h𝓕.predeformation)
    let hS2𝓖 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓖 h𝓖.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓖.satisfiesRS)
      (.inl h𝓖.predeformation)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered))) := ⟨hS2𝓖⟩
    letI := liftAction 𝓕 h𝓕 f hf hann x
    letI := liftAction 𝓖 h𝓖 f hf hann ((fiberFunctor φ A).obj x)
    let dφ := IsLinearMap.mk' (differential h𝓕.predeformation.cofibered
      h𝓖.predeformation.cofibered φ)
      (differential_isLinearMap 𝓕 𝓖 h𝓕.predeformation h𝓖.predeformation hS2𝓕 hS2𝓖 φ)
    ∀ (a : LiftClasses 𝓕.p f x)
      (t : TensorProduct k
        (artinianTangentSpace Λ k
          (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))
        (RingHom.ker f.hom.toRingHom)),
      mapLiftClasses φ f x (t +ᵥ a) =
        (TensorProduct.map dφ (LinearMap.id :
          RingHom.ker f.hom.toRingHom →ₗ[k] RingHom.ker f.hom.toRingHom) t) +ᵥ
          mapLiftClasses φ f x a := by
  intro hS2F hS2G
  let : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖.predeformation⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2F⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered))) := ⟨hS2G⟩
  let := liftAction 𝓕 h𝓕 f hf hann x
  let := liftAction 𝓖 h𝓖 f hf hann ((fiberFunctor φ A).obj x)
  intro dφ
  refine map_vadd_of_natural_difference
    (liftDifference 𝓕 h𝓕 f hf hann x)
    (liftDifference 𝓖 h𝓖 f hf hann ((fiberFunctor φ A).obj x))
    (liftAction_difference 𝓕 h𝓕 f hf hann x)
    (liftAction_difference 𝓖 h𝓖 f hf hann ((fiberFunctor φ A).obj x))
    (liftAction_bijective 𝓖 h𝓖 f hf hann ((fiberFunctor φ A).obj x))
    (mapLiftClasses φ f x) _ fun a b ↦ ?_
  obtain ⟨hfinF, htargetF, a₀F, b₀F, zF, r₁F, r₂F, yF, qF, haF, hbF, hr₁F, hr₂F, hfac₁F,
    hfac₂F, -, hqF, -, hcoordF⟩ := liftDifference_isPushforward 𝓕 h𝓕 f hf hann x a b
  obtain ⟨hfinG, htargetG, a₀G, b₀G, zG, r₁G, r₂G, yG, qG, haG, hbG, hr₁G, hr₂G, -, -, hpbG, hqG,
    -, hcoordG⟩ := liftDifference_isPushforward 𝓖 h𝓖 f hf hann ((fiberFunctor φ A).obj x)
      (mapLiftClasses φ f x a) (mapLiftClasses φ f x b)
  obtain ⟨i₁⟩ := Quotient.exact
    ((mapLiftClasses_mk φ f x a₀F).symm.trans ((congrArg _ haF).trans haG.symm))
  obtain ⟨i₂⟩ := Quotient.exact
    ((mapLiftClasses_mk φ f x b₀F).symm.trans ((congrArg _ hbF).trans hbG.symm))
  let p₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)
  let p₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)
  let P := ArtinianLocalAlgCat.pullbackObj_of_surjective f f (.inl hf)
  let z₀F : 𝓕.p.Fiber P := ⟨zF.obj, IsHomLift.domain_eq 𝓕.p (p₁ ≫ f) zF.hom⟩
  let z₀G : 𝓖.p.Fiber P := ⟨zG.obj, IsHomLift.domain_eq 𝓖.p (p₁ ≫ f) zG.hom⟩
  let g := infinitesimalDifferenceMap f hf hann
  have hz : mapIsomorphismClasses h𝓕.predeformation.cofibered
        h𝓖.predeformation.cofibered φ P (classOf 𝓕 h𝓕.predeformation.cofibered z₀F) =
      classOf 𝓖 h𝓖.predeformation.cofibered z₀G := by
    have hcone : (φ.map r₁F ≫ i₁.hom.hom) ≫ a₀G.hom = (φ.map r₂F ≫ i₂.hom.hom) ≫ b₀G.hom := by
      rw [Category.assoc, Category.assoc, i₁.hom.fac, i₂.hom.fac]
      change φ.map r₁F ≫ φ.map a₀F.hom = φ.map r₂F ≫ φ.map b₀F.hom
      rw [← φ.map_comp, ← φ.map_comp, hfac₁F, hfac₂F]
    have : 𝓖.p.IsHomLift p₁ r₁G := hr₁G
    have : 𝓖.p.IsHomLift p₂ r₂G := hr₂G
    have := i₁.hom.isHomLift
    have := i₂.hom.isHomLift
    have : 𝓕.p.IsHomLift p₁ r₁F := hr₁F
    have : 𝓕.p.IsHomLift p₂ r₂F := hr₂F
    have : 𝓖.p.IsHomLift p₁ (φ.map r₁F) := φ.preserves_isHomLift p₁ r₁F
    have : 𝓖.p.IsHomLift p₂ (φ.map r₂F) := φ.preserves_isHomLift p₂ r₂F
    have hproj {X Y Y₁ : 𝓖.obj} {j : X ⟶ Y} {r : Y ⟶ Y₁} {u : X ⟶ Y₁} (q : P ⟶ A')
        [𝓖.p.IsHomLift q r] [𝓖.p.IsHomLift q u] (h : j ≫ r = u) :
        (eqToHom (IsHomLift.domain_eq 𝓖.p q u).symm ≫ 𝓖.p.map j ≫
          eqToHom (IsHomLift.domain_eq 𝓖.p q r)) ≫ q = q := by
      simpa [IsHomLift.fac' 𝓖.p q r, IsHomLift.fac' 𝓖.p q u] using congrArg
        (fun t => eqToHom (IsHomLift.domain_eq 𝓖.p q u).symm ≫ 𝓖.p.map t ≫
          eqToHom (IsHomLift.codomain_eq 𝓖.p q r)) h
    have hjLift : 𝓖.p.IsHomLift (𝟙 P) (hpbG.lift _ _ hcone) :=
      IsHomLift.of_fac 𝓖.p _ _ (IsHomLift.domain_eq 𝓖.p p₁ (φ.map r₁F ≫ i₁.hom.hom))
        (IsHomLift.domain_eq 𝓖.p p₁ r₁G)
        ((ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)).hom_ext
          ((Category.id_comp _).trans (hproj p₁ (hpbG.lift_fst _ _ hcone)).symm)
          ((Category.id_comp _).trans (hproj p₂ (hpbG.lift_snd _ _ hcone)).symm))
    rw [mapIsomorphismClasses_classOf]
    simpa using (@map_classOf _ _ 𝓖 h𝓖.predeformation.cofibered
      P P (𝟙 P) ((fiberFunctor φ P).obj z₀F) z₀G _ hjLift)
  have := hqF
  have := hqG
  have := hfinF
  let V := FGModuleCat.of k (RingHom.ker f.hom.toRingHom)
  have key : (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered).map (eqToHom htargetG)
        (classOf 𝓖 h𝓖.predeformation.cofibered yG) =
      mapIsomorphismClasses h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ
        ((squareZeroExtensionArtinian Λ k).obj V)
        ((isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map (eqToHom htargetF)
          (classOf 𝓕 h𝓕.predeformation.cofibered yF)) := by
    rw [mapIsomorphismClasses_naturality
        h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ (eqToHom htargetF),
      ← map_classOf 𝓕 h𝓕.predeformation.cofibered g.g z₀F yF qF,
      mapIsomorphismClasses_naturality
        h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ g.g, hz,
      map_classOf 𝓖 h𝓖.predeformation.cofibered g.g z₀G yG qG]
  rw [hcoordG, hcoordF]
  refine (congrArg (fun c => (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
    𝓖 h𝓖.predeformation hS2G V).symm (tangentLiftCoord 𝓖 h𝓖 hS2G V c)) key).trans ?_
  apply (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
    𝓖 h𝓖.predeformation hS2G V).injective
  rw [LinearEquiv.apply_symm_apply, ← squareZeroLinearMap_tensor 𝓕 𝓖 φ V,
    LinearEquiv.apply_symm_apply]
  exact (congrArg (fun z => tangentLiftCoord 𝓖 h𝓖 hS2G V
    (mapIsomorphismClasses h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ
      ((squareZeroExtensionArtinian Λ k).obj V) z))
    (linearFunctorLiftEquiv_tangentLiftCoord 𝓕 h𝓕 hS2F V _)).symm

end

end Deformation
