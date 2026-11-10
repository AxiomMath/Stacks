module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.LiftsOfObjects.Action.Difference
public import StacksFrontier.Deformation.LiftsOfObjects.CompositeProjection
public import StacksFrontier.Deformation.LiftsOfObjects.SquareZeroPullback

/-!
# Pairs of lifts and their difference, as a bijection

The second coordinate of a pair of lifts can be replaced by the infinitesimal difference of
the two: the map `(a, b) ↦ (a, d(a, b))` is a bijection

`LiftClasses f x × LiftClasses f x ≃ LiftClasses f x × T𝓕 ⊗_k I`.

This is the content of Tag 06JI apart from the formal reconstruction of the action, and it is
assembled here from three bijections already available: the fibre-product bijection of Tag
06JH, the difference isomorphism `A' ×_A A' ≅ A' ×_k k[I]` of Tag 06TA, and the two-coordinate
description of lifts over a composite of fibre squares of Tag 06TC.

## Main definitions

* `Deformation.pairLiftEquiv`: the bijection above, with its second coordinate identified with
  `Deformation.differenceClass`.
* `Deformation.tangentPairEquiv`: the same bijection in tangent coordinates, carrying in
  addition the three properties — first coordinate, vanishing on the diagonal, cocycle — that
  reconstruct the action.

## Implementation notes

Both results are packaged as subtypes rather than as structures: the data is one `Equiv` and
what matters about it is a conjunction of equations, so there is nothing to name.

The chain of three bijections is composed over the residue-field pullback square: `x` is
pushed forward to an object `x₀` of the special fibre along the canonical morphism
`A ⟶ k`, and the composite square is `A' ×_A (A ×_k k[I]) ≅ A' ×_k k[I]`. The second
coordinate of Tag 06TC is then a lift over `k[I]`, and `liftClassesEquivFiber` turns its class
into a class in the fibre over `k[I]`, i.e. an element of the associated functor there.

## References

* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
-/

@[expose] public section

namespace Deformation

/-! ### Replacing the second lift by the difference -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w uF vF

/-- Pairs of isomorphism classes of lifts of `x` along `f` are in bijection with a class
together with a class at the target of the infinitesimal difference map, the second coordinate
being `Deformation.differenceClass`. -/
public noncomputable def pairLiftEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    {e : (LiftClasses 𝓕.p f x × LiftClasses 𝓕.p f x) ≃
        (LiftClasses 𝓕.p f x ×
          (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).obj
            (infinitesimalDifferenceMap f hf hann).target) //
      ∀ a b, (e (a, b)).1 = a ∧
        (e (a, b)).2 = differenceClass 𝓕 h𝓕 f hf hann x a b} := by
  classical
  let I := RingHom.ker f.hom.toRingHom
  letI : Module k I := kernelModule f hann
  letI : Module.Finite k I := kernelModule_finite f hann
  letI : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  let H := isomorphismClasses 𝓕 h𝓕.predeformation.cofibered
  let V : FGModuleCat.{w} k := FGModuleCat.of k I
  let T := (squareZeroExtensionArtinian Λ k).obj V
  letI : CommRing (TrivSqZeroExt k I) := T.commRing
  letI : Algebra Λ (TrivSqZeroExt k I) := T.algebra
  letI : Module A' I := inferInstance
  letI : IsScalarTower Λ A' I := inferInstance
  have hTors : Module.IsTorsionBySet A' I (maximalIdeal A') :=
    fun i m => Subtype.ext (hann m.1 m.2 i)
  letI : Module (ResidueField A') I := hTors.module
  have hsmul (a : A') (i : I) :
      a • i = (A'.residueEquiv (residue A' a)) • i := by
    apply Subtype.ext
    change a * (i : A') =
      ((A'.residueEquiv.symm (A'.residueEquiv (residue A' a)) • i : I) : A')
    rw [A'.residueEquiv.symm_apply_apply]
    exact congrArg Subtype.val (Module.IsTorsionBySet.mk_smul hTors a i).symm
  have hresidueAlgMap (a : Λ) :
      residue A' (algebraMap Λ A' a) = algebraMap Λ (ResidueField A') a := by
    symm
    rw [IsScalarTower.algebraMap_apply Λ A' (ResidueField A') a]
    simp [IsLocalRing.ResidueField.algebraMap_eq]
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun a i => by
    calc
      (algebraMap Λ k a) • i =
          (A'.residueEquiv (residue A' (algebraMap Λ A' a))) • i := by
            rw [← A'.residueEquiv.commutes a, hresidueAlgMap]
      _ = (algebraMap Λ A' a) • i := (hsmul _ i).symm
      _ = a • i := IsScalarTower.algebraMap_smul (R := Λ) (A := A') (M := V) a i
  letI : IsScalarTower Λ kᵐᵒᵖ V := IsScalarTower.of_algebraMap_smul fun a i =>
    (show (algebraMap Λ kᵐᵒᵖ a) • i = (algebraMap Λ k a) • i from rfl).trans
      (algebraMap_smul k a i)
  let K := residueFieldObject.{u, w, w} Λ k
  let rA : A ⟶ K := residueFieldMorphism (B := A)
  let rT : T ⟶ K := residueFieldMorphism (B := T)
  let p₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)
  let p₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)
  let hrA : Function.Surjective rA.hom := residueFieldMorphism_surjective
  let r₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective rA rT (.inl hrA)
  let r₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective rA rT (.inl hrA)
  let q₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective f r₁ (.inl hf)
  let q₂ := (ArtinianLocalAlgCat.pullbackSnd_of_surjective f r₁ (.inl hf)) ≫ r₂
  let hP := ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)
  let hR := ArtinianLocalAlgCat.isPullback_of_surjective rA rT (.inl hrA)
  let hL := ArtinianLocalAlgCat.isPullback_of_surjective f r₁ (.inl hf)
  let hQ := hL.paste_vert hR
  let resA' : A' ⟶ K := f ≫ rA
  let coord : T ≃+* TrivSqZeroExt k I := RingEquiv.refl _
  let hx₀ := residuePushforwardLift 𝓕.p h𝓕.predeformation.cofibered x
  let x₀ := hx₀.1
  let a₀ := hx₀.2
  let hdiff := infinitesimalDifferenceMap f hf hann
  let hpairs := Classical.choice (liftClassesProdEquivPullback 𝓕.p h𝓕.satisfiesRS
    hP.cone hP.isLimit (.inl hf) x)
  let hdTA := Classical.choice (liftClassesEquivSquareZeroPullback
    𝓕.p h𝓕 f hf hann
    (fun a i => (hsmul a i).symm)
    coord
    (fun a => TrivSqZeroExt.algebraMap_eq_inl' Λ k V a)
    (fun z => (squareZeroExtensionArtinian_residue Λ k V z).symm)
    (Iso.refl K) resA' rT p₁ p₂ hP q₁ q₂ hQ x)
  let hc := Classical.choice (liftClassesEquivProdOfResiduePullback
    𝓕.p h𝓕 hR.cone hR.isLimit hL.cone hL.isLimit hf hrA x₀ a₀)
  let hcEquiv : LiftClasses 𝓕.p (q₁ ≫ f) x ≃
      LiftClasses 𝓕.p f x × LiftClasses 𝓕.p rT x₀ := hc.equiv
  let e0 : LiftClasses 𝓕.p f x × LiftClasses 𝓕.p f x ≃
      LiftClasses 𝓕.p f x × LiftClasses 𝓕.p rT x₀ :=
    (hpairs.equiv.trans hdTA.equiv).trans hcEquiv
  let e1 := (liftClassesEquivFiber 𝓕.p h𝓕.predeformation rT x₀).trans
    (fiberClassEquiv 𝓕 h𝓕.predeformation.cofibered T)
  refine ⟨e0.trans (Equiv.prodCongr (Equiv.refl _) e1), ?_⟩
  intro a b
  obtain ⟨a, rfl⟩ : ∃ a' : Lift 𝓕.p f x, ThinSkeleton.mk a' = a := Quotient.exists_rep a
  obtain ⟨b, rfl⟩ : ∃ b' : Lift 𝓕.p f x, ThinSkeleton.mk b' = b := Quotient.exists_rep b
  obtain ⟨z, ⟨w₁, w₂, hw, hr₁, hr₂, h₁, h₂, hlim⟩, hz⟩ :=
    hpairs.maps_pair_to_fiberProduct a b
  obtain ⟨z', hz', t, ht, htfac⟩ := hdTA.maps_lift z
  have hr₁' : 𝓕.p.IsHomLift p₁ w₁ := hr₁
  let := hr₁'
  let := ht
  let := isStronglyCocartesian_of_isCofiberedInGroupoids h𝓕.predeformation.cofibered
    hdTA.baseEquiv.hom t ht
  let : IsIso t := Functor.IsStronglyCocartesian.isIso_of_base_isIso
    𝓕.p hdTA.baseEquiv.hom t
  have htAsIso : 𝓕.p.IsHomLift hdTA.baseEquiv.hom (asIso t).hom := ht
  have hfirst : (hcEquiv (ThinSkeleton.mk z')).1 = ThinSkeleton.mk a := by
    apply (hc.fst_eq_iff z' a).mpr
    refine ⟨inv t ≫ w₁, ?_, ?_⟩
    · let := htAsIso
      have hinvLift : 𝓕.p.IsHomLift hdTA.baseEquiv.inv (inv t) :=
        CategoryTheory.IsHomLift.inv_lift_inv 𝓕.p hdTA.baseEquiv (asIso t)
      let := hinvLift
      have hi := CategoryTheory.IsHomLift.comp 𝓕.p hdTA.baseEquiv.inv p₁ (inv t) w₁
      have he : hdTA.baseEquiv.inv ≫ p₁ = q₁ :=
        (congrArg (hdTA.baseEquiv.inv ≫ ·) hdTA.first.symm).trans
          (hdTA.baseEquiv.inv_hom_id_assoc q₁)
      rwa [he] at hi
    · calc (inv t ≫ w₁) ≫ a.hom = inv t ≫ (w₁ ≫ a.hom) := Category.assoc _ _ _
        _ = inv t ≫ z.hom := congrArg (inv t ≫ ·) h₁
        _ = inv t ≫ (t ≫ z'.hom) := congrArg (inv t ≫ ·) htfac.symm
        _ = z'.hom := IsIso.inv_hom_id_assoc t z'.hom
  have hg : hdTA.baseEquiv.hom ≫ q₂ = hdiff.g :=
    ArtinianLocalAlgCat.hom_ext <| AlgHom.ext fun y =>
      TrivSqZeroExt.ext (hdTA.residue y) (Subtype.ext (hdTA.difference y))
  obtain ⟨c, hcclass⟩ : ∃ c' : Lift 𝓕.p rT x₀,
      ThinSkeleton.mk c' = (hcEquiv (ThinSkeleton.mk z')).2 :=
    Quotient.exists_rep (hcEquiv (ThinSkeleton.mk z')).2
  obtain ⟨r, hr, hrfac⟩ := (hc.snd_eq_iff z' c).mp hcclass.symm
  have hr' : 𝓕.p.IsHomLift q₂ r := hr
  let := hr'
  have htr : 𝓕.p.IsHomLift hdiff.g (t ≫ r) := by
    rw [← hg]
    exact CategoryTheory.IsHomLift.comp 𝓕.p hdTA.baseEquiv.hom q₂ t r
  have hclass : e1 (ThinSkeleton.mk c) =
      classOf 𝓕 h𝓕.predeformation.cofibered
        ((liftForgetFunctor 𝓕.p rT x₀).obj c) :=
    fiberClassEquiv_mk 𝓕 h𝓕.predeformation.cofibered
      ((liftForgetFunctor 𝓕.p rT x₀).obj c)
  have hpair : hcEquiv (hdTA.equiv (hpairs.equiv (ThinSkeleton.mk a, ThinSkeleton.mk b))) =
      hcEquiv (ThinSkeleton.mk z') :=
    congrArg (fun y : LiftClasses 𝓕.p (q₁ ≫ f) x => hcEquiv y)
      ((congrArg (fun y : LiftClasses 𝓕.p (p₁ ≫ f) x => hdTA.equiv y) hz).trans hz')
  have hdc : differenceClass 𝓕 h𝓕 f hf hann x (ThinSkeleton.mk a) (ThinSkeleton.mk b) =
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map hdiff.g
        (classOf 𝓕 h𝓕.predeformation.cofibered
          ((liftForgetFunctor 𝓕.p _ x).obj z)) := by
    dsimp only [differenceClass]
    rw [hz]
    exact congrArg _ (liftSourceClass_mk 𝓕 h𝓕.predeformation.cofibered _ x z)
  refine ⟨?_, ?_⟩
  · change (hcEquiv (hdTA.equiv (hpairs.equiv (ThinSkeleton.mk a, ThinSkeleton.mk b)))).1 = _
    rwa [hpair]
  · change e1 (hcEquiv (hdTA.equiv
      (hpairs.equiv (ThinSkeleton.mk a, ThinSkeleton.mk b)))).2 = _
    rw [hpair, ← hcclass, hclass, hdc]
    exact (map_classOf 𝓕 h𝓕.predeformation.cofibered hdiff.g
      ((liftForgetFunctor 𝓕.p _ x).obj z)
      ((liftForgetFunctor 𝓕.p rT x₀).obj c) (t ≫ r)).symm

end

/-! ### The bijection in tangent coordinates -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w uF vF

/-- Pairs of isomorphism classes of lifts of `x` along `f` are in bijection with a class
together with a tangent vector tensored with the kernel, the second coordinate being the
tangent coordinate of `Deformation.differenceClass`; moreover that coordinate is the first
projection, vanishes on the diagonal, and satisfies the cocycle identity. -/
public noncomputable def tangentPairEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    letI : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
    let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 h𝓕.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
      (.inl h𝓕.predeformation)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
    let V := FGModuleCat.of k (RingHom.ker f.hom.toRingHom)
    {e : (LiftClasses 𝓕.p f x × LiftClasses 𝓕.p f x) ≃
        (LiftClasses 𝓕.p f x × TensorProduct k
          (artinianTangentSpace Λ k
            (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)) V) //
      (∀ a b, (e (a, b)).1 = a) ∧
      (∀ a, (e (a, a)).2 = 0) ∧
      (∀ a b c, (e (a, b)).2 + (e (b, c)).2 = (e (a, c)).2) ∧
      (∀ a b, (e (a, b)).2 = tensorCoordinate 𝓕 h𝓕 V
        (differenceClass 𝓕 h𝓕 f hf hann x a b))} := by
  intro hS2 V
  letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  letI : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
  let E := pairLiftEquiv 𝓕 h𝓕 f hf hann x
  let e := E.1.trans (Equiv.prodCongr (Equiv.refl _) (tensorCoordinate 𝓕 h𝓕 V))
  have hd (a b) : (e (a, b)).2 = tensorCoordinate 𝓕 h𝓕 V
      (differenceClass 𝓕 h𝓕 f hf hann x a b) :=
    congrArg (tensorCoordinate 𝓕 h𝓕 V) (E.2 a b).2
  have hc (a b c) : (e (a, b)).2 + (e (b, c)).2 = (e (a, c)).2 := by
    rw [hd, hd, hd]
    exact difference_cocycle 𝓕 h𝓕 f hf hann x a b c
  exact ⟨e, fun a b => (E.2 a b).1,
    fun a => add_left_cancel ((hc a a a).trans (add_zero (e (a, a)).2).symm), hc, hd⟩

end

end Deformation
