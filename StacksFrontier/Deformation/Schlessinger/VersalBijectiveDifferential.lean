module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.FormalObject.RestrictionEquivalence
public import StacksFrontier.Deformation.Formal.VersalObject.MapsToFormalObject
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.Schlessinger.VersalImpliesS1
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.TangentSpace.BijectiveDifferential
public import StacksFrontier.Deformation.TangentSpace.Derivations
public import StacksFrontier.Deformation.TangentSpace.Functor
public import StacksFrontier.Deformation.TangentSpace.LinearFunctor

/-!
# A versal formal object with bijective differential forces (S1), (S2) and finiteness (Stacks 06IV)

Let `p : F ⥤ 𝒞_Λ` be a predeformation category with a versal formal object `ξ` whose
differential is bijective (Tag 06IM). Then `p` satisfies Schlessinger's conditions (S1)
and (S2), and its tangent space is finite-dimensional over `k`.

Condition (S1) does not need the differential: it follows from versality alone (Tag 06SY).

For (S2), the input is a pushout diagram in `𝒞_Λ` with one leg a small extension by the
dual numbers. The versal object supplies a map from the completion of `p` and the
bijectivity of the differential makes the induced map on tangent vectors injective, which
is exactly the surjectivity-and-injectivity statement (S2) asks for. The argument runs
through the Tag 06SJ equivalence between the restriction of `p` and its completion, and
the Tag 06HS lifting criterion for versality.

Finite-dimensionality then follows: the tangent space of `p` is identified with that of
the functor prorepresented by `ξ.base` under the bijective differential, and the latter is
finite-dimensional by Tag 06IC under the chapter's standing assumption `Module.Finite Λ k`.

## Main results

* `Deformation.schlessingerConditionS1_of_versal_bijectiveDifferential`: a predeformation
  category with a versal formal object of bijective differential satisfies (S1).
* `Deformation.schlessingerConditionS2_of_versal_bijectiveDifferential`: under the same
  hypotheses, it satisfies (S2).
* `Deformation.finiteDimensional_tangentSpace_of_versal_bijectiveDifferential`: under the same
  hypotheses, its tangent space is finite-dimensional.
-/

@[expose] public section

open CategoryTheory
open IsLocalRing

namespace Deformation

universe u v w uF vF

private lemma surjective_fst_of_isPullback_of_surjective_snd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₁ A₂ A₀ : Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f₁ : A₁ ⟶ A₀) (f₂ : A₂ ⟶ A₀)
    (hf₂ : Function.Surjective f₂.hom)
    {P : Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g₁ : P ⟶ A₁) (g₂ : P ⟶ A₂)
    (hpb : IsPullback g₂ g₁ f₂ f₁) : Function.Surjective g₁.hom := by
  obtain ⟨hC, _⟩ :=
    Deformation.ArtinianLocalAlgCat.hasPullback_of_surjective
      f₂ f₁ (Or.inl hf₂)
  let C := Deformation.ArtinianLocalAlgCat.IsConcretePullback.obj hC
  let c₁ := Deformation.ArtinianLocalAlgCat.IsConcretePullback.fst hC
  let c₂ := Deformation.ArtinianLocalAlgCat.IsConcretePullback.snd hC
  have hCpb : IsPullback c₁ c₂ f₂ f₁ :=
    Deformation.ArtinianLocalAlgCat.IsConcretePullback.isPullback hC
  have hc₂ : Function.Surjective c₂.hom := by
    rw [Deformation.ArtinianLocalAlgCat.IsConcretePullback.snd_hom]
    exact AlgHom.surjective_pullbackSnd_of_surjective f₂.hom f₁.hom hf₂
  let j : C ⟶ P := hpb.lift c₁ c₂ hCpb.w
  have hj : j ≫ g₁ = c₂ := by simp [j]
  intro y
  obtain ⟨z, hz⟩ := hc₂ y
  refine ⟨j.hom z, ?_⟩
  have hv := congrArg (fun a : C ⟶ A₁ => a.hom z) hj
  show g₁.hom (j.hom z) = y
  rw [← hz]
  exact hv

/-- Every high enough power of the maximal ideal of an Artinian local algebra vanishes. -/
private lemma exists_maximalIdeal_pow_eq_bot
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k) :
    ∃ n, ∀ m ≥ n, maximalIdeal A ^ (m + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  exact ⟨n, fun m hm => eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)⟩

private lemma versal_lift_strict_representative
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : Deformation.IsPredeformationCategory p)
    (ξ : Deformation.FormalObject p)
    (hversal : Deformation.IsVersal hp.cofibered ξ)
    (E : Deformation.RestrictionCompletionEquivalence p)
    {X₂ X : CategoryTheory.Limits.CategoricalPullback E.inclusion
      (Deformation.FormalObject.projection (p := p))}
    (h₂ : X₂.snd.base = Deformation.artinianToComplete.obj X₂.fst)
    (h : X.snd.base = Deformation.artinianToComplete.obj X.fst)
    (hi₂ : X₂.iso = E.inclusionIso.app X₂.fst ≪≫ (eqToIso h₂).symm)
    (hi : X.iso = E.inclusionIso.app X.fst ≪≫ (eqToIso h).symm)
    (f : X₂ ⟶ X) (hf : Function.Surjective f.fst.hom)
    (a : ξ ⟶ X.snd) : ∃ b : ξ ⟶ X₂.snd, b ≫ f.snd = a :=
  (Deformation.isVersal_iff_lifts_artinian hp.cofibered ξ).mp hversal
    (B := X₂.fst) (A := X.fst) f.fst hf
    (y := X₂.snd) (x := X.snd) f.snd
    (strict_restriction_morphism_lift p E f h₂ h hi₂ hi) a



/-- The point of the functor prorepresented by `R` given by the quotient map of `R` onto its
`n`-th adic truncation `Deformation.AdicTruncation.obj R n`, read as a morphism of complete local
algebras into the image of that truncation. -/
public noncomputable def truncationPoint
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    R ⟶ Deformation.artinianToComplete.obj (AdicTruncation.obj R n) where
  hom := Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)
  isLocal := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  residue_comm := AdicTruncation.residueEquiv_residue_mk R n

private lemma transitionTo_self'
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ξ : FormalObject p) (n : ℕ) : transitionTo ξ (le_refl n) = 𝟙 _ := by
  unfold transitionTo
  generalize_proofs h
  revert h
  rw [Nat.sub_self]
  intro h
  simp [transitionIter]

private lemma transitionTo_succ'
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ξ : FormalObject p) {n m : ℕ} (h : n ≤ m) :
    transitionTo ξ (h.trans (Nat.le_succ m)) = ξ.transition m ≫ transitionTo ξ h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold transitionTo
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [Nat.succ_sub h, Nat.add_sub_cancel_left]
  intro h₁ h₂
  simp [transitionIter]

private lemma transitionTo_lift'
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ξ : FormalObject p) {n m : ℕ} (h : n ≤ m) :
    ∃ t : AdicTruncation.obj ξ.base m ⟶ AdicTruncation.obj ξ.base n,
      truncationPoint ξ.base m ≫ Deformation.artinianToComplete.map t =
        truncationPoint ξ.base n ∧ p.IsHomLift t (transitionTo ξ h) := by
  induction m, h using Nat.le_induction with
  | base =>
    refine ⟨𝟙 _, by simp, ?_⟩
    rw [transitionTo_self']
    exact IsHomLift.id (ξ.level_eq n)
  | succ m hm ih =>
    obtain ⟨t, ht, htl⟩ := ih
    refine ⟨AdicTruncation.transition ξ.base m ≫ t, ?_, ?_⟩
    · apply CompleteLocalAlgCat.Hom.ext
      exact congrArg (fun f => f.hom) ht
    · rw [transitionTo_succ' ξ hm]
      let : p.IsHomLift (AdicTruncation.transition ξ.base m) (ξ.transition m) := ξ.transition_lift m
      let := htl
      exact IsHomLift.comp p _ _ _ _

/-- The isomorphism class of the pushforward of a formal object `ξ` along a point `a` of the
functor prorepresented by `ξ.base`: the value at `a` of the morphism associated to `ξ`, taken
up to isomorphism in the fibre over `A`. -/
public noncomputable def pointClass
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (P : ChosenPushforwards p) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (a : (Deformation.restrictedCoyoneda ξ.base).obj A) :
    (Deformation.isomorphismClasses (BasedCategory.ofFunctor p) hp).obj A :=
  let φ := (associatedMorphism hp ξ P).toBasedFunctor
  Deformation.classOf (BasedCategory.ofFunctor p) hp
    ⟨φ.obj ((Deformation.restrictedCoyoneda ξ.base).elementsMk A a), φ.w_obj ((Deformation.restrictedCoyoneda ξ.base).elementsMk A a)⟩

/-- The class of a pushforward is natural in the base: precomposing the point with a
morphism of Artinian local algebras is pushing the class forward along it. -/
public theorem pointClass_naturality
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (P : ChosenPushforwards p) {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ B) (a : (Deformation.restrictedCoyoneda ξ.base).obj A) :
    pointClass hp ξ P B (a ≫ Deformation.artinianToComplete.map f) =
      (Deformation.isomorphismClasses (BasedCategory.ofFunctor p) hp).map f
        (pointClass hp ξ P A a) := by
  let φ := (associatedMorphism hp ξ P).toBasedFunctor
  let α : (Deformation.restrictedCoyoneda ξ.base).Elements := (Deformation.restrictedCoyoneda ξ.base).elementsMk A a
  let β : (Deformation.restrictedCoyoneda ξ.base).Elements :=
    (Deformation.restrictedCoyoneda ξ.base).elementsMk B (a ≫ Deformation.artinianToComplete.map f)
  let g : α ⟶ β := ⟨f, rfl⟩
  have : (CategoryOfElements.π (Deformation.restrictedCoyoneda ξ.base)).IsHomLift f g :=
    IsHomLift.map (CategoryOfElements.π (Deformation.restrictedCoyoneda ξ.base)) g
  have : (BasedCategory.ofFunctor (CategoryOfElements.π
      (Deformation.restrictedCoyoneda ξ.base))).p.IsHomLift f g :=
    IsHomLift.map (CategoryOfElements.π (Deformation.restrictedCoyoneda ξ.base)) g
  have := BasedFunctor.preserves_isHomLift φ f g
  exact (Deformation.map_classOf (BasedCategory.ofFunctor p) hp f
    ⟨φ.obj α, φ.w_obj _⟩ ⟨φ.obj β, φ.w_obj _⟩ (φ.map g)).symm

/-- The class of the pushforward of `ξ` along the point `truncationPoint ξ.base n ≫ f` is the
isomorphism class of any object of the fibre over `A` that receives a lift of `f` from the level
`n` object of `ξ`. -/
public lemma pointClass_of_lift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (P : ChosenPushforwards p) (n : ℕ)
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : AdicTruncation.obj ξ.base n ⟶ A) {x : F} (hx : p.obj x = A)
    (i : ξ.level n ⟶ x) (hi : p.IsHomLift f i) :
    pointClass hp ξ P A (truncationPoint ξ.base n ≫ Deformation.artinianToComplete.map f) =
      Deformation.classOf (BasedCategory.ofFunctor p) hp ⟨x, hx⟩ := by
  let a := truncationPoint ξ.base n ≫ Deformation.artinianToComplete.map f
  let φ := associatedMorphism hp ξ P
  let α : (Deformation.restrictedCoyoneda ξ.base).Elements := (Deformation.restrictedCoyoneda ξ.base).elementsMk A a
  have hpoint : p.IsHomLift (φ.factor α) (φ.pointInclusion α) := by
    have hh := (P (φ.factor α)).cocartesian
      ⟨ξ.level (φ.level α), ξ.level_eq (φ.level α)⟩ |>.toIsHomLift
    rw [← φ.pointInclusion_eq α] at hh
    have cancel_transport (y : F) (h : φ.toBasedFunctor.obj α = y)
        (hj : p.IsHomLift (φ.factor α) (φ.pointInclusion α ≫ eqToHom h)) :
        p.IsHomLift (φ.factor α) (φ.pointInclusion α) := by
      subst y
      exact (Category.comp_id (φ.pointInclusion α)) ▸ hj
    exact cancel_transport _ _ hh
  obtain ⟨t, ht, htl⟩ := transitionTo_lift' ξ (Nat.le_max_left n (φ.level α))
  obtain ⟨s, hs, hsl⟩ := transitionTo_lift' ξ (Nat.le_max_right n (φ.level α))
  have hf : t ≫ f = s ≫ φ.factor α := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have ht' := congrArg (fun h => h.hom r) ht
    have hs' := congrArg (fun h => h.hom r) hs
    have ha' := DFunLike.congr_fun (φ.factor_spec α).2.2 r
    show (f.hom (t.hom _)) = (φ.factor α).hom (s.hom _)
    exact (congrArg f.hom ht').trans ((ha').symm.trans (congrArg (φ.factor α).hom hs').symm)
  let := htl
  let := hsl
  let := hi
  let := hpoint
  have : (BasedCategory.ofFunctor p).p.IsHomLift (t ≫ f)
      (transitionTo ξ (Nat.le_max_left n (φ.level α)) ≫ i) := IsHomLift.comp p _ _ _ _
  have : (BasedCategory.ofFunctor p).p.IsHomLift (s ≫ φ.factor α)
      (transitionTo ξ (Nat.le_max_right n (φ.level α)) ≫ φ.pointInclusion α) :=
    IsHomLift.comp p _ _ _ _
  have h₁ := Deformation.map_classOf (BasedCategory.ofFunctor p) hp (t ≫ f)
    ⟨ξ.level _, ξ.level_eq _⟩ ⟨x, hx⟩ (transitionTo ξ (Nat.le_max_left n (φ.level α)) ≫ i)
  have h₂ := Deformation.map_classOf (BasedCategory.ofFunctor p) hp (s ≫ φ.factor α)
    ⟨ξ.level _, ξ.level_eq _⟩ ⟨φ.toBasedFunctor.obj α, φ.toBasedFunctor.w_obj α⟩
    (transitionTo ξ (Nat.le_max_right n (φ.level α)) ≫ φ.pointInclusion α)
  exact h₂.symm.trans (by rw [← hf]; exact h₁)

/-- The differential of a formal object is the class of the point it names. -/
public theorem derivationToTangent_eq_pointClass
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (P : ChosenPushforwards p) :
    letI : Algebra ξ.base k := (Deformation.residueHom ξ.base).toRingHom.toAlgebra
    ∀ d : Derivation Λ ξ.base k,
      Deformation.derivationToTangent hp ξ P d =
        pointClass hp ξ P (Deformation.artinianDualNumbers Λ k)
          ((Deformation.tangentSpaceDerivationsLinearEquiv ξ.base).symm d) :=
  fun _ => Deformation.mapIsomorphismClasses_classOf _ _ _ _

private lemma pointClass_injective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (P : ChosenPushforwards p)
    (h : Function.Bijective (Deformation.derivationToTangent hp ξ P)) :
    Function.Injective (pointClass hp ξ P (Deformation.artinianDualNumbers Λ k)) := by
  intro a b hab
  apply (Deformation.tangentSpaceDerivationsLinearEquiv ξ.base).injective
  apply h.1
  rwa [derivationToTangent_eq_pointClass hp ξ P, derivationToTangent_eq_pointClass hp ξ P,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

private lemma exists_dualNumberEmbedding
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (e : A ≃ₐ[Λ] DualNumber k) :
    ∃ f : A ⟶ Deformation.artinianDualNumbers.{u, w, v} Λ k,
      Function.Injective f.hom := by
  let : IsLocalRing (DualNumber k) := IsLocalRing.of_surjective' e.toRingHom e.surjective
  let rε : ResidueField (DualNumber k) ≃ₐ[Λ] k :=
    Deformation.residueEquivOfAugmentation (TrivSqZeroExt.fstHom Λ k k)
      TrivSqZeroExt.fst_surjective
  let σ : k ≃ₐ[Λ] k := rε.symm.trans ((ResidueField.mapAlgEquiv e).symm.trans A.residueEquiv)
  have hσ (a : A) : σ (e a).fst = A.residueEquiv (residue A a) := by
    have hr : rε (residue (DualNumber k) (e a)) = (e a).fst :=
      Deformation.residueEquivOfAugmentation_residue _ _ _
    rw [← hr]
    show A.residueEquiv ((ResidueField.mapAlgEquiv e).symm (rε.symm (rε _))) = _
    rw [rε.symm_apply_apply, ← ResidueField.mapAlgEquiv_residue e, AlgEquiv.symm_apply_apply]
  let D := Deformation.artinianDualNumbers.{u, w, v} Λ k
  let twist : DualNumber k →ₐ[Λ] D :=
    { toFun := fun x => ⟨σ x.fst, ⟨σ x.snd⟩⟩
      map_zero' := by
        apply TrivSqZeroExt.ext
        · exact map_zero σ
        · apply ULift.ext; exact map_zero σ
      map_one' := by
        apply TrivSqZeroExt.ext
        · exact map_one σ
        · apply ULift.ext; exact map_zero σ
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext
        · show σ (x.fst + y.fst) = σ x.fst + σ y.fst
          exact map_add σ _ _
        · apply ULift.ext
          show σ (x.snd + y.snd) = σ x.snd + σ y.snd
          exact map_add σ _ _
      map_mul' := by
        intro x y
        apply TrivSqZeroExt.ext
        · show σ (x.fst * y.fst) = σ x.fst * σ y.fst
          exact map_mul σ _ _
        · apply ULift.ext
          show σ (x.fst * y.snd + x.snd * y.fst) =
            σ x.fst * σ y.snd + σ y.fst * σ x.snd
          simp only [map_add, map_mul, mul_comm]
      commutes' := by
        intro r
        apply TrivSqZeroExt.ext
        · exact σ.commutes r
        · apply ULift.ext
          exact map_zero σ }
  let f : A ⟶ Deformation.artinianDualNumbers.{u, w, v} Λ k :=
    { hom := twist.comp e.toAlgHom
      isLocal := by
        constructor
        intro a ha
        let fst : D →+* k :=
          { toFun := TrivSqZeroExt.fst
            map_zero' := rfl
            map_one' := rfl
            map_add' := fun _ _ => rfl
            map_mul' := fun _ _ => rfl }
        have hf : IsUnit (σ (e a).fst) := ha.map fst
        have he : IsUnit (e a).fst := by
          simpa using hf.map σ.symm.toMonoidHom
        have he' : IsUnit (e a) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr he
        simpa using he'.map e.symm.toMonoidHom
      residue_comm := hσ }
  refine ⟨f, ?_⟩
  intro a b hab
  apply e.injective
  apply TrivSqZeroExt.ext
  · exact σ.injective (congrArg (fun x => x.fst) hab)
  · exact σ.injective (congrArg (fun x => x.snd.down) hab)

private lemma maps_to_dualNumbers_eq
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (hbij : Deformation.HasBijectiveDifferential hp ξ)
    {x : F} (e : p.obj x ≃ₐ[Λ] DualNumber k) (n : ℕ)
    (a b : ξ.level n ⟶ x) : p.map a = p.map b := by
  obtain ⟨P, hP⟩ := hbij
  let fa := eqToHom (ξ.level_eq n).symm ≫ p.map a
  let fb := eqToHom (ξ.level_eq n).symm ≫ p.map b
  have hla : p.IsHomLift fa a := IsHomLift.of_fac p fa a (ξ.level_eq n) rfl (by simp [fa])
  have hlb : p.IsHomLift fb b := IsHomLift.of_fac p fb b (ξ.level_eq n) rfl (by simp [fb])
  have hclasses : pointClass hp ξ P (p.obj x)
      (truncationPoint ξ.base n ≫ Deformation.artinianToComplete.map fa) =
      pointClass hp ξ P (p.obj x)
      (truncationPoint ξ.base n ≫ Deformation.artinianToComplete.map fb) :=
    (pointClass_of_lift hp ξ P n fa rfl a hla).trans
      (pointClass_of_lift hp ξ P n fb rfl b hlb).symm
  obtain ⟨j, hj⟩ := exists_dualNumberEmbedding (p.obj x) e
  have heq := pointClass_injective hp ξ P hP
    ((pointClass_naturality hp ξ P j _).trans
      ((congrArg (fun z => (Deformation.isomorphismClasses (BasedCategory.ofFunctor p) hp).map j z)
        hclasses).trans (pointClass_naturality hp ξ P j _).symm))
  have hfab : fa = fb := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact hj (congrArg (fun f => f.hom r) heq)
  have hh := congrArg (fun f => eqToHom (ξ.level_eq n) ≫ f) hfab
  simpa [fa, fb] using hh

add_to_stacks 06IV "part (1): condition (S1)" Deformation.schlessingerConditionS1_of_versal

/-- A versal formal object with bijective differential forces Schlessinger's
condition (S1). The bijectivity of the differential is not used. -/
@[stacks 06IV "part (1): condition (S1)"]
public theorem schlessingerConditionS1_of_versal_bijectiveDifferential
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : Deformation.IsPredeformationCategory p)
    (ξ : Deformation.FormalObject p)
    (hversal : Deformation.IsVersal hp.cofibered ξ)
    (_hbij : Deformation.HasBijectiveDifferential hp.cofibered ξ) :
    Deformation.SchlessingerConditionS1 p :=
  Deformation.schlessingerConditionS1_of_versal p hp ξ hversal

/-- A versal formal object with bijective differential forces Schlessinger's
condition (S2). -/
@[stacks 06IV "part (2): condition (S2)"]
public theorem schlessingerConditionS2_of_versal_bijectiveDifferential
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : Deformation.IsPredeformationCategory p)
    (ξ : Deformation.FormalObject p)
    (hversal : Deformation.IsVersal hp.cofibered ξ)
    (hbij : Deformation.HasBijectiveDifferential hp.cofibered ξ) :
    Deformation.SchlessingerConditionS2 p := by
  let hS1 := Deformation.schlessingerConditionS1_of_versal p hp ξ hversal
  refine ⟨?_, ?_⟩
  · intro x xε x₀ d e he Aε g gε hpb
    exact hS1.completion d e (surjective_of_isDualNumberProjection (p.map e) he)
      g gε hpb
  · intro x xε x₀ d e he Aε g gε hpb P Q
    let E := Deformation.restrictionCompletionEquivalence p hp.cofibered
    obtain ⟨X, hX, hiX, ⟨iX⟩⟩ :=
      exists_strict_representative p hp.cofibered E x
    let : E.can.IsEquivalence := E.isEquivalence
    let : E.can.Full := E.isEquivalence.full
    let : E.can.Faithful := E.isEquivalence.faithful
    have hg : Function.Surjective g.hom :=
      surjective_fst_of_isPullback_of_surjective_snd (p.map d) (p.map e)
        (surjective_of_isDualNumberProjection (p.map e) he) g gε hpb
    let u : ξ ⟶ X.snd := Classical.choice
      (Deformation.nonempty_hom_of_isVersal hp ξ X.snd hversal)
    have side : ∀ R : PullbackCompletion p d e g gε, ∃ n, ∀ m ≥ n,
        ∀ hmX : maximalIdeal X.fst ^ (m + 1) = ⊥, ∃ a : ξ.level m ⟶ R.apex,
          a ≫ R.toFirst = u.app m ≫ (E.objIsoLevel X m hmX).inv ≫ iX.hom := by
      intro R
      obtain ⟨XR, hXR, hiR, ⟨iR⟩⟩ := exists_strict_representative p hp.cofibered E R.apex
      let qR : XR ⟶ X := E.can.preimage (iR.hom ≫ R.toFirst ≫ iX.inv)
      have hqR : E.can.map qR = iR.hom ≫ R.toFirst ≫ iX.inv := by simp [qR]
      have hsurjR : Function.Surjective (p.map R.toFirst).hom := by
        rw [R.map_toFirst]
        exact surjective_hom_comp (eqToHom R.apex_eq) g
          (surjective_hom_of_isIso (eqToHom R.apex_eq)) hg
      obtain ⟨uR, huR⟩ := versal_lift_strict_representative p hp ξ hversal E hXR hX hiR hiX qR
        (surjective_fst_of_equivalence_preimage p E iR iX R.toFirst hsurjR qR hqR) u
      obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_bot XR.fst
      refine ⟨n, fun m hm hmX => ?_⟩
      let lR := E.objIsoLevel XR m (hn m hm)
      let lX := E.objIsoLevel X m hmX
      have happ : uR.app m ≫ qR.snd.app m = u.app m := congrArg (fun z : ξ ⟶ X.snd => z.app m) huR
      have hrel : qR.snd.app m ≫ lX.inv ≫ iX.hom = lR.inv ≫ iR.hom ≫ R.toFirst := by
        have hn' := congrArg (fun k => lR.inv ≫ k ≫ lX.inv ≫ iX.hom)
          (E.objIsoLevel_naturality qR m (hn m hm) hmX)
        calc
          qR.snd.app m ≫ lX.inv ≫ iX.hom =
              lR.inv ≫ lR.hom ≫ qR.snd.app m ≫ lX.inv ≫ iX.hom := by simp
          _ = lR.inv ≫ E.can.map qR ≫ lX.hom ≫ lX.inv ≫ iX.hom := by
                simpa [Category.assoc] using hn'.symm
          _ = lR.inv ≫ E.can.map qR ≫ iX.hom := by simp
          _ = lR.inv ≫ iR.hom ≫ R.toFirst := by rw [hqR]; simp [Category.assoc]
      refine ⟨uR.app m ≫ lR.inv ≫ iR.hom, ?_⟩
      rw [Category.assoc, Category.assoc, ← hrel, ← Category.assoc, happ]
    obtain ⟨nP, hnP⟩ := side P
    obtain ⟨nQ, hnQ⟩ := side Q
    obtain ⟨nX, hnX⟩ := exists_maximalIdeal_pow_eq_bot X.fst
    let m := nP + nQ + nX
    have hmX := hnX m (by omega)
    obtain ⟨aP, haP⟩ := hnP m (by omega) hmX
    obtain ⟨aQ, haQ⟩ := hnQ m (by omega) hmX
    have hfirst : aP ≫ P.toFirst = aQ ≫ Q.toFirst := haP.trans haQ.symm
    have hsecond : p.map (aP ≫ P.toSecond) = p.map (aQ ≫ Q.toSecond) :=
      maps_to_dualNumbers_eq hp.cofibered ξ hbij he.choose_spec.choose m _ _
    have hbase : p.map aP ≫ eqToHom P.apex_eq = p.map aQ ≫ eqToHom Q.apex_eq := by
      apply hpb.hom_ext
      · simpa only [Category.assoc, ← P.map_toSecond, ← Q.map_toSecond,
          ← Functor.map_comp] using hsecond
      · simpa only [Category.assoc, ← P.map_toFirst, ← Q.map_toFirst,
          ← Functor.map_comp] using congrArg p.map hfirst
    obtain ⟨b, hb, hab⟩ := cofibered_factor p hp.cofibered aP aQ
      (eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm) (by
        rw [← Category.assoc, hbase]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
    refine ⟨b, ?_, hb⟩
    obtain ⟨c, hc, huniq⟩ := existsUnique_factor_of_isHomLift hp.cofibered aP
      (aP ≫ P.toFirst) (p.map P.toFirst) (p.map_comp aP P.toFirst).symm
    have h₁ : P.toFirst = c := huniq _ ⟨rfl, rfl⟩
    have h₂ : b ≫ Q.toFirst = c := huniq _ ⟨by
      rw [Functor.map_comp, hb, Q.map_toFirst, P.map_toFirst]
      simp, by simpa only [← Category.assoc, hab] using hfirst.symm⟩
    exact h₁.trans h₂.symm

/-- The point of the functor prorepresented by `R` at the square-zero extension by
`k × k` whose two coordinates are two given tangent vectors. -/
public noncomputable def pairPoint
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (a b : Deformation.tangentSpaceArtinian Λ k (Deformation.restrictedCoyoneda R)) :
    (Deformation.restrictedCoyoneda R).obj
      ((Deformation.squareZeroExtensionArtinian Λ k).obj
        (FGModuleCat.of k (ULift.{v} k × ULift.{v} k))) := by
  have hfst (s : R) : (a.hom s).fst = (b.hom s).fst :=
    (a.residue_comm s).trans (b.residue_comm s).symm
  let B := (Deformation.squareZeroExtensionArtinian Λ k).obj
    (FGModuleCat.of k (ULift.{v} k × ULift.{v} k))
  let f : R →ₐ[Λ] B :=
    { toFun := fun s => ⟨(a.hom s).fst, ((a.hom s).snd, (b.hom s).snd)⟩
      map_zero' := by
        apply TrivSqZeroExt.ext
        · exact congrArg
            (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.fst) a.hom.map_zero
        · apply Prod.ext
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) a.hom.map_zero
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) b.hom.map_zero
      map_one' := by
        apply TrivSqZeroExt.ext
        · exact congrArg
            (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.fst) a.hom.map_one
        · apply Prod.ext
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) a.hom.map_one
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) b.hom.map_one
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext
        · exact congrArg
            (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.fst) (a.hom.map_add x y)
        · apply Prod.ext
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) (a.hom.map_add x y)
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) (b.hom.map_add x y)
      map_mul' := by
        intro x y
        apply TrivSqZeroExt.ext
        · exact congrArg
            (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.fst) (a.hom.map_mul x y)
        · apply Prod.ext
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) (a.hom.map_mul x y)
          · change (b.hom (x * y)).snd = (a.hom x).fst • (b.hom y).snd +
              (a.hom y).fst • (b.hom x).snd
            rw [hfst, hfst]
            exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) (b.hom.map_mul x y)
      commutes' := by
        intro r
        apply TrivSqZeroExt.ext
        · exact congrArg
            (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.fst) (a.hom.commutes r)
        · apply Prod.ext
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) (a.hom.commutes r)
          · exact congrArg
              (fun z : Deformation.artinianDualNumbers.{u, w, v} Λ k => z.snd) (b.hom.commutes r) }
  let g : B ⟶ Deformation.artinianDualNumbers Λ k :=
    (Deformation.squareZeroExtensionArtinian Λ k).map
      (FGModuleCat.ofHom (LinearMap.fst k (ULift.{v} k) (ULift.{v} k)))
  have hga (s : R) : g.hom (f s) = a.hom s := by
    let mP : Module kᵐᵒᵖ (ULift.{v} k × ULift.{v} k) := Module.compHom _
      { toFun := MulOpposite.unop
        map_one' := rfl
        map_mul' := by simp [mul_comm]
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let mU : Module kᵐᵒᵖ (ULift.{v} k) := Module.compHom _
      { toFun := MulOpposite.unop
        map_one' := rfl
        map_mul' := by simp [mul_comm]
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let : SMul kᵐᵒᵖ (ULift.{v} k × ULift.{v} k) := mP.toSMul
    let : SMul kᵐᵒᵖ (ULift.{v} k) := mU.toSMul
    let : @IsCentralScalar k (ULift.{v} k × ULift.{v} k) inferInstance mP.toSMul :=
      ⟨fun _ _ => rfl⟩
    let : @IsCentralScalar k (ULift.{v} k) inferInstance mU.toSMul :=
      ⟨fun _ _ => rfl⟩
    apply TrivSqZeroExt.ext
    · exact TrivSqZeroExt.fst_map _ _
    · exact TrivSqZeroExt.snd_map _ _
  exact
    { hom := f
      isLocal := ⟨fun s hs => a.isLocal.map_nonunit s ((hga s) ▸ (hs.map g.hom.toRingHom))⟩
      residue_comm := a.residue_comm }

/-- Two tangent vectors of a prorepresentable functor agree as soon as their square-zero
components agree at every element. -/
public theorem tangentPoint_ext
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    {a b : Deformation.tangentSpaceArtinian Λ k (Deformation.restrictedCoyoneda R)}
    (h : ∀ r : R, (a.hom r).snd.down = (b.hom r).snd.down) : a = b := by
  let : Algebra R k :=
    (Deformation.residueHom R).toRingHom.toAlgebra
  apply (Deformation.tangentSpaceDerivationsLinearEquiv R).injective
  apply Derivation.ext
  intro r
  simpa only [Deformation.tangentSpaceDerivationsLinearEquiv_apply]
    using h r

/-- A family of maps from the square-zero points of `R` into the values of an additive
`k`-linear functor on finitely generated modules, natural in the module, is a `k`-linear map
on the tangent space of the functor prorepresented by `R`. -/
public noncomputable def linearMapOfPointNaturality
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (L : FGModuleCat.{max v w} k ⥤ ModuleCat.{uF} k) [L.Additive] [L.Linear k]
    (η : ∀ V : FGModuleCat.{max v w} k,
      (Deformation.restrictedCoyoneda R).obj ((Deformation.squareZeroExtensionArtinian Λ k).obj V) →
        L.obj V)
    (hη : ∀ {V W : FGModuleCat.{max v w} k} (f : V ⟶ W) a,
      η W (a ≫ Deformation.artinianToComplete.map
          ((Deformation.squareZeroExtensionArtinian Λ k).map f)) =
        (L.map f) (η V a)) :
    Deformation.tangentSpaceArtinian Λ k (Deformation.restrictedCoyoneda R) →ₗ[k]
      L.obj (FGModuleCat.of k (ULift.{v} k)) where
  toFun := η _
  map_add' a b := by
    let V := FGModuleCat.of k (ULift.{v} k)
    let W := FGModuleCat.of k (ULift.{v} k × ULift.{v} k)
    let π₁ : W ⟶ V := FGModuleCat.ofHom (LinearMap.fst k _ _)
    let π₂ : W ⟶ V := FGModuleCat.ofHom (LinearMap.snd k _ _)
    let S := Deformation.squareZeroExtensionArtinian Λ k
    let c := pairPoint R a b
    have hc₁ : c ≫ Deformation.artinianToComplete.map (S.map π₁) = a := by
      apply tangentPoint_ext R
      intro r
      exact congrArg ULift.down (TrivSqZeroExt.snd_map π₁.hom.hom (c.hom r))
    have hc₂ : c ≫ Deformation.artinianToComplete.map (S.map π₂) = b := by
      apply tangentPoint_ext R
      intro r
      exact congrArg ULift.down (TrivSqZeroExt.snd_map π₂.hom.hom (c.hom r))
    have hc : c ≫ Deformation.artinianToComplete.map (S.map (π₁ + π₂)) = a + b := by
      apply tangentPoint_ext R
      intro r
      have hh := congrArg (fun d => d r)
        ((Deformation.tangentSpaceDerivationsLinearEquiv R).map_add a b)
      simp only [Derivation.add_apply,
        Deformation.tangentSpaceDerivationsLinearEquiv_apply] at hh
      exact (congrArg ULift.down
        (TrivSqZeroExt.snd_map (π₁ + π₂).hom.hom (c.hom r))).trans hh.symm
    rw [← hc, hη, L.map_add]
    change (L.map π₁) (η W c) + (L.map π₂) (η W c) = _
    rw [← hη, ← hη, hc₁, hc₂]
  map_smul' r a := by
    let V := FGModuleCat.of k (ULift.{v} k)
    let S := Deformation.squareZeroExtensionArtinian Λ k
    have hc : a ≫ Deformation.artinianToComplete.map (S.map (r • 𝟙 V)) = r • a := by
      apply tangentPoint_ext R
      intro x
      have hh := congrArg (fun d => d x)
        ((Deformation.tangentSpaceDerivationsLinearEquiv R).map_smul r a)
      simp only [Derivation.smul_apply,
        Deformation.tangentSpaceDerivationsLinearEquiv_apply] at hh
      exact (congrArg ULift.down
        (TrivSqZeroExt.snd_map (r • 𝟙 V).hom.hom (a.hom x))).trans hh.symm
    rw [← hc, hη, L.map_smul, L.map_id]
    rfl

/-- The class of the pushforward of `ξ` along a square-zero point, read inside the module
supplied by a linear lift of the associated isomorphism-class functor. -/
public noncomputable def pointToModule
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (P : ChosenPushforwards p)
    (L : Deformation.LinearFunctorLift k (Deformation.squareZeroExtensionArtinian Λ k ⋙
      Deformation.isomorphismClasses (BasedCategory.ofFunctor p) hp))
    (V : FGModuleCat.{max v w} k)
    (a : (Deformation.restrictedCoyoneda ξ.base).obj
      ((Deformation.squareZeroExtensionArtinian Λ k).obj V)) : L.functor.obj V :=
    (eqToHom L.forget_comp.symm).app V (pointClass hp ξ P _ a)

/-- Reading the class of a pushforward inside the module of a linear lift is natural in the
finitely generated module. -/
public theorem pointToModule_naturality
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (P : ChosenPushforwards p)
    (L : Deformation.LinearFunctorLift k (Deformation.squareZeroExtensionArtinian Λ k ⋙
      Deformation.isomorphismClasses (BasedCategory.ofFunctor p) hp))
    {V W : FGModuleCat.{max v w} k} (f : V ⟶ W) a :
    pointToModule hp ξ P L W (a ≫ Deformation.artinianToComplete.map
      ((Deformation.squareZeroExtensionArtinian Λ k).map f)) =
        (L.functor.map f) (pointToModule hp ξ P L V a) := by
  have h := ConcreteCategory.congr_hom ((eqToHom L.forget_comp.symm).naturality f)
    (pointClass hp ξ P _ a)
  dsimp only [pointToModule]
  rw [pointClass_naturality]
  exact h

private noncomputable def moduleDataEquiv
    {k : Type w} [Field k] {α β : Type uF} (e : α = β)
    (D : Σ G : AddCommGroup α, letI := G; Module k α) :
    letI := D.1
    letI := D.2
    let E : Σ G : AddCommGroup β, letI := G; Module k β := e.rec D
    letI := E.1
    letI := E.2
    α ≃ₗ[k] β := by
  cases e
  letI := D.1
  letI := D.2
  exact LinearEquiv.refl k α

/-- A versal formal object with bijective differential has a
finite-dimensional tangent space. -/
@[stacks 06IV "part (3): finite-dimensional tangent space"]
public theorem finiteDimensional_tangentSpace_of_versal_bijectiveDifferential
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (𝓕 : BasedCategory.{vF, uF} (Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hp : Deformation.IsPredeformationCategory 𝓕.p)
    (ξ : Deformation.FormalObject 𝓕.p)
    (hversal : Deformation.IsVersal hp.cofibered ξ)
    (hbij : Deformation.HasBijectiveDifferential hp.cofibered ξ) :
    let hS2 := schlessingerConditionS2_of_versal_bijectiveDifferential
      𝓕.p hp ξ hversal hbij
    let hAssocS2 :=
      Deformation.schlessingerConditionS2_of_isIsomorphismClasses
        𝓕 hp.cofibered hS2 (Or.inl hp)
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hp.cofibered))) :=
      ⟨hAssocS2⟩
    FiniteDimensional k
      (Deformation.tangentSpaceArtinian Λ k
        (Deformation.isomorphismClasses 𝓕 hp.cofibered)) := by
  dsimp only
  let hS2 := schlessingerConditionS2_of_versal_bijectiveDifferential
    𝓕.p hp ξ hversal hbij
  let hAssocS2 :=
    Deformation.schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 hp.cofibered hS2 (Or.inl hp)
  let : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  let : Fact (Deformation.SchlessingerConditionS2
    (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hp.cofibered))) := ⟨hAssocS2⟩
  let L := Deformation.associatedTangentSpaceModuleStructure 𝓕 hp hAssocS2
  obtain ⟨P, hP⟩ := hbij
  let f := linearMapOfPointNaturality ξ.base L.functor
    (pointToModule hp.cofibered ξ P L) (pointToModule_naturality hp.cofibered ξ P L)
  have hsurj : Function.Surjective f := by
    intro y
    let V := FGModuleCat.of k (ULift.{v} k)
    let z := (eqToHom L.forget_comp).app V y
    obtain ⟨d, hd⟩ := hP.2 z
    let E := Deformation.tangentSpaceDerivationsLinearEquiv ξ.base
    have hpoint : Deformation.derivationToTangent hp.cofibered ξ P d =
        pointClass hp.cofibered ξ P _ (E.symm d) :=
      derivationToTangent_eq_pointClass hp.cofibered ξ P d
    refine ⟨E.symm d, ?_⟩
    show (eqToHom L.forget_comp.symm).app V
      (pointClass hp.cofibered ξ P _ (E.symm d)) = y
    rw [← hpoint, hd]
    show ((eqToHom L.forget_comp ≫ eqToHom L.forget_comp.symm).app V) y = y
    simp only [eqToHom_trans, eqToHom_refl, NatTrans.id_app, types_id_apply]
  let := Deformation.tangentSpace_finiteDimensional ξ.base
  let := Module.Finite.of_surjective f hsurj
  let M := L.functor.obj (FGModuleCat.of k (ULift.{v} k))
  let e := Deformation.associatedTangentSpaceModuleStructure_carrier 𝓕 hp hAssocS2
  let D : Σ G : AddCommGroup (M : Type uF), let := G; Module k (M : Type uF) :=
    ⟨M.isAddCommGroup, M.isModule⟩
  exact Module.Finite.equiv (moduleDataEquiv e D)


end Deformation
