module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Completion
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.EssentiallySurjective
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksCore.Tactic.StacksAttribute

/-!
# A versal formal object maps to every formal object

In a predeformation category, a versal formal object is quasi-initial among
formal objects: it admits a morphism to each formal object.

## Main results

* `Deformation.adicTruncation_maximalIdeal_pow`: the maximal ideal of an adic truncation is
  nilpotent with the expected exponent.
* `Deformation.nonempty_hom_completionMap_obj` gives a morphism from a formal object to the
  image, under the completion of its own associated morphism, of any formal object of the
  functor it prorepresents.
* `Deformation.nonempty_hom_of_isVersal` gives a morphism from a versal formal
  object to any formal object.

## Implementation notes

The existence of a morphism is expressed by `Nonempty (ξ ⟶ η)`; the morphism
includes its map between the underlying complete local algebras.

The morphism associated to a formal object is a `BasedFunctor` out of
`BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base))`, so
its values are indexed by objects of that based category rather than by elements
of `restrictedCoyoneda ξ.base`. The two index types agree only after unfolding
`BasedCategory.ofFunctor`, which is why that definition is made locally
`implicit_reducible` here.

## References

* [Stacks Project, Tag 06HT](https://stacks.math.columbia.edu/tag/06HT)
-/

@[expose] public section

namespace Deformation

open CategoryTheory
open IsLocalRing

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v w uF vF

/-- The Artinian algebra underlying level `n` of a formal object of a restricted
representable functor is the `n`-th adic truncation of its base. -/
public theorem sourceLevelEq
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject (Functor.Elements.π (restrictedCoyoneda R)))
    (n : ℕ) : (X.level n).1 = AdicTruncation.obj X.base n :=
  X.level_eq n

/-- The maximal ideal of the `n`-th adic truncation of a complete local algebra is nilpotent
with exponent `n + 1`. -/
public theorem adicTruncation_maximalIdeal_pow
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    maximalIdeal (AdicTruncation.obj R n) ^ (n + 1) = ⊥ := by
  let I := AdicTruncation.ideal R n
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hI : I < ⊤ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  change maximalIdeal (R ⧸ I) ^ (n + 1) = ⊥
  rw [← IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

private noncomputable def sourceAdicSection
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject (Functor.Elements.π (restrictedCoyoneda R))) :
    AdicSection
      (artinianToComplete ⋙ coyoneda.obj (Opposite.op R)) X.base where
  value n := (restrictedCoyoneda R).map
    (eqToHom (sourceLevelEq X n)) (X.level n).2
  compatible n := by
    let q := Functor.Elements.π (restrictedCoyoneda R)
    let f := (AdicTruncation.transitionNat n).app X.base
    let a := X.transition n
    have h₁ := sourceLevelEq X (n + 1)
    have h₀ := sourceLevelEq X n
    let := X.transition_lift n
    have hbase := IsHomLift.fac' q f a
    have hcomp : eqToHom h₁ ≫ f = a.hom ≫ eqToHom h₀ := by
      simpa [q, a, f] using (congrArg (· ≫ eqToHom h₀) hbase).symm
    change (restrictedCoyoneda R).map f ((restrictedCoyoneda R).map (eqToHom h₁) _) = _
    rw [← Functor.map_comp_apply, hcomp, Functor.map_comp_apply]
    exact congrArg _ (X.transition n).map_val

private lemma associated_pointInclusion_lift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {ξ : FormalObject p}
    {pushforwards : ChosenPushforwards p}
    (M : AssociatedMorphism ξ pushforwards)
    (α : (restrictedCoyoneda ξ.base).Elements) :
    p.IsHomLift (M.factor α) (M.pointInclusion α) := by
  apply (IsHomLift.eqToHom_comp_lift_iff p (M.factor α) (M.pointInclusion α)
    (M.obj_eq α)).mp
  rw [M.pointInclusion_eq]
  exact (pushforwards (M.factor α)).cocartesian _ |>.toIsHomLift

private noncomputable def sourceBaseMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject (Functor.Elements.π (restrictedCoyoneda R))) :
    R ⟶ X.base :=
  (coyonedaIsoAdicCompletion R).inv.app X.base
    (sourceAdicSection X)

private theorem sourceBaseMap_quotient
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject (Functor.Elements.π (restrictedCoyoneda R)))
    (n : ℕ) :
    (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal X.base n)).comp
        (sourceBaseMap X).hom =
      (artinianToComplete.map (eqToHom (sourceLevelEq X n))).hom.comp
        (X.level n).2.hom := by
  have hs : (coyonedaIsoAdicCompletion R).hom.app X.base (sourceBaseMap X) =
      sourceAdicSection X := by
    change ((coyonedaIsoAdicCompletion R).inv.app X.base ≫
      (coyonedaIsoAdicCompletion R).hom.app X.base) (sourceAdicSection X) =
        sourceAdicSection X
    rw [(coyonedaIsoAdicCompletion R).inv_hom_id_app X.base]
    rfl
  have h := congrArg (fun s => (s.value n).hom) hs
  rw [coyonedaIsoAdicCompletion_hom_apply] at h
  rw [h]
  exact restrictedCoyoneda_map_hom (eqToHom (sourceLevelEq X n)) (X.level n).2

/-- A formal object admits a morphism to the image, under the completion of its own associated
morphism, of every formal object of the functor it prorepresents. -/
public theorem nonempty_hom_completionMap_obj
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (P : ChosenPushforwards p)
    (X : FormalObject (Functor.Elements.π (restrictedCoyoneda ξ.base))) :
    Nonempty (ξ ⟶ (completionMap (associatedMorphism hp ξ P).toBasedFunctor).obj X) := by
  classical
  let M := associatedMorphism hp ξ P
  let φ := M.toBasedFunctor
  let X₀ : FormalObject (Functor.Elements.π
      (restrictedCoyoneda ξ.base)) := X
  let f := sourceBaseMap X₀
  have hlevel (n : ℕ) : M.level (X₀.level n) ≤ n := by
    apply (M.factor_spec (X₀.level n)).2.1
    rw [sourceLevelEq X₀ n]
    exact adicTruncation_maximalIdeal_pow X₀.base n
  choose t ht using fun n => transitionTo_lift ξ (hlevel n)
  have hbase_map (n : ℕ) :
      AdicTruncation.map f n =
        t n ≫
          M.factor (X₀.level n) ≫ eqToHom (sourceLevelEq X₀ n) := by
    let αn := X₀.level n
    have hq :
        (AdicTruncation.map f n).hom.comp
            (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n)) =
          (artinianToComplete.map (eqToHom (sourceLevelEq X₀ n))).hom.comp
            αn.2.hom :=
      sourceBaseMap_quotient X₀ n
    have htq :
        ((t n).hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n))) =
          Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base (M.level αn)) := (ht n).1
    have hright :
        (t n ≫ M.factor αn ≫ eqToHom (sourceLevelEq X₀ n)).hom.comp
            (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n)) =
          (artinianToComplete.map (eqToHom (sourceLevelEq X₀ n))).hom.comp
            αn.2.hom := by
      change ((artinianToComplete.map (eqToHom (sourceLevelEq X₀ n))).hom).comp
          ((M.factor αn).hom.comp
            ((t n).hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n)))) = _
      rw [htq, (M.factor_spec αn).2.2]
    refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun z => ?_)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact congrArg (fun g => g r) (hq.trans hright.symm)
  let T : FormalObject p := (completionMap φ).obj X₀
  let app₀ (n : ℕ) : ξ.level n ⟶ φ.obj (X₀.level n) :=
    transitionTo ξ (hlevel n) ≫
      M.pointInclusion (X₀.level n)
  let app (n : ℕ) : ξ.level n ⟶ T.level n :=
    app₀ n ≫ eqToHom (completionMap_obj_level φ X₀ n).symm
  have happ_lift (n : ℕ) : p.IsHomLift (AdicTruncation.map f n) (app n) := by
    have hpoint := associated_pointInclusion_lift M (X₀.level n)
    have := (ht n).2
    have h₀ : p.IsHomLift (t n ≫ M.factor (X₀.level n)) (app₀ n) :=
      IsHomLift.comp p (t n) (M.factor (X₀.level n))
        (transitionTo ξ (hlevel n))
        (M.pointInclusion (X₀.level n))
    have happCast : p.IsHomLift
        ((t n ≫ M.factor (X₀.level n)) ≫ eqToHom (sourceLevelEq X₀ n)) (app n) := by
      refine (IsHomLift.eqToHom_comp_lift_iff p
        ((t n ≫ M.factor (X₀.level n)) ≫ eqToHom (sourceLevelEq X₀ n)) (app₀ n)
        (completionMap_obj_level φ X₀ n).symm).mpr ?_
      exact (IsHomLift.lift_comp_eqToHom_iff p (t n ≫ M.factor (X₀.level n)) (app₀ n)
        (sourceLevelEq X₀ n)).mpr h₀
    simpa only [hbase_map n, Category.assoc] using happCast
  have hstep (n : ℕ) : ξ.transition n = transitionTo ξ (Nat.le_succ n) := by
    simpa [transitionTo_self] using (transitionTo_succ ξ (le_refl n)).symm
  have happ₀_natural (n : ℕ) :
      ξ.transition n ≫ app₀ n =
        app₀ (n + 1) ≫ M.toBasedFunctor.map (X₀.transition n) := by
    have hm : max (M.level (X₀.level (n + 1))) (M.level (X₀.level n)) ≤ n + 1 :=
      max_le (hlevel (n + 1)) ((hlevel n).trans (Nat.le_succ n))
    have hk₁ : M.level (X₀.level (n + 1)) ≤
        max (M.level (X₀.level (n + 1))) (M.level (X₀.level n)) := Nat.le_max_left _ _
    have hk₀ : M.level (X₀.level n) ≤
        max (M.level (X₀.level (n + 1))) (M.level (X₀.level n)) := Nat.le_max_right _ _
    have hhigh :
        transitionTo ξ hm ≫
            transitionTo ξ hk₁ =
          transitionTo ξ (hlevel (n + 1)) :=
      transitionTo_comp ξ hk₁ hm
    have hlowUp : M.level (X₀.level n) ≤ n + 1 := (hlevel n).trans (Nat.le_succ n)
    have hlow :
        transitionTo ξ hm ≫
            transitionTo ξ hk₀ =
          transitionTo ξ hlowUp :=
      transitionTo_comp ξ hk₀ hm
    have hcomm := M.map_pointInclusion (X₀.transition n)
    calc
      ξ.transition n ≫ app₀ n =
          transitionTo ξ hlowUp ≫
            M.pointInclusion (X₀.level n) := by
              change ξ.transition n ≫ transitionTo ξ (hlevel n) ≫
                M.pointInclusion (X₀.level n) = _
              rw [← Category.assoc, hstep n, transitionTo_comp ξ (hlevel n) (Nat.le_succ n)]
      _ = transitionTo ξ hm ≫
            (transitionTo ξ hk₀ ≫
              M.pointInclusion (X₀.level n)) := by
                rw [← hlow, Category.assoc]
      _ = transitionTo ξ hm ≫
            (transitionTo ξ hk₁ ≫
              M.pointInclusion (X₀.level (n + 1)) ≫
                M.toBasedFunctor.map (X₀.transition n)) :=
          congrArg (fun t => transitionTo ξ hm ≫ t) hcomm.symm
      _ = app₀ (n + 1) ≫ M.toBasedFunctor.map (X₀.transition n) := by
              change _ = (transitionTo ξ (hlevel (n + 1)) ≫
                M.pointInclusion (X₀.level (n + 1))) ≫
                  M.toBasedFunctor.map (X₀.transition n)
              rw [← hhigh]
              simp only [Category.assoc]
  have happ_natural (n : ℕ) :
      ξ.transition n ≫ app n = app (n + 1) ≫ T.transition n := by
    rw [completionMap_obj_transition φ X₀ n]
    dsimp only [app]
    calc
      ξ.transition n ≫ app₀ n ≫
          eqToHom (completionMap_obj_level φ X₀ n).symm =
        (app₀ (n + 1) ≫ φ.map (X₀.transition n)) ≫
          eqToHom (completionMap_obj_level φ X₀ n).symm := by
            rw [← Category.assoc, happ₀_natural n]
      _ = (app₀ (n + 1) ≫
          eqToHom (completionMap_obj_level φ X₀ (n + 1)).symm) ≫
          (eqToHom (completionMap_obj_level φ X₀ (n + 1)) ≫
            φ.map (X₀.transition n) ≫
            eqToHom (completionMap_obj_level φ X₀ n).symm) := by
              simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
                Category.id_comp]
  have hbaseT : T.base = X₀.base := completionMap_obj_base φ X₀
  let fT : ξ.base ⟶ T.base := f ≫ eqToHom hbaseT.symm
  let g : ξ ⟶ T :=
    { base := fT
      app := app
      app_lift := by
        intro n
        let q := AdicTruncation.functor (Λ := Λ) (k := k) n
        have : p.IsHomLift (q.map f) (app n) := happ_lift n
        have hfac := IsHomLift.fac p (q.map f) (app n)
        apply IsHomLift.of_fac p (q.map fT) (app n) (ξ.level_eq n) (T.level_eq n)
        calc
          q.map fT = q.map f ≫ eqToHom (congrArg q.obj hbaseT.symm) := by
            rw [q.map_comp, eqToHom_map]
          _ = (eqToHom (IsHomLift.domain_eq p (q.map f) (app n)).symm ≫
              p.map (app n) ≫
              eqToHom (IsHomLift.codomain_eq p (q.map f) (app n))) ≫
              eqToHom (congrArg q.obj hbaseT.symm) := by rw [← hfac]
          _ = eqToHom (ξ.level_eq n).symm ≫ p.map (app n) ≫
              eqToHom (T.level_eq n) := by simp [Category.assoc]
      naturality := happ_natural }
  exact ⟨g⟩

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- A versal formal object admits a morphism to every formal object. -/
@[stacks 06HT]
public theorem nonempty_hom_of_isVersal (hp : IsPredeformationCategory p)
    (ξ η : FormalObject p) (hξ : IsVersal hp.cofibered ξ) :
    Nonempty (ξ ⟶ η) := by
  classical
  let push := chosenPushforwardsOfCofibered p hp.cofibered
  let M := associatedMorphism hp.cofibered ξ push
  let φ := M.toBasedFunctor
  let K := residueFieldObject Λ k
  let α : (restrictedCoyoneda ξ.base).Elements :=
    (restrictedCoyoneda ξ.base).elementsMk K (residuePoint ξ.base)
  let sourceProjection := Functor.Elements.π (restrictedCoyoneda ξ.base)
  let x : sourceProjection.Fiber K := ⟨α, rfl⟩
  have h₀ : (fiberFunctor φ K).EssSurj := by
    let E := Classical.choice hp.specialFiber
    refine ⟨fun y => ?_⟩
    let x' := (fiberFunctor φ K).obj x
    have hinv : E.inverse.obj (E.functor.obj x') = E.inverse.obj (E.functor.obj y) :=
      congrArg E.inverse.obj (Subsingleton.elim _ _)
    exact ⟨x, ⟨E.unitIso.app x' ≪≫ eqToIso hinv ≪≫ (E.unitIso.app y).symm⟩⟩
  have hess := completionMap_essSurj_of_isSmooth_of_fiber_essSurj φ hp.cofibered
    (hξ push) h₀
  obtain ⟨X, ⟨i⟩⟩ := hess.mem_essImage η
  obtain ⟨g⟩ := nonempty_hom_completionMap_obj hp.cofibered ξ push X
  exact ⟨g ≫ i.hom⟩

end Deformation
