module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.FormalObject.RestrictionEquivalence
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.FormalObject.YonedaEquivalence
public import StacksFrontier.Deformation.Smooth.Versal

/-!
# Intrinsic lifting criterion for a versal formal object (Stacks 06HS)

A formal object is versal precisely when every diagram from it to a formal object over an
Artinian algebra lifts across a surjective map of Artinian algebras. It suffices to test
small extensions. This criterion also shows that smoothness of the morphism associated to a
formal object does not depend on the chosen pushforwards.

Versality is *defined* as smoothness of the associated morphism for every choice of
pushforwards, so the content of the tag is that smoothness of that morphism can be read off
the formal objects alone. The Stacks proof, carried out here, goes through the Yoneda
equivalence of Stacks 06SK/06HC: a lifting problem for the associated morphism over a
surjection `B → A` of Artinian algebras is, under that equivalence, a lifting problem for
formal objects, because every object of the restricted coyoneda category of `ξ.base` over an
Artinian algebra extends to a formal object over it (Stacks 06SJ identifies the restriction
of the completion with the completion of the restriction). Reduction to small extensions is
Stacks 06GE, which factors any surjection of Artinian local algebras into a finite chain of
small extensions. Independence of the pushforwards follows because two associated morphisms
for different choices are isomorphic over the base.

## Main results

* `Deformation.isVersal_iff_lifts_artinian`: **Stacks 06HS**, the intrinsic lifting
  criterion.
* `Deformation.isVersal_iff_lifts_smallExtensions`: **Stacks 06HS**, the criterion
  restricted to small extensions.
* `Deformation.isSmooth_associatedMorphism_iff_isVersal`: **Stacks 06HS**, independence of
  the chosen pushforwards.

## Implementation notes

An Artinian algebra is regarded as a complete local algebra by the canonical inclusion.
`IsHomLift` records both endpoints of the arrow in the completion and its prescribed
Artinian base map. The lifting criterion uses the entire commutative triangle in the
category of formal objects.

## References

* [Stacks Project, Tag 06HS](https://stacks.math.columbia.edu/tag/06HS)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w uF vF
universe u₁ v₁ u₂ v₂
universe u₃ v₃ u₄ v₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

private lemma smooth_of_iso
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {φ ψ : BasedFunctor 𝓕 𝓖} (e : φ ≅ ψ)
    (hφ : IsSmooth φ) : IsSmooth ψ := by
  intro B A f hf y x g hg
  let g' := g ≫ e.inv.app x
  have hg' : 𝓖.p.IsHomLift f g' := by
    have : 𝓖.p.IsHomLift (𝟙 A) (e.inv.app x) :=
      e.inv.isHomLift ((BasedFunctor.w_obj ψ x).symm.trans
        (IsHomLift.codomain_eq 𝓖.p f g))
    exact IsHomLift.comp_lift_id_right' (p := 𝓖.p) f g A (e.inv.app x)
  obtain ⟨x', h, a, hh, ha, heq⟩ := hφ f hf y x g' hg'
  refine ⟨x', h, e.inv.app x' ≫ a, hh, ?_, ?_⟩
  · have : 𝓖.p.IsHomLift (𝟙 B) (e.inv.app x') :=
      e.inv.isHomLift (IsHomLift.domain_eq 𝓕.p f h)
    simpa using IsHomLift.comp 𝓖.p (𝟙 B) (𝟙 B) (e.inv.app x') a
  · dsimp [g'] at heq
    apply (cancel_mono (e.inv.app x)).1
    calc
      ψ.map h ≫ e.inv.app x = e.inv.app x' ≫ φ.map h := e.inv.naturality h
      _ = ((e.inv.app x' ≫ a) ≫ g) ≫ e.inv.app x := by
        rw [heq]
        simp [Category.assoc]

private def basedFunctor_iso_of_images_iso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (E : C ≌ D) {φ ψ : C}
    (h : E.functor.obj φ ≅ E.functor.obj ψ) : φ ≅ ψ :=
  E.fullyFaithfulFunctor.preimageIso h

/-- For `q.op` fibered in groupoids, an arrow is invertible when its image under `q` is. -/
private lemma isIso_of_fibered_map_isIso
    {C : Type u₃} [Category.{v₃} C] {P : Type u₄} [Category.{v₄} P]
    (q : P ⥤ C) (hq : q.op.IsFiberedInGroupoids) {x y : P} (a : x ⟶ y)
    (h : IsIso (q.map a)) : IsIso a := by
  let : IsIso (q.op.map a.op) := isIso_op (q.map a)
  let : q.op.IsStronglyCartesian (q.op.map a.op) a.op := hq.isStronglyCartesian a.op
  have : IsIso a.op :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := q.op)
      (f := q.op.map a.op) a.op
  exact isIso_of_op a

private lemma lift_iso
    {C : Type u} [Category.{v} C] {P : Type uF} [Category.{vF} P]
    (q : P ⥤ C) (hq : q.op.IsFiberedInGroupoids)
    {R S : C} (e : R ≅ S) {x : P} (hx : q.obj x = S) :
    ∃ (y : P) (l : y ⟶ x), q.IsHomLift e.hom l ∧ IsIso l := by
  subst S
  obtain ⟨yop, lop, hlop⟩ := hq.exists_lift e.inv.op (Opposite.op x) rfl
  let y := Opposite.unop yop
  have hy : q.obj y = R := by
    simpa [y] using congrArg Opposite.unop (IsHomLift.domain_eq q.op e.inv.op lop)
  subst R
  let m : x ⟶ y := lop.unop
  have hmap : q.map m = e.inv :=
    congrArg Quiver.Hom.unop (IsHomLift.eq_of_isHomLift q.op e.inv.op lop).symm
  let : IsIso m := isIso_of_fibered_map_isIso q hq m (hmap ▸ inferInstance)
  have hm : q.IsHomLift e.inv m := hmap ▸ IsHomLift.map q m
  have hl : q.IsHomLift e.hom (inv m) := by
    simpa using IsHomLift.inv q e.inv m
  exact ⟨y, inv m, hl, inferInstance⟩

private lemma isIso_of_lift_iso
    {C : Type u₃} [Category.{v₃} C] {P : Type u₄} [Category.{v₄} P]
    (q : P ⥤ C) (hq : q.op.IsFiberedInGroupoids)
    {R S : C} (f : R ≅ S) {x y : P} (a : x ⟶ y)
    (ha : q.IsHomLift f.hom a) : IsIso a := by
  have hdom : q.obj x = R := IsHomLift.domain_eq q f.hom a
  have hcod : q.obj y = S := IsHomLift.codomain_eq q f.hom a
  subst R S
  refine isIso_of_fibered_map_isIso q hq a ?_
  rw [IsHomLift.fac' q f.hom a]
  infer_instance

private lemma formal_transition_isIso
    (hp : IsCofiberedInGroupoids p) (X : FormalObject p) (n : ℕ)
    (hbase : IsIso ((AdicTruncation.transitionNat n).app X.base)) :
    IsIso (X.transition n) := by
  exact isIso_of_lift_iso p hp (asIso ((AdicTruncation.transitionNat n).app X.base))
    (X.transition n) (X.transition_lift n)

private lemma lifts_small_chain
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (hsmall : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ {y x : FormalObject p} (g : y ⟶ x),
        (FormalObject.projection (p := p)).IsHomLift
          (artinianToComplete.map f) g →
        ∀ a : ξ ⟶ x, ∃ b : ξ ⟶ y, b ≫ g = a)
    {n : ℕ} (D : ComposableArrows (ArtinianLocalAlgCat.{u, v, w} Λ k) n)
    (hD : ∀ (i : ℕ) (hi : i < n), InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom
        (D.map' i (i + 1) (Nat.le_succ i) (Nat.succ_le_of_lt hi)).hom.toRingHom)) :
    ∀ {y x : FormalObject p} (g : y ⟶ x),
      (FormalObject.projection (p := p)).IsHomLift
        (artinianToComplete.map D.hom) g →
      ∀ a : ξ ⟶ x, ∃ b : ξ ⟶ y, b ≫ g = a := by
  induction n with
  | zero =>
      intro y x g hg a
      let q := FormalObject.projection (p := p)
      let hqp := formalObjectProjection_isCofiberedInGroupoids p hp
      have hgid : q.IsHomLift (𝟙 (artinianToComplete.obj D.left)) g := by
        convert hg using 1
        simp [ComposableArrows.hom, ComposableArrows.left, ComposableArrows.right]
      let : IsIso g := isIso_of_lift_iso q hqp (Iso.refl _) g hgid
      exact ⟨a ≫ inv g, by simp⟩
  | succ n ih =>
      intro y x g hg a
      let q := FormalObject.projection (p := p)
      let f := D.map' 0 1
      let E := D.δ₀
      have hEtail : ∀ (i : ℕ) (hi : i < n), InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom
            (E.map' i (i + 1) (Nat.le_succ i) (Nat.succ_le_of_lt hi)).hom.toRingHom) := by
        intro i hi
        show InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom
            (D.map' (i + 1) (i + 2) (Nat.le_succ _)
              (Nat.succ_le_of_lt (Nat.succ_lt_succ hi))).hom.toRingHom)
        exact hD (i + 1) (by omega)
      have hfac : D.hom = f ≫ E.hom := ComposableArrows.map'_comp D 0 1 (n + 1)
      have hg' : q.IsHomLift (artinianToComplete.map (f ≫ E.hom)) g := hfac ▸ hg
      obtain ⟨z, u, v, hu, hv, huv⟩ :=
        exists_factor_of_isHomLift_comp
          (formalObjectProjection_isCofiberedInGroupoids p hp)
          (artinianToComplete.map f)
          (artinianToComplete.map E.hom) g hg'
      obtain ⟨a', ha'⟩ := ih E hEtail v hv a
      obtain ⟨b, hb⟩ := hsmall f (hD 0 (by omega)) u hu a'
      refine ⟨b, ?_⟩
      rw [← huv, ← Category.assoc, hb, ha']

open IsLocalRing

-- The proofs below identify morphisms of based categories through the `abbrev`s of Stacks
-- 06GX/06GW/06H3, whose objects and category instances are reached through
-- `BasedCategory.ofFunctor`. That definition is semireducible, so the generic category and
-- `eqToHom` lemmas do not match up to `implicit` transparency; naming it here is what makes
-- them apply, and `local` keeps the change from leaking to importers.
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-- For a functor cofibered in groupoids, every arrow lying over a morphism is strongly
cocartesian. -/
public lemma all_cocartesian
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {p : D ⥤ C} (hp : IsCofiberedInGroupoids p)
    {A B : C} {x y : D}
    (f : A ⟶ B) (φ : x ⟶ y) [p.IsHomLift f φ] : p.IsStronglyCocartesian f φ :=
  isStronglyCocartesian_of_isCofiberedInGroupoids hp f φ inferInstance

private lemma artinianAdicQuotient_injective
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hA : maximalIdeal A ^ (n + 1) = ⊥) :
    Function.Injective (artinianAdicQuotient A n).hom := by
  show Function.Injective (Ideal.Quotient.mkₐ Λ (maximalIdeal A ^ (n + 1)))
  rw [hA]
  exact (AlgEquiv.quotientBot Λ A).symm.injective

private lemma truncation_map_injective
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hS : S = artinianToComplete.obj A)
    (n : ℕ) (hA : maximalIdeal A ^ (n + 1) = ⊥) :
    Function.Injective (fun f : R ⟶ S ↦ (AdicTruncation.functor n).map f) := by
  subst S
  intro f g h
  apply CompleteLocalAlgCat.Hom.ext
  ext r
  apply artinianAdicQuotient_injective A n hA
  exact congrArg (fun t : AdicTruncation.obj R n ⟶
    AdicTruncation.obj (artinianToComplete.obj A) n ↦
      t.hom (Ideal.Quotient.mk _ r)) h

private lemma base_eq_of_app_lift
    {X Y : FormalObject p} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hY : Y.base = artinianToComplete.obj A)
    (n : ℕ) (hA : maximalIdeal A ^ (n + 1) = ⊥)
    (f : X ⟶ Y) (t : X.base ⟶ Y.base)
    (ht : p.IsHomLift ((AdicTruncation.functor n).map t) (f.app n)) : f.base = t := by
  have hf := f.app_lift n
  apply truncation_map_injective hY n hA
  exact (IsHomLift.fac p ((AdicTruncation.functor n).map f.base) (f.app n)).trans
    (IsHomLift.fac p ((AdicTruncation.functor n).map t) (f.app n)).symm

private def artinianMap {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : artinianToComplete.obj A ⟶ artinianToComplete.obj B) : A ⟶ B :=
  ⟨f.hom, f.isLocal, f.residue_comm⟩

private def artinianPullback (e : RestrictionCompletionEquivalence p)
    (X : FormalObject p) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hX : X.base = artinianToComplete.obj A) :
    Limits.CategoricalPullback e.inclusion (FormalObject.projection (p := p)) :=
  ⟨A, X, e.inclusionIso.app A ≪≫ eqToIso hX.symm⟩

private def artinianPullbackMap (e : RestrictionCompletionEquivalence p)
    {X Y : FormalObject p} {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hX : X.base = artinianToComplete.obj A)
    (hY : Y.base = artinianToComplete.obj B) (f : X ⟶ Y) :
    artinianPullback e X A hX ⟶ artinianPullback e Y B hY where
  fst := artinianMap (eqToHom hX.symm ≫ f.base ≫ eqToHom hY)
  snd := f
  w := by
    change e.inclusion.map (artinianMap (eqToHom hX.symm ≫ f.base ≫ eqToHom hY)) ≫
        (e.inclusionIso.hom.app B ≫ eqToHom hY.symm) =
      (e.inclusionIso.hom.app A ≫ eqToHom hX.symm) ≫ f.base
    -- `e.inclusionIso.hom.naturality` is stated with the generic composition of the functor
    -- category, which does not match this goal up to `implicit` transparency; restating it at
    -- the goal's own spelling is what lets it be rewritten with.
    have hnat : e.inclusion.map (artinianMap (eqToHom hX.symm ≫ f.base ≫ eqToHom hY)) ≫
          e.inclusionIso.hom.app B =
        e.inclusionIso.hom.app A ≫
          artinianToComplete.map (artinianMap (eqToHom hX.symm ≫ f.base ≫ eqToHom hY)) :=
      e.inclusionIso.hom.naturality _
    rw [← Category.assoc, hnat]
    change (e.inclusionIso.hom.app A ≫
      (eqToHom hX.symm ≫ f.base ≫ eqToHom hY)) ≫ eqToHom hY.symm = _
    simp

-- The second component of an `artinianPullback` is the formal object it was built from, and
-- the level maps below compose with the evaluation isomorphisms only through that
-- identification, which is not visible at `implicit` transparency.
attribute [local implicit_reducible] artinianPullback

private lemma exists_hom_of_stable_level
    (hp : IsCofiberedInGroupoids p)
    {X Y : FormalObject p} {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hX : X.base = artinianToComplete.obj A)
    (hY : Y.base = artinianToComplete.obj B)
    (n : ℕ) (hA : maximalIdeal A ^ (n + 1) = ⊥)
    (hB : maximalIdeal B ^ (n + 1) = ⊥) (c : X.level n ⟶ Y.level n) :
    ∃ f : X ⟶ Y, f.app n = c := by
  let e := restrictionCompletionEquivalence p hp
  let x := artinianPullback e X A hX
  let y := artinianPullback e Y B hY
  let := e.isEquivalence
  let a := e.objIsoLevel x n hA
  let b := e.objIsoLevel y n hB
  let f := e.can.preimage (a.hom ≫ c ≫ b.inv)
  refine ⟨f.snd, ?_⟩
  have h : (a.hom ≫ c ≫ b.inv) ≫ b.hom = a.hom ≫ f.snd.app n := by
    have h0 := e.objIsoLevel_naturality f n hA hB
    rw [e.can.map_preimage] at h0
    exact h0
  simpa [a, b, Category.assoc] using h.symm

private lemma hom_ext_stable_level
    (hp : IsCofiberedInGroupoids p)
    {X Y : FormalObject p} {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hX : X.base = artinianToComplete.obj A)
    (hY : Y.base = artinianToComplete.obj B)
    (n : ℕ) (hA : maximalIdeal A ^ (n + 1) = ⊥)
    (hB : maximalIdeal B ^ (n + 1) = ⊥)
    {f g : X ⟶ Y} (h : f.app n = g.app n) : f = g := by
  let e := restrictionCompletionEquivalence p hp
  let f' := artinianPullbackMap e hX hY f
  let g' := artinianPullbackMap e hX hY g
  let := e.isEquivalence
  have hh : e.can.map f' = e.can.map g' := by
    apply (cancel_mono (e.objIsoLevel _ n hB).hom).mp
    rw [e.objIsoLevel_naturality f' n hA hB,
      e.objIsoLevel_naturality g' n hA hB]
    exact congrArg ((e.objIsoLevel _ n hA).hom ≫ ·) h
  exact congrArg Limits.CategoricalPullback.Hom.snd (e.can.map_injective hh)

private noncomputable def artinianQuotientTo {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hS : S = artinianToComplete.obj A) (n : ℕ) :
    A ⟶ AdicTruncation.obj S n :=
  artinianAdicQuotient A n ≫ (AdicTruncation.functor n).map (eqToHom hS.symm)

private lemma factor_comp_quotient
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hS : S = artinianToComplete.obj A) (f : R ⟶ S)
    {n : ℕ} (t : AdicTruncation.obj R n ⟶ A)
    (ht : t.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) =
      (f ≫ eqToHom hS).hom) :
    t ≫ artinianQuotientTo hS n = (AdicTruncation.functor n).map f := by
  subst S
  apply ArtinianLocalAlgCat.hom_ext
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  show Ideal.Quotient.mk _ (t.hom (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (f.hom r)
  exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun ht r)

private lemma pointInclusion_lift (ξ : FormalObject p)
    {P : ChosenPushforwards p} (φ : AssociatedMorphism ξ P)
    (α : (restrictedCoyoneda ξ.base).Elements) :
    p.IsHomLift (φ.factor α) (φ.pointInclusion α) := by
  apply (IsHomLift.eqToHom_comp_lift_iff p (φ.factor α) (φ.pointInclusion α)
    (φ.obj_eq α)).mp
  rw [φ.pointInclusion_eq]
  exact (P (φ.factor α)).cocartesian _ |>.toIsHomLift

private lemma exists_point_comparison
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    {P : ChosenPushforwards p} (φ : AssociatedMorphism ξ P)
    {X : FormalObject p} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hX : X.base = artinianToComplete.obj A) (a : ξ ⟶ X)
    (n : ℕ) (hn : φ.level ⟨A, a.base ≫ eqToHom hX⟩ ≤ n) :
    ∃ c : φ.toBasedFunctor.obj ⟨A, a.base ≫ eqToHom hX⟩ ⟶ X.level n,
      p.IsHomLift (artinianQuotientTo hX n) c ∧
      (transitionTo ξ hn ≫ φ.pointInclusion ⟨A, a.base ≫ eqToHom hX⟩) ≫ c =
        a.app n := by
  let α : (restrictedCoyoneda ξ.base).Elements := ⟨A, a.base ≫ eqToHom hX⟩
  obtain ⟨t, ht, hi⟩ := point_lift ξ (φ.factor_spec α).2.2
    (φ.pointInclusion α) (pointInclusion_lift ξ φ α) hn
  have := all_cocartesian hp t (transitionTo ξ hn ≫ φ.pointInclusion α)
  have := a.app_lift n
  obtain ⟨c, hc, _⟩ := Functor.IsStronglyCocartesian.universal_property p t
    (transitionTo ξ hn ≫ φ.pointInclusion α) (artinianQuotientTo hX n)
    ((AdicTruncation.functor n).map a.base) (factor_comp_quotient hX a.base t ht).symm
    (a.app n)
  exact ⟨c, hc⟩

private lemma formal_hom_ext_of_stable_target
    (hp : IsCofiberedInGroupoids p)
    {X Y : FormalObject p} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hY : Y.base = artinianToComplete.obj A)
    (n : ℕ) (hA : maximalIdeal A ^ (n + 1) = ⊥)
    {f g : X ⟶ Y} (h : f.app n = g.app n) : f = g := by
  let q := FormalObject.projection (p := p)
  have hq := formalObjectProjection_isCofiberedInGroupoids p hp
  have hb : f.base = g.base :=
    base_eq_of_app_lift hY n hA f g.base (h ▸ g.app_lift n)
  have hf : q.IsHomLift (f.base ≫ 𝟙 Y.base) f := by
    rw [Category.comp_id]
    exact IsHomLift.map (FormalObject.projection (p := p)) f
  obtain ⟨Z, i, j, hi, hj, hij⟩ := exists_factor_of_isHomLift_comp hq f.base (𝟙 Y.base) f hf
  have hi' := all_cocartesian hq f.base i
  have hg : q.IsHomLift f.base g := hb.symm ▸ IsHomLift.map q g
  obtain ⟨l, ⟨hl, hil⟩, _⟩ :=
    Functor.IsCocartesian.universal_property (p := q) (f := f.base) (φ := i) g
  have hZ : Z.base = artinianToComplete.obj A :=
    (IsHomLift.codomain_eq q f.base i).trans hY
  have hjl : j.base = l.base :=
    (IsHomLift.fac' q (𝟙 Y.base) j).trans (IsHomLift.fac' q (𝟙 Y.base) l).symm
  have hjn := j.app_lift n
  have hln : p.IsHomLift ((AdicTruncation.functor n).map j.base) (l.app n) :=
    hjl.symm ▸ l.app_lift n
  have hin := i.app_lift n
  have := all_cocartesian hp ((AdicTruncation.functor n).map i.base) (i.app n)
  have hjln : j.app n = l.app n := by
    apply Functor.IsStronglyCocartesian.ext p
      ((AdicTruncation.functor n).map i.base) (i.app n)
      ((AdicTruncation.functor n).map j.base)
    show (i ≫ j).app n = (i ≫ l).app n
    rwa [hij, hil]
  have he := hom_ext_stable_level hp hZ hY n hA hA hjln
  exact hij.symm.trans ((congrArg (i ≫ ·) he).trans hil)

private lemma pointInclusion_naturality_at
    (ξ : FormalObject p) {P : ChosenPushforwards p} (φ : AssociatedMorphism ξ P)
    {α β : (restrictedCoyoneda ξ.base).Elements} (g : α ⟶ β)
    {n : ℕ} (hα : φ.level α ≤ n) (hβ : φ.level β ≤ n) :
    (transitionTo ξ hα ≫ φ.pointInclusion α) ≫ φ.toBasedFunctor.map g =
      transitionTo ξ hβ ≫ φ.pointInclusion β := by
  simpa only [← Category.assoc, transitionTo_comp] using
    congrArg (transitionTo ξ (max_le hα hβ) ≫ ·) (φ.map_pointInclusion g)

private lemma pointInclusion_cancel
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) {P : ChosenPushforwards p} (φ : AssociatedMorphism ξ P)
    (α : (restrictedCoyoneda ξ.base).Elements) {n : ℕ} (hn : φ.level α ≤ n)
    {B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : α.1 ⟶ B)
    {y : F} {a b : φ.toBasedFunctor.obj α ⟶ y}
    (ha : p.IsHomLift f a) (hb : p.IsHomLift f b)
    (h : (transitionTo ξ hn ≫ φ.pointInclusion α) ≫ a =
      (transitionTo ξ hn ≫ φ.pointInclusion α) ≫ b) : a = b := by
  obtain ⟨t, ht, hi⟩ := point_lift ξ (φ.factor_spec α).2.2
    (φ.pointInclusion α) (pointInclusion_lift ξ φ α) hn
  have := all_cocartesian hp t (transitionTo ξ hn ≫ φ.pointInclusion α)
  exact Functor.IsStronglyCocartesian.ext p t _ f h

private def artinianRepresentable (B : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π
        (restrictedCoyoneda (artinianToComplete.obj B))))
      (BasedCategory.ofFunctor (CategoryOfElements.π (coyoneda.obj (Opposite.op B)))) where
  obj α := ⟨α.1, artinianMap α.2⟩
  map f := ⟨f.val, ArtinianLocalAlgCat.hom_ext (congrArg CompleteLocalAlgCat.Hom.hom f.property)⟩
  map_id _ := rfl
  map_comp _ _ := rfl
  w := rfl

-- The value of the represented morphism at an Artinian point is the chosen pushforward only
-- after these three definitions are unfolded, so the arrow out of a chosen inclusion and the
-- arrow out of `φ.obj` are recognized as having the same source only at that transparency.
attribute [local implicit_reducible] yonedaPushforward artinianRepresentable
  CategoryTheory.BasedFunctor.comp

private lemma exists_formal_over
    (hp : IsCofiberedInGroupoids p)
    {B : ArtinianLocalAlgCat.{u, v, w} Λ k} (y : F) (hy : p.obj y = B)
    (n : ℕ) :
    ∃ (Y : FormalObject p) (hY : Y.base = artinianToComplete.obj B)
      (c : y ⟶ Y.level n), p.IsHomLift (artinianQuotientTo hY n) c := by
  let P : ChosenPushforwards p := chosenPushforwardsOfCofibered p hp
  let φ := (artinianRepresentable B).comp (yonedaPushforward p P ⟨y, hy⟩)
  let E := representableMorphismFormalObjectEquivalence p hp
    (artinianToComplete.obj B)
  let Y := E.equivalence.functor.obj φ
  let α : (restrictedCoyoneda (artinianToComplete.obj B)).Elements :=
    ⟨_, E.quotientPoint n⟩
  let i := (P (artinianMap α.2)).inclusion ⟨y, hy⟩
  have hi := (P (artinianMap α.2)).cocartesian ⟨y, hy⟩ |>.toIsHomLift
  have he : artinianMap α.2 = artinianAdicQuotient B n :=
    ArtinianLocalAlgCat.hom_ext (E.quotientPoint_hom n)
  -- Stated at the spelling the instance search needs: the structure field's own statement
  -- mentions the base of `E`, which is only `AdicTruncation.obj (artinianToComplete.obj B) n`
  -- after unfolding.
  have hlev : p.IsHomLift (𝟙 (AdicTruncation.obj (artinianToComplete.obj B) n))
      (E.levelIso φ n).hom := E.levelIso_over φ n
  let c : y ⟶ Y.1.level n := i ≫ (E.levelIso φ n).hom
  have hc : p.IsHomLift (artinianAdicQuotient B n) c := by
    rw [← he]
    exact IsHomLift.comp_lift_id_right' p (artinianMap α.2) i
      (AdicTruncation.obj (artinianToComplete.obj B) n) (E.levelIso φ n).hom
  refine ⟨Y.1, Y.2, c, ?_⟩
  unfold artinianQuotientTo
  rw [eqToHom_map]
  exact (IsHomLift.lift_comp_eqToHom_iff p _ c _).mpr hc

private lemma artinianQuotientTo_isIso
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hS : S = artinianToComplete.obj A) (n : ℕ)
    (hA : maximalIdeal A ^ (n + 1) = ⊥) : IsIso (artinianQuotientTo hS n) := by
  have := artinianAdicQuotient_isIso A n hA
  unfold artinianQuotientTo
  infer_instance

/-- An arrow over the quotient map onto a truncation of an Artinian algebra is invertible. -/
private lemma isIso_of_lift_quotientTo
    (hp : IsCofiberedInGroupoids p)
    {S : CompleteLocalAlgCat.{u, v, w} Λ k} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hS : S = artinianToComplete.obj A) (n : ℕ) (hA : maximalIdeal A ^ (n + 1) = ⊥)
    {x y : F} (c : x ⟶ y) (hc : p.IsHomLift (artinianQuotientTo hS n) c) : IsIso c :=
  have := artinianQuotientTo_isIso hS n hA
  isIso_of_lift_iso p hp (asIso (artinianQuotientTo hS n)) c hc

/-- The truncation of a map between Artinian algebras, in terms of the quotient maps. -/
private lemma truncation_map_eq_inv_comp
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hR : R = artinianToComplete.obj B)
    (hS : S = artinianToComplete.obj A)
    (f : B ⟶ A) (n : ℕ) [IsIso (artinianQuotientTo hR n)] :
    (AdicTruncation.functor n).map (eqToHom hR ≫ artinianToComplete.map f ≫ eqToHom hS.symm) =
      inv (artinianQuotientTo hR n) ≫ f ≫ artinianQuotientTo hS n := by
  apply (cancel_epi (artinianQuotientTo hR n)).mp
  have hnat : artinianQuotientTo hR n ≫ (AdicTruncation.functor n).map
      (eqToHom hR ≫ artinianToComplete.map f ≫ eqToHom hS.symm) =
      f ≫ artinianQuotientTo hS n := by
    subst R S
    apply ArtinianLocalAlgCat.hom_ext
    ext b
    rfl
  simpa only [IsIso.hom_inv_id_assoc] using hnat

private lemma common_nilpotence (A B : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    ∃ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥ ∧ maximalIdeal B ^ (n + 1) = ⊥ := by
  obtain ⟨a, ha⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  obtain ⟨b, hb⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance
  exact ⟨a + b, pow_eq_zero_of_le (by omega) ha, pow_eq_zero_of_le (by omega) hb⟩

private lemma exists_point_comparison_lift
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    {P : ChosenPushforwards p} (φ : AssociatedMorphism ξ P)
    {X : FormalObject p} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hX : X.base = artinianToComplete.obj A)
    (α : (restrictedCoyoneda ξ.base).obj A) (a : ξ ⟶ X)
    (ha : (FormalObject.projection (p := p)).IsHomLift α a)
    (n : ℕ) (hn : φ.level ⟨A, α⟩ ≤ n) :
    ∃ c : φ.toBasedFunctor.obj ⟨A, α⟩ ⟶ X.level n,
      p.IsHomLift (artinianQuotientTo hX n) c ∧
      (transitionTo ξ hn ≫ φ.pointInclusion ⟨A, α⟩) ≫ c = a.app n := by
  have he : α = a.base ≫ eqToHom hX := by
    simpa only [eqToHom_refl, Category.id_comp, FormalObject.projection_map] using
      IsHomLift.fac (FormalObject.projection (p := p)) α a
  subst α
  exact exists_point_comparison hp ξ φ hX a n hn

private lemma formal_app_lift_artinian
    {X Y : FormalObject p} {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hX : X.base = artinianToComplete.obj B)
    (hY : Y.base = artinianToComplete.obj A)
    (f : B ⟶ A) (g : X ⟶ Y)
    (hg : (FormalObject.projection (p := p)).IsHomLift
      (artinianToComplete.map f) g)
    (n : ℕ) (hB : maximalIdeal B ^ (n + 1) = ⊥)
    [IsIso (artinianQuotientTo hX n)] :
    p.IsHomLift (inv (artinianQuotientTo hX n) ≫ f ≫ artinianQuotientTo hY n)
      (g.app n) := by
  have := artinianQuotientTo_isIso hX n hB
  have hb : g.base = eqToHom hX ≫ artinianToComplete.map f ≫
      eqToHom hY.symm := IsHomLift.fac' (FormalObject.projection (p := p)) _ g
  have he : (AdicTruncation.functor n).map g.base =
      inv (artinianQuotientTo hX n) ≫ f ≫ artinianQuotientTo hY n := by
    rw [hb]
    exact truncation_map_eq_inv_comp hX hY f n
  exact he ▸ g.app_lift n

private lemma lifts_artinian_of_smooth
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    {P : ChosenPushforwards p} (φ : AssociatedMorphism ξ P)
    (hφ : IsSmooth φ.toBasedFunctor)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) {Y X : FormalObject p} (g : Y ⟶ X)
    (hg : (FormalObject.projection (p := p)).IsHomLift
      (artinianToComplete.map f) g) (a : ξ ⟶ X) :
    ∃ b : ξ ⟶ Y, b ≫ g = a := by
  let q := FormalObject.projection (p := p)
  have hq := formalObjectProjection_isCofiberedInGroupoids p hp
  have hX : X.base = artinianToComplete.obj A :=
    IsHomLift.codomain_eq q (artinianToComplete.map f) g
  have hY : Y.base = artinianToComplete.obj B :=
    IsHomLift.domain_eq q (artinianToComplete.map f) g
  obtain ⟨n, hA, hB⟩ := common_nilpotence A B
  let α : (restrictedCoyoneda ξ.base).Elements := ⟨A, a.base ≫ eqToHom hX⟩
  have hnα : φ.level α ≤ n := (φ.factor_spec α).2.1 n hA
  obtain ⟨c, hc, hac⟩ := exists_point_comparison hp ξ φ hX a n hnα
  have hQA := artinianQuotientTo_isIso hX n hA
  have hQB := artinianQuotientTo_isIso hY n hB
  have hciso : IsIso c := isIso_of_lift_quotientTo hp hX n hA c hc
  obtain ⟨y, j, hj, hjiso⟩ := lift_iso p hp (asIso (artinianQuotientTo hY n)) (Y.level_eq n)
  have hj' : p.IsHomLift (artinianQuotientTo hY n) j := hj
  have hgn := formal_app_lift_artinian hY hX f g hg n hB
  have hci := IsHomLift.inv p (artinianQuotientTo hX n) c
  let g₀ := (j ≫ g.app n) ≫ inv c
  have hg₀ : p.IsHomLift f g₀ := by
    have h₁ := IsHomLift.comp p (artinianQuotientTo hY n)
      (inv (artinianQuotientTo hY n) ≫ f ≫ artinianQuotientTo hX n) j (g.app n)
    have h₂ := IsHomLift.comp p
      (artinianQuotientTo hY n ≫
        (inv (artinianQuotientTo hY n) ≫ f ≫ artinianQuotientTo hX n))
      (inv (artinianQuotientTo hX n)) (j ≫ g.app n) (inv c)
    simpa only [g₀, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
      Category.comp_id] using h₂
  obtain ⟨β, h, t, hh, ht, hht⟩ := hφ f hf y α g₀ hg₀
  have hh' : (CategoryOfElements.π (restrictedCoyoneda ξ.base)).IsHomLift f h := hh
  have hβ : β.1 = B := IsHomLift.domain_eq (CategoryOfElements.π (restrictedCoyoneda ξ.base)) f h
  rcases β with ⟨B', β⟩
  dsimp at hβ
  subst B'
  have hnβ : φ.level ⟨B, β⟩ ≤ n := (φ.factor_spec ⟨B, β⟩).2.1 n hB
  obtain ⟨Z, i, hi⟩ := exists_pushforward hq β ξ rfl
  have hZ : Z.base = artinianToComplete.obj B := IsHomLift.codomain_eq q β i
  obtain ⟨d, hd, hid⟩ := exists_point_comparison_lift hp ξ φ hZ β i hi n hnβ
  have hQZ := artinianQuotientTo_isIso hZ n hB
  have hdiso : IsIso d := isIso_of_lift_quotientTo hp hZ n hB d hd
  obtain ⟨k, hk⟩ := exists_hom_of_stable_level hp hZ hY n hB hB (inv d ≫ t ≫ j)
  refine ⟨i ≫ k, formal_hom_ext_of_stable_target hp hX n hA ?_⟩
  show (i.app n ≫ k.app n) ≫ g.app n = a.app n
  rw [hk, ← hid]
  calc
    (((transitionTo ξ hnβ ≫ φ.pointInclusion ⟨B, β⟩) ≫ d) ≫
        (inv d ≫ t ≫ j)) ≫ g.app n =
      (transitionTo ξ hnβ ≫ φ.pointInclusion ⟨B, β⟩) ≫
        (t ≫ g₀) ≫ c := by simp [g₀, Category.assoc]
    _ = (transitionTo ξ hnβ ≫ φ.pointInclusion ⟨B, β⟩) ≫
        φ.toBasedFunctor.map h ≫ c := by rw [hht]
    _ = a.app n := by
      rw [← Category.assoc, pointInclusion_naturality_at ξ φ h hnβ hnα]
      exact hac

private lemma smooth_of_lifts_artinian
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    {P : ChosenPushforwards p} (φ : AssociatedMorphism ξ P)
    (H : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      Function.Surjective f.hom → ∀ {Y X : FormalObject p} (g : Y ⟶ X),
      (FormalObject.projection (p := p)).IsHomLift
        (artinianToComplete.map f) g →
      ∀ a : ξ ⟶ X, ∃ b : ξ ⟶ Y, b ≫ g = a) :
    IsSmooth φ.toBasedFunctor := by
  intro B A f hf y α g hg
  have hg' : p.IsHomLift f g := hg
  have hα : α.1 = A := (φ.toBasedFunctor.w_obj α).symm.trans
    (IsHomLift.codomain_eq p f g)
  rcases α with ⟨A', α⟩
  dsimp at hα
  subst A'
  have hy : p.obj y = B := IsHomLift.domain_eq p f g
  let q := FormalObject.projection (p := p)
  have hq := formalObjectProjection_isCofiberedInGroupoids p hp
  obtain ⟨n, hA, hB⟩ := common_nilpotence A B
  obtain ⟨X, i, hi⟩ := exists_pushforward hq α ξ rfl
  have hX : X.base = artinianToComplete.obj A := IsHomLift.codomain_eq q α i
  have hnα : φ.level ⟨A, α⟩ ≤ n := (φ.factor_spec ⟨A, α⟩).2.1 n hA
  obtain ⟨cx, hcx, hicx⟩ := exists_point_comparison_lift hp ξ φ hX α i hi n hnα
  obtain ⟨Y, hY, cy, hcy⟩ := exists_formal_over hp y hy n
  have hQA := artinianQuotientTo_isIso hX n hA
  have hQB := artinianQuotientTo_isIso hY n hB
  have hcxiso : IsIso cx := isIso_of_lift_quotientTo hp hX n hA cx hcx
  have hcyiso : IsIso cy := isIso_of_lift_quotientTo hp hY n hB cy hcy
  obtain ⟨G, hG⟩ := exists_hom_of_stable_level hp hY hX n hB hA (inv cy ≫ g ≫ cx)
  have hGapp : p.IsHomLift
      (inv (artinianQuotientTo hY n) ≫ f ≫ artinianQuotientTo hX n) (G.app n) := by
    rw [hG]
    have hcyi := IsHomLift.inv p (artinianQuotientTo hY n) cy
    have hgc := IsHomLift.comp p f (artinianQuotientTo hX n) g cx
    exact IsHomLift.comp p _ _ (inv cy) (g ≫ cx)
  let baseG := eqToHom hY ≫ artinianToComplete.map f ≫ eqToHom hX.symm
  have hbaseG : G.base = baseG := by
    apply base_eq_of_app_lift hX n hA G baseG
    rwa [truncation_map_eq_inv_comp hY hX f n]
  have hGlift : q.IsHomLift (artinianToComplete.map f) G :=
    IsHomLift.of_fac' q _ G hY hX hbaseG
  obtain ⟨b, hb⟩ := H f hf G hGlift i
  let β : (restrictedCoyoneda ξ.base).Elements := ⟨B, b.base ≫ eqToHom hY⟩
  have hpoint : (b.base ≫ eqToHom hY) ≫ artinianToComplete.map f = α := by
    have he : b.base ≫ G.base = i.base := congrArg FormalObject.Hom.base hb
    have hi' : i.base ≫ eqToHom hX = α := by
      simpa only [q, FormalObject.projection_map, eqToHom_refl, Category.id_comp] using
        (IsHomLift.fac q α i).symm
    rw [← hi', ← he, hbaseG]
    simp [baseG, Category.assoc]
  let h : β ⟶ ⟨A, α⟩ := ⟨f, hpoint⟩
  have hh : (CategoryOfElements.π (restrictedCoyoneda ξ.base)).IsHomLift f h :=
    IsHomLift.map _ h
  have hnβ : φ.level β ≤ n := (φ.factor_spec β).2.1 n hB
  obtain ⟨cb, hcb, hbcb⟩ := exists_point_comparison hp ξ φ hY b n hnβ
  let t := cb ≫ inv cy
  have ht : p.IsHomLift (𝟙 B) t := by
    have hcyi := IsHomLift.inv p (artinianQuotientTo hY n) cy
    have hc := IsHomLift.comp p (artinianQuotientTo hY n)
      (inv (artinianQuotientTo hY n)) cb (inv cy)
    simpa only [IsIso.hom_inv_id] using hc
  refine ⟨β, h, t, hh, ht, ?_⟩
  have hφh : p.IsHomLift f (φ.toBasedFunctor.map h) :=
    (φ.toBasedFunctor.isHomLift_iff f h).mpr hh
  have htg : p.IsHomLift f (t ≫ g) := IsHomLift.comp_lift_id_left' p B t f g
  apply pointInclusion_cancel hp ξ φ β hnβ f hφh htg
  apply (cancel_mono cx).mp
  calc
    ((transitionTo ξ hnβ ≫ φ.pointInclusion β) ≫ φ.toBasedFunctor.map h) ≫ cx =
        i.app n := by rw [pointInclusion_naturality_at ξ φ h hnβ hnα]; exact hicx
    _ = b.app n ≫ G.app n := (congrArg (fun a : ξ ⟶ X ↦ a.app n) hb).symm
    _ = ((transitionTo ξ hnβ ≫ φ.pointInclusion β) ≫ (t ≫ g)) ≫ cx := by
      rw [hG, ← hbcb]
      simp only [t, β, Category.assoc]

/-- Versality is equivalent to solving every lifting triangle in the completion
whose lower arrow is a surjective map of Artinian local algebras. -/
@[stacks 06HS "lifting criterion",
  sga "7 VI 2.2(d)" "lifting criterion",
  sga "7 VI 1.9" "versal formal object", sga "7 VI 1.19" "(1)"]
public theorem isVersal_iff_lifts_artinian
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) :
    IsVersal hp ξ ↔
      ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
        Function.Surjective f.hom →
          ∀ {y x : FormalObject p} (g : y ⟶ x),
            (FormalObject.projection (p := p)).IsHomLift
              (artinianToComplete.map f) g →
              ∀ (a : ξ ⟶ x), ∃ b : ξ ⟶ y, b ≫ g = a := by
  constructor
  · intro h
    let P : ChosenPushforwards p := chosenPushforwardsOfCofibered p hp
    intro B A f hf y x g hg a
    exact lifts_artinian_of_smooth hp ξ (associatedMorphism hp ξ P) (h P) f hf g hg a
  · intro h P
    exact smooth_of_lifts_artinian hp ξ (associatedMorphism hp ξ P) h

/-- Versality is invariant under an isomorphism of formal objects. -/
public theorem isVersal_of_iso (hp : IsCofiberedInGroupoids p)
    {ξ η : FormalObject p} (e : ξ ≅ η) (hξ : IsVersal hp ξ) : IsVersal hp η := by
  apply (isVersal_iff_lifts_artinian hp η).2
  intro B A f hf y x g hg a
  obtain ⟨b, hb⟩ := (isVersal_iff_lifts_artinian hp ξ).1 hξ f hf g hg (e.hom ≫ a)
  refine ⟨e.inv ≫ b, ?_⟩
  rw [Category.assoc, hb, e.inv_hom_id_assoc]

/-- In the intrinsic lifting criterion, it suffices to test small extensions
of Artinian local algebras. -/
@[stacks 06HS "small-extension criterion"]
public theorem isVersal_iff_lifts_smallExtensions
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) :
    IsVersal hp ξ ↔
      ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
        InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom f.hom.toRingHom) →
          ∀ {y x : FormalObject p} (g : y ⟶ x),
            (FormalObject.projection (p := p)).IsHomLift
              (artinianToComplete.map f) g →
              ∀ (a : ξ ⟶ x), ∃ b : ξ ⟶ y, b ≫ g = a := by
  constructor
  · intro h B A f hf y x g hg a
    rcases hf with ⟨_, _, _, _, hsurj, _⟩
    exact (isVersal_iff_lifts_artinian hp ξ).mp h f hsurj g hg a
  · intro h
    apply (isVersal_iff_lifts_artinian hp ξ).mpr
    intro B A f hsurj y x g hg a
    obtain ⟨n, D, hB, e, hfactor, hsmall⟩ :=
      surjective_factors_into_smallExtensions f hsurj
    let q := FormalObject.projection (p := p)
    let hq := formalObjectProjection_isCofiberedInGroupoids p hp
    have hy : q.obj y = artinianToComplete.obj B :=
      IsHomLift.domain_eq q (artinianToComplete.map f) g
    have hx : q.obj x = artinianToComplete.obj A :=
      IsHomLift.codomain_eq q (artinianToComplete.map f) g
    obtain ⟨y₀, k, hk, hkis⟩ :=
      lift_iso q hq (artinianToComplete.mapIso (eqToIso hB)) hy
    obtain ⟨x₀, l, hl, hlis⟩ :=
      lift_iso q hq (artinianToComplete.mapIso e) hx
    let g₀ := k ≫ g ≫ inv l
    let a₀ := a ≫ inv l
    have hkl : q.IsHomLift
        (artinianToComplete.map (eqToHom hB)) k := hk
    have hff : q.IsHomLift (artinianToComplete.map f) g := hg
    have hli : q.IsHomLift
        (inv (artinianToComplete.map e.hom)) (inv l) := by
      let : q.IsHomLift (artinianToComplete.map e.hom) l := hl
      exact IsHomLift.inv q (artinianToComplete.map e.hom) l
    have hcomp₁ : q.IsHomLift
        (artinianToComplete.map (eqToHom hB) ≫
          artinianToComplete.map f) (k ≫ g) := by
      simpa only [Functor.map_comp] using IsHomLift.comp q
        (artinianToComplete.map (eqToHom hB))
        (artinianToComplete.map f) k g
    have hcomp₂ : q.IsHomLift
        ((artinianToComplete.map (eqToHom hB) ≫
          artinianToComplete.map f) ≫
          inv (artinianToComplete.map e.hom)) ((k ≫ g) ≫ inv l) := by
      simpa only [Functor.map_comp] using IsHomLift.comp q
        (artinianToComplete.map (eqToHom hB) ≫
          artinianToComplete.map f)
        (inv (artinianToComplete.map e.hom)) (k ≫ g) (inv l)
    have hpath : eqToHom hB ≫ f ≫ e.inv = D.hom := by
      simp [← hfactor]
    have hg₀ : q.IsHomLift (artinianToComplete.map D.hom) g₀ := by
      simpa [g₀, ← Functor.map_comp, ← Functor.map_inv, hpath, Category.assoc] using hcomp₂
    obtain ⟨b, hb⟩ := lifts_small_chain hp ξ h D hsmall g₀ hg₀ a₀
    refine ⟨b ≫ k, ?_⟩
    calc
      (b ≫ k) ≫ g = ((b ≫ k) ≫ g ≫ inv l) ≫ l := by simp [Category.assoc]
      _ = (b ≫ g₀) ≫ l := by simp [g₀, Category.assoc]
      _ = (a ≫ inv l) ≫ l := by rw [hb]
      _ = a := by simp [Category.assoc]

/-- Smoothness of the morphism associated to a formal object is independent of
the choices of pushforwards used to construct that morphism. -/
@[stacks 06HS "independence of pushforwards", sga "7 VI 2.2(d)" "smooth ⟺ versal"]
public theorem isSmooth_associatedMorphism_iff_isVersal
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p) :
    IsSmooth (associatedMorphism hp ξ pushforwards).toBasedFunctor ↔
      IsVersal hp ξ := by
  constructor
  · intro h pushforwards'
    let E := representableMorphismFormalObjectEquivalence p hp ξ.base
    let e₁ := Classical.choice (associatedMorphism_maps_to hp ξ E pushforwards)
    let e₂ := Classical.choice (associatedMorphism_maps_to hp ξ E pushforwards')
    exact smooth_of_iso (basedFunctor_iso_of_images_iso E.equivalence (e₁ ≪≫ e₂.symm)) h
  · exact fun h => h pushforwards

end Deformation

end
