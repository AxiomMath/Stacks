module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.SplitPushforward
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.OverSiteDisjointCover
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.SplitPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# Local `Q`-constancy and direct image under finite étale morphisms

Local `Q`-constancy of étale sheaves, for a predicate `Q` on the coefficient category stable
under finite products, its stability under restriction, finite products and locality on the
base, and the resulting statements of Stacks 095B: direct image along a finite étale morphism
preserves local constancy and the accompanying finiteness condition for sheaves of sets, of
abelian groups and of modules.

## References

* [Stacks Project, Tag 095B](https://stacks.math.columbia.edu/tag/095B)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v r w

namespace Stacks.ConstantSheaf

section LocallyQConstant

open CategoryTheory.Limits

/-- Sheafification transports along an equivalence of sites. -/
private lemma hasWeakSheafify_of_equivalence {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D) (A : Type*)
    [Category* A] [HasWeakSheafify K A] [e.inverse.IsDenseSubsite K J] :
    HasWeakSheafify J A := by
  have hiso := Equivalence.transportIsoSheafToPresheaf J K e A
  exact ⟨_, ⟨((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction K A)).comp
    (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight hiso⟩⟩

/-- The small étale site of the scheme underlying an object of a small étale site admits
sheafification. -/
private lemma hasWeakSheafify_smallEtale_left {X : Scheme.{u}} (U : X.Etale) (A : Type*)
    [Category* A] [HasWeakSheafify ((smallEtaleTopology X).over U) A] :
    HasWeakSheafify (smallEtaleTopology U.left) A := by
  let _ := smallEtaleOverInverse_isDenseSubsite U
  let _ : Functor.IsDenseSubsite ((smallEtaleTopology X).over U) (smallEtaleTopology U.left)
      (smallEtaleOverEquivalence U).symm.inverse :=
    inferInstanceAs (Functor.IsDenseSubsite ((smallEtaleTopology X).over U)
      (smallEtaleTopology U.left) (smallEtaleOverEquivalence U).functor)
  exact hasWeakSheafify_of_equivalence (smallEtaleTopology U.left)
    ((smallEtaleTopology X).over U) (smallEtaleOverEquivalence U).symm A

/-- Local `Q`-constancy of a sheaf on the small étale site of a scheme: every object of the
site is covered by objects on which the sheaf restricts to a constant sheaf whose value
satisfies `Q`. -/
private def IsLocallyQConstant {Z : Scheme.{u}} {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) : Prop :=
  ∀ W : Z.Etale, ∃ (I : Type (u + 1)) (T : I → Z.Etale) (g : ∀ i, T i ⟶ W),
    Sieve.ofArrows T g ∈ smallEtaleTopology Z W ∧ ∀ i, ∃ E : A, Q E ∧ Nonempty
      ((constantSheaf (smallEtaleTopology (T i).left) A).obj E ≅
        (etaleRestrict (T i).hom (T i).prop A).obj G)

/-- Composition of étale morphisms, as a comparison of the induced functors. -/
private def etaleCompComp {Z'' Z' Z : Scheme.{u}} (q : Z'' ⟶ Z') (hq : Etale q)
    (p : Z' ⟶ Z) (hp : Etale p) (hqp : Etale (q ≫ p)) :
    etaleComp q hq ⋙ etaleComp p hp ≅ etaleComp (q ≫ p) hqp :=
  NatIso.ofComponents (fun W ↦ MorphismProperty.Over.isoMk (Iso.refl W.left) (by simp))
    (fun g ↦ by
      apply MorphismProperty.Over.Hom.ext
      change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
      simp)

/-- Restricting twice is restricting along the composite. -/
private def etaleRestrictComp {Z'' Z' Z : Scheme.{u}} (q : Z'' ⟶ Z') (hq : Etale q)
    (p : Z' ⟶ Z) (hp : Etale p) (hqp : Etale (q ≫ p)) (A : Type*) [Category* A]
    (F : Sheaf (smallEtaleTopology Z) A) :
    (etaleRestrict q hq A).obj ((etaleRestrict p hp A).obj F) ≅
      (etaleRestrict (q ≫ p) hqp A).obj F :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology Z'') A).preimageIso
    (Functor.isoWhiskerRight (NatIso.op (etaleCompComp q hq p hp hqp)) F.obj).symm

private lemma etaleRestrict_congr {Z' Z : Scheme.{u}} {p p' : Z' ⟶ Z} (hp : Etale p)
    (hp' : Etale p') (hpp' : p = p') (A : Type*) [Category* A] :
    etaleRestrict p hp A = etaleRestrict p' hp' A := by
  subst hpp'
  rfl

/-- Transfer of a trivialization from the localized site to the small étale site of the
underlying scheme. -/
private def constantIso_etaleRestrict {X : Scheme.{u}} (U : X.Etale) {A : Type*} [Category* A]
    [HasWeakSheafify ((smallEtaleTopology X).over U) A]
    [HasWeakSheafify (smallEtaleTopology U.left) A] (G : Sheaf (smallEtaleTopology X) A)
    (E : A) (e : (constantSheaf ((smallEtaleTopology X).over U) A).obj E ≅
      ((smallEtaleTopology X).overPullback A U).obj G) :
    (constantSheaf (smallEtaleTopology U.left) A).obj E ≅
      (etaleRestrict U.hom U.prop A).obj G :=
  ((constantSheaf_smallEtaleOverSheafEquivalence_iso U A).app E).symm ≪≫
    (smallEtaleOverSheafEquivalence U A).functor.mapIso e

/-- Transfer of a trivialization from the small étale site of the underlying scheme to the
localized site. -/
private def constantIso_overPullback {X : Scheme.{u}} (U : X.Etale) {A : Type*} [Category* A]
    [HasWeakSheafify ((smallEtaleTopology X).over U) A]
    [HasWeakSheafify (smallEtaleTopology U.left) A] (G : Sheaf (smallEtaleTopology X) A)
    (E : A) (e : (constantSheaf (smallEtaleTopology U.left) A).obj E ≅
      (etaleRestrict U.hom U.prop A).obj G) :
    (constantSheaf ((smallEtaleTopology X).over U) A).obj E ≅
      ((smallEtaleTopology X).overPullback A U).obj G :=
  (smallEtaleOverSheafEquivalence U A).functor.preimageIso
    ((constantSheaf_smallEtaleOverSheafEquivalence_iso U A).app E ≪≫ e)

/-- Sheafification on a localized small étale site, from sheafification on the small étale
site of the underlying scheme. -/
private lemma hasWeakSheafify_over_of_left {Z : Scheme.{u}} (T : Z.Etale) (A : Type*)
    [Category* A] [HasWeakSheafify (smallEtaleTopology T.left) A] :
    HasWeakSheafify ((smallEtaleTopology Z).over T) A := by
  let _ := smallEtaleOverInverse_isDenseSubsite T
  exact hasWeakSheafify_of_equivalence ((smallEtaleTopology Z).over T)
    (smallEtaleTopology T.left) (smallEtaleOverEquivalence T) A

/-- Objects of the small étale site of `T.left` are objects of the small étale site of `Z`. -/
private lemma hasWeakSheafify_left_of_etale {Z : Scheme.{u}} (T : Z.Etale) (A : Type*)
    [Category* A] [hA : ∀ S : Z.Etale, HasWeakSheafify (smallEtaleTopology S.left) A] :
    ∀ S : T.left.Etale, HasWeakSheafify (smallEtaleTopology S.left) A :=
  fun S ↦ hA ((etaleComp T.hom T.prop).obj S)

/-- Restriction of a constant sheaf is constant. -/
private def etaleRestrict_constantSheaf_iso {Z : Scheme.{u}} (T : Z.Etale) (A : Type*)
    [Category* A] [hA : ∀ S : Z.Etale, HasWeakSheafify (smallEtaleTopology S.left) A]
    [HasWeakSheafify (smallEtaleTopology Z) A] (E : A) :
    (etaleRestrict T.hom T.prop A).obj ((constantSheaf (smallEtaleTopology Z) A).obj E) ≅
      (constantSheaf (smallEtaleTopology T.left) A).obj E := by
  letI : ∀ S : Z.Etale, HasWeakSheafify ((smallEtaleTopology Z).over S) A := fun S ↦
    hasWeakSheafify_over_of_left S A
  exact constantSheaf_smallEtaleRestriction_iso T A E

/-- Restriction along an étale morphism preserves finite products of sheaves. -/
private lemma preservesFiniteProducts_etaleRestrict {Z' Z : Scheme.{u}} (p : Z' ⟶ Z)
    (hp : Etale p) (A : Type*) [Category* A] [HasFiniteProducts A] :
    PreservesFiniteProducts (etaleRestrict p hp A) := by
  constructor
  intro K
  have hcomp : PreservesLimitsOfShape (Discrete (Fin K))
      (etaleRestrict p hp A ⋙ sheafToPresheaf (smallEtaleTopology Z') A) := by
    change PreservesLimitsOfShape (Discrete (Fin K))
      (sheafToPresheaf (smallEtaleTopology Z) A ⋙
        (Functor.whiskeringLeft _ _ A).obj (etaleComp p hp).op)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves (etaleRestrict p hp A)
    (sheafToPresheaf (smallEtaleTopology Z') A)

/-- A trivialization over an object of the small étale site restricts to any object over
it. -/
private def constantIso_of_hom {Z : Scheme.{u}} {A : Type*} [Category* A]
    [hA : ∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    {S T : Z.Etale} (t : S ⟶ T) (G : Sheaf (smallEtaleTopology Z) A) (E : A)
    (e : (constantSheaf (smallEtaleTopology T.left) A).obj E ≅
      (etaleRestrict T.hom T.prop A).obj G) :
    (constantSheaf (smallEtaleTopology S.left) A).obj E ≅
      (etaleRestrict S.hom S.prop A).obj G := by
  letI := hasWeakSheafify_left_of_etale T A
  have hetale : Etale t.left := inferInstance
  have hcomp : Etale (t.left ≫ T.hom) := by
    rw [MorphismProperty.Over.w t]
    exact S.prop
  have e1 : (constantSheaf (smallEtaleTopology S.left) A).obj E ≅
      (etaleRestrict t.left hetale A).obj
        ((constantSheaf (smallEtaleTopology T.left) A).obj E) :=
    (etaleRestrict_constantSheaf_iso (MorphismProperty.Over.mk ⊤ t.left hetale) A E).symm
  have e2 : (etaleRestrict t.left hetale A).obj
        ((constantSheaf (smallEtaleTopology T.left) A).obj E) ≅
      (etaleRestrict t.left hetale A).obj ((etaleRestrict T.hom T.prop A).obj G) :=
    (etaleRestrict t.left hetale A).mapIso e
  have e3 : (etaleRestrict t.left hetale A).obj ((etaleRestrict T.hom T.prop A).obj G) ≅
      (etaleRestrict (t.left ≫ T.hom) hcomp A).obj G :=
    etaleRestrictComp t.left hetale T.hom T.prop hcomp A G
  have e4 : (etaleRestrict (t.left ≫ T.hom) hcomp A).obj G =
      (etaleRestrict S.hom S.prop A).obj G :=
    congrArg (fun k ↦ k.obj G) (etaleRestrict_congr hcomp S.prop (MorphismProperty.Over.w t) A)
  exact e1 ≪≫ e2 ≪≫ e3 ≪≫ eqToIso e4

/-- The sieve of objects over `W` on which `G` restricts to a constant sheaf whose value
satisfies `Q`. -/
private def qSieve {Z : Scheme.{u}} {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) (W : Z.Etale) : Sieve W where
  arrows S _ := ∃ E : A, Q E ∧ Nonempty
    ((constantSheaf (smallEtaleTopology S.left) A).obj E ≅
      (etaleRestrict S.hom S.prop A).obj G)
  downward_closed := by
    rintro S S' t ⟨E, hE, ⟨e⟩⟩ t'
    exact ⟨E, hE, ⟨constantIso_of_hom t' G E e⟩⟩

private lemma isLocallyQConstant_iff_qSieve_mem {Z : Scheme.{u}} {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) :
    IsLocallyQConstant Q G ↔ ∀ W : Z.Etale, qSieve Q G W ∈ smallEtaleTopology Z W := by
  refine ⟨fun h W ↦ ?_, fun h W ↦ ?_⟩
  · obtain ⟨I, T, g, hg, hT⟩ := h W
    refine (smallEtaleTopology Z).superset_covering ?_ hg
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro S t ⟨i⟩
    exact hT i
  · obtain ⟨I, T, g, heq⟩ := (qSieve Q G W).exists_eq_ofArrows
    exact ⟨I, T, g, heq ▸ h W,
      fun i ↦ (heq ▸ Sieve.ofArrows_mk T g i : qSieve Q G W (g i))⟩

/-- The trivializing sieve is local on the small étale site. -/
private lemma qSieve_mem_of_cover {Z : Scheme.{u}} {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) {W : Z.Etale}
    {I : Type*} (T : I → Z.Etale) (g : ∀ i, T i ⟶ W)
    (hg : Sieve.ofArrows T g ∈ smallEtaleTopology Z W)
    (hT : ∀ i, qSieve Q G (T i) ∈ smallEtaleTopology Z (T i)) :
    qSieve Q G W ∈ smallEtaleTopology Z W := by
  refine (smallEtaleTopology Z).transitive hg _ fun S t ht ↦ ?_
  obtain ⟨i, lift, -⟩ := Sieve.ofArrows.exists ht
  exact (smallEtaleTopology Z).superset_covering (fun R r hr ↦ hr)
    ((smallEtaleTopology Z).pullback_stable lift (hT i))

/-- If the restriction of `G` to the scheme underlying `W` is locally `Q`-constant, then the
trivializing sieve at `W` is covering. -/
private lemma qSieve_mem_of_restriction {Z : Scheme.{u}} {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) (W : Z.Etale)
    (h : @IsLocallyQConstant W.left A _ (hasWeakSheafify_left_of_etale W A) Q
      ((etaleRestrict W.hom W.prop A).obj G)) :
    qSieve Q G W ∈ smallEtaleTopology Z W := by
  let _ := hasWeakSheafify_left_of_etale W A
  obtain ⟨I, S, t, ht, hS⟩ := h (MorphismProperty.Over.mk ⊤ (𝟙 W.left)
    (inferInstanceAs (Etale (𝟙 W.left))))
  have hleft : ∀ i, (t i).left = (S i).hom := fun i ↦ by
    rw [← MorphismProperty.Over.w (t i)]
    exact (Category.comp_id _).symm
  have hcov : Sieve.ofArrows (fun i ↦ (etaleComp W.hom W.prop).obj (S i))
      (fun i ↦ MorphismProperty.Over.homMk (S i).hom rfl) ∈ smallEtaleTopology Z W := by
    refine (ofArrows_mem_smallEtaleTopology_iff _).mpr (Set.eq_univ_of_forall fun x ↦ ?_)
    have hx : x ∈ ⋃ i, Set.range (t i).left := by
      rw [(ofArrows_mem_smallEtaleTopology_iff t).mp ht]
      trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 hx
    refine Set.mem_iUnion.2 ⟨i, y, ?_⟩
    change (S i).hom y = x
    rw [← hleft i]
    exact hy
  refine (smallEtaleTopology Z).superset_covering ?_ hcov
  intro R r hr
  obtain ⟨i, lift, -⟩ := Sieve.ofArrows.exists hr
  obtain ⟨E, hE, ⟨e⟩⟩ := hS i
  have hc : Etale ((S i).hom ≫ W.hom) := ((etaleComp W.hom W.prop).obj (S i)).prop
  exact ⟨E, hE, ⟨constantIso_of_hom lift G E
    (e ≪≫ etaleRestrictComp (S i).hom (S i).prop W.hom W.prop hc A G)⟩⟩

/-- Local `Q`-constancy is stable under restriction along an étale morphism. -/
private lemma isLocallyQConstant_etaleRestrict {Z' Z : Scheme.{u}} (p : Z' ⟶ Z) (hp : Etale p)
    {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    [∀ T : Z'.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) (hG : IsLocallyQConstant Q G) :
    IsLocallyQConstant Q ((etaleRestrict p hp A).obj G) := by
  intro W
  obtain ⟨I, T, g, hg, hT⟩ := hG ((etaleComp p hp).obj W)
  let gl : ∀ i, (T i).left ⟶ W.left := fun i ↦ (g i).left
  have hgl : ∀ i, Etale (gl i) := fun i ↦ inferInstanceAs (Etale (g i).left)
  have hW : Etale W.hom := W.prop
  have hetale : ∀ i, Etale (gl i ≫ W.hom) := fun i ↦ by
    have := hgl i
    infer_instance
  refine ⟨I, fun i ↦ MorphismProperty.Over.mk ⊤ (gl i ≫ W.hom) (hetale i),
    fun i ↦ MorphismProperty.Over.homMk (gl i) rfl, ?_, fun i ↦ ?_⟩
  · exact (ofArrows_mem_smallEtaleTopology_iff _).mpr
      ((ofArrows_mem_smallEtaleTopology_iff g).mp hg)
  · obtain ⟨E, hE, ⟨e⟩⟩ := hT i
    have heq : (gl i ≫ W.hom) ≫ p = (T i).hom := by
      rw [Category.assoc]
      exact MorphismProperty.Over.w (g i)
    have hc : Etale ((gl i ≫ W.hom) ≫ p) := by
      rw [heq]
      exact (T i).prop
    have e5 : (etaleRestrict (T i).hom (T i).prop A).obj G =
        (etaleRestrict ((gl i ≫ W.hom) ≫ p) hc A).obj G :=
      congrArg (fun k ↦ k.obj G) (etaleRestrict_congr (T i).prop hc heq.symm A)
    exact ⟨E, hE, ⟨e ≪≫ eqToIso e5 ≪≫
      (etaleRestrictComp (gl i ≫ W.hom) (hetale i) p hp hc A G).symm⟩⟩

/-- A finite product of locally `Q`-constant sheaves is locally `Q`-constant, provided `Q` is
stable under the corresponding finite products. -/
private lemma isLocallyQConstant_pi {Z : Scheme.{u}} {A : Type*} [Category* A]
    [HasFiniteProducts A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (hconst : ∀ T : Z.Etale,
      PreservesFiniteProducts (constantSheaf (smallEtaleTopology T.left) A))
    (Q : A → Prop) {n : ℕ} (G : Fin n → Sheaf (smallEtaleTopology Z) A)
    (hQ : ∀ E : Fin n → A, (∀ j, Q (E j)) → Q (∏ᶜ E))
    (hG : ∀ j, IsLocallyQConstant Q (G j)) :
    IsLocallyQConstant Q (∏ᶜ G) := by
  classical
  intro W
  choose I T g hg hT using fun j ↦ hG j W
  obtain ⟨K, V, h, heq⟩ := (⨅ j, Sieve.ofArrows (T j) (g j)).exists_eq_ofArrows
  refine ⟨K, V, h, heq ▸ finite_intersection_covering (smallEtaleTopology Z) _ hg, fun k ↦ ?_⟩
  have hmem : ∀ j, Sieve.ofArrows (T j) (g j) (h k) := fun j ↦
    (iInf_le _ j : (⨅ j, Sieve.ofArrows (T j) (g j)) ≤ _) (h k)
      (heq ▸ Sieve.ofArrows_mk V h k)
  choose idx lift hfac using fun j ↦ Sieve.ofArrows.exists (hmem j)
  choose E hE e using fun j ↦ hT j (idx j)
  refine ⟨∏ᶜ E, hQ E hE, ⟨?_⟩⟩
  let := hconst (V k)
  let := preservesFiniteProducts_etaleRestrict (V k).hom (V k).prop A
  refine PreservesProduct.iso (constantSheaf (smallEtaleTopology (V k).left) A) E ≪≫ ?_
  refine Pi.mapIso (fun j ↦ constantIso_of_hom (lift j) (G j) (E j) (e j).some) ≪≫ ?_
  exact (PreservesProduct.iso (etaleRestrict (V k).hom (V k).prop A) G).symm

/-- Local `Q`-constancy stated on the localized sites. -/
private def IsOverQConstant {Z : Scheme.{u}} {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify ((smallEtaleTopology Z).over T) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) : Prop :=
  ∀ W : Z.Etale, ∃ (I : Type (u + 1)) (T : I → Z.Etale) (g : ∀ i, T i ⟶ W),
    Sieve.ofArrows T g ∈ smallEtaleTopology Z W ∧ ∀ i, ∃ E : A, Q E ∧ Nonempty
      ((constantSheaf ((smallEtaleTopology Z).over (T i)) A).obj E ≅
        ((smallEtaleTopology Z).overPullback A (T i)).obj G)

private lemma isOverQConstant_iff {Z : Scheme.{u}} {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify ((smallEtaleTopology Z).over T) A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) :
    IsOverQConstant Q G ↔ IsLocallyQConstant Q G := by
  refine ⟨fun h W ↦ ?_, fun h W ↦ ?_⟩
  · obtain ⟨I, T, g, hg, hT⟩ := h W
    refine ⟨I, T, g, hg, fun i ↦ ?_⟩
    obtain ⟨E, hE, ⟨e⟩⟩ := hT i
    exact ⟨E, hE, ⟨constantIso_etaleRestrict (T i) G E e⟩⟩
  · obtain ⟨I, T, g, hg, hT⟩ := h W
    refine ⟨I, T, g, hg, fun i ↦ ?_⟩
    obtain ⟨E, hE, ⟨e⟩⟩ := hT i
    exact ⟨E, hE, ⟨constantIso_overPullback (T i) G E e⟩⟩

/-- Local `Q`-constancy only depends on the isomorphism class of the sheaf. -/
private lemma isLocallyQConstant_of_iso {Z : Scheme.{u}} {A : Type*} [Category* A]
    [∀ T : Z.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (Q : A → Prop) {G G' : Sheaf (smallEtaleTopology Z) A} (ee : G ≅ G')
    (h : IsLocallyQConstant Q G) : IsLocallyQConstant Q G' := by
  intro W
  obtain ⟨I, T, g, hg, hT⟩ := h W
  refine ⟨I, T, g, hg, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hT i
  exact ⟨E, hE, ⟨e ≪≫ (etaleRestrict (T i).hom (T i).prop A).mapIso ee⟩⟩

/-- **The main step.** The direct image of a locally `Q`-constant sheaf along a morphism that
is étale-locally split is locally `Q`-constant, provided `Q` is stable under finite
products. -/
private lemma isLocallyQConstant_smallEtalePushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type*} [Category* A] [HasFiniteProducts A]
    [∀ T : X.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    [∀ T : Y.Etale, HasWeakSheafify (smallEtaleTopology T.left) A]
    (hconstY : ∀ T : Y.Etale,
      PreservesFiniteProducts (constantSheaf (smallEtaleTopology T.left) A))
    (hsplit : ∀ U : Y.Etale, ∃ (I : Type (u + 1)) (V : I → Y.Etale) (g : ∀ i, V i ⟶ U),
      Sieve.ofArrows V g ∈ smallEtaleTopology Y U ∧ ∀ i, Nonempty (Splitting f (V i)))
    (Q : A → Prop) (hQ : ∀ (n : ℕ) (E : Fin n → A), (∀ j, Q (E j)) → Q (∏ᶜ E))
    (F : Sheaf (smallEtaleTopology X) A) (hF : IsLocallyQConstant Q F) :
    IsLocallyQConstant Q ((smallEtalePushforward f A).obj F) := by
  rw [isLocallyQConstant_iff_qSieve_mem]
  intro U
  obtain ⟨I, V, g, hg, hV⟩ := hsplit U
  refine qSieve_mem_of_cover Q _ V g hg (fun i ↦ ?_)
  refine qSieve_mem_of_restriction Q _ (V i) ?_
  have := hasWeakSheafify_left_of_etale (V i) A
  obtain ⟨s⟩ := hV i
  obtain ⟨iso⟩ := nonempty_splitRestrictionIso s F
  refine isLocallyQConstant_of_iso Q iso.symm ?_
  refine isLocallyQConstant_pi
    (fun T ↦ hconstY ((etaleComp (V i).hom (V i).prop).obj T)) Q _ (hQ s.sheets) (fun j ↦ ?_)
  exact isLocallyQConstant_etaleRestrict (s.sheet j) (s.etale_sheet j) Q F hF

/-- `Stacks.ConstantSheaf.IsLocallyConstant` is the case of trivial `Q`. -/
private lemma isOverQConstant_true_of_isLocallyConstant {Z : Scheme.{u}} {A : Type*}
    [Category* A] [∀ T : Z.Etale, HasWeakSheafify ((smallEtaleTopology Z).over T) A]
    (G : Sheaf (smallEtaleTopology Z) A)
    [h : Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology Z) G] :
    IsOverQConstant (fun _ ↦ True) G := by
  intro W
  obtain ⟨I, T, g, hg, hT⟩ := h.exists_cover W
  refine ⟨I, T, g, hg, fun i ↦ ?_⟩
  obtain ⟨E, ⟨e⟩⟩ := (hT i).mem_essImage
  exact ⟨E, trivial, ⟨e⟩⟩

private lemma isLocallyConstant_of_isOverQConstant {Z : Scheme.{u}} {A : Type*}
    [Category* A] [∀ T : Z.Etale, HasWeakSheafify ((smallEtaleTopology Z).over T) A]
    (Q : A → Prop) (G : Sheaf (smallEtaleTopology Z) A) (h : IsOverQConstant Q G) :
    Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology Z) G := by
  refine ⟨fun W ↦ ?_⟩
  obtain ⟨I, T, g, hg, hT⟩ := h W
  refine ⟨I, T, g, hg, fun i ↦ ?_⟩
  obtain ⟨E, -, ⟨e⟩⟩ := hT i
  exact ⟨E, ⟨e⟩⟩

/-- Constant sheaves have finite products when sheafification is left exact. -/
private lemma preservesFiniteProducts_constantSheaf_of_hasSheafify {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (A : Type*) [Category* A]
    [CategoryTheory.Limits.HasFiniteLimits A] [HasSheafify J A] :
    CategoryTheory.Limits.PreservesFiniteProducts (constantSheaf J A) := by
  have hlim : CategoryTheory.Limits.PreservesFiniteLimits (constantSheaf J A) := by
    change CategoryTheory.Limits.PreservesFiniteLimits
      (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A)
    infer_instance
  constructor
  intro n
  infer_instance

/-- Constant sheaves have finite products when the target category is preadditive. -/
private lemma preservesFiniteProducts_constantSheaf_of_preadditive {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (A : Type*) [Category* A] [Preadditive A]
    [HasWeakSheafify J A] :
    CategoryTheory.Limits.PreservesFiniteProducts (constantSheaf J A) := by
  have h1 : (presheafToSheaf J A).Additive := (sheafificationAdjunction J A).left_adjoint_additive
  have h2 : (Functor.const Cᵒᵖ : A ⥤ _).Additive := { }
  have h3 : (constantSheaf J A).Additive :=
    inferInstanceAs (Functor.const _ ⋙ presheafToSheaf _ _).Additive
  infer_instance

/-- `Stacks.ConstantSheaf.IsFiniteLocallyConstant` is the case of finite values. -/
private lemma isOverQConstant_of_isFiniteLocallyConstant {Z : Scheme.{u}} {A : Type*}
    [Category* A] {FD : A → A → Type*} {CD : A → Type w}
    [∀ E E', FunLike (FD E E') (CD E) (CD E')] [ConcreteCategory.{w} A FD]
    [∀ T : Z.Etale, HasWeakSheafify ((smallEtaleTopology Z).over T) A]
    (G : Sheaf (smallEtaleTopology Z) A)
    [h : Stacks.ConstantSheaf.IsFiniteLocallyConstant (smallEtaleTopology Z) G] :
    IsOverQConstant (fun E ↦ Finite (CD E)) G :=
  h.exists_finite_cover

private lemma isFiniteLocallyConstant_of_isOverQConstant {Z : Scheme.{u}} {A : Type*}
    [Category* A] {FD : A → A → Type*} {CD : A → Type w}
    [∀ E E', FunLike (FD E E') (CD E) (CD E')] [ConcreteCategory.{w} A FD]
    [∀ T : Z.Etale, HasWeakSheafify ((smallEtaleTopology Z).over T) A]
    (G : Sheaf (smallEtaleTopology Z) A)
    (h : IsOverQConstant (fun E ↦ Finite (CD E)) G) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (smallEtaleTopology Z) G :=
  ⟨h⟩

/-- A finite product of objects with finite underlying type has finite underlying type. -/
private lemma finite_piObj {A : Type*} [Category* A] {FD : A → A → Type*} {CD : A → Type w}
    [∀ E E', FunLike (FD E E') (CD E) (CD E')] [ConcreteCategory.{w} A FD]
    [CategoryTheory.Limits.HasFiniteProducts A]
    [CategoryTheory.Limits.PreservesFiniteProducts (CategoryTheory.forget A)]
    {n : ℕ} (E : Fin n → A) (hE : ∀ j, Finite (CD (E j))) :
    Finite (CD (CategoryTheory.Limits.piObj E)) := by
  have hfin : ∀ j, Finite ((CategoryTheory.forget A).obj (E j)) := hE
  have e1 : (CategoryTheory.forget A).obj (CategoryTheory.Limits.piObj E) ≅
      CategoryTheory.Limits.piObj (fun j ↦ (CategoryTheory.forget A).obj (E j)) :=
    CategoryTheory.Limits.PreservesProduct.iso (CategoryTheory.forget A) E
  have e2 : CategoryTheory.Limits.piObj (fun j ↦ (CategoryTheory.forget A).obj (E j)) ≅
      (∀ j, (CategoryTheory.forget A).obj (E j)) :=
    CategoryTheory.Limits.Types.productIso _
  exact Finite.of_equiv _ (e1 ≪≫ e2).toEquiv.symm

/-- The direct image of a sheaf that is locally constant with values satisfying `Q` is again
locally constant with values satisfying `Q`. -/
private lemma isOverQConstant_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    {A : Type*} [Category* A] [CategoryTheory.Limits.HasFiniteProducts A]
    [∀ T : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over T) A]
    [∀ T : Y.Etale, HasWeakSheafify ((smallEtaleTopology Y).over T) A]
    (hconstY : ∀ (T : Y.Etale) [HasWeakSheafify (smallEtaleTopology T.left) A],
      CategoryTheory.Limits.PreservesFiniteProducts (constantSheaf (smallEtaleTopology T.left) A))
    (Q : A → Prop)
    (hQ : ∀ (n : ℕ) (E : Fin n → A), (∀ j, Q (E j)) → Q (CategoryTheory.Limits.piObj E))
    (F : Sheaf (smallEtaleTopology X) A) (hF : IsOverQConstant Q F) :
    IsOverQConstant Q ((smallEtalePushforward f A).obj F) := by
  let _ : ∀ T : X.Etale, HasWeakSheafify (smallEtaleTopology T.left) A :=
    fun T ↦ hasWeakSheafify_smallEtale_left T A
  let _ : ∀ T : Y.Etale, HasWeakSheafify (smallEtaleTopology T.left) A :=
    fun T ↦ hasWeakSheafify_smallEtale_left T A
  rw [isOverQConstant_iff] at hF ⊢
  exact isLocallyQConstant_smallEtalePushforward f (fun T ↦ hconstY T)
    (exists_splitting_cover f) Q hQ F hF

end LocallyQConstant

/-- Direct image of a locally constant étale sheaf of sets along a finite étale
morphism is locally constant. -/
@[stacks 095B "locally constant sheaves of sets"]
public theorem isLocallyConstant_finiteEtalePushforward {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    [Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology X) F] :
    Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology Y)
      (((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X)).obj F) := by
  exact isLocallyConstant_of_isOverQConstant _ _
    (isOverQConstant_pushforward f
      (fun _ ↦ preservesFiniteProducts_constantSheaf_of_hasSheafify _ _)
      (fun _ ↦ True) (fun _ _ _ ↦ trivial) F
      (isOverQConstant_true_of_isLocallyConstant F))

/-- Direct image of a finite locally constant étale sheaf of sets along a finite
étale morphism is finite locally constant. -/
@[stacks 095B "finite locally constant sheaves of sets"]
public theorem isFiniteLocallyConstant_finiteEtalePushforward {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant (smallEtaleTopology X) F] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (smallEtaleTopology Y)
      (((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X)).obj F) := by
  exact isFiniteLocallyConstant_of_isOverQConstant _
    (isOverQConstant_pushforward f
      (fun _ ↦ preservesFiniteProducts_constantSheaf_of_hasSheafify _ _)
      _ (fun _ E hE ↦ finite_piObj E hE) F
      (isOverQConstant_of_isFiniteLocallyConstant F))

/-- Direct image of a locally constant étale sheaf of abelian groups along a
finite étale morphism is locally constant. -/
@[stacks 095B "locally constant sheaves of abelian groups"]
public theorem isLocallyConstant_finiteEtalePushforward_abelian {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    [∀ U : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{max (u + 1) v}]
    [∀ V : Y.Etale, HasWeakSheafify ((smallEtaleTopology Y).over V) AddCommGrpCat.{max (u + 1) v}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})
    [Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology X) F] :
    Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology Y)
      (((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology Y) (smallEtaleTopology X)).obj F) := by
  exact isLocallyConstant_of_isOverQConstant _ _
    (isOverQConstant_pushforward f
      (fun _ ↦ preservesFiniteProducts_constantSheaf_of_preadditive _ _)
      (fun _ ↦ True) (fun _ _ _ ↦ trivial) F
      (isOverQConstant_true_of_isLocallyConstant F))

/-- Direct image of a finite locally constant étale sheaf of abelian groups
along a finite étale morphism is finite locally constant. -/
@[stacks 095B "finite locally constant sheaves of abelian groups"]
public theorem isFiniteLocallyConstant_finiteEtalePushforward_abelian {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    [∀ U : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{max (u + 1) v}]
    [∀ V : Y.Etale, HasWeakSheafify ((smallEtaleTopology Y).over V) AddCommGrpCat.{max (u + 1) v}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant (smallEtaleTopology X) F] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (smallEtaleTopology Y)
      (((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology Y) (smallEtaleTopology X)).obj F) := by
  exact isFiniteLocallyConstant_of_isOverQConstant _
    (isOverQConstant_pushforward f
      (fun _ ↦ preservesFiniteProducts_constantSheaf_of_preadditive _ _)
      _ (fun _ E hE ↦ finite_piObj E hE) F
      (isOverQConstant_of_isFiniteLocallyConstant F))

/-- Direct image of a locally constant étale sheaf of modules along a finite
étale morphism is locally constant. -/
@[stacks 095B "locally constant sheaves of modules"]
public theorem isLocallyConstant_finiteEtalePushforward_modules {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    (R : Type r) [Ring R]
    [∀ U : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over U) (ModuleCat.{max (u + 1) v} R)]
    [∀ V : Y.Etale, HasWeakSheafify ((smallEtaleTopology Y).over V) (ModuleCat.{max (u + 1) v} R)]
    (F : Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} R))
    [Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology X) F] :
    Stacks.ConstantSheaf.IsLocallyConstant (smallEtaleTopology Y)
      (((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) v} R) (smallEtaleTopology Y) (smallEtaleTopology X)).obj F) := by
  exact isLocallyConstant_of_isOverQConstant _ _
    (isOverQConstant_pushforward f
      (fun _ ↦ preservesFiniteProducts_constantSheaf_of_preadditive _ _)
      (fun _ ↦ True) (fun _ _ _ ↦ trivial) F
      (isOverQConstant_true_of_isLocallyConstant F))

/-- Direct image of a finite-type locally constant étale sheaf of modules
along a finite étale morphism is finite-type locally constant. -/
@[stacks 095B "finite-type locally constant sheaves of modules"]
public theorem isFiniteTypeLocallyConstant_finiteEtalePushforward_modules {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    (R : Type r) [Ring R]
    [∀ U : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over U) (ModuleCat.{max (u + 1) v} R)]
    [∀ V : Y.Etale, HasWeakSheafify ((smallEtaleTopology Y).over V) (ModuleCat.{max (u + 1) v} R)]
    (F : Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} R))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R (smallEtaleTopology X) F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R (smallEtaleTopology Y)
      (((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) v} R) (smallEtaleTopology Y) (smallEtaleTopology X)).obj F) := by
  exact isOverQConstant_pushforward f
    (fun _ ↦ preservesFiniteProducts_constantSheaf_of_preadditive _ _) (ModuleCat.isFG R)
    (fun _ E hE ↦ module_product_isFG R E hE) F hF

end Stacks.ConstantSheaf
