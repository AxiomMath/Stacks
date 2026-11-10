module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitOver
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Localized étale sites and sheaves on disjoint covers

Auxiliary material for the direct image of locally constant étale sheaves under finite étale
morphisms (Stacks 095B): the equivalence between the localized small étale site `X_étale/U` and
the small étale site of `U`, compatible with constant sheaves; the fact that a sheaf takes a
disjoint covering family to the product of its values; and the empty initial object of the
small étale site.

## References

* [Stacks Project, Tag 095B](https://stacks.math.columbia.edu/tag/095B)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v r

namespace Stacks.ConstantSheaf

/-- The constant sheaf on the localized site `J.over U` is the restriction of the constant
sheaf on `J`. -/
def constantSheaf_overPullback_iso
    {C : Type*} [Category* C] [CategoryTheory.Limits.HasFiniteLimits C]
    (J : GrothendieckTopology C) {A : Type*} [Category* A]
    [HasWeakSheafify J A] [∀ U : C, HasWeakSheafify (J.over U) A]
    (U : C) (E : A) :
    (constantSheaf (J.over U) A).obj E ≅
      (J.overPullback A U).obj ((constantSheaf J A).obj E) := by
  let adj := Over.forgetAdjStar U
  letI := adj.isRightAdjoint
  exact (((constantSheafAdj J A CategoryTheory.Limits.terminalIsTerminal).comp
    (adj.sheafPushforwardContinuous (J.over U) J)).leftAdjointUniq
      (constantSheafAdj (J.over U) A
        (CategoryTheory.Limits.terminalIsTerminal.isTerminalObj (Over.star U)
          (CategoryTheory.Limits.terminal C)))).app E |>.symm

private lemma finite_intersection_covering
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {U : C} {index : Type*} [Finite index] (S : index → Sieve U)
    (hS : ∀ component, S component ∈ J U) : (⨅ component, S component) ∈ J U := by
  classical
  let := Fintype.ofFinite index
  have hfinite : ∀ components : Finset index,
      (⨅ component ∈ components, S component) ∈ J U := by
    intro components
    induction components using Finset.induction_on with
    | empty => simp
    | @insert component components hnotmem hind =>
      simpa only [Finset.iInf_insert] using J.intersection_covering (hS component) hind
  simpa using hfinite Finset.univ

/-- A finite product of finitely generated modules is finitely generated. -/
lemma module_product_isFG
    (R : Type r) [Ring R] {index : Type} [Finite index]
    (E : index → ModuleCat.{v} R) (hE : ∀ component, ModuleCat.isFG R (E component)) :
    ModuleCat.isFG R (∏ᶜ E) := by
  classical
  let := Fintype.ofFinite index
  have : ∀ component, Module.Finite R (E component) := hE
  exact Module.Finite.equiv (ModuleCat.piIsoPi E).toLinearEquiv.symm

private def smallEtaleOverFunctor {X : Scheme.{u}} (U : X.Etale) :
    Over U ⥤ U.left.Etale where
  obj V := MorphismProperty.Over.mk ⊤ V.hom.left inferInstance
  map g := MorphismProperty.Over.homMk g.left.left (by
    have := congrArg (fun morphism ↦ morphism.left) g.w
    exact this)
  map_id _ := rfl
  map_comp _ _ := rfl

private def smallEtaleOverInverse {X : Scheme.{u}} (U : X.Etale) :
    U.left.Etale ⥤ Over U where
  obj V := Over.mk (MorphismProperty.Over.homMk
    (A := MorphismProperty.Over.mk (P := (@Etale : MorphismProperty Scheme.{u}))
      ⊤ (V.hom ≫ U.hom) inferInstance)
    (B := U) V.hom)
  map {V W} g := Over.homMk (MorphismProperty.Over.homMk g.left (by
    change g.left ≫ (W.hom ≫ U.hom) = V.hom ≫ U.hom
    have h : g.left ≫ W.hom = V.hom := by simp
    rw [← Category.assoc, h])) (by
      apply MorphismProperty.Comma.Hom.ext
      · exact g.w
      · apply Subsingleton.elim)
  map_id _ := rfl
  map_comp _ _ := rfl

private def smallEtaleOverEquivalence {X : Scheme.{u}} (U : X.Etale) :
    Over U ≌ U.left.Etale where
  functor := smallEtaleOverFunctor U
  inverse := smallEtaleOverInverse U
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk
    (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (V.hom.left ≫ U.hom) = V.left.hom
      simp)) (by
        apply MorphismProperty.Comma.Hom.ext
        · change 𝟙 _ ≫ V.hom.left = V.hom.left
          simp
        · apply Subsingleton.elim)) (by
          intro V W g
          apply Over.OverMorphism.ext
          apply MorphismProperty.Comma.Hom.ext
          · change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
            simp
          · apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _)) (by
      intro V W g
      apply MorphismProperty.Comma.Hom.ext
      · change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
        simp
      · apply Subsingleton.elim)

private lemma smallEtaleOverFunctor_coverPreserving {X : Scheme.{u}} (U : X.Etale) :
    CoverPreserving ((smallEtaleTopology X).over U) (smallEtaleTopology U.left)
      (smallEtaleOverFunctor U) := by
  constructor
  intro V S hS
  obtain ⟨members, W, g, rfl⟩ := S.exists_eq_ofArrows
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hS
  rw [Sieve.functorPushforward_ofArrows]
  exact (ofArrows_mem_smallEtaleTopology_iff _).mpr
    ((ofArrows_mem_smallEtaleTopology_iff (fun member ↦ (g member).left)).mp hS)

private lemma smallEtaleOverInverse_coverPreserving {X : Scheme.{u}} (U : X.Etale) :
    CoverPreserving (smallEtaleTopology U.left) ((smallEtaleTopology X).over U)
      (smallEtaleOverInverse U) := by
  constructor
  intro V S hS
  obtain ⟨members, W, g, rfl⟩ := S.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  exact (ofArrows_mem_smallEtaleTopology_iff _).mpr ((ofArrows_mem_smallEtaleTopology_iff g).mp hS)

private lemma smallEtaleOverInverse_isDenseSubsite {X : Scheme.{u}} (U : X.Etale) :
    (smallEtaleOverEquivalence U).inverse.IsDenseSubsite
      (smallEtaleTopology U.left) ((smallEtaleTopology X).over U) := by
  have : (smallEtaleOverEquivalence U).functor.IsCocontinuous
      ((smallEtaleTopology X).over U) (smallEtaleTopology U.left) :=
    ((smallEtaleOverEquivalence U).toAdjunction.isCocontinuous_iff_coverPreserving
      _ _).mpr (smallEtaleOverInverse_coverPreserving U)
  have : (smallEtaleOverEquivalence U).inverse.IsCocontinuous
      (smallEtaleTopology U.left) ((smallEtaleTopology X).over U) :=
    ((smallEtaleOverEquivalence U).symm.toAdjunction.isCocontinuous_iff_coverPreserving
      _ _).mpr (smallEtaleOverFunctor_coverPreserving U)
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

private def smallEtaleOverSheafEquivalence {X : Scheme.{u}} (U : X.Etale)
    (A : Type*) [Category* A] :
    Sheaf ((smallEtaleTopology X).over U) A ≌ Sheaf (smallEtaleTopology U.left) A := by
  let := smallEtaleOverInverse_isDenseSubsite U
  exact (smallEtaleOverEquivalence U).sheafCongr _ _ A

private def smallEtaleRestriction {X : Scheme.{u}} (U : X.Etale)
    (A : Type*) [Category* A] :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology U.left) A :=
  (smallEtaleTopology X).overPullback A U ⋙
    (smallEtaleOverSheafEquivalence U A).functor

private def smallEtaleComposition {X : Scheme.{u}} (U : X.Etale) :
    U.left.Etale ⥤ X.Etale :=
  smallEtaleOverInverse U ⋙ Over.forget U

private lemma smallEtaleComposition_isContinuous {X : Scheme.{u}} (U : X.Etale) :
    (smallEtaleComposition U).IsContinuous
      (smallEtaleTopology U.left) (smallEtaleTopology X) := by
  let := smallEtaleOverInverse_isDenseSubsite U
  have : (smallEtaleOverInverse U).IsContinuous
      (smallEtaleTopology U.left) ((smallEtaleTopology X).over U) :=
    inferInstanceAs ((smallEtaleOverEquivalence U).inverse.IsContinuous _ _)
  exact Functor.isContinuous_comp _ _ (smallEtaleTopology U.left)
    ((smallEtaleTopology X).over U) (smallEtaleTopology X)

private def constantSheaf_smallEtaleOverSheafEquivalence_iso
    {X : Scheme.{u}} (U : X.Etale) (A : Type*) [Category* A]
    [HasWeakSheafify ((smallEtaleTopology X).over U) A]
    [HasWeakSheafify (smallEtaleTopology U.left) A] :
    constantSheaf ((smallEtaleTopology X).over U) A ⋙
      (smallEtaleOverSheafEquivalence U A).functor ≅
        constantSheaf (smallEtaleTopology U.left) A := by
  let := smallEtaleOverInverse_isDenseSubsite U
  let adj := (smallEtaleOverEquivalence U).symm.toAdjunction
  have : (smallEtaleOverEquivalence U).symm.functor.IsContinuous (smallEtaleTopology U.left)
      ((smallEtaleTopology X).over U) :=
    inferInstanceAs ((smallEtaleOverEquivalence U).inverse.IsContinuous _ _)
  have : (smallEtaleOverEquivalence U).symm.inverse.IsContinuous ((smallEtaleTopology X).over U)
      (smallEtaleTopology U.left) :=
    inferInstanceAs ((smallEtaleOverEquivalence U).functor.IsContinuous _ _)
  let hterminal := Over.mkIdTerminal (X := U)
  exact ((constantSheafAdj ((smallEtaleTopology X).over U) A hterminal).comp
    (adj.sheafPushforwardContinuous (smallEtaleTopology U.left)
      ((smallEtaleTopology X).over U))).leftAdjointUniq
        (constantSheafAdj (smallEtaleTopology U.left) A
          (hterminal.isTerminalObj (smallEtaleOverEquivalence U).functor (Over.mk (𝟙 U))))

private def constantSheaf_smallEtaleRestriction_iso
    {X : Scheme.{u}} (U : X.Etale) (A : Type*) [Category* A]
    [HasWeakSheafify (smallEtaleTopology X) A]
    [∀ V : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over V) A]
    [HasWeakSheafify (smallEtaleTopology U.left) A] (E : A) :
    (smallEtaleRestriction U A).obj ((constantSheaf (smallEtaleTopology X) A).obj E) ≅
      (constantSheaf (smallEtaleTopology U.left) A).obj E :=
  (smallEtaleOverSheafEquivalence U A).functor.mapIso
    (constantSheaf_overPullback_iso (smallEtaleTopology X) U E).symm ≪≫
    (constantSheaf_smallEtaleOverSheafEquivalence_iso U A).app E

section DisjointSections

open CategoryTheory.Limits Opposite

/-- The sieve generated by the empty family of arrows is the bottom sieve. -/
private lemma sieve_ofArrows_empty {C : Type*} [Category* C] (T : C) :
    Sieve.ofArrows (X := T) Empty.elim Empty.instIsEmpty.elim = ⊥ := by
  ext W g
  simp only [Sieve.mem_ofArrows_iff]
  exact ⟨fun ⟨member, _, _⟩ ↦ member.elim, fun h ↦ h.elim⟩

/-- Two arrows into the summands of a disjoint cofan that agree on the sum induce the same
map on sections, provided maps into the sections over the initial object are unique. -/
private theorem eq_of_comp_inj_eq {C : Type*} [Category* C] [HasInitial C]
    {D : Type*} [Category* D] (F : Cᵒᵖ ⥤ D)
    {index : Type*} {Z : index → C} (c : Cofan Z) (hmono : ∀ member, Mono (c.inj member))
    {A : D} (p : ∀ member, A ⟶ F.obj (op (Z member)))
    (hdisj : Pairwise fun first second ↦ IsPullback (initial.to (Z first))
      (initial.to (Z second)) (c.inj first) (c.inj second))
    (hzero : Subsingleton (A ⟶ F.obj (op (⊥_ C))))
    {T : C} {first second : index} (q : T ⟶ Z first) (q' : T ⟶ Z second)
    (hq : q ≫ c.inj first = q' ≫ c.inj second) :
    p first ≫ F.map q.op = p second ≫ F.map q'.op := by
  by_cases hfs : first = second
  · subst hfs
    have := hmono first
    obtain rfl : q = q' := (cancel_mono (c.inj first)).1 hq
    rfl
  · have hpb := hdisj hfs
    have hzero' : p first ≫ F.map (initial.to (Z first)).op =
        p second ≫ F.map (initial.to (Z second)).op := hzero.elim _ _
    calc p first ≫ F.map q.op
        = p first ≫ F.map (initial.to (Z first)).op ≫ F.map (hpb.lift q q' hq).op := by
          rw [← F.map_comp, ← op_comp, hpb.lift_fst]
      _ = p second ≫ F.map (initial.to (Z second)).op ≫ F.map (hpb.lift q q' hq).op := by
          rw [← Category.assoc, ← Category.assoc, hzero']
      _ = p second ≫ F.map q'.op := by
          rw [← F.map_comp, ← op_comp, hpb.lift_snd]

/-- Sections over an object admitting a map to the initial object are unique, for a sheaf
whose topology covers the initial object by the empty sieve. -/
private theorem subsingleton_hom_sections_of_to_initial {C : Type*} [Category* C] [HasInitial C]
    {D : Type*} [Category* D] (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ D)
    (hF : Presheaf.IsSheaf J F) (hempty : (⊥ : Sieve (⊥_ C)) ∈ J (⊥_ C))
    (A : D) (T : C) (q : T ⟶ ⊥_ C) : Subsingleton (A ⟶ F.obj (op T)) := by
  classical
  have hsheaf : Presieve.IsSheafFor (F ⋙ coyoneda.obj (op A))
      (Presieve.ofArrows (X := T) Empty.elim Empty.instIsEmpty.elim) := by
    refine (hF A).isSheafFor _ ?_
    rw [show Sieve.generate (Presieve.ofArrows (X := T) Empty.elim Empty.instIsEmpty.elim) =
      Sieve.ofArrows (X := T) Empty.elim Empty.instIsEmpty.elim from rfl,
      sieve_ofArrows_empty T]
    simpa using J.pullback_stable q hempty
  have hterm := Presieve.isTerminal_of_isSheafFor_empty_presieve T
    (F ⋙ coyoneda.obj (op A)) hsheaf
  refine ⟨fun a b ↦ ?_⟩
  change (F ⋙ coyoneda.obj (op A)).obj (op T) at a b
  have hunique : Unique ((F ⋙ coyoneda.obj (op A)).obj (op T)) :=
    (Types.isTerminalEquivUnique _).toFun hterm
  exact (hunique.uniq a).trans (hunique.uniq b).symm

/-- A factorization of every arrow of the sieve generated by a cofan through one of the
cofan's injections. -/
private abbrev CofanFactor {C : Type*} [Category* C]
    {index : Type*} {Z : index → C} (c : Cofan Z) : Type _ :=
  ∀ {T : C} (p : T ⟶ c.pt), (Sieve.ofArrows Z c.inj).arrows p →
    Σ member, {q : T ⟶ Z member // p = q ≫ c.inj member}

/-- The family of local sections of `F` over the sieve generated by a cofan that is
determined by a fan of sections over the cofan's summands. -/
private def cofanFamily {C : Type*} [Category* C]
    {D : Type*} [Category* D] (F : Cᵒᵖ ⥤ D)
    {index : Type*} {Z : index → C} (c : Cofan Z) (factor : CofanFactor c)
    (s : Fan fun member ↦ F.obj (op (Z member))) :
    Presieve.FamilyOfElements (F ⋙ coyoneda.obj (op s.pt))
      (Sieve.ofArrows Z c.inj).arrows :=
  fun {_} p hp ↦ s.proj (factor p hp).1 ≫ F.map (factor p hp).2.1.op

/-- The family of local sections determined by a fan is compatible, because the summands of a
disjoint cofan meet only in the initial object. -/
private theorem cofanFamily_compatible {C : Type*} [Category* C] [HasInitial C]
    {D : Type*} [Category* D] (F : Cᵒᵖ ⥤ D)
    {index : Type*} {Z : index → C} (c : Cofan Z) (factor : CofanFactor c)
    (hmono : ∀ member, Mono (c.inj member))
    (s : Fan fun member ↦ F.obj (op (Z member)))
    (hdisj : Pairwise fun first second ↦ IsPullback (initial.to (Z first))
      (initial.to (Z second)) (c.inj first) (c.inj second))
    (hzero : Subsingleton (s.pt ⟶ F.obj (op (⊥_ C)))) :
    (cofanFamily F c factor s).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro T W p g hp
  let d := factor p hp
  let d' := factor (g ≫ p) ((Sieve.ofArrows Z c.inj).downward_closed hp g)
  have heq : d'.2.1 ≫ c.inj d'.1 = (g ≫ d.2.1) ≫ c.inj d.1 := by
    calc d'.2.1 ≫ c.inj d'.1 = g ≫ p := d'.2.2.symm
      _ = g ≫ d.2.1 ≫ c.inj d.1 := congrArg (fun k : T ⟶ c.pt ↦ g ≫ k) d.2.2
      _ = _ := by simp
  have heq' := eq_of_comp_inj_eq F c hmono s.proj hdisj hzero d'.2.1 (g ≫ d.2.1) heq
  change s.proj d'.1 ≫ F.map d'.2.1.op = (s.proj d.1 ≫ F.map d.2.1.op) ≫ F.map g.op
  calc s.proj d'.1 ≫ F.map d'.2.1.op = s.proj d.1 ≫ F.map (g ≫ d.2.1).op := heq'
    _ = (s.proj d.1 ≫ F.map d.2.1.op) ≫ F.map g.op := by
        simp [← Functor.map_comp]

/-- **Sections over a disjoint union.** For a sheaf `F`, the restriction maps to the summands
of a disjoint covering cofan exhibit the sections over the sum as their product. The cofan is
only required to be disjoint and covering; it need not be a colimit. -/
private noncomputable def isLimit_fan_sections_of_disjoint_cover {C : Type*} [Category* C]
    [HasInitial C] {D : Type*} [Category* D]
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ D) (hF : Presheaf.IsSheaf J F)
    {index : Type*} {Z : index → C} (c : Cofan Z) (factor : CofanFactor c)
    (hmono : ∀ member, Mono (c.inj member))
    (hdisj : Pairwise fun first second ↦ IsPullback (initial.to (Z first))
      (initial.to (Z second)) (c.inj first) (c.inj second))
    (hempty : (⊥ : Sieve (⊥_ C)) ∈ J (⊥_ C))
    (hcover : Sieve.ofArrows Z c.inj ∈ J c.pt) :
    IsLimit (Fan.mk (F.obj (op c.pt)) (fun member ↦ F.map (c.inj member).op)) := by
  have hzero : ∀ A : D, Subsingleton (A ⟶ F.obj (op (⊥_ C))) := fun A ↦
    subsingleton_hom_sections_of_to_initial J F hF hempty A _ (𝟙 _)
  have hPS : ∀ s : Fan fun member ↦ F.obj (op (Z member)),
      Presieve.IsSheafFor (F ⋙ coyoneda.obj (op s.pt))
        (Sieve.ofArrows Z c.inj).arrows := fun s ↦
    (hF s.pt).isSheafFor _ (by simpa using hcover)
  have hcomp : ∀ s : Fan fun member ↦ F.obj (op (Z member)),
      (cofanFamily F c factor s).Compatible := fun s ↦
    cofanFamily_compatible F c factor hmono s hdisj (hzero s.pt)
  refine Fan.IsLimit.mk _
    (fun s ↦ (hPS s).amalgamate (cofanFamily F c factor s) (hcomp s)) (fun s member ↦ ?_)
    (fun s m hm ↦ ?_)
  · change (hPS s).amalgamate (cofanFamily F c factor s) (hcomp s) ≫ F.map (c.inj member).op =
      s.proj member
    have hin : (Sieve.ofArrows Z c.inj).arrows (c.inj member) :=
      (Sieve.mem_ofArrows_iff Z c.inj (c.inj member)).2 ⟨member, 𝟙 _, by simp⟩
    have ham := (hPS s).isAmalgamation (hcomp s) (c.inj member) hin
    change (hPS s).amalgamate (cofanFamily F c factor s) (hcomp s) ≫ F.map (c.inj member).op =
      cofanFamily F c factor s (c.inj member) hin at ham
    rw [ham]
    let d := factor (c.inj member) hin
    change s.proj d.1 ≫ F.map d.2.1.op = s.proj member
    have heq := eq_of_comp_inj_eq F c hmono s.proj hdisj (hzero s.pt) d.2.1 (𝟙 (Z member))
      (by simpa using d.2.2.symm)
    simpa using heq
  · have hm' : ∀ member, m ≫ F.map (c.inj member).op = s.proj member := hm
    refine ((hPS s) (cofanFamily F c factor s) (hcomp s)).unique ?_
      ((hPS s).isAmalgamation (hcomp s))
    intro T p hp
    let d := factor p hp
    change m ≫ F.map p.op = s.proj d.1 ≫ F.map d.2.1.op
    calc m ≫ F.map p.op = m ≫ F.map (d.2.1 ≫ c.inj d.1).op :=
          congrArg (fun k : T ⟶ c.pt ↦ m ≫ F.map k.op) d.2.2
      _ = (m ≫ F.map (c.inj d.1).op) ≫ F.map d.2.1.op := by simp [← Functor.map_comp]
      _ = s.proj d.1 ≫ F.map d.2.1.op := by rw [hm' d.1]

end DisjointSections

section EtaleSiteInitial

open CategoryTheory.Limits

/-- An object of the small étale site whose underlying scheme is empty is initial. -/
private def etaleIsInitial_of_isEmpty {X : Scheme.{u}} (T : X.Etale) (hT : IsEmpty T.left) :
    IsInitial T := by
  letI := hT
  refine IsInitial.ofUniqueHom (fun S ↦ MorphismProperty.Over.homMk
    (isInitialOfIsEmpty.to S.left) (isInitialOfIsEmpty.hom_ext _ _)) (fun S m ↦ ?_)
  apply MorphismProperty.Comma.Hom.ext
  · exact isInitialOfIsEmpty.hom_ext _ _
  · apply Subsingleton.elim

/-- The empty scheme is initial in the small étale site. -/
private def etaleEmptyIsInitial (X : Scheme.{u}) :
    IsInitial (Etale.mk (initial.to X)) :=
  etaleIsInitial_of_isEmpty _ initial_isEmpty

private instance hasInitial_etale (X : Scheme.{u}) : HasInitial X.Etale :=
  (etaleEmptyIsInitial X).hasInitial

/-- The underlying scheme of the initial object of the small étale site is empty. -/
private lemma isEmpty_left_initial (X : Scheme.{u}) : IsEmpty (⊥_ X.Etale).left := by
  let _ : IsEmpty (Etale.mk (initial.to X)).left := initial_isEmpty
  exact Function.isEmpty (f := fun x ↦ (initialIsoIsInitial (etaleEmptyIsInitial X)).hom.left x)

/-- The initial object of the small étale site is covered by the empty family. -/
private lemma empty_mem_smallEtaleTopology (X : Scheme.{u}) :
    (⊥ : Sieve (⊥_ X.Etale)) ∈ smallEtaleTopology X (⊥_ X.Etale) := by
  rw [← sieve_ofArrows_empty (⊥_ X.Etale)]
  refine (ofArrows_mem_smallEtaleTopology_iff _).mpr ?_
  exact Set.eq_univ_of_forall fun x ↦ (isEmpty_left_initial X).elim x

/-- The vertex of a cone over two arrows of the small étale site with disjoint images has
empty underlying scheme. -/
private lemma isEmpty_left_of_cone {X : Scheme.{u}} {A B T : X.Etale}
    (a : A ⟶ T) (b : B ⟶ T)
    (hab : Disjoint (Set.range a.left) (Set.range b.left))
    (s : PullbackCone a b) : IsEmpty s.pt.left :=
  @Function.isEmpty _ _ (isEmpty_pullback_iff.mpr hab)
    (fun x ↦ Limits.pullback.lift (f := a.left) (g := b.left) s.fst.left s.snd.left
      (congrArg (fun k ↦ k.left) s.condition) x)

/-- Two arrows of the small étale site whose images are disjoint form a pullback square over
the initial object. -/
private lemma isPullback_initial_of_disjoint_range {X : Scheme.{u}} {A B T : X.Etale}
    (a : A ⟶ T) (b : B ⟶ T)
    (hab : Disjoint (Set.range a.left) (Set.range b.left)) :
    IsPullback (initial.to A) (initial.to B) a b := by
  have hinit (s : PullbackCone a b) : IsInitial s.pt :=
    etaleIsInitial_of_isEmpty s.pt (isEmpty_left_of_cone a b hab s)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (initial.hom_ext _ _)
    (fun s ↦ (hinit s).to _) (fun s ↦ (hinit s).hom_ext _ _) (fun s ↦ (hinit s).hom_ext _ _)
    (fun s m _ _ ↦ (hinit s).hom_ext _ _))

end EtaleSiteInitial

end Stacks.ConstantSheaf
