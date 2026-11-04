module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.FilteredColimitsAndCohomology

/-!
# Filtered colimits and cohomology over an object of a locally small site

Stacks 0739 says that filtered colimits of abelian sheaves commute with cohomology over an object
of a collection `B` which admits cofinal finite coverings whose iterated fibre products stay in
`B`. `Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections` states it for a small site,
with the coefficients and the index category of the diagram in the universe of the site.

This file proves it for a locally small site `C : Type u` with `Category.{v} C`, with
coefficients `Ab.{max z v u}` for every `z` and a filtered index category of that size. Such a
site need not be essentially small: the small étale site of a scheme `X : Scheme.{u}` has its
objects in `Type (u + 1)` and contains the coproduct `∐ i : I, X` for every `I : Type u`.

## Main results

* `Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections_largeCoefficients`:
  Stacks 0739 on a locally small site, with coefficients in any universe containing the site and
  an index category of that size.
* `Stacks.Cohomology.exists_widePullback_in`: a collection of objects closed under fibre products
  of two of its members over a third contains the vertex of a limiting wide-pullback cone over
  any finite family of its members.

## Implementation notes

`AsSmall.{z} C` is a small category whose objects and morphisms both lie in `Type (max z v u)`.
The site `C` is replaced by it, with the induced topology, and the comparison is carried back
along the induced equivalence of sheaf categories by `compRightDerivedNatIso`, since the
restriction functor is exact and preserves injectives. The collection `B` and the covering
families are transported by `hasIntersectionsIn_asSmall` and `exists_cover_asSmall`; since
`AsSmall.down` acts on objects by `ULift.down`, this can be stated for `B` itself rather than for
its isomorphism closure.

## References

* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe z t v u

namespace Stacks.Cohomology

noncomputable section

/-! ### Finite wide pullbacks from binary fibre products -/

/-- A collection of objects which contains the vertex of a fibre product of any two of its
members over any third contains the vertex of a limiting wide-pullback cone over any finite
family of its members. -/
theorem exists_widePullback_in {C : Type*} [Category* C] (B : Set C)
    (hpb : ∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W),
      B U → B V → B W → ∃ t : PullbackCone f g, Nonempty (IsLimit t) ∧ B t.pt)
    {U : C} (hU : B U) (n : ℕ) (Y : Fin n → C) (f : ∀ i, Y i ⟶ U)
    (hY : ∀ i, B (Y i)) :
    ∃ t : WidePullbackCone f, Nonempty (IsLimit t) ∧ B t.pt := by
  classical
  induction n with
  | zero =>
      let t : WidePullbackCone f := WidePullbackCone.mk (𝟙 U) (fun i ↦ Fin.elim0 i)
        (fun i ↦ Fin.elim0 i)
      refine ⟨t, ⟨?_⟩, hU⟩
      apply WidePullbackCone.IsLimit.mk t (fun s ↦ s.base)
      · exact fun s ↦ Category.comp_id _
      · exact fun s i ↦ Fin.elim0 i
      · exact fun s m hm _ ↦ (Category.comp_id m).symm.trans hm
  | succ n ih =>
      obtain ⟨t, ⟨ht⟩, htB⟩ := ih (fun i ↦ Y i.succ) (fun i ↦ f i.succ)
        (fun i ↦ hY i.succ)
      obtain ⟨q, ⟨hq⟩, hqB⟩ := hpb (f 0) t.base (hY 0) htB hU
      have hp : IsPullback q.fst q.snd (f 0) t.base := IsPullback.of_isLimit hq
      let a : ∀ i, q.pt ⟶ Y i := Fin.cases q.fst (fun i ↦ q.snd ≫ t.π i)
      have ha (i) : a i ≫ f i = q.fst ≫ f 0 := by
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rfl
        · dsimp [a]
          rw [Category.assoc, t.condition, q.condition]
      let s : WidePullbackCone f := WidePullbackCone.mk (q.fst ≫ f 0) a ha
      let tail (c : WidePullbackCone f) : c.pt ⟶ t.pt :=
        WidePullbackCone.IsLimit.lift ht c.base (fun i ↦ c.π i.succ)
          (fun i ↦ c.condition i.succ)
      have htail (c : WidePullbackCone f) : tail c ≫ t.base = c.base :=
        WidePullbackCone.IsLimit.lift_base _ _ _ _
      have htailπ (c : WidePullbackCone f) (i : Fin n) :
          tail c ≫ t.π i = c.π i.succ :=
        WidePullbackCone.IsLimit.lift_π _ _ _ _ _
      let lift (c : WidePullbackCone f) : c.pt ⟶ q.pt :=
        hp.lift (c.π 0) (tail c) ((c.condition 0).trans (htail c).symm)
      have hfst (c : WidePullbackCone f) : lift c ≫ q.fst = c.π 0 :=
        hp.lift_fst _ _ _
      have hsnd (c : WidePullbackCone f) : lift c ≫ q.snd = tail c :=
        hp.lift_snd _ _ _
      refine ⟨s, ⟨?_⟩, hqB⟩
      apply WidePullbackCone.IsLimit.mk s lift
      · intro c
        show lift c ≫ (q.fst ≫ f 0) = c.base
        rw [← Category.assoc, hfst, c.condition]
      · intro c i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact hfst c
        · show lift c ≫ (q.snd ≫ t.π j) = _
          rw [← Category.assoc, hsnd, htailπ]
      · intro c m hm hπ
        change c.pt ⟶ q.pt at m
        change m ≫ (q.fst ≫ f 0) = c.base at hm
        change ∀ i, m ≫ a i = c.π i at hπ
        apply hp.hom_ext
        · exact (hπ 0).trans (hfst c).symm
        · rw [hsnd]
          apply WidePullbackCone.IsLimit.hom_ext ht
          · rw [Category.assoc, ← q.condition, ← Category.assoc]
            simpa only [Category.assoc] using hm.trans (htail c).symm
          · intro i
            rw [Category.assoc, htailπ]
            exact hπ i.succ

/-! ### Transporting the hypotheses of Stacks 0739 to the small model -/

/-- A limiting wide-pullback cone over a family of arrows of a locally small category transports
to the equivalent small category `AsSmall C`, with the same vertex up to the universe lift. -/
theorem widePullback_asSmall {C : Type u} [Category.{v} C] {K : Type*}
    {U : AsSmall.{z} C} {Y : K → AsSmall.{z} C} (f : ∀ i, Y i ⟶ U)
    (c : WidePullbackCone (fun i ↦ (f i).down)) (hc : IsLimit c) :
    ∃ s : WidePullbackCone f, Nonempty (IsLimit s) ∧ ULift.down s.pt = c.pt := by
  let s : WidePullbackCone f :=
    WidePullbackCone.mk (W := (⟨c.pt⟩ : AsSmall.{z} C)) ⟨c.base⟩
      (fun i ↦ ⟨c.π i⟩) (fun i ↦ ULift.ext _ _ (c.condition i))
  refine ⟨s, ⟨?_⟩, rfl⟩
  apply WidePullbackCone.IsLimit.mk s
    (fun r ↦ ⟨WidePullbackCone.IsLimit.lift hc r.base.down
      (fun i ↦ (r.π i).down) (fun i ↦ congrArg ULift.down (r.condition i))⟩)
  · intro r
    exact ULift.ext _ _ (WidePullbackCone.IsLimit.lift_base _ _ _ _)
  · intro r i
    exact ULift.ext _ _ (WidePullbackCone.IsLimit.lift_π _ _ _ _ _)
  · intro r m hm hπ
    apply ULift.ext
    apply WidePullbackCone.IsLimit.hom_ext hc
    · exact (congrArg ULift.down hm).trans
        (WidePullbackCone.IsLimit.lift_base _ _ _ _).symm
    · intro i
      exact (congrArg ULift.down (hπ i)).trans
        (WidePullbackCone.IsLimit.lift_π hc _ (fun i ↦ (r.π i).down) _ i).symm

/-- The hypothesis of Stacks 0739 on a covering family — finiteness, and all nonempty iterated
fibre products lying in a given collection — transports from a locally small category to the
equivalent small category `AsSmall C`. -/
theorem hasIntersectionsIn_asSmall {C : Type u} [Category.{v} C] (B : Set C)
    {U : AsSmall.{z} C} (E : PreZeroHypercover.{t} U)
    (h : HasIntersectionsIn B (E.map AsSmall.down)) :
    HasIntersectionsIn (fun V : AsSmall.{z} C ↦ B (ULift.down V)) E := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro n a
  obtain ⟨c, ⟨hc⟩, hB⟩ := h.2.2.2 n a
  obtain ⟨s, hs, he⟩ := widePullback_asSmall (fun i ↦ E.f (a i)) c hc
  exact ⟨s, hs, show B (ULift.down s.pt) from he.symm ▸ hB⟩

/-- Cofinality of a family of coverings among the covering sieves of the objects of a collection
transports from a locally small category to the equivalent small category `AsSmall C`, along the
topology induced by the equivalence. -/
theorem exists_cover_asSmall {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (PreZeroHypercover.{t} U))
    (hcofinal : ∀ U, B U → ∀ R ∈ J U, ∃ E, Cov U E ∧ E.sieve₀ ≤ R)
    (U : AsSmall.{z} C) (hU : B (ULift.down U)) (R : Sieve U)
    (hR : R ∈ (AsSmall.down.inducedTopology J) U) :
    ∃ E : PreZeroHypercover.{t} U, Cov (ULift.down U) (E.map AsSmall.down) ∧ E.sieve₀ ≤ R := by
  have : (AsSmall.down : AsSmall.{z} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv : C ≌ AsSmall.{z} C).isEquivalence_inverse
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hR
  obtain ⟨E, hE, hle⟩ := hcofinal (ULift.down U) hU _ hR
  let E' : PreZeroHypercover.{t} U :=
    ⟨E.I₀, fun i ↦ ⟨E.X i⟩, fun i ↦ ⟨E.f i⟩⟩
  refine ⟨E', hE, ?_⟩
  rw [← Sieve.functorPullback_functorPushforward_eq (F := AsSmall.down) (S := R),
    ← Sieve.functorPushforward_le_iff_le_functorPullback, ← PreZeroHypercover.sieve₀_map]
  exact hle

/-! ### Moving the comparison across the transports -/

/-- Whether the canonical comparison `colimit.post` from the colimit of the composite to the
functor applied to the colimit is an isomorphism depends only on the isomorphism class of the
functor. -/
theorem isIso_colimit_post_of_natIso {I : Type*} [Category* I] {A D : Type*}
    [Category* A] [Category* D] (F : I ⥤ A) (G H : A ⥤ D) (α : G ≅ H)
    [HasColimitsOfShape I D] [HasColimit F]
    [HasColimit (F ⋙ G)] [HasColimit (F ⋙ H)]
    [IsIso (colimit.post F G)] : IsIso (colimit.post F H) := by
  have := preservesColimit_of_isIso_post G F
  have := preservesColimit_of_natIso F α
  infer_instance

/-! ### Stacks 0739 at a free coefficient universe -/

/-- Sections over an object of a site are an additive functor on sheaves of abelian groups. -/
instance sheafSections_additive {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type*) [Category* A] [Preadditive A] [HasWeakSheafify J A]
    [(sheafToPresheaf J A).Additive] (U : C) :
    ((sheafSections J A).obj (op U)).Additive where
  map_add := by intros; rfl

variable {C : Type u} [Category.{v} C]

/-- A locally small category is essentially small in any universe containing its objects and its
morphisms, by way of `AsSmall`. -/
theorem essentiallySmall_asSmall : EssentiallySmall.{max z v u} C :=
  EssentiallySmall.mk' (AsSmall.equiv.{v, u, max z v u} (C := C))

attribute [local instance] essentiallySmall_asSmall

/-- Abelian sheaves on a locally small site can be sheafified at any coefficient universe
containing the site. -/
theorem hasSheafify_largeCoefficients (J : GrothendieckTopology C) :
    HasSheafify J Ab.{max z v u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max z v u, v, u} J

attribute [local instance] hasSheafify_largeCoefficients

/-- Abelian sheaves on a locally small site have enough injectives at any coefficient universe
containing the site. -/
theorem enoughInjectives_largeCoefficients (J : GrothendieckTopology C) :
    EnoughInjectives (Sheaf J Ab.{max z v u}) :=
  (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max z v u} J Ab.{max z v u}).enoughInjectives

attribute [local instance] enoughInjectives_largeCoefficients

/-- **Stacks 0739 on a locally small site, with coefficients in any universe containing it.**
Let `B` be a collection of objects of a site `C` and let `Cov` be a collection of covering
families which is cofinal among the coverings of every object of `B`, is finite, and whose
nonempty iterated fibre products again lie in `B`. Then for every object `U` of `B`, every
degree `p` and every filtered diagram `F` of abelian sheaves with coefficients in
`Ab.{max z v u}`, the canonical map

> `colim_i H^p(U, F_i) ⟶ H^p(U, colim_i F_i)`

is an isomorphism. -/
theorem isIso_colimit_post_rightDerived_sheafSections_largeCoefficients
    (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (PreZeroHypercover.{t} U))
    (hCov : ∀ U E, Cov U E → E.sieve₀ ∈ J U)
    (hfinite : ∀ U E, Cov U E → HasIntersectionsIn B E)
    (hcofinal : ∀ U, B U → ∀ R ∈ J U, ∃ E, Cov U E ∧ E.sieve₀ ≤ R)
    (p : ℕ) (U : C) (hU : B U)
    {I : Type (max z v u)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J Ab.{max z v u}) :
    IsIso (colimit.post F
      (((sheafSections J Ab.{max z v u}).obj (op U)).rightDerived p)) := by
  let e : C ≌ AsSmall.{z} C := AsSmall.equiv
  let K := e.inverse.inducedTopology J
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  have : e.functor.IsDenseSubsite J K := inferInstance
  let R := e.functor.sheafPushforwardContinuous Ab.{max z v u} J K
  let eR := R.asEquivalence
  have : R.Additive := ⟨by intros; rfl⟩
  let Q : Set (AsSmall.{z} C) := fun V ↦ B (ULift.down V)
  let Cov' : ∀ V : AsSmall.{z} C, Set (PreZeroHypercover.{t} V) :=
    fun V E ↦ Cov (ULift.down V) (E.map e.inverse)
  have : IsIso (colimit.post (F ⋙ eR.symm.functor)
      (((sheafSections K Ab.{max z v u}).obj (op (e.functor.obj U))).rightDerived p)) := by
    apply isIso_colimit_post_rightDerived_sheafSections K Q Cov' ?_ ?_ ?_
      p (e.functor.obj U) hU (F ⋙ eR.symm.functor)
    · intro V E hE
      rw [Functor.mem_inducedTopology_iff_of_isCoverDense, ← PreZeroHypercover.sieve₀_map]
      exact hCov _ _ hE
    · intro V E hE
      exact hasIntersectionsIn_asSmall B E (hfinite _ _ hE)
    · intro V hV S hS
      exact exists_cover_asSmall J B Cov hcofinal V hV S hS
  let a : R ⋙ ((sheafSections J Ab.{max z v u}).obj (op U)).rightDerived p ≅
      ((sheafSections K Ab.{max z v u}).obj (op (e.functor.obj U))).rightDerived p :=
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso R
      ((sheafSections J Ab.{max z v u}).obj (op U)) p).symm ≪≫
      Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso (Iso.refl _) p
  let b : eR.inverse ⋙
        ((sheafSections K Ab.{max z v u}).obj (op (e.functor.obj U))).rightDerived p ≅
      ((sheafSections J Ab.{max z v u}).obj (op U)).rightDerived p :=
    Functor.isoWhiskerLeft eR.inverse a.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eR.counitIso _ ≪≫ Functor.leftUnitor _
  have : IsIso (colimit.post F (eR.inverse ⋙
      ((sheafSections K Ab.{max z v u}).obj (op (e.functor.obj U))).rightDerived p)) :=
    ColimitsOfCohomology.isIso_colimit_post_of_equivalence_comp F eR.symm
      (((sheafSections K Ab.{max z v u}).obj (op (e.functor.obj U))).rightDerived p)
  exact isIso_colimit_post_of_natIso F _ _ b

end

end Stacks.Cohomology

end
