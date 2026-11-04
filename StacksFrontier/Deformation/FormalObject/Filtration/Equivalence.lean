module

public import StacksFrontier.Deformation.FormalObject.Filtration.ComparisonFunctors

/-!
# Formal objects for a different filtration

Formal objects computed with respect to a different filtration of the
underlying complete local algebra agree with the original ones.

## Main results

* `filteredFormalObjectsEquivalence` states that filtered formal objects are equivalent
  to the fibre of the usual category of formal objects.

## References

* [Stacks Project, Tag 06H6](https://stacks.math.columbia.edu/tag/06H6)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory
open IsLocalRing
universe u v w uF vF


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

private lemma toAdicObject_path_fac {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I)
    (n m : ℕ) (h : n ≤ m) :
    chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I m))
        (X.level (toAdicIndex I m)) (X.level_eq (toAdicIndex I m)) ≫
      formalPath (toAdicObject p R I hp X) n m h =
      filteredPath X (toAdicIndex I n) (toAdicIndex I m)
        (toAdicIndex_mono I h) ≫
        chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
          (X.level (toAdicIndex I n)) (X.level_eq (toAdicIndex I n)) := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [formalPath_self, filteredPath_self]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ m hm ih =>
      rw [formalPath_succ, ← Category.assoc, toAdicObject_transition_fac,
        Category.assoc, ih, ← Category.assoc, filteredPath_comp]
      all_goals assumption

private lemma toIdealObject_path_fac {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FormalObject p)
    (hX : X.base = R) (n m : ℕ) (h : n ≤ m) :
    chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I m))
        (X.level (toIdealIndex I m))
        (by simpa only [hX, AdicTruncation.functor] using X.level_eq (toIdealIndex I m)) ≫
      filteredPath (toIdealObject p R I hp X hX) n m h =
      formalPath X (toIdealIndex I n) (toIdealIndex I m)
        (toIdealIndex_mono I h) ≫
        chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
          (X.level (toIdealIndex I n))
          (by simpa only [hX, AdicTruncation.functor] using
            X.level_eq (toIdealIndex I n)) := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [filteredPath_self, formalPath_self]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ m hm ih =>
      rw [filteredPath_succ, ← Category.assoc, toIdealObject_transition_fac,
        Category.assoc, ih, ← Category.assoc, formalPath_comp]
      all_goals assumption

/-- `toAdicIndex I n` is at least `n`. -/
lemma toAdicIndex_ge {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) : n ≤ toAdicIndex I n := by
  classical exact Nat.le_max_left _ _

private lemma toIdealIndex_ge {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) : n ≤ toIdealIndex I n := by
  classical exact Nat.le_max_left _ _

private lemma filtered_roundtrip_base {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) :
    idealToAdic I (toAdicIndex_le I (toIdealIndex I n)) ≫
        adicToIdeal I (toIdealIndex_le I n) =
      filteredBasePath I n (toAdicIndex I (toIdealIndex I n))
        ((toIdealIndex_ge I n).trans (toAdicIndex_ge I (toIdealIndex I n))) := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (adicToIdeal I (toIdealIndex_le I n)).hom
      ((idealToAdic I (toAdicIndex_le I (toIdealIndex I n))).hom
        (Ideal.Quotient.mk _ r)) = _
  rw [idealToAdic_mk, adicToIdeal_mk, filteredBasePath_mk]

private lemma formal_roundtrip_base {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) :
    adicToIdeal I (toIdealIndex_le I (toAdicIndex I n)) ≫
        idealToAdic I (toAdicIndex_le I n) =
      formalBasePath (R := R) n (toIdealIndex I (toAdicIndex I n))
        ((toAdicIndex_ge I n).trans (toIdealIndex_ge I (toAdicIndex I n))) := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (idealToAdic I (toAdicIndex_le I n)).hom
      ((adicToIdeal I (toIdealIndex_le I (toAdicIndex I n))).hom
        (Ideal.Quotient.mk _ r)) = _
  rw [adicToIdeal_mk, idealToAdic_mk, formalBasePath_mk]

private noncomputable def filteredCompare {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I) (n : ℕ) :
    ((toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp).obj X).level n ⟶ X.level n := by
  let a := toIdealIndex I n
  let c := toAdicIndex I a
  let q₁ := idealToAdic I (toAdicIndex_le I a)
  let q₂ := adicToIdeal I (toIdealIndex_le I n)
  let A := toAdicObject p R I hp X
  have hc : n ≤ c := (toIdealIndex_ge I n).trans (toAdicIndex_ge I a)
  have hpath : p.IsHomLift (q₁ ≫ q₂) (filteredPath X n c hc) := by
    rw [filtered_roundtrip_base]
    exact filteredPath_lift X n c hc
  let d₁ := pushforwardDesc hp q₁ q₂ (X.level c) (X.level n) (X.level_eq c)
    (filteredPath X n c hc) hpath
  have hd₁ : p.IsHomLift q₂ d₁ :=
    pushforwardDesc_lift hp q₁ q₂ (X.level c) (X.level n) (X.level_eq c)
      (filteredPath X n c hc) hpath
  have hd₁' : p.IsHomLift (q₂ ≫ 𝟙 (I.quotient n)) d₁ := by
    simpa only [Category.comp_id] using hd₁
  exact pushforwardDesc hp q₂ (𝟙 (I.quotient n)) (A.level a) (X.level n)
    (A.level_eq a) d₁ hd₁'

private lemma filteredCompare_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I) (n : ℕ) :
    p.IsHomLift (𝟙 (I.quotient n)) (filteredCompare p R I hp X n) := by
  unfold filteredCompare
  exact pushforwardDesc_lift hp _ _ _ _ _ _ _

private lemma filteredCompare_fac {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I) (n : ℕ) :
    (chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I (toIdealIndex I n)))
        (X.level (toAdicIndex I (toIdealIndex I n)))
        (X.level_eq (toAdicIndex I (toIdealIndex I n))) ≫
      chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
        ((toAdicObject p R I hp X).level (toIdealIndex I n))
        ((toAdicObject p R I hp X).level_eq (toIdealIndex I n))) ≫
      filteredCompare p R I hp X n =
        filteredPath X n (toAdicIndex I (toIdealIndex I n))
          ((toIdealIndex_ge I n).trans (toAdicIndex_ge I (toIdealIndex I n))) := by
  simp only [filteredCompare, toAdicObject, Category.assoc, pushforwardDesc_fac]

private noncomputable def formalCompare {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    (X : (FormalObject.projection (p := p)).Fiber R) (n : ℕ) :
    (((toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).obj X).val).level n ⟶ X.val.level n := by
  let a := toAdicIndex I n
  let c := toIdealIndex I a
  let q₁ := adicToIdeal I (toIdealIndex_le I a)
  let q₂ := idealToAdic I (toAdicIndex_le I n)
  let A := toIdealObject p R I hp X.val X.property
  have hc : n ≤ c := (toAdicIndex_ge I n).trans (toIdealIndex_ge I a)
  have hpath : p.IsHomLift (q₁ ≫ q₂) (formalPath X.val n c hc) := by
    rw [formal_roundtrip_base]
    rcases X with ⟨X, hX⟩
    change X.base = R at hX
    subst R
    exact formalPath_lift X n c hc
  let d₁ := pushforwardDesc hp q₁ q₂ (X.val.level c) (X.val.level n) (fiber_level_eq p R X c)
    (formalPath X.val n c hc) hpath
  have hd₁ : p.IsHomLift q₂ d₁ :=
    pushforwardDesc_lift hp q₁ q₂ (X.val.level c) (X.val.level n) (fiber_level_eq p R X c)
      (formalPath X.val n c hc) hpath
  have hd₁' : p.IsHomLift (q₂ ≫ 𝟙 (AdicTruncation.obj R n)) d₁ := by
    simpa only [Category.comp_id] using hd₁
  exact pushforwardDesc hp q₂ (𝟙 (AdicTruncation.obj R n)) (A.level a) (X.val.level n)
    (A.level_eq a) d₁ hd₁'

private lemma formalCompare_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    (X : (FormalObject.projection (p := p)).Fiber R) (n : ℕ) :
    p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (formalCompare p R I hp X n) := by
  unfold formalCompare
  exact pushforwardDesc_lift hp _ _ _ _ _ _ _

private lemma formalCompare_fac {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    (X : (FormalObject.projection (p := p)).Fiber R) (n : ℕ) :
    (chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I (toAdicIndex I n)))
        (X.val.level (toIdealIndex I (toAdicIndex I n)))
        (fiber_level_eq p R X (toIdealIndex I (toAdicIndex I n))) ≫
      chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
        ((toIdealObject p R I hp X.val X.property).level (toAdicIndex I n))
        ((toIdealObject p R I hp X.val X.property).level_eq (toAdicIndex I n))) ≫
      formalCompare p R I hp X n =
        formalPath X.val n (toIdealIndex I (toAdicIndex I n))
          ((toAdicIndex_ge I n).trans (toIdealIndex_ge I (toAdicIndex I n))) := by
  simp only [formalCompare, toIdealObject, Category.assoc, pushforwardDesc_fac]

/-- Maps out of the target of a strongly cocartesian arrow are determined by their precomposite
once they lie over the same base morphism. -/
private lemma eq_of_comp_eq_of_isHomLift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {x y z : F} {R S S' : ArtinianLocalAlgCat.{u, v, w} Λ k} {f : R ⟶ S}
    (φ : x ⟶ y) (hφ : p.IsHomLift f φ) (g : S ⟶ S') {ψ ψ' : y ⟶ z}
    (hψ : p.IsHomLift g ψ) (hψ' : p.IsHomLift g ψ') (h : φ ≫ ψ = φ ≫ ψ') : ψ = ψ' := by
  let := hφ
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp f φ hφ
  exact Functor.IsStronglyCocartesian.ext p f φ g h

/-- Pasting two commuting squares to compare two composites of pushforwards. -/
private lemma comp_comp_eq_of_squares {C : Type*} [Category C] {a a' b c d m e : C}
    {u₁ : a ⟶ b} {v₁ : b ⟶ c} {D : c ⟶ d} {P : b ⟶ m} {v₀ : m ⟶ d} {Q : a ⟶ a'}
    {u₀ : a' ⟶ m} (φ : d ⟶ e) (hD : v₁ ≫ D = P ≫ v₀) (hA : u₁ ≫ P = Q ≫ u₀) :
    (u₁ ≫ v₁) ≫ D ≫ φ = Q ≫ (u₀ ≫ v₀) ≫ φ := by
  rw [Category.assoc, ← Category.assoc v₁, hD]
  simp [reassoc_of% hA]

private lemma filteredCompare_transition {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I) (n : ℕ) :
    ((toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp).obj X).transition n ≫
        filteredCompare p R I hp X n =
      filteredCompare p R I hp X (n + 1) ≫ X.transition n := by
  let a := toIdealIndex I
  let c := fun j ↦ toAdicIndex I (a j)
  let A := toAdicObject p R I hp X
  let D := (toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp).obj X
  let q₁ := fun j ↦ idealToAdic I (toAdicIndex_le I (a j))
  let q₂ := fun j ↦ adicToIdeal I (toIdealIndex_le I j)
  let u := fun j ↦ chosenPushforwardMap hp (q₁ j) (X.level (c j)) (X.level_eq (c j))
  let v := fun j ↦ chosenPushforwardMap hp (q₂ j) (A.level (a j)) (A.level_eq (a j))
  have ha : a n ≤ a (n + 1) := toIdealIndex_mono I (Nat.le_succ n)
  have hc : c n ≤ c (n + 1) := toAdicIndex_mono I ha
  have hD : v (n + 1) ≫ D.transition n =
      formalPath A (a n) (a (n + 1)) ha ≫ v n :=
    toIdealObject_transition_fac p R I A rfl hp n
  have hA : u (n + 1) ≫ formalPath A (a n) (a (n + 1)) ha =
      filteredPath X (c n) (c (n + 1)) hc ≫ u n :=
    toAdicObject_path_fac p R I hp X (a n) (a (n + 1)) ha
  have hcm (j : ℕ) : (u j ≫ v j) ≫ filteredCompare p R I hp X j =
      filteredPath X j (c j)
        ((toIdealIndex_ge I j).trans (toAdicIndex_ge I (a j))) :=
    filteredCompare_fac p R I hp X j
  let := chosenPushforwardMap_lift hp (q₁ (n + 1)) (X.level (c (n + 1)))
    (X.level_eq (c (n + 1)))
  let := chosenPushforwardMap_lift hp (q₂ (n + 1)) (A.level (a (n + 1)))
    (A.level_eq (a (n + 1)))
  have hsource : p.IsHomLift (q₁ (n + 1) ≫ q₂ (n + 1))
      (u (n + 1) ≫ v (n + 1)) := inferInstance
  have hl : p.IsHomLift (I.transition n) (D.transition n ≫ filteredCompare p R I hp X n) := by
    let : p.IsHomLift (I.transition n) (D.transition n) :=
      ((toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp).obj X).transition_lift n
    let := filteredCompare_lift p R I hp X n
    infer_instance
  have hr : p.IsHomLift (I.transition n)
      (filteredCompare p R I hp X (n + 1) ≫ X.transition n) := by
    let := filteredCompare_lift p R I hp X (n + 1)
    let := X.transition_lift n
    exact IsHomLift.comp_lift_id_left p (I.transition n) _ _
  have hge : n + 1 ≤ c (n + 1) :=
    (toIdealIndex_ge I (n + 1)).trans (toAdicIndex_ge I (a (n + 1)))
  have hcore : (u (n + 1) ≫ v (n + 1)) ≫
        (D.transition n ≫ filteredCompare p R I hp X n) =
      (u (n + 1) ≫ v (n + 1)) ≫
        (filteredCompare p R I hp X (n + 1) ≫ X.transition n) := by
    calc _ = filteredPath X (c n) (c (n + 1)) hc ≫ (u n ≫ v n) ≫ filteredCompare p R I hp X n :=
          comp_comp_eq_of_squares _ hD hA
      _ = filteredPath X (n + 1) (c (n + 1)) hge ≫ X.transition n := by
          rw [hcm n, filteredPath_comp,
            ← filteredPath_comp X n (n + 1) (c (n + 1)) (Nat.le_succ n) hge,
            filteredPath_succ X n n le_rfl, filteredPath_self, Category.comp_id]
      _ = _ := by rw [← hcm (n + 1)]; exact Category.assoc _ _ _
  exact eq_of_comp_eq_of_isHomLift p hp (u (n + 1) ≫ v (n + 1)) hsource (I.transition n)
    hl hr hcore

private lemma formalCompare_transition {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    (X : (FormalObject.projection (p := p)).Fiber R) (n : ℕ) :
    ((toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).obj X).val.transition n ≫
        formalCompare p R I hp X n =
      formalCompare p R I hp X (n + 1) ≫ X.val.transition n := by
  let a := toAdicIndex I
  let c := fun j ↦ toIdealIndex I (a j)
  let A := toIdealObject p R I hp X.val X.property
  let D := ((toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).obj X).val
  let q₁ := fun j ↦ adicToIdeal I (toIdealIndex_le I (a j))
  let q₂ := fun j ↦ idealToAdic I (toAdicIndex_le I j)
  let u := fun j ↦ chosenPushforwardMap hp (q₁ j) (X.val.level (c j)) (fiber_level_eq p R X (c j))
  let v := fun j ↦ chosenPushforwardMap hp (q₂ j) (A.level (a j)) (A.level_eq (a j))
  have ha : a n ≤ a (n + 1) := toAdicIndex_mono I (Nat.le_succ n)
  have hc : c n ≤ c (n + 1) := toIdealIndex_mono I ha
  have hD : v (n + 1) ≫ D.transition n =
      filteredPath A (a n) (a (n + 1)) ha ≫ v n :=
    toAdicObject_transition_fac p R I hp A n
  have hA : u (n + 1) ≫ filteredPath A (a n) (a (n + 1)) ha =
      formalPath X.val (c n) (c (n + 1)) hc ≫ u n :=
    toIdealObject_path_fac p R I hp X.val X.property (a n) (a (n + 1)) ha
  have hcm (j : ℕ) : (u j ≫ v j) ≫ formalCompare p R I hp X j =
      formalPath X.val j (c j)
        ((toAdicIndex_ge I j).trans (toIdealIndex_ge I (a j))) :=
    formalCompare_fac p R I hp X j
  let := chosenPushforwardMap_lift hp (q₁ (n + 1)) (X.val.level (c (n + 1)))
    (fiber_level_eq p R X (c (n + 1)))
  let := chosenPushforwardMap_lift hp (q₂ (n + 1)) (A.level (a (n + 1)))
    (A.level_eq (a (n + 1)))
  have hsource : p.IsHomLift (q₁ (n + 1) ≫ q₂ (n + 1))
      (u (n + 1) ≫ v (n + 1)) := inferInstance
  have hl : p.IsHomLift (AdicTruncation.transition R n)
      (D.transition n ≫ formalCompare p R I hp X n) := by
    let : p.IsHomLift (AdicTruncation.transition R n) (D.transition n) := by
      have hbase : D.base = R := rfl
      have ht := D.transition_lift n
      rw [hbase] at ht
      simpa only [AdicTruncation.transitionNat, AdicTruncation.functor] using ht
    let := formalCompare_lift p R I hp X n
    infer_instance
  have hr : p.IsHomLift (AdicTruncation.transition R n)
      (formalCompare p R I hp X (n + 1) ≫ X.val.transition n) := by
    let := formalCompare_lift p R I hp X (n + 1)
    let := fiber_transition_lift p R X n
    exact IsHomLift.comp_lift_id_left p (AdicTruncation.transition R n) _ _
  have hge : n + 1 ≤ c (n + 1) :=
    (toAdicIndex_ge I (n + 1)).trans (toIdealIndex_ge I (a (n + 1)))
  have hcore : (u (n + 1) ≫ v (n + 1)) ≫
        (D.transition n ≫ formalCompare p R I hp X n) =
      (u (n + 1) ≫ v (n + 1)) ≫
        (formalCompare p R I hp X (n + 1) ≫ X.val.transition n) := by
    calc _ = formalPath X.val (c n) (c (n + 1)) hc ≫ (u n ≫ v n) ≫ formalCompare p R I hp X n :=
          comp_comp_eq_of_squares _ hD hA
      _ = formalPath X.val (n + 1) (c (n + 1)) hge ≫ X.val.transition n := by
          rw [hcm n, formalPath_comp,
            ← formalPath_comp X.val n (n + 1) (c (n + 1)) (Nat.le_succ n) hge,
            formalPath_succ X.val n n le_rfl, formalPath_self, Category.comp_id]
      _ = _ := by rw [← hcm (n + 1)]; exact Category.assoc _ _ _
  exact eq_of_comp_eq_of_isHomLift p hp (u (n + 1) ≫ v (n + 1)) hsource
    (AdicTruncation.transition R n) hl hr hcore

private lemma filteredCompare_map {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) {X Y : FilteredFormalObject p R I}
    (f : X ⟶ Y) (n : ℕ) :
    ((toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp).map f).app n ≫
        filteredCompare p R I hp Y n =
      filteredCompare p R I hp X n ≫ f.app n := by
  let a := toIdealIndex I n
  let c := toAdicIndex I a
  let AX := toAdicObject p R I hp X
  let AY := toAdicObject p R I hp Y
  let g := (toAdicFunctor p R I hp).map f
  let uX := chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I a))
    (X.level c) (X.level_eq c)
  let uY := chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I a))
    (Y.level c) (Y.level_eq c)
  let vX := chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
    (AX.level a) (AX.level_eq a)
  let vY := chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
    (AY.level a) (AY.level_eq a)
  have hc : n ≤ c := (toIdealIndex_ge I n).trans (toAdicIndex_ge I a)
  have hD : vX ≫ toIdealApp p R I hp g n = toAdicApp p R I hp f a ≫ vY := by
    simpa only [g, toAdicFunctor] using toIdealApp_fac p R I hp g n
  have hA : uX ≫ toAdicApp p R I hp f a = f.app c ≫ uY :=
    toAdicApp_fac p R I hp f a
  have hcmpX : (uX ≫ vX) ≫ filteredCompare p R I hp X n =
      filteredPath X n c hc := filteredCompare_fac p R I hp X n
  have hcmpY : (uY ≫ vY) ≫ filteredCompare p R I hp Y n =
      filteredPath Y n c hc := filteredCompare_fac p R I hp Y n
  have hsource : p.IsHomLift
      (idealToAdic I (toAdicIndex_le I a) ≫ adicToIdeal I (toIdealIndex_le I n))
      (uX ≫ vX) := by
    let := chosenPushforwardMap_lift hp (idealToAdic I (toAdicIndex_le I a))
      (X.level c) (X.level_eq c)
    let := chosenPushforwardMap_lift hp (adicToIdeal I (toIdealIndex_le I n))
      (AX.level a) (AX.level_eq a)
    infer_instance
  have hl : p.IsHomLift (𝟙 (I.quotient n))
      (toIdealApp p R I hp g n ≫ filteredCompare p R I hp Y n) := by
    change p.IsHomLift (𝟙 (I.quotient n))
      (((toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp).map f).app n ≫
        filteredCompare p R I hp Y n)
    let := ((toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp).map f).app_lift n
    let := filteredCompare_lift p R I hp Y n
    infer_instance
  have hr : p.IsHomLift (𝟙 (I.quotient n))
      (filteredCompare p R I hp X n ≫ f.app n) := by
    let := filteredCompare_lift p R I hp X n
    let := f.app_lift n
    infer_instance
  have hcore : (uX ≫ vX) ≫ (toIdealApp p R I hp g n ≫ filteredCompare p R I hp Y n) =
      (uX ≫ vX) ≫ (filteredCompare p R I hp X n ≫ f.app n) := by
    calc _ = f.app c ≫ (uY ≫ vY) ≫ filteredCompare p R I hp Y n :=
          comp_comp_eq_of_squares _ hD hA
      _ = filteredPath X n c hc ≫ f.app n := by rw [hcmpY, filteredPath_naturality]
      _ = _ := by rw [← hcmpX]; exact Category.assoc _ _ _
  exact eq_of_comp_eq_of_isHomLift p hp (uX ≫ vX) hsource (𝟙 _) hl hr hcore

private lemma formalCompare_map {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) {X Y : (FormalObject.projection (p := p)).Fiber R}
    (f : X ⟶ Y) (n : ℕ) :
    ((toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).map f).val.app n ≫
        formalCompare p R I hp Y n =
      formalCompare p R I hp X n ≫ f.val.app n := by
  let a := toAdicIndex I n
  let c := toIdealIndex I a
  let AX := toIdealObject p R I hp X.val X.property
  let AY := toIdealObject p R I hp Y.val Y.property
  let g := (toIdealFunctor p R I hp).map f
  let uX := chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I a))
    (X.val.level c) (fiber_level_eq p R X c)
  let uY := chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I a))
    (Y.val.level c) (fiber_level_eq p R Y c)
  let vX := chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
    (AX.level a) (AX.level_eq a)
  let vY := chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
    (AY.level a) (AY.level_eq a)
  have hc : n ≤ c := (toAdicIndex_ge I n).trans (toIdealIndex_ge I a)
  have hD : vX ≫ toAdicApp p R I hp g n = toIdealApp p R I hp f a ≫ vY := by
    simpa only [g, toIdealFunctor] using toAdicApp_fac p R I hp g n
  have hA : uX ≫ toIdealApp p R I hp f a = f.val.app c ≫ uY :=
    toIdealApp_fac p R I hp f a
  have hcmpX : (uX ≫ vX) ≫ formalCompare p R I hp X n =
      formalPath X.val n c hc := formalCompare_fac p R I hp X n
  have hcmpY : (uY ≫ vY) ≫ formalCompare p R I hp Y n =
      formalPath Y.val n c hc := formalCompare_fac p R I hp Y n
  have hsource : p.IsHomLift
      (adicToIdeal I (toIdealIndex_le I a) ≫ idealToAdic I (toAdicIndex_le I n))
      (uX ≫ vX) := by
    let := chosenPushforwardMap_lift hp (adicToIdeal I (toIdealIndex_le I a))
      (X.val.level c) (fiber_level_eq p R X c)
    let := chosenPushforwardMap_lift hp (idealToAdic I (toAdicIndex_le I n))
      (AX.level a) (AX.level_eq a)
    infer_instance
  have hl : p.IsHomLift (𝟙 (AdicTruncation.obj R n))
      (toAdicApp p R I hp g n ≫ formalCompare p R I hp Y n) := by
    change p.IsHomLift (𝟙 (AdicTruncation.obj R n))
      (((toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).map f).val.app n ≫
        formalCompare p R I hp Y n)
    let := fiber_app_lift p R ((toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).map f) n
    let := formalCompare_lift p R I hp Y n
    infer_instance
  have hr : p.IsHomLift (𝟙 (AdicTruncation.obj R n))
      (formalCompare p R I hp X n ≫ f.val.app n) := by
    let := formalCompare_lift p R I hp X n
    let := fiber_app_lift p R f n
    infer_instance
  have hcore : (uX ≫ vX) ≫ (toAdicApp p R I hp g n ≫ formalCompare p R I hp Y n) =
      (uX ≫ vX) ≫ (formalCompare p R I hp X n ≫ f.val.app n) := by
    calc _ = f.val.app c ≫ (uY ≫ vY) ≫ formalCompare p R I hp Y n :=
          comp_comp_eq_of_squares _ hD hA
      _ = formalPath X.val n c hc ≫ f.val.app n := by rw [hcmpY, formalPath_naturality]
      _ = _ := by rw [← hcmpX]; exact Category.assoc _ _ _
  exact eq_of_comp_eq_of_isHomLift p hp (uX ≫ vX) hsource (𝟙 _) hl hr hcore

private lemma isIso_lift_id {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x y : F} (φ : x ⟶ y) (hφ : p.IsHomLift (𝟙 A) φ) : IsIso φ := by
  let := hφ
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp (𝟙 A) φ hφ
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p (𝟙 A) φ

private noncomputable def filteredHomIsoOfPointwise {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : FilteredFormalObject p R I} (f : X ⟶ Y) : X ≅ Y := by
  letI (n : ℕ) : IsIso (f.app n) := isIso_lift_id p hp (f.app n) (f.app_lift n)
  refine
    { hom := f
      inv :=
        { app := fun n ↦ inv (f.app n)
          app_lift := fun n ↦ by
            let := f.app_lift n
            infer_instance
          naturality := fun n ↦ by
            apply (cancel_mono (f.app n)).mp
            rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
            rw [Category.assoc, f.naturality n, ← Category.assoc,
              IsIso.inv_hom_id, Category.id_comp] }
      hom_inv_id := FilteredFormalObject.Hom.ext (fun n ↦ by
        change f.app n ≫ inv (f.app n) = 𝟙 (X.level n)
        simp)
      inv_hom_id := FilteredFormalObject.Hom.ext (fun n ↦ by
        change inv (f.app n) ≫ f.app n = 𝟙 (Y.level n)
        simp) }

private noncomputable def filteredCompareIso {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I) :
    (toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp).obj X ≅ X :=
  filteredHomIsoOfPointwise p R I hp
    { app := filteredCompare p R I hp X
      app_lift := filteredCompare_lift p R I hp X
      naturality := filteredCompare_transition p R I hp X }

private noncomputable def filteredCompareNatIso {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) :
    (toAdicFunctor p R I hp ⋙ toIdealFunctor p R I hp) ≅
      𝟭 (FilteredFormalObject p R I) :=
  NatIso.ofComponents (filteredCompareIso p R I hp) fun f ↦
    FilteredFormalObject.Hom.ext fun n ↦ filteredCompare_map p R I hp f n

private noncomputable def formalCompareHom {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    (X : (FormalObject.projection (p := p)).Fiber R) :
    (toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).obj X ⟶ X := by
  rcases X with ⟨X, hX⟩
  change X.base = R at hX
  subst R
  let XF : (FormalObject.projection (p := p)).Fiber X.base := ⟨X, rfl⟩
  let D := (toIdealFunctor p X.base I hp ⋙ toAdicFunctor p X.base I hp).obj XF
  let φ : D.val ⟶ X :=
    { base := 𝟙 X.base
      app := formalCompare p X.base I hp XF
      app_lift := fun n ↦ by
        have hid : (AdicTruncation.functor (Λ := Λ) (k := k) n).map (𝟙 X.base) =
            𝟙 (AdicTruncation.obj X.base n) :=
          (AdicTruncation.functor n).map_id X.base
        exact hid.symm ▸ formalCompare_lift p X.base I hp XF n
      naturality := formalCompare_transition p X.base I hp XF }
  refine ⟨φ, ?_⟩
  have hmap : (FormalObject.projection (p := p)).map φ = 𝟙 X.base := rfl
  rw [← hmap]
  exact IsHomLift.map (FormalObject.projection (p := p)) φ

private noncomputable def formalCompareIso {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    (X : (FormalObject.projection (p := p)).Fiber R) :
    (toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).obj X ≅ X := by
  rcases X with ⟨X, hX⟩
  change X.base = R at hX
  subst R
  let XF : (FormalObject.projection (p := p)).Fiber X.base := ⟨X, rfl⟩
  let D := (toIdealFunctor p X.base I hp ⋙ toAdicFunctor p X.base I hp).obj XF
  let h := formalCompareHom p X.base I hp XF
  let φ := h.val
  have hφ (n : ℕ) : p.IsHomLift (𝟙 (AdicTruncation.obj X.base n)) (φ.app n) :=
    formalCompare_lift p X.base I hp XF n
  letI (n : ℕ) : IsIso (φ.app n) := isIso_lift_id p hp (φ.app n) (hφ n)
  let ψ : X ⟶ D.val :=
    { base := 𝟙 X.base
      app := fun n ↦ inv (φ.app n)
      app_lift := fun n ↦ by
        have hid : (AdicTruncation.functor (Λ := Λ) (k := k) n).map (𝟙 X.base) =
            𝟙 (AdicTruncation.obj X.base n) :=
          (AdicTruncation.functor n).map_id X.base
        let := hφ n
        exact hid.symm ▸ (inferInstance : p.IsHomLift
          (𝟙 (AdicTruncation.obj X.base n)) (inv (φ.app n)))
      naturality := fun n ↦ by
        apply (cancel_mono (φ.app n)).mp
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc, φ.naturality n,
          ← Category.assoc, IsIso.inv_hom_id, Category.id_comp] }
  have hψ : (FormalObject.projection (p := p)).IsHomLift (𝟙 X.base) ψ := by
    have hmap : (FormalObject.projection (p := p)).map ψ = 𝟙 X.base := rfl
    rw [← hmap]
    exact IsHomLift.map (FormalObject.projection (p := p)) ψ
  change D ≅ XF
  refine
    { hom := h
      inv := ⟨ψ, hψ⟩
      hom_inv_id := Functor.Fiber.hom_ext <| FormalObject.Hom.ext rfl fun n ↦
        IsIso.hom_inv_id (φ.app n)
      inv_hom_id := Functor.Fiber.hom_ext <| FormalObject.Hom.ext rfl fun n ↦
        IsIso.inv_hom_id (φ.app n) }

private lemma fiber_hom_base_eq {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    {X Y : (FormalObject.projection (p := p)).Fiber R}
    (f g : X ⟶ Y) : f.val.base = g.val.base := by
  rcases X with ⟨⟨RX, lx, ex, tx, etx⟩, hX⟩
  rcases Y with ⟨⟨RY, ly, ey, ty, ety⟩, hY⟩
  change RX = R at hX
  change RY = R at hY
  cases hX
  cases hY
  have hf : f.val.base = 𝟙 R := by
    let := f.property
    have heq := IsHomLift.fac (FormalObject.projection (p := p))
      (𝟙 R) f.val
    simpa [FormalObject.projection] using heq.symm
  have hg : g.val.base = 𝟙 R := by
    let := g.property
    have heq := IsHomLift.fac (FormalObject.projection (p := p))
      (𝟙 R) g.val
    simpa [FormalObject.projection] using heq.symm
  exact hf.trans hg.symm

private lemma formalCompareIso_hom_app {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    (X : (FormalObject.projection (p := p)).Fiber R) (n : ℕ) :
    (formalCompareIso p R I hp X).hom.val.app n = formalCompare p R I hp X n := by
  rcases X with ⟨X, hX⟩
  change X.base = R at hX
  subst R
  rfl

private noncomputable def formalCompareNatIso {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) :
    (toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp) ≅
      𝟭 ((FormalObject.projection (p := p)).Fiber R) :=
  NatIso.ofComponents (formalCompareIso p R I hp) (fun f ↦ by
    apply Functor.Fiber.hom_ext
    apply FormalObject.Hom.ext
    · exact fiber_hom_base_eq p R
        ((toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).map f ≫
          (formalCompareIso p R I hp _).hom)
        ((formalCompareIso p R I hp _).hom ≫
          (𝟭 ((FormalObject.projection (p := p)).Fiber R)).map f)
    · intro n
      change ((toIdealFunctor p R I hp ⋙ toAdicFunctor p R I hp).map f).val.app n ≫
        (formalCompareIso p R I hp _).hom.val.app n =
        (formalCompareIso p R I hp _).hom.val.app n ≫ f.val.app n
      rw [formalCompareIso_hom_app, formalCompareIso_hom_app]
      exact formalCompare_map p R I hp f n)

/-- A cofinal ideal filtration gives the same category of formal objects over `R` as the
maximal-ideal filtration. -/
@[stacks 06H6]
theorem filteredFormalObjectsEquivalence {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) :
    Nonempty
      (FilteredFormalObject p R I ≌
        (FormalObject.projection (p := p)).Fiber R) :=
  ⟨CategoryTheory.Equivalence.mk (toAdicFunctor p R I hp) (toIdealFunctor p R I hp)
    (filteredCompareNatIso p R I hp).symm (formalCompareNatIso p R I hp)⟩

end

end Deformation
