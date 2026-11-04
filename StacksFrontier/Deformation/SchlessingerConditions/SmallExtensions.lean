module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts

/-!
# Testing Schlessinger's condition (S1) on small extensions

For a category cofibered in groupoids over `𝒞_Λ`, Schlessinger's condition (S1) follows from
its completion clause in the special case where the second base map is a small extension
(Stacks 06HX).

The argument is an induction on a factorization of the given surjection into small extensions.
With the surjection written as `B → B_{n-1} → ⋯ → A`, the cospan is pushed forward along the
first arrow — which is where cofiberedness is used — the remaining map to `A` is the strongly
cocartesian comparison, and the hypothesis supplies a completion over the last small
extension. Base-changing the prescribed pullback square along the factorization keeps it a
pullback square, so the inductive hypothesis applies to the shorter chain. In the base case
the map is an isomorphism and the completion is produced by inverting it.

## Main results

* `Deformation.schlessingerConditionS1_of_smallExtensions`: the small-extension cases of the
  completion property suffice for condition (S1).

## Implementation notes

The restricted hypothesis is exactly the completion clause of `SchlessingerConditionS1` with
the second base map required to be a small extension; like that clause it quantifies over
every prescribed pullback square rather than over one chosen fibre product. The factorization
into small extensions is the `CategoryTheory.ComposableArrows` produced by Stacks 06GE, whose
target is only isomorphic to the target of the given morphism, so the induction carries that
isomorphism and absorbs it into the last small extension.

## References

* [Stacks Project, Tag 06HX](https://stacks.math.columbia.edu/tag/06HX)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits InfinitesimalLifting IsLocalRing
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Composing a small extension with an isomorphism of its target leaves it a small
extension. -/
private theorem smallExtension_comp_iso
    {B A C : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) (e : A ≅ C)
    (hsmall : IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom)) :
    IsSmallExtension (CommRingCat.ofHom (f ≫ e.hom).hom.toRingHom) := by
  rcases hsmall with ⟨-, -, -, -, hsurj, hlen⟩
  have hinv : ∀ x, e.inv.hom (e.hom.hom x) = x := fun x =>
    congrArg (fun g : A ⟶ A => g.hom x) e.hom_inv_id
  have hEinj : Function.Injective e.hom.hom := Function.LeftInverse.injective hinv
  have hker : RingHom.ker (e.hom.hom.comp f.hom).toRingHom =
      RingHom.ker f.hom.toRingHom := by
    ext x
    change e.hom.hom (f.hom x) = 0 ↔ f.hom x = 0
    exact ⟨fun h => hEinj (by simpa using h), fun h => by simp [h]⟩
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro c
    obtain ⟨b, hb⟩ := hsurj (e.inv.hom c)
    have hb' : f.hom b = e.inv.hom c := by simpa using hb
    refine ⟨b, ?_⟩
    change e.hom.hom (f.hom b) = c
    rw [hb']
    exact congrArg (fun g : C ⟶ C => g.hom c) e.inv_hom_id
  · change Module.length B (RingHom.ker (e.hom.hom.comp f.hom).toRingHom) = 1
    rw [hker]
    exact hlen

/-- Transporting a small extension along an equality of its source. -/
private theorem smallExtension_precomp_eq
    {B₁ B₂ C : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (e : B₁ = B₂) (f : B₂ ⟶ C)
    (hsmall : IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom)) :
    IsSmallExtension (CommRingCat.ofHom (eqToHom e ≫ f).hom.toRingHom) := by
  cases e
  simpa using hsmall

/-- The comparison map from the apex of a pullback square into the base change of that square
along a factorization of its right-hand map. -/
private noncomputable def pullbackBaseChangeLift {C : Type u} [Category.{v} C]
    {A₁ A₂ A B P D : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    {e : A₂ ⟶ B} {g : B ⟶ A} {u : P ⟶ A₁} {v : P ⟶ B}
    {l₁ : D ⟶ A₁} {l₂ : D ⟶ A₂}
    (hOrig : IsPullback l₁ l₂ f₁ f₂)
    (hP : IsPullback u v f₁ g)
    (heq : f₂ = e ≫ g) : D ⟶ P :=
  hP.lift l₁ (l₂ ≫ e) (by rw [hOrig.w, heq, Category.assoc])

/-- Base-changing a pullback square along a factorization of its right-hand map keeps it a
pullback square. -/
private theorem pullbackBaseChange_isPullback {C : Type u} [Category.{v} C]
    {A₁ A₂ A B P D : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    {e : A₂ ⟶ B} {g : B ⟶ A} {u : P ⟶ A₁} {v : P ⟶ B}
    {l₁ : D ⟶ A₁} {l₂ : D ⟶ A₂}
    (hOrig : IsPullback l₁ l₂ f₁ f₂)
    (hP : IsPullback u v f₁ g)
    (heq : f₂ = e ≫ g) :
    IsPullback l₂ (pullbackBaseChangeLift hOrig hP heq) e v := by
  subst f₂
  exact (hOrig.of_right' hP).flip

/-- Two stacked completions, the lower one over `r` and the upper one over `f₂'`, compose to a
completion over `r ≫ f₂'`. -/
private def pullbackCompletionComp {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C]
    {p : F ⥤ C} {x₁ x₂ x b : F} {f₁ : x₁ ⟶ x} {f₂ : x₂ ⟶ x} {r : x₂ ⟶ b} {f₂' : b ⟶ x}
    (hfac : r ≫ f₂' = f₂) {A₁₂ B₁ : C} {g₁ : A₁₂ ⟶ p.obj x₁} {g₂ : A₁₂ ⟶ p.obj x₂}
    {h₁ : B₁ ⟶ p.obj x₁} {h₂ : B₁ ⟶ p.obj b}
    (Y : PullbackCompletion p f₁ f₂' h₁ h₂) {g₁' : A₁₂ ⟶ p.obj Y.apex}
    (Z : PullbackCompletion p Y.toSecond r g₁' g₂)
    (hg : g₁' ≫ eqToHom Y.apex_eq ≫ h₁ = g₁) :
    PullbackCompletion p f₁ f₂ g₁ g₂ where
  apex := Z.apex
  apex_eq := Z.apex_eq
  toFirst := Z.toFirst ≫ Y.toFirst
  toSecond := Z.toSecond
  comm := by rw [← hfac, reassoc_of% Z.comm, Y.comm, Category.assoc]
  map_toFirst := by
    rw [Functor.map_comp, Z.map_toFirst, Y.map_toFirst, Category.assoc, hg]
  map_toSecond := Z.map_toSecond

/-- Over a base isomorphism `p.map f₂`, a completion is obtained by inverting a pushforward of
the first leg. -/
private theorem completion_of_isIso_map
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x) [IsIso (p.map f₂)]
    {A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k} (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂)
    (hPB : IsPullback g₂ g₁ (p.map f₂) (p.map f₁)) :
    Nonempty (PullbackCompletion p f₁ f₂ g₁ g₂) := by
  have : IsIso f₂ := isIso_of_isIso_map hp f₂
  have : IsIso g₁ := hPB.flip.isIso_fst_of_isIso
  obtain ⟨y, a, ha⟩ := exists_pushforward hp (inv g₁) x₁ rfl
  have : p.IsStronglyCocartesian (inv g₁) a :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp (inv g₁) a ha
  have : IsIso a := Functor.IsStronglyCocartesian.isIso_of_base_isIso p (inv g₁) a
  have hApex : p.obj y = A₁₂ := IsHomLift.codomain_eq p (inv g₁) a
  have hMapA : p.map (inv a) = eqToHom hApex ≫ g₁ := by
    have hma : p.map a ≫ eqToHom hApex = inv g₁ := by
      simpa [hApex] using (IsHomLift.fac p (inv g₁) a).symm
    have hma' : eqToHom hApex.symm ≫ p.map (inv a) = g₁ := by
      refine (cancel_mono (p.map a ≫ eqToHom hApex)).mp ?_
      calc
        (eqToHom hApex.symm ≫ p.map (inv a)) ≫
            (p.map a ≫ eqToHom hApex) = 𝟙 A₁₂ := by simp [Category.assoc]
        _ = g₁ ≫ inv g₁ := by simp
        _ = g₁ ≫ (p.map a ≫ eqToHom hApex) := by rw [hma]
    rw [← hma']
    simp
  have hlegs : g₁ ≫ p.map f₁ ≫ inv (p.map f₂) = g₂ :=
    (cancel_mono (p.map f₂)).mp (by
      rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, hPB.w])
  refine ⟨{
    apex := y
    apex_eq := hApex
    toFirst := inv a
    toSecond := inv a ≫ f₁ ≫ inv f₂
    comm := by simp [Category.assoc]
    map_toFirst := hMapA
    map_toSecond := ?_ }⟩
  calc
    p.map (inv a ≫ f₁ ≫ inv f₂) = p.map (inv a) ≫ p.map f₁ ≫ inv (p.map f₂) := by simp
    _ = eqToHom hApex ≫ (g₁ ≫ p.map f₁ ≫ inv (p.map f₂)) := by
      rw [hMapA]
      simp [Category.assoc]
    _ = eqToHom hApex ≫ g₂ := by rw [hlegs]

/-- A completion over `r ≫ f₂'`, where `p.map f₂'` is a small extension, assembled from the
completion over `f₂'` and completions over `r`. -/
private theorem completion_of_comp
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hsmall : ∀ {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x),
      IsSmallExtension (CommRingCat.ofHom (p.map f₂).hom.toRingHom) →
        ∀ {A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k}
          (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂),
          IsPullback g₂ g₁ (p.map f₂) (p.map f₁) →
            Nonempty (PullbackCompletion p f₁ f₂ g₁ g₂))
    {x₁ x₂ x b : F} (f₁ : x₁ ⟶ x) {f₂ : x₂ ⟶ x} {r : x₂ ⟶ b} {f₂' : b ⟶ x}
    (hfac : r ≫ f₂' = f₂)
    (hsmallLast : IsSmallExtension (CommRingCat.ofHom (p.map f₂').hom.toRingHom))
    (ih : ∀ {y : F} {A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : y ⟶ b)
      (g₁ : A ⟶ p.obj y) (g₂ : A ⟶ p.obj x₂),
      IsPullback g₂ g₁ (p.map r) (p.map f) → Nonempty (PullbackCompletion p f r g₁ g₂))
    {A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k} (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂)
    (hPB : IsPullback g₂ g₁ (p.map f₂) (p.map f₁)) :
    Nonempty (PullbackCompletion p f₁ f₂ g₁ g₂) := by
  have hsurj : Function.Surjective (p.map f₂').hom := by
    obtain ⟨-, -, -, -, hs, -⟩ := hsmallLast
    exact hs
  have kPB := ArtinianLocalAlgCat.isPullback_of_surjective (p.map f₂') (p.map f₁) (Or.inl hsurj)
  obtain ⟨Y⟩ := hsmall f₁ f₂' hsmallLast _ _ kPB
  have heq : p.map f₂ = p.map r ≫ p.map f₂' := by rw [← hfac, Functor.map_comp]
  have hPBbase := pullbackBaseChange_isPullback hPB.flip kPB.flip heq
  obtain ⟨Z⟩ := ih Y.toSecond
    (pullbackBaseChangeLift hPB.flip kPB.flip heq ≫ eqToHom Y.apex_eq.symm) g₂ (by
      apply hPBbase.of_iso (Iso.refl _) (Iso.refl _) (eqToIso Y.apex_eq.symm) (Iso.refl _)
      · simp
      · rfl
      · simp
      · simp [Y.map_toSecond])
  exact ⟨pullbackCompletionComp hfac Y Z (by simp [pullbackBaseChangeLift])⟩

/-- The induction on the length of a factorization into small extensions. -/
private theorem completion_of_factorization
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (hsmall : ∀ {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x),
      IsSmallExtension (CommRingCat.ofHom (p.map f₂).hom.toRingHom) →
        ∀ {A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k}
          (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂),
          IsPullback g₂ g₁ (p.map f₂) (p.map f₁) →
            Nonempty (PullbackCompletion p f₁ f₂ g₁ g₂)) :
    ∀ (n : ℕ) {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
      (D : ComposableArrows (ArtinianLocalAlgCat.{u, v, w} Λ k) n)
      (hleft : D.left = p.obj x₂) (e : D.right ≅ p.obj x)
      (hfactor : eqToHom hleft.symm ≫ D.hom ≫ e.hom = p.map f₂)
      (_hD : ∀ (i : ℕ) (hi : i < n),
        IsSmallExtension (CommRingCat.ofHom (D.map' i (i + 1)).hom.toRingHom))
      {A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k}
      (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂),
      IsPullback g₂ g₁ (p.map f₂) (p.map f₁) →
      Nonempty (PullbackCompletion p f₁ f₂ g₁ g₂) := by
  intro n
  induction n with
  | zero =>
      intro x₁ x₂ x f₁ f₂ D hleft e hfactor hD A₁₂ g₁ g₂ hPB
      have : IsIso (p.map f₂) := by
        rw [← hfactor]
        have : IsIso D.hom := by
          change IsIso (D.map' 0 0)
          rw [D.map'_self 0 (by omega)]
          infer_instance
        infer_instance
      exact completion_of_isIso_map hp f₁ f₂ g₁ g₂ hPB
  | succ n ih =>
      intro x₁ x₂ x f₁ f₂ D hleft e hfactor hD A₁₂ g₁ g₂ hPB
      let B := D.obj' n
      let rbase : p.obj x₂ ⟶ B := eqToHom hleft.symm ≫ D.map' 0 n
      let sbase : B ⟶ p.obj x := D.map' n (n + 1) ≫ e.hom
      have hfactorBase : rbase ≫ sbase = p.map f₂ := by
        rw [← hfactor]
        change (eqToHom hleft.symm ≫ D.map' 0 n) ≫ (D.map' n (n + 1) ≫ e.hom) =
          eqToHom hleft.symm ≫ D.map' 0 (n + 1) ≫ e.hom
        simp only [D.map'_comp 0 n (n + 1) (by omega) (by omega) (by omega), Category.assoc]
      obtain ⟨b, r, hr⟩ := exists_pushforward hp rbase x₂ rfl
      have hb : p.obj b = B := IsHomLift.codomain_eq p rbase r
      have hrBase : p.map r = rbase ≫ eqToHom hb.symm := by
        have hfac : rbase = p.map r ≫ eqToHom hb := by simpa using IsHomLift.fac p rbase r
        rw [hfac]
        simp
      let sMap : p.obj b ⟶ p.obj x := eqToHom hb ≫ sbase
      have hfactorLift : p.map r ≫ sMap = p.map f₂ := by
        simp [sMap, hrBase, hfactorBase]
      have : p.IsStronglyCocartesian (p.map r) r :=
        isStronglyCocartesian_of_isCofiberedInGroupoids hp (p.map r) r (IsHomLift.map p r)
      let f₂' : b ⟶ x := Functor.IsStronglyCocartesian.map p (p.map r) r hfactorLift.symm f₂
      have hsmallLast : IsSmallExtension (CommRingCat.ofHom (p.map f₂').hom.toRingHom) := by
        rw [← IsHomLift.eq_of_isHomLift p sMap f₂']
        simpa [sMap, Category.assoc] using smallExtension_precomp_eq hb
          (D.map' n (n + 1) ≫ e.hom)
          (smallExtension_comp_iso (D.map' n (n + 1)) e (hD n (by omega)))
      have hD' : ∀ (i : ℕ) (hi : i < n), IsSmallExtension
          (CommRingCat.ofHom (D.δlast.map' i (i + 1)).hom.toRingHom) :=
        fun i _ => hD i (by omega)
      refine completion_of_comp hsmall f₁
        (Functor.IsStronglyCocartesian.fac p (p.map r) r hfactorLift.symm f₂) hsmallLast
        (fun f g₁' g₂' h => ih f r D.δlast hleft (eqToIso hb.symm) ?_ hD' g₁' g₂' h) g₁ g₂ hPB
      change eqToHom hleft.symm ≫ D.map' 0 n ≫ eqToHom hb.symm = p.map r
      exact (Category.assoc _ _ _).symm.trans hrBase.symm

/-- The small-extension cases of the completion property suffice for
Schlessinger's condition (S1). -/
@[stacks 06HX]
theorem schlessingerConditionS1_of_smallExtensions
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (h : ∀ {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x),
      IsSmallExtension (CommRingCat.ofHom (p.map f₂).hom.toRingHom) →
        ∀ {A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k}
          (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂),
          IsPullback g₂ g₁ (p.map f₂) (p.map f₁) →
            Nonempty (PullbackCompletion p f₁ f₂ g₁ g₂)) :
    SchlessingerConditionS1 p := by
  refine ⟨?_⟩
  intro x₁ x₂ x f₁ f₂ hf A₁₂ g₁ g₂ hPB
  obtain ⟨n, D, hleft, e, hfactor, hD⟩ :=
    surjective_factors_into_smallExtensions (p.map f₂) hf
  exact completion_of_factorization hp h n f₁ f₂ D hleft e hfactor hD g₁ g₂ hPB

end

end Deformation

end
