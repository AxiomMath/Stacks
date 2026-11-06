module

public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.RimSchlessingerCategory.SmallExtensionCriterion
public import StacksFrontier.Deformation.Schlessinger.Comparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Condition (RS) and equivalences of fibre categories

For a category cofibered in groupoids over the category `𝒞_Λ` of Artinian local `Λ`-algebras,
condition (RS) is equivalent to the comparison functor from the fibre over a pullback to the
categorical 2-fibre product being an equivalence. It suffices to test either all surjective
second maps or only small extensions.

## Main results

* `Deformation.satisfiesRS_iff_comparison_isEquivalence_of_surjective` characterizes condition
  (RS) by all surjective squares.
* `Deformation.satisfiesRS_iff_comparison_isEquivalence_of_smallExtension` characterizes
  condition (RS) by squares with a small extension.

## Implementation notes

The comparison functor is the canonical functor of Tag 06SP. Its construction uses choices of
pushforwards, so the equivalence is asserted for every such choice. The base fibre square is
supplied as an `IsPullback`; this includes any model of the fibre product. In the
small-extension formulation, surjectivity is obtained from the small-extension hypothesis.

## References

* [Stacks Project, Tag 06J5](https://stacks.math.columbia.edu/tag/06J5)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberCategory
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  PushforwardFunctor.toFunctor SquareComparisonFunctor.toFunctor

universe u v w u₁ v₁

/-- Two cocartesian arrows over one base morphism have isomorphic targets in the fibre. -/
private noncomputable def fiberIsoOfCocartesian
    {X : Type u₁} [Category.{v₁} X] {C : Type u} [Category.{v} C] {q : X ⥤ C}
    {A B : C} {x : q.Fiber A} {y z : q.Fiber B}
    (f : A ⟶ B) (a : x.1 ⟶ y.1) (b : x.1 ⟶ z.1)
    (ha : q.IsStronglyCocartesian f a) (hb : q.IsStronglyCocartesian f b) : y ≅ z := by
  haveI : q.IsStronglyCocartesian f a := ha
  haveI : q.IsStronglyCocartesian f b := hb
  let j := CategoryTheory.Functor.IsCocartesian.codomainUniqueUpToIso q f a b
  have hjhom : q.IsHomLift (𝟙 B) j.hom := by
    change q.IsHomLift (𝟙 B) (CategoryTheory.Functor.IsCocartesian.map q f a b)
    exact CategoryTheory.Functor.IsCocartesian.map_isHomLift q f a b
  have hjinv : q.IsHomLift (𝟙 B) j.inv := by
    change q.IsHomLift (𝟙 B) (CategoryTheory.Functor.IsCocartesian.map q f b a)
    exact CategoryTheory.Functor.IsCocartesian.map_isHomLift q f b a
  exact ⟨⟨j.hom, hjhom⟩, ⟨j.inv, hjinv⟩,
    Functor.Fiber.hom_ext j.hom_inv_id, Functor.Fiber.hom_ext j.inv_hom_id⟩

private theorem exists_iso_lift_of_cofibered
    {X : Type u₁} [Category.{v₁} X] {C : Type u} [Category.{v} C] {q : X ⥤ C}
    (hq : IsCofiberedInGroupoids q) {z : X} {U : C} (c : q.obj z ≅ U) :
    ∃ (y : X) (_ : q.obj y = U) (β : z ≅ y), q.IsHomLift c.hom β.hom := by
  obtain ⟨y, βm, hβm⟩ := exists_pushforward hq c.hom z rfl
  have : q.IsStronglyCocartesian c.hom βm :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hq c.hom βm hβm
  have hβiso : IsIso βm := Functor.IsStronglyCocartesian.isIso_of_base_isIso q c.hom βm
  exact ⟨y, IsHomLift.codomain_eq q c.hom βm, asIso βm, hβm⟩

section
variable {C : Type u} [Category.{v} C] {X : Type u₁} [Category.{v₁} X] {p : X ⥤ C}

private lemma map_lift_eq {A B : C} {x y : X} (f : A ⟶ B) (g : x ⟶ y) [p.IsHomLift f g]
    (hx : p.obj x = A) (hy : p.obj y = B) :
    p.map g = eqToHom hx ≫ f ≫ eqToHom hy.symm :=
  IsHomLift.fac' p f g

private lemma map_isPullback_of_lifts
    {P A₁ A₂ A : C} {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hP : IsPullback p₁ p₂ f₁ f₂)
    {y x₁ x₂ x : X} (a : y ⟶ x₁) (b : y ⟶ x₂) (c : x₁ ⟶ x) (d : x₂ ⟶ x)
    [p.IsHomLift p₁ a] [p.IsHomLift p₂ b] [p.IsHomLift f₁ c] [p.IsHomLift f₂ d] :
    IsPullback (p.map a) (p.map b) (p.map c) (p.map d) := by
  apply hP.of_iso
    (eqToIso (IsHomLift.domain_eq p p₁ a)).symm
    (eqToIso (IsHomLift.codomain_eq p p₁ a)).symm
    (eqToIso (IsHomLift.codomain_eq p p₂ b)).symm
    (eqToIso (IsHomLift.codomain_eq p f₂ d)).symm
  · dsimp
    rw [IsHomLift.fac' p p₁ a]
    simp
  · dsimp
    rw [IsHomLift.fac' p p₂ b]
    simp
  · dsimp
    rw [IsHomLift.fac' p f₁ c]
    simp
  · dsimp
    rw [IsHomLift.fac' p f₂ d]
    simp

private noncomputable def map_cone_isLimit {x₁ x₂ x : X} {f₁ : x₁ ⟶ x} {f₂ : x₂ ⟶ x}
    (c : PullbackCone f₁ f₂)
    (hc : IsPullback (p.map c.fst) (p.map c.snd) (p.map f₁) (p.map f₂)) :
    IsLimit (c.map p) :=
  IsLimit.ofIsoLimit hc.isLimit (PullbackCone.ext (Iso.refl _)
    (by change p.map c.fst = 𝟙 _ ≫ p.map c.fst; simp)
    (by change p.map c.snd = 𝟙 _ ≫ p.map c.snd; simp))

private noncomputable def pushforwardChoiceOfCofibered
    (hp : IsCofiberedInGroupoids p) {A B : C} (f : A ⟶ B) : PushforwardChoice p f := by
  classical
  choose y a ha using fun x : p.Fiber A => exists_pushforward hp f x.1 x.2
  exact ⟨fun x => ⟨y x, IsHomLift.codomain_eq p f (a x)⟩, a,
    fun x => isStronglyCocartesian_of_isCofiberedInGroupoids hp f (a x) (ha x)⟩

private lemma exists_pushforwardFunctor (hp : IsCofiberedInGroupoids p) {A B : C} {f : A ⟶ B}
    (P : PushforwardChoice p f) : Nonempty (PushforwardFunctor P) := by
  obtain ⟨Q⟩ := pushforwardFunctorsFormTwoCommutativeSquare p p hp (𝟭 X) rfl P P
  exact ⟨Q.source⟩

private lemma fiber_ext_of_cocartesian
    {A B : C} {z : X} {x y : p.Fiber B} (f : A ⟶ B) (a : z ⟶ x.1)
    (ha : p.IsStronglyCocartesian f a) (g h : x ⟶ y) (heq : a ≫ g.1 = a ≫ h.1) : g = h := by
  have := g.2
  have := h.2
  exact Functor.Fiber.hom_ext (Functor.IsCocartesian.ext p f a g.1 h.1 heq)

private lemma fiber_iso_exists (hp : IsCofiberedInGroupoids p)
    {A B : C} {z : X} {x y : p.Fiber B} (f : A ⟶ B)
    (a : z ⟶ x.1) (b : z ⟶ y.1) [p.IsHomLift f a] [p.IsHomLift f b] :
    ∃ e : x ≅ y, a ≫ e.hom.1 = b := by
  have ha := isStronglyCocartesian_of_isCofiberedInGroupoids hp f a inferInstance
  have hb := isStronglyCocartesian_of_isCofiberedInGroupoids hp f b inferInstance
  exact ⟨fiberIsoOfCocartesian (x := ⟨z, IsHomLift.domain_eq p f a⟩) f a b ha hb,
    Functor.IsCocartesian.fac p f a b⟩

end

section Comparison

variable {C : Type u} [Category.{v} C] {X : Type u₁} [Category.{v₁} X]
  {p : X ⥤ C} {P A₁ A₂ A : C}
  {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
  {P₁ : PushforwardChoice p p₁} {P₂ : PushforwardChoice p p₂}
  {F₁ : PushforwardChoice p f₁} {F₂ : PushforwardChoice p f₂}
  {Qp₁ : PushforwardFunctor P₁} {Qp₂ : PushforwardFunctor P₂}
  {Qf₁ : PushforwardFunctor F₁} {Qf₂ : PushforwardFunctor F₂}
  (K : SquareComparisonFunctor p p₁ p₂ f₁ f₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂)

private lemma comparison_w (y : p.Fiber P)
    (t : CategoricalPullback Qf₁.toFunctor Qf₂.toFunctor)
    (a : P₁.obj y ⟶ t.fst) (b : P₂.obj y ⟶ t.snd)
    (h : (P₁.inclusion y ≫ a.1) ≫ (F₁.inclusion t.fst ≫ t.iso.hom.1) =
      (P₂.inclusion y ≫ b.1) ≫ F₂.inclusion t.snd) :
    Qf₁.map a ≫ t.iso.hom = K.squareIso.hom.app y ≫ Qf₂.map b := by
  have := P₁.cocartesian y
  have := F₁.cocartesian (P₁.obj y)
  apply fiber_ext_of_cocartesian (p₁ ≫ f₁)
    (P₁.inclusion y ≫ F₁.inclusion (P₁.obj y)) inferInstance
  have ha := Qf₁.inclusion_naturality a
  have hb := Qf₂.inclusion_naturality b
  have hk := K.compatibility y
  change (P₁.inclusion y ≫ F₁.inclusion (P₁.obj y)) ≫
      (Functor.Fiber.fiberInclusion.map (Qf₁.map a) ≫
        Functor.Fiber.fiberInclusion.map t.iso.hom) =
    (P₁.inclusion y ≫ F₁.inclusion (P₁.obj y)) ≫
      (Functor.Fiber.fiberInclusion.map (K.squareIso.hom.app y) ≫
        Functor.Fiber.fiberInclusion.map (Qf₂.map b))
  calc
    _ = (P₁.inclusion y ≫ a.1) ≫ (F₁.inclusion t.fst ≫ t.iso.hom.1) := by
      simpa only [Category.assoc, Functor.Fiber.fiberInclusion] using
        congrArg (fun q => P₁.inclusion y ≫ q ≫ t.iso.hom.1) ha
    _ = (P₂.inclusion y ≫ b.1) ≫ F₂.inclusion t.snd := h
    _ = (P₂.inclusion y ≫ F₂.inclusion (P₂.obj y)) ≫
        Functor.Fiber.fiberInclusion.map (Qf₂.map b) := by
      simpa only [Category.assoc, Functor.Fiber.fiberInclusion] using
        congrArg (fun q => P₂.inclusion y ≫ q) hb.symm
    _ = (P₁.inclusion y ≫ F₁.inclusion (P₁.obj y)) ≫
        (Functor.Fiber.fiberInclusion.map (K.squareIso.hom.app y) ≫
          Functor.Fiber.fiberInclusion.map (Qf₂.map b)) := by
      simpa only [Category.assoc, Functor.Fiber.fiberInclusion] using
        congrArg (fun q => q ≫ Functor.Fiber.fiberInclusion.map (Qf₂.map b)) hk.symm

private lemma comparison_obj_iso_of_cone (hp : IsCofiberedInGroupoids p)
    (y : p.Fiber P) (t : CategoricalPullback Qf₁.toFunctor Qf₂.toFunctor)
    (a : y.1 ⟶ t.fst.1) (b : y.1 ⟶ t.snd.1)
    [p.IsHomLift p₁ a] [p.IsHomLift p₂ b]
    (h : a ≫ (F₁.inclusion t.fst ≫ t.iso.hom.1) = b ≫ F₂.inclusion t.snd) :
    Nonempty (K.toFunctor.obj y ≅ t) := by
  have := P₁.cocartesian y
  have := P₂.cocartesian y
  obtain ⟨e₁, he₁⟩ := fiber_iso_exists hp p₁ (P₁.inclusion y) a
  obtain ⟨e₂, he₂⟩ := fiber_iso_exists hp p₂ (P₂.inclusion y) b
  exact ⟨CategoricalPullback.mkIso e₁ e₂
    (comparison_w K y t e₁.hom e₂.hom (by rwa [he₁, he₂]))⟩

/-- The cone of the fibre inclusions over `y` maps to a limit cone under `p`. -/
private lemma comparison_map_cone_isLimit (hP : IsPullback p₁ p₂ f₁ f₂) (y : p.Fiber P) :
    Nonempty (IsLimit ((PullbackCone.mk (P₁.inclusion y) (P₂.inclusion y) (K.compatibility y) :
      PullbackCone (F₁.inclusion (P₁.obj y) ≫ (K.squareIso.hom.app y).1)
        (F₂.inclusion (P₂.obj y))).map p)) := by
  have := (P₁.cocartesian y).toIsHomLift
  have := (P₂.cocartesian y).toIsHomLift
  have := (F₁.cocartesian (P₁.obj y)).toIsHomLift
  have := (F₂.cocartesian (P₂.obj y)).toIsHomLift
  have : p.IsHomLift (𝟙 A) (K.squareIso.hom.app y).1 := (K.squareIso.hom.app y).2
  exact ⟨map_cone_isLimit _ (map_isPullback_of_lifts hP (P₁.inclusion y) (P₂.inclusion y) _ _)⟩

end Comparison

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]

/-- Under (RS), the cone of the fibre inclusions over `y` is a limit cone. -/
private lemma comparison_cone_isLimit_of_satisfiesRS
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} (hRS : SatisfiesRS p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hP : IsPullback p₁ p₂ f₁ f₂) (hf₂ : Function.Surjective f₂.hom)
    {P₁ : PushforwardChoice p p₁} {P₂ : PushforwardChoice p p₂}
    {F₁ : PushforwardChoice p f₁} {F₂ : PushforwardChoice p f₂}
    {Qp₁ : PushforwardFunctor P₁} {Qp₂ : PushforwardFunctor P₂}
    {Qf₁ : PushforwardFunctor F₁} {Qf₂ : PushforwardFunctor F₂}
    (K : SquareComparisonFunctor p p₁ p₂ f₁ f₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂) (y : p.Fiber P) :
    Nonempty (IsLimit (PullbackCone.mk (P₁.inclusion y) (P₂.inclusion y) (K.compatibility y) :
      PullbackCone (F₁.inclusion (P₁.obj y) ≫ (K.squareIso.hom.app y).1)
        (F₂.inclusion (P₂.obj y)))) := by
  have := (F₁.cocartesian (P₁.obj y)).toIsHomLift
  have := (F₂.cocartesian (P₂.obj y)).toIsHomLift
  have : p.IsHomLift (𝟙 A) (K.squareIso.hom.app y).1 := (K.squareIso.hom.app y).2
  exact isLimit_of_map_isLimit hRS _ _ _
    (surjective_map_of_lift p f₂ (F₂.inclusion (P₂.obj y)) hf₂) (comparison_map_cone_isLimit K hP y)

private lemma comparison_fullFaithful_of_satisfiesRS
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} (hRS : SatisfiesRS p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hP : IsPullback p₁ p₂ f₁ f₂) (hf₂ : Function.Surjective f₂.hom)
    (P₁ : PushforwardChoice p p₁) (P₂ : PushforwardChoice p p₂)
    (F₁ : PushforwardChoice p f₁) (F₂ : PushforwardChoice p f₂)
    (Qp₁ : PushforwardFunctor P₁) (Qp₂ : PushforwardFunctor P₂)
    (Qf₁ : PushforwardFunctor F₁) (Qf₂ : PushforwardFunctor F₂)
    (K : SquareComparisonFunctor p p₁ p₂ f₁ f₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂) :
    K.toFunctor.Full ∧ K.toFunctor.Faithful := by
  classical
  let i₁ := Functor.Fiber.fiberInclusion (p := p) (S := A₁)
  let i₂ := Functor.Fiber.fiberInclusion (p := p) (S := A₂)
  let iA := Functor.Fiber.fiberInclusion (p := p) (S := A)
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · intro x y g
    have hP₁ : p.IsHomLift p₁ (P₁.inclusion y) := (P₁.cocartesian y).toIsHomLift
    have hP₂ : p.IsHomLift p₂ (P₂.inclusion y) := (P₂.cocartesian y).toIsHomLift
    obtain ⟨hc⟩ := comparison_cone_isLimit_of_satisfiesRS hRS hP hf₂ K y
    obtain ⟨hcbase⟩ := comparison_map_cone_isLimit K hP y
    let d₁ := F₁.inclusion (P₁.obj y) ≫ (K.squareIso.hom.app y).1
    let d₂ := F₂.inclusion (P₂.obj y)
    let c : PullbackCone d₁ d₂ :=
      PullbackCone.mk (P₁.inclusion y) (P₂.inclusion y) (K.compatibility y)
    let l₁ : x.1 ⟶ (P₁.obj y).1 := P₁.inclusion x ≫ i₁.map g.fst
    let l₂ : x.1 ⟶ (P₂.obj y).1 := P₂.inclusion x ≫ i₂.map g.snd
    have hl : l₁ ≫ d₁ = l₂ ≫ d₂ := by
      dsimp only [l₁, l₂, d₁, d₂]
      have hn₁ : F₁.inclusion (P₁.obj x) ≫ iA.map (Qf₁.map g.fst) =
          i₁.map g.fst ≫ F₁.inclusion (P₁.obj y) := Qf₁.inclusion_naturality g.fst
      have hn₂ : F₂.inclusion (P₂.obj x) ≫ iA.map (Qf₂.map g.snd) =
          i₂.map g.snd ≫ F₂.inclusion (P₂.obj y) := Qf₂.inclusion_naturality g.snd
      have hw : Qf₁.map g.fst ≫ K.squareIso.hom.app y =
          K.squareIso.hom.app x ≫ Qf₂.map g.snd := g.w
      change (P₁.inclusion x ≫ i₁.map g.fst) ≫
        (F₁.inclusion (P₁.obj y) ≫ iA.map (K.squareIso.hom.app y)) =
        (P₂.inclusion x ≫ i₂.map g.snd) ≫ F₂.inclusion (P₂.obj y)
      have hn₁a := congrArg (fun t => t ≫ iA.map (K.squareIso.hom.app y)) hn₁
      simp only [Category.assoc] at hn₁a ⊢
      rw [← hn₁a, ← hn₂, ← iA.map_comp, hw, iA.map_comp]
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ iA.map (Qf₂.map g.snd)) (K.compatibility x)
    let m := PullbackCone.IsLimit.lift hc l₁ l₂ hl
    have hm₁ : m ≫ c.fst = l₁ := PullbackCone.IsLimit.lift_fst hc l₁ l₂ hl
    have hm₂ : m ≫ c.snd = l₂ := PullbackCone.IsLimit.lift_snd hc l₁ l₂ hl
    have hlift₁ : p.IsHomLift p₁ l₁ := by
      dsimp only [l₁]
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _ p₁
        (P₁.inclusion x) (P₁.cocartesian x).toIsHomLift A₁ (i₁.map g.fst) g.fst.2
    have hlift₂ : p.IsHomLift p₂ l₂ := by
      dsimp only [l₂]
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _ p₂
        (P₂.inclusion x) (P₂.cocartesian x).toIsHomLift A₂ (i₂.map g.snd) g.snd.2
    have hm_base : p.map m = eqToHom (x.2.trans y.2.symm) := by
      apply PullbackCone.IsLimit.hom_ext hcbase
      · change p.map m ≫ p.map (P₁.inclusion y) =
          eqToHom (x.2.trans y.2.symm) ≫ p.map (P₁.inclusion y)
        calc
          p.map m ≫ p.map (P₁.inclusion y) = p.map (m ≫ P₁.inclusion y) :=
            (Functor.map_comp p m (P₁.inclusion y)).symm
          _ = p.map l₁ := congrArg p.map hm₁
          _ = eqToHom (x.2.trans y.2.symm) ≫ p.map (P₁.inclusion y) := by
            rw [IsHomLift.fac' p p₁ l₁, IsHomLift.fac' p p₁ (P₁.inclusion y)]
            simp
      · change p.map m ≫ p.map (P₂.inclusion y) =
          eqToHom (x.2.trans y.2.symm) ≫ p.map (P₂.inclusion y)
        calc
          p.map m ≫ p.map (P₂.inclusion y) = p.map (m ≫ P₂.inclusion y) :=
            (Functor.map_comp p m (P₂.inclusion y)).symm
          _ = p.map l₂ := congrArg p.map hm₂
          _ = eqToHom (x.2.trans y.2.symm) ≫ p.map (P₂.inclusion y) := by
            rw [IsHomLift.fac' p p₂ l₂, IsHomLift.fac' p p₂ (P₂.inclusion y)]
            simp
    have : p.IsHomLift (𝟙 P) m := IsHomLift.of_fac' p (𝟙 P) m x.2 y.2 (by rw [hm_base]; simp)
    let m₀ : x ⟶ y := Functor.Fiber.homMk p P m
    refine ⟨m₀, ?_⟩
    apply CategoricalPullback.Hom.ext
    · apply fiber_ext_of_cocartesian p₁ (P₁.inclusion x) (P₁.cocartesian x)
      exact (Qp₁.inclusion_naturality m₀).trans hm₁
    · apply fiber_ext_of_cocartesian p₂ (P₂.inclusion x) (P₂.cocartesian x)
      exact (Qp₂.inclusion_naturality m₀).trans hm₂
  · intro x y f g hfg
    apply Functor.Fiber.hom_ext
    have h₁ : Qp₁.map f = Qp₁.map g := congrArg CategoricalPullback.Hom.fst hfg
    have h₂ : Qp₂.map f = Qp₂.map g := congrArg CategoricalPullback.Hom.snd hfg
    obtain ⟨hc⟩ := comparison_cone_isLimit_of_satisfiesRS hRS hP hf₂ K y
    apply PullbackCone.IsLimit.hom_ext hc
    · exact (Qp₁.inclusion_naturality f).symm.trans (h₁ ▸ Qp₁.inclusion_naturality g)
    · exact (Qp₂.inclusion_naturality f).symm.trans (h₂ ▸ Qp₂.inclusion_naturality g)

private lemma exists_fiber_cone
    {C : Type u} [Category.{v} C] {X : Type u₁} [Category.{v₁} X]
    {p : X ⥤ C} (hp : IsCofiberedInGroupoids p)
    {P A₁ A₂ A : C} {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hP : IsPullback p₁ p₂ f₁ f₂)
    {x₁ : p.Fiber A₁} {x₂ : p.Fiber A₂} {x : p.Fiber A}
    (d₁ : x₁.1 ⟶ x.1) (d₂ : x₂.1 ⟶ x.1) [p.IsHomLift f₁ d₁] [p.IsHomLift f₂ d₂]
    (c : PullbackCone d₁ d₂) (hc : IsLimit (c.map p)) :
    ∃ (y : p.Fiber P) (a : y.1 ⟶ x₁.1) (b : y.1 ⟶ x₂.1),
      p.IsHomLift p₁ a ∧ p.IsHomLift p₂ b ∧ a ≫ d₁ = b ≫ d₂ := by
  classical
  have hc' : IsPullback (p.map c.fst ≫ eqToHom x₁.2) (p.map c.snd ≫ eqToHom x₂.2) f₁ f₂ := by
    apply (IsPullback.of_isLimit hc).of_iso (Iso.refl _) (eqToIso x₁.2)
      (eqToIso x₂.2) (eqToIso x.2)
    · simp
    · simp
    · change p.map d₁ ≫ eqToHom x.2 = eqToHom x₁.2 ≫ f₁
      rw [map_lift_eq f₁ d₁ x₁.2 x.2]
      simp
    · change p.map d₂ ≫ eqToHom x.2 = eqToHom x₂.2 ≫ f₂
      rw [map_lift_eq f₂ d₂ x₂.2 x.2]
      simp
  let e := hc'.isoIsPullback _ _ hP
  obtain ⟨y, hy, β, hβ⟩ := exists_iso_lift_of_cofibered hp e
  refine ⟨⟨y, hy⟩, β.inv ≫ c.fst, β.inv ≫ c.snd, ?_, ?_, ?_⟩
  · apply IsHomLift.of_fac' p p₁ _ hy x₁.2
    rw [p.map_comp, map_lift_eq e.inv β.inv hy rfl]
    have he : e.inv ≫ p.map c.fst ≫ eqToHom x₁.2 = p₁ := by
      simpa only [e, Category.assoc] using IsPullback.isoIsPullback_inv_fst _ _ hc' hP
    simpa [Category.assoc] using
      congrArg (fun t => eqToHom hy ≫ t ≫ eqToHom x₁.2.symm) he
  · apply IsHomLift.of_fac' p p₂ _ hy x₂.2
    rw [p.map_comp, map_lift_eq e.inv β.inv hy rfl]
    have he : e.inv ≫ p.map c.snd ≫ eqToHom x₂.2 = p₂ := by
      simpa only [e, Category.assoc] using IsPullback.isoIsPullback_inv_snd _ _ hc' hP
    simpa [Category.assoc] using
      congrArg (fun t => eqToHom hy ≫ t ≫ eqToHom x₂.2.symm) he
  · simpa only [Category.assoc] using congrArg (fun t => β.inv ≫ t) c.condition

private lemma comparison_essSurj_of_satisfiesRS
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} (hRS : SatisfiesRS p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (hP : IsPullback p₁ p₂ f₁ f₂) (hf₂ : Function.Surjective f₂.hom)
    (P₁ : PushforwardChoice p p₁) (P₂ : PushforwardChoice p p₂)
    (F₁ : PushforwardChoice p f₁) (F₂ : PushforwardChoice p f₂)
    (Qp₁ : PushforwardFunctor P₁) (Qp₂ : PushforwardFunctor P₂)
    (Qf₁ : PushforwardFunctor F₁) (Qf₂ : PushforwardFunctor F₂)
    (K : SquareComparisonFunctor p p₁ p₂ f₁ f₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂) :
    K.toFunctor.EssSurj := by
  classical
  refine ⟨fun t => ?_⟩
  let d₁ : t.fst.1 ⟶ (F₂.obj t.snd).1 := F₁.inclusion t.fst ≫ t.iso.hom.1
  let d₂ := F₂.inclusion t.snd
  have := F₁.cocartesian t.fst
  have := F₂.cocartesian t.snd
  have hinc : p.IsHomLift f₁ (F₁.inclusion t.fst) := (F₁.cocartesian t.fst).toIsHomLift
  have hiso : p.IsHomLift (𝟙 A) t.iso.hom.1 := t.iso.hom.2
  have hd₁ : p.IsHomLift f₁ d₁ := by
    dsimp only [d₁]
    infer_instance
  obtain ⟨c, _, ⟨hc⟩⟩ := hRS.2 d₁ d₂ (surjective_map_of_lift p f₂ d₂ hf₂)
  obtain ⟨y, a, b, ha, hb, h⟩ := exists_fiber_cone hRS.1 hP
    (x₁ := t.fst) (x₂ := t.snd) (x := F₂.obj t.snd) d₁ d₂ c hc
  exact ⟨y, comparison_obj_iso_of_cone K hRS.1 y t a b h⟩

section ComparisonLimit

variable {C : Type u} [Category.{v} C] {X : Type u₁} [Category.{v₁} X]
  {p : X ⥤ C} {P A₁ A₂ A : C}
  {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
  {P₁ : PushforwardChoice p p₁} {P₂ : PushforwardChoice p p₂}
  {F₁ : PushforwardChoice p f₁} {F₂ : PushforwardChoice p f₂}
  {Qp₁ : PushforwardFunctor P₁} {Qp₂ : PushforwardFunctor P₂}
  {Qf₁ : PushforwardFunctor F₁} {Qf₂ : PushforwardFunctor F₂}
  (K : SquareComparisonFunctor p p₁ p₂ f₁ f₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂)

private lemma comparison_isPullback (hp : IsCofiberedInGroupoids p)
    (hP : IsPullback p₁ p₂ f₁ f₂) [K.toFunctor.Full] [K.toFunctor.Faithful]
    (y : p.Fiber P) :
    IsPullback (P₁.inclusion y) (P₂.inclusion y)
      (F₁.inclusion (P₁.obj y) ≫ (K.squareIso.hom.app y).1) (F₂.inclusion (P₂.obj y)) := by
  classical
  let d₁ := F₁.inclusion (P₁.obj y) ≫ (K.squareIso.hom.app y).1
  let d₂ := F₂.inclusion (P₂.obj y)
  let c : PullbackCone d₁ d₂ :=
    PullbackCone.mk (P₁.inclusion y) (P₂.inclusion y) (K.compatibility y)
  have := P₁.cocartesian y
  have := P₂.cocartesian y
  have := F₁.cocartesian (P₁.obj y)
  have := F₂.cocartesian (P₂.obj y)
  have hiso : p.IsHomLift (𝟙 A) (K.squareIso.hom.app y).1 := (K.squareIso.hom.app y).2
  have hd₁ : p.IsHomLift f₁ d₁ := by
    dsimp only [d₁]
    infer_instance
  obtain ⟨hcbase⟩ := comparison_map_cone_isLimit K hP y
  have hl : ∀ s : PullbackCone d₁ d₂, ∃ l : s.pt ⟶ c.pt,
      l ≫ c.fst = s.fst ∧ l ≫ c.snd = s.snd ∧
        ∀ {m}, m ≫ c.fst = s.fst → m ≫ c.snd = s.snd → m = l := by
    intro s
    let f := PullbackCone.IsLimit.lift hcbase (p.map s.fst) (p.map s.snd)
      (by simpa only [← p.map_comp] using congrArg p.map s.condition)
    have hf₁ : f ≫ p.map (P₁.inclusion y) = p.map s.fst :=
      PullbackCone.IsLimit.lift_fst hcbase _ _ _
    have hf₂ : f ≫ p.map (P₂.inclusion y) = p.map s.snd :=
      PullbackCone.IsLimit.lift_snd hcbase _ _ _
    let h := f ≫ eqToHom y.2
    have hs₁ : p.IsHomLift (h ≫ p₁) s.fst := by
      apply IsHomLift.of_fac' p _ _ rfl (P₁.obj y).2
      rw [← hf₁, map_lift_eq p₁ (P₁.inclusion y) y.2 (P₁.obj y).2]
      simp [h, Category.assoc]
    have hs₂ : p.IsHomLift (h ≫ p₂) s.snd := by
      apply IsHomLift.of_fac' p _ _ rfl (P₂.obj y).2
      rw [← hf₂, map_lift_eq p₂ (P₂.inclusion y) y.2 (P₂.obj y).2]
      simp [h, Category.assoc]
    obtain ⟨z, q, hq⟩ := exists_pushforward hp h s.pt rfl
    have := isStronglyCocartesian_of_isCofiberedInGroupoids hp h q hq
    let zf : p.Fiber P := ⟨z, IsHomLift.codomain_eq p h q⟩
    obtain ⟨a, ⟨ha, hqa⟩, _⟩ :=
      Functor.IsStronglyCocartesian.universal_property p h q p₁ (h ≫ p₁) rfl s.fst
    obtain ⟨b, ⟨hb, hqb⟩, _⟩ :=
      Functor.IsStronglyCocartesian.universal_property p h q p₂ (h ≫ p₂) rfl s.snd
    have hab : a ≫ d₁ = b ≫ d₂ := by
      have : p.IsHomLift (p₁ ≫ f₁) (b ≫ d₂) := by rw [hP.w]; infer_instance
      apply Functor.IsStronglyCocartesian.ext p h q (p₁ ≫ f₁)
      simpa only [← Category.assoc, hqa, hqb] using s.condition
    have := P₁.cocartesian zf
    have := P₂.cocartesian zf
    obtain ⟨e₁, he₁⟩ := fiber_iso_exists hp p₁ (P₁.inclusion zf) a
    obtain ⟨e₂, he₂⟩ := fiber_iso_exists hp p₂ (P₂.inclusion zf) b
    let g : K.toFunctor.obj zf ⟶ K.toFunctor.obj y :=
      ⟨e₁.hom, e₂.hom, comparison_w K zf (K.toFunctor.obj y) e₁.hom e₂.hom
        (by rw [he₁, he₂]; exact hab)⟩
    let n₀ := K.toFunctor.preimage g
    have hn₀₁ : n₀.1 ≫ P₁.inclusion y = a := by
      have hg : Qp₁.map n₀ = e₁.hom :=
        congrArg CategoricalPullback.Hom.fst (K.toFunctor.map_preimage g)
      have hn := Qp₁.inclusion_naturality n₀
      rw [hg] at hn
      exact hn.symm.trans he₁
    have hn₀₂ : n₀.1 ≫ P₂.inclusion y = b := by
      have hg : Qp₂.map n₀ = e₂.hom :=
        congrArg CategoricalPullback.Hom.snd (K.toFunctor.map_preimage g)
      have hn := Qp₂.inclusion_naturality n₀
      rw [hg] at hn
      exact hn.symm.trans he₂
    refine ⟨q ≫ n₀.1, ?_, ?_, ?_⟩
    · change (q ≫ n₀.1) ≫ P₁.inclusion y = s.fst
      rw [Category.assoc, hn₀₁, hqa]
    · change (q ≫ n₀.1) ≫ P₂.inclusion y = s.snd
      rw [Category.assoc, hn₀₂, hqb]
    · intro m hm₁ hm₂
      change m ≫ P₁.inclusion y = s.fst at hm₁
      change m ≫ P₂.inclusion y = s.snd at hm₂
      have hm : p.map m = f := by
        apply PullbackCone.IsLimit.hom_ext hcbase
        · change p.map m ≫ p.map (P₁.inclusion y) = f ≫ p.map (P₁.inclusion y)
          rw [← p.map_comp, hm₁, hf₁]
        · change p.map m ≫ p.map (P₂.inclusion y) = f ≫ p.map (P₂.inclusion y)
          rw [← p.map_comp, hm₂, hf₂]
      have hmlift : p.IsHomLift h m := by
        apply IsHomLift.of_fac' p h m rfl y.2
        simp [h, hm]
      let n : zf ⟶ y := ⟨Functor.IsCocartesian.map p h q m, inferInstance⟩
      have hqn : q ≫ n.1 = m := Functor.IsCocartesian.fac p h q m
      have hn₁ : n.1 ≫ P₁.inclusion y = a := by
        have : p.IsHomLift (𝟙 P) n.1 := n.2
        have : p.IsHomLift p₁ (n.1 ≫ P₁.inclusion y) :=
          IsHomLift.comp_lift_id_left' p P _ p₁ _
        apply Functor.IsStronglyCocartesian.ext p h q p₁
        rw [← Category.assoc, hqn, hm₁, hqa]
      have hn₂ : n.1 ≫ P₂.inclusion y = b := by
        have : p.IsHomLift (𝟙 P) n.1 := n.2
        have : p.IsHomLift p₂ (n.1 ≫ P₂.inclusion y) :=
          IsHomLift.comp_lift_id_left' p P _ p₂ _
        apply Functor.IsStronglyCocartesian.ext p h q p₂
        rw [← Category.assoc, hqn, hm₂, hqb]
      have hnn : n = n₀ := by
        apply K.toFunctor.map_injective
        rw [K.toFunctor.map_preimage]
        apply CategoricalPullback.Hom.ext
        · apply fiber_ext_of_cocartesian p₁ (P₁.inclusion zf) (P₁.cocartesian zf)
          exact (Qp₁.inclusion_naturality n).trans (hn₁.trans he₁.symm)
        · apply fiber_ext_of_cocartesian p₂ (P₂.inclusion zf) (P₂.cocartesian zf)
          exact (Qp₂.inclusion_naturality n).trans (hn₂.trans he₂.symm)
      rw [← hqn, hnn]
  exact IsPullback.of_isLimit (PullbackCone.isLimitAux' c
    (fun s => ⟨(hl s).choose, (hl s).choose_spec⟩))

end ComparisonLimit

section ComparisonIso

variable {C : Type u} [Category.{v} C] {X : Type u₁} [Category.{v₁} X]
  {p : X ⥤ C} {P A₁ A₂ A : C}
  {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
  {P₁ : PushforwardChoice p p₁} {P₂ : PushforwardChoice p p₂}
  {F₁ : PushforwardChoice p f₁} {F₂ : PushforwardChoice p f₂}
  {Qp₁ : PushforwardFunctor P₁} {Qp₂ : PushforwardFunctor P₂}
  {Qf₁ : PushforwardFunctor F₁} {Qf₂ : PushforwardFunctor F₂}
  (K : SquareComparisonFunctor p p₁ p₂ f₁ f₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂)

private lemma isPullback_of_comparison_iso (hp : IsCofiberedInGroupoids p)
    (hP : IsPullback p₁ p₂ f₁ f₂) [K.toFunctor.Full] [K.toFunctor.Faithful]
    (y : p.Fiber P) (t : CategoricalPullback Qf₁.toFunctor Qf₂.toFunctor)
    (e : K.toFunctor.obj y ≅ t) :
    IsPullback (P₁.inclusion y ≫ e.hom.fst.1) (P₂.inclusion y ≫ e.hom.snd.1)
      (F₁.inclusion t.fst ≫ t.iso.hom.1) (F₂.inclusion t.snd) := by
  let e₁ := (CategoricalPullback.π₁ _ _).mapIso e
  let e₂ := (CategoricalPullback.π₂ _ _).mapIso e
  apply (comparison_isPullback K hp hP y).of_iso (Iso.refl _)
    (Functor.Fiber.fiberInclusion.mapIso e₁)
    (Functor.Fiber.fiberInclusion.mapIso e₂)
    (Functor.Fiber.fiberInclusion.mapIso (Qf₂.toFunctor.mapIso e₂))
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · change (F₁.inclusion (P₁.obj y) ≫ (K.squareIso.hom.app y).1) ≫
        (Qf₂.map e.hom.snd).1 = e.hom.fst.1 ≫ (F₁.inclusion t.fst ≫ t.iso.hom.1)
    have hw := congrArg Functor.Fiber.fiberInclusion.map e.hom.w
    change (Qf₁.map e.hom.fst).1 ≫ t.iso.hom.1 =
      (K.squareIso.hom.app y).1 ≫ (Qf₂.map e.hom.snd).1 at hw
    rw [Category.assoc, ← hw, ← Category.assoc]
    have hn := Qf₁.inclusion_naturality e.hom.fst
    change F₁.inclusion (P₁.obj y) ≫ (Qf₁.map e.hom.fst).1 =
      e.hom.fst.1 ≫ F₁.inclusion t.fst at hn
    rw [hn, Category.assoc]
  · exact Qf₂.inclusion_naturality e.hom.snd

private lemma exists_pullback_of_comparison_isEquivalence
    (hp : IsCofiberedInGroupoids p) (hP : IsPullback p₁ p₂ f₁ f₂)
    [K.toFunctor.IsEquivalence]
    (x₁ : p.Fiber A₁) (x₂ : p.Fiber A₂) (x : p.Fiber A)
    (d₁ : x₁.1 ⟶ x.1) (d₂ : x₂.1 ⟶ x.1) [p.IsHomLift f₁ d₁] [p.IsHomLift f₂ d₂] :
    ∃ c : PullbackCone d₁ d₂, Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map p)) := by
  classical
  have := F₁.cocartesian x₁
  have := F₂.cocartesian x₂
  obtain ⟨j₁, hj₁⟩ := fiber_iso_exists hp f₁ (F₁.inclusion x₁) d₁
  obtain ⟨j₂, hj₂⟩ := fiber_iso_exists hp f₂ (F₂.inclusion x₂) d₂
  let t : CategoricalPullback Qf₁.toFunctor Qf₂.toFunctor := ⟨x₁, x₂, j₁ ≪≫ j₂.symm⟩
  let y := K.toFunctor.objPreimage t
  let e := K.toFunctor.objObjPreimageIso t
  let a := P₁.inclusion y ≫ e.hom.fst.1
  let b := P₂.inclusion y ≫ e.hom.snd.1
  have hc : IsPullback a b d₁ d₂ := by
    apply (isPullback_of_comparison_iso K hp hP y t e).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Functor.Fiber.fiberInclusion.mapIso j₂)
    · simp [a]
    · simp [b]
    · have hj : j₂.inv.1 ≫ j₂.hom.1 = 𝟙 _ :=
        congrArg Functor.Fiber.fiberInclusion.map j₂.inv_hom_id
      change (F₁.inclusion x₁ ≫ (j₁.hom.1 ≫ j₂.inv.1)) ≫ j₂.hom.1 = 𝟙 _ ≫ d₁
      simp only [Category.assoc, hj, Category.comp_id, Category.id_comp, hj₁]
    · simpa [t, Functor.Fiber.fiberInclusion] using hj₂
  have := P₁.cocartesian y
  have := P₂.cocartesian y
  have hef : p.IsHomLift (𝟙 A₁) e.hom.fst.1 := e.hom.fst.2
  have hes : p.IsHomLift (𝟙 A₂) e.hom.snd.1 := e.hom.snd.2
  have ha : p.IsHomLift p₁ a := IsHomLift.comp_lift_id_right' p p₁ _ A₁ _
  have hb : p.IsHomLift p₂ b := IsHomLift.comp_lift_id_right' p p₂ _ A₂ _
  exact ⟨hc.cone, ⟨hc.isLimit⟩,
    ⟨map_cone_isLimit (p := p) hc.cone (map_isPullback_of_lifts (p := p) hP a b d₁ d₂)⟩⟩

end ComparisonIso

/-- If the comparison functors of the pullback square of `p.map d₁` and `p.map d₂` are
equivalences, then `d₁, d₂` admit a pullback cone preserved by `p`. -/
private lemma exists_pullback_of_comparisons
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} (hp : IsCofiberedInGroupoids p)
    {x₁ x₂ x : F} (d₁ : x₁ ⟶ x) (d₂ : x₂ ⟶ x) (hd₂ : Function.Surjective (p.map d₂).hom)
    (h : ∀ {P : ArtinianLocalAlgCat.{u, v, w} Λ k} (p₁ : P ⟶ p.obj x₁) (p₂ : P ⟶ p.obj x₂)
      (hP : IsPullback p₁ p₂ (p.map d₁) (p.map d₂))
      (P₁ : PushforwardChoice p p₁) (P₂ : PushforwardChoice p p₂)
      (F₁ : PushforwardChoice p (p.map d₁)) (F₂ : PushforwardChoice p (p.map d₂))
      (Qp₁ : PushforwardFunctor P₁) (Qp₂ : PushforwardFunctor P₂)
      (Qf₁ : PushforwardFunctor F₁) (Qf₂ : PushforwardFunctor F₂),
      (squareComparisonFunctor p hp p₁ p₂ (p.map d₁) (p.map d₂) hP hd₂
        P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂).toFunctor.IsEquivalence) :
    ∃ c : PullbackCone d₁ d₂, Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map p)) := by
  let p₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective (p.map d₁) (p.map d₂) (Or.inr hd₂)
  let p₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective (p.map d₁) (p.map d₂) (Or.inr hd₂)
  have hP := ArtinianLocalAlgCat.isPullback_of_surjective (p.map d₁) (p.map d₂) (Or.inr hd₂)
  let P₁ := pushforwardChoiceOfCofibered hp p₁
  let P₂ := pushforwardChoiceOfCofibered hp p₂
  let F₁ := pushforwardChoiceOfCofibered hp (p.map d₁)
  let F₂ := pushforwardChoiceOfCofibered hp (p.map d₂)
  obtain ⟨Qp₁⟩ := exists_pushforwardFunctor hp P₁
  obtain ⟨Qp₂⟩ := exists_pushforwardFunctor hp P₂
  obtain ⟨Qf₁⟩ := exists_pushforwardFunctor hp F₁
  obtain ⟨Qf₂⟩ := exists_pushforwardFunctor hp F₂
  let K := squareComparisonFunctor p hp p₁ p₂ (p.map d₁) (p.map d₂)
    hP hd₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂
  have hK : K.toFunctor.IsEquivalence := h p₁ p₂ hP P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂
  exact exists_pullback_of_comparison_isEquivalence K hp hP
    ⟨x₁, rfl⟩ ⟨x₂, rfl⟩ ⟨x, rfl⟩ d₁ d₂

/-- **Stacks Project, Tag 06J5.** Condition (RS) holds precisely when the canonical functor
from the fibre over a pullback to the 2-fibre product of fibres is an equivalence for every
square whose second map is surjective. -/
@[stacks 06J5 "surjective maps", sga "7 VI 2.6(b)" "homogeneous criterion"]
theorem satisfiesRS_iff_comparison_isEquivalence_of_surjective
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    SatisfiesRS p ↔
      ∀ {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
        (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
        (hP : IsPullback p₁ p₂ f₁ f₂)
        (hf₂ : Function.Surjective f₂.hom)
        (P₁ : PushforwardChoice p p₁) (P₂ : PushforwardChoice p p₂)
        (F₁ : PushforwardChoice p f₁) (F₂ : PushforwardChoice p f₂)
        (Qp₁ : PushforwardFunctor P₁) (Qp₂ : PushforwardFunctor P₂)
        (Qf₁ : PushforwardFunctor F₁) (Qf₂ : PushforwardFunctor F₂),
        (squareComparisonFunctor p hp p₁ p₂ f₁ f₂ hP hf₂
          P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂).toFunctor.IsEquivalence := by
  constructor
  · intro hRS P A₁ A₂ A p₁ p₂ f₁ f₂ hP hf₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂
    let K := squareComparisonFunctor p hp p₁ p₂ f₁ f₂ hP hf₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂
    obtain ⟨hFull, hFaithful⟩ := comparison_fullFaithful_of_satisfiesRS hRS hP hf₂
      P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂ K
    have := comparison_essSurj_of_satisfiesRS hRS hP hf₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂ K
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro h
    refine ⟨hp, fun {x₁ x₂ x} d₁ d₂ hd₂ => ?_⟩
    exact exists_pullback_of_comparisons hp d₁ d₂ hd₂ fun _ _ hP => h _ _ _ _ hP hd₂

/-- **Stacks Project, Tag 06J5.** It is enough to test the comparison functor on squares whose
second map is a small extension. -/
@[stacks 06J5 "small extensions", sga "7 VI 2.6(b)" "small extensions"]
theorem satisfiesRS_iff_comparison_isEquivalence_of_smallExtension
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    SatisfiesRS p ↔
      ∀ {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
        (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
        (hP : IsPullback p₁ p₂ f₁ f₂)
        (hsmall : InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom f₂.hom.toRingHom))
        (P₁ : PushforwardChoice p p₁) (P₂ : PushforwardChoice p p₂)
        (F₁ : PushforwardChoice p f₁) (F₂ : PushforwardChoice p f₂)
        (Qp₁ : PushforwardFunctor P₁) (Qp₂ : PushforwardFunctor P₂)
        (Qf₁ : PushforwardFunctor F₁) (Qf₂ : PushforwardFunctor F₂),
        (squareComparisonFunctor p hp p₁ p₂ f₁ f₂ hP
          hsmall.2.2.2.2.1 P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂).toFunctor.IsEquivalence := by
  constructor
  · intro hRS P A₁ A₂ A p₁ p₂ f₁ f₂ hP hsmall P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂
    exact (satisfiesRS_iff_comparison_isEquivalence_of_surjective p hp).mp hRS
      p₁ p₂ f₁ f₂ hP hsmall.2.2.2.2.1 P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂
  · intro h
    refine satisfiesRS_of_small_extensions hp fun {x₁ x₂ x} d₁ d₂ hsmall => ?_
    have hd₂ := hsmall.2.2.2.2.1
    exact exists_pullback_of_comparisons hp d₁ d₂ hd₂ fun _ _ hP => h _ _ _ _ hP hsmall

end

end Deformation
