module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.RimSchlessingerCategory.ElementsCofibered
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Rim-Schlessinger condition for the associated functor

For a category cofibered in groupoids satisfying (RS), the associated functor of isomorphism
classes satisfies (RS) exactly when automorphisms lift along surjections of Artinian local
algebras, or equivalently along small extensions. An intermediate condition is injectivity of
the comparison from isomorphism classes of gluing data to pairs of isomorphism classes in the two
fibres. Gluing data are given by two arrows to a common object over given maps of Artinian local
algebras, and an isomorphism of gluing data by three fibrewise isomorphisms commuting with these
arrows.

## Main definitions

* `Deformation.IsInjectiveOnGluingClasses`: the injectivity condition on isomorphism classes
  of gluing data.
* `Deformation.AutomorphismsLiftAlong`: every automorphism of the target of an arrow over a given
  base arrow is induced by an automorphism of its source.

## Main results

* `Deformation.associatedSatisfiesRS_iff_gluingClassesInjective`: the associated functor
  satisfies (RS) exactly when `Deformation.IsInjectiveOnGluingClasses` holds.
* `Deformation.gluingClassesInjective_iff_automorphismsLift`: injectivity on gluing classes is
  equivalent to automorphisms lifting along every surjection.
* `Deformation.automorphismsLift_iff_smallExtensions`: automorphisms lift along every surjection
  exactly when they lift along every small extension.

## References

* [Stacks Project, Tag 06J8](https://stacks.math.columbia.edu/tag/06J8)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁

/-- Injectivity of the map from isomorphism classes of gluing data to pairs of isomorphism
classes in the two fibres. -/
def IsInjectiveOnGluingClasses
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) : Prop :=
  ∀ {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A), Function.Surjective f₂.hom →
    ∀ (x₁ y₁ : p.Fiber A₁) (x₂ y₂ : p.Fiber A₂) (x y : p.Fiber A)
      (g₁ : x₁.1 ⟶ x.1) (g₂ : x₂.1 ⟶ x.1)
      (h₁ : y₁.1 ⟶ y.1) (h₂ : y₂.1 ⟶ y.1),
      p.IsHomLift f₁ g₁ → p.IsHomLift f₂ g₂ →
      p.IsHomLift f₁ h₁ → p.IsHomLift f₂ h₂ →
      Nonempty (x₁ ≅ y₁) → Nonempty (x₂ ≅ y₂) →
      ∃ (b₁ : x₁ ≅ y₁) (b₂ : x₂ ≅ y₂) (b : x ≅ y),
        ((b₁.hom.1 ≫ h₁ = g₁ ≫ b.hom.1) ∧
          (b₂.hom.1 ≫ h₂ = g₂ ≫ b.hom.1))

/-- Every automorphism of the target of an arrow over `f` is induced by an automorphism of
its source. -/
def AutomorphismsLiftAlong
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    {A' A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A' ⟶ A) : Prop :=
  ∀ (x' : p.Fiber A') (x : p.Fiber A) (g : x'.1 ⟶ x.1),
    p.IsHomLift f g → ∀ a : x ≅ x,
      ∃ b : x' ≅ x', b.hom.1 ≫ g = g ≫ a.hom.1

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]

/-- Each strict fibre of a category cofibered in groupoids is a groupoid. -/
public theorem fiber_isGroupoid
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) : IsGroupoid (p.Fiber A) := by
  constructor
  intro x y f
  let : p.IsHomLift (𝟙 A) f.1 := f.2
  have hmap := IsHomLift.fac' p (𝟙 A) f.1
  have hliftop : p.op.IsHomLift (𝟙 (Opposite.op A)) f.1.op := by
    apply IsHomLift.of_fac p.op (𝟙 (Opposite.op A)) f.1.op
      (congrArg Opposite.op y.2) (congrArg Opposite.op x.2)
    simp [hmap]
  let := hp.isStronglyCartesian_homLift (𝟙 (Opposite.op A)) f.1.op
  have hisoop : IsIso f.1.op :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso p.op (𝟙 (Opposite.op A)) f.1.op
  have hiso : IsIso f.1 := (isIso_op_iff f.1).mp hisoop
  have hinv : p.IsHomLift (𝟙 A) (@CategoryTheory.inv _ _ _ _ f.1 hiso) := by
    simpa using IsHomLift.inv p (𝟙 A) f.1
  refine ⟨⟨⟨@CategoryTheory.inv _ _ _ _ f.1 hiso, hinv⟩, ?_, ?_⟩⟩
  · apply Functor.Fiber.hom_ext
    change f.1 ≫ @CategoryTheory.inv _ _ _ _ f.1 hiso = 𝟙 x.1
    simp
  · apply Functor.Fiber.hom_ext
    change @CategoryTheory.inv _ _ _ _ f.1 hiso ≫ f.1 = 𝟙 y.1
    simp

/-- A morphism over an identity in a category cofibered in groupoids is an isomorphism of
fibre objects. -/
private theorem exists_fiber_iso_of_isHomLift
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} {x y : p.Fiber A} (g : x.1 ⟶ y.1)
    (hg : p.IsHomLift (𝟙 A) g) : ∃ e : x ≅ y, e.hom.1 = g := by
  let : IsGroupoid (p.Fiber A) := fiber_isGroupoid p hp A
  exact ⟨asIso (⟨g, hg⟩ : x ⟶ y), rfl⟩

private theorem automorphismsLiftAlong_iso
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {A' A : ArtinianLocalAlgCat.{u, v, w} Λ k} (i : A' ≅ A) :
    AutomorphismsLiftAlong p i.hom := by
  intro x' x g hg a
  have hmapIso : IsIso (p.map g) := by
    have hfac := IsHomLift.fac' p i.hom g
    rw [hfac]
    infer_instance
  let : IsIso (p.op.map g.op) := by
    change IsIso ((p.map g).op)
    exact isIso_op (p.map g)
  let : p.op.IsStronglyCartesian (p.op.map g.op) g.op := hp.isStronglyCartesian g.op
  have hgiso : IsIso g := by
    have hop : IsIso g.op :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p.op)
        (f := p.op.map g.op) g.op
    exact isIso_of_op g
  let : IsIso g := hgiso
  have hginv : p.IsHomLift i.inv (inv g) := by
    let : p.IsHomLift i.hom g := hg
    simpa using IsHomLift.inv p i.hom g
  have hraw : p.IsHomLift (i.hom ≫ 𝟙 A ≫ i.inv) (g ≫ a.hom.1 ≫ inv g) := by
    let : p.IsHomLift i.hom g := hg
    let : p.IsHomLift (𝟙 A) a.hom.1 := a.hom.2
    let : p.IsHomLift i.inv (inv g) := hginv
    infer_instance
  have hb : p.IsHomLift (𝟙 A') (g ≫ a.hom.1 ≫ inv g) := by simpa using hraw
  obtain ⟨b, hb'⟩ := exists_fiber_iso_of_isHomLift p hp _ hb
  refine ⟨b, ?_⟩
  rw [hb']
  simp

private theorem automorphismsLiftAlong_comp
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {A₀ A₁ A₂ : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)
    (hf : AutomorphismsLiftAlong p f) (hg : AutomorphismsLiftAlong p g) :
    AutomorphismsLiftAlong p (f ≫ g) := by
  intro x₀ x₂ φ hφ a
  obtain ⟨y, q, r, hq, hr, hqr⟩ := exists_factor_of_isHomLift_comp hp f g φ hφ
  let x₁ : p.Fiber A₁ := ⟨y, IsHomLift.codomain_eq p f q⟩
  obtain ⟨b₁, hb₁⟩ := hg x₁ x₂ r hr a
  obtain ⟨b₀, hb₀⟩ := hf x₀ x₁ q hq b₁
  refine ⟨b₀, ?_⟩
  rw [← hqr, Category.assoc, reassoc_of% hb₀, hb₁]

private theorem automorphismsLiftAlong_composable
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {n : ℕ} (D : ComposableArrows (ArtinianLocalAlgCat.{u, v, w} Λ k) n)
    (hstep : ∀ (i : ℕ) (hi : i < n), AutomorphismsLiftAlong p (D.map' i (i + 1))) :
    AutomorphismsLiftAlong p D.hom := by
  induction n with
  | zero =>
      have hD : D.hom = 𝟙 D.left := by
        simp [ComposableArrows.hom, ComposableArrows.left, ComposableArrows.right]
      exact hD.symm ▸ automorphismsLiftAlong_iso p hp (Iso.refl D.left)
  | succ n ih =>
      let f := D.map' 0 1
      let E := D.δ₀
      have htail : ∀ (i : ℕ) (hi : i < n),
          AutomorphismsLiftAlong p (E.map' i (i + 1)) := by
        intro i hi
        change AutomorphismsLiftAlong p (D.map' (i + 1) (i + 2))
        exact hstep (i + 1) (by omega)
      have hE := ih E htail
      have hf := hstep 0 (by omega)
      have hcomp := automorphismsLiftAlong_comp p hp f E.hom hf hE
      have hD : D.hom = f ≫ E.hom := by
        change D.map' 0 (n + 1) = D.map' 0 1 ≫ D.map' 1 (n + 1)
        exact ComposableArrows.map'_comp D 0 1 (n + 1)
      exact hD.symm ▸ hcomp

private theorem cofibered_exists_lift
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) (x : p.Fiber A) :
    ∃ (y : p.Fiber B) (g : x.1 ⟶ y.1), p.IsHomLift f g := by
  obtain ⟨yraw, g, hg⟩ := exists_pushforward hp f x.1 x.2
  let := hg
  exact ⟨⟨yraw, IsHomLift.codomain_eq p f g⟩, g, hg⟩

private theorem associatedFiberEqOfIso
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} (x y : p.Fiber A) (h : Nonempty (x ≅ y)) :
    (fiberFunctor (isomorphismClassesData (BasedCategory.ofFunctor p) hp).projection A).obj x =
      (fiberFunctor
        (isomorphismClassesData (BasedCategory.ofFunctor p) hp).projection A).obj y :=
  (isomorphismClassesData (BasedCategory.ofFunctor p) hp).quotient.obj_eq_iff_isomorphic
    A x y |>.2 h

private theorem associatedFiberIsoOfValueEq
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} (x y : p.Fiber A)
    (h : elementsFiberValue
        (isomorphismClassesData (BasedCategory.ofFunctor p) hp).classes A
        ((fiberFunctor
          (isomorphismClassesData (BasedCategory.ofFunctor p) hp).projection A).obj x) =
      elementsFiberValue
        (isomorphismClassesData (BasedCategory.ofFunctor p) hp).classes A
        ((fiberFunctor
          (isomorphismClassesData (BasedCategory.ofFunctor p) hp).projection A).obj y)) :
    Nonempty (x ≅ y) := by
  let d := isomorphismClassesData (BasedCategory.ofFunctor p) hp
  let G := d.classes
  let x' := (fiberFunctor d.projection A).obj x
  let y' := (fiberFunctor d.projection A).obj y
  have hxy : Nonempty (x' ≅ y') :=
    elementsFiberIsoOfValueEq G A x' y' (by simpa [G, x', y'] using h)
  let hsk : Skeletal (Functor.Fiber (Functor.Elements.π G) A) := d.quotient.fiber_skeletal A
  have heq : x' = y' := hsk ⟨Classical.choice hxy⟩
  exact (d.quotient.obj_eq_iff_isomorphic A x y).1 (by simpa [x', y'] using heq)

private theorem associatedFiberValue_map
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (x : p.Fiber A) (y : p.Fiber B) (m : x.1 ⟶ y.1) (hm : p.IsHomLift f m) :
    (isomorphismClassesData (BasedCategory.ofFunctor p) hp).classes.map f
        (elementsFiberValue
          (isomorphismClassesData (BasedCategory.ofFunctor p) hp).classes A
          ((fiberFunctor
            (isomorphismClassesData (BasedCategory.ofFunctor p) hp).projection A).obj x)) =
      elementsFiberValue
        (isomorphismClassesData (BasedCategory.ofFunctor p) hp).classes B
        ((fiberFunctor
          (isomorphismClassesData (BasedCategory.ofFunctor p) hp).projection B).obj y) := by
  let d := isomorphismClassesData (BasedCategory.ofFunctor p) hp
  let φ := d.projection
  let G := d.classes
  let := hm
  have hm' : (Functor.Elements.π G).IsHomLift f (φ.toFunctor.map m) := by
    change (BasedCategory.ofFunctor p).p.IsHomLift f m at hm
    exact BasedFunctor.preserves_isHomLift φ f m
  exact elementsFiberValue_map G f
    ((fiberFunctor φ A).obj x) ((fiberFunctor φ B).obj y) (φ.toFunctor.map m) hm'

private theorem cofibered_iso_compare_lifts
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (z z' : p.Fiber A) (x y : p.Fiber B) (e : z ≅ z')
    (q : z.1 ⟶ x.1) (hq : p.IsHomLift f q)
    (r : z'.1 ⟶ y.1) (hr : p.IsHomLift f r) :
    ∃ b : x ≅ y, q ≫ b.hom.1 = e.hom.1 ≫ r := by
  let : p.IsHomLift (𝟙 A) e.hom.1 := e.hom.2
  let : p.IsHomLift f r := hr
  have hm : p.IsHomLift f (e.hom.1 ≫ r) := by infer_instance
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp f q hq
  obtain ⟨b, ⟨hb, hfac⟩, _⟩ :=
    Functor.IsStronglyCocartesian.universal_property p f q (𝟙 B) f (by simp) (e.hom.1 ≫ r)
  obtain ⟨e', he'⟩ := exists_fiber_iso_of_isHomLift p hp b hb
  exact ⟨e', by rw [he']; exact hfac⟩

private theorem cofibered_cancel_cocartesian
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {P A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (i : P ⟶ A) (f : A ⟶ B)
    {z x y : F} (q : z ⟶ x) (hq : p.IsHomLift i q)
    (a b : x ⟶ y) (ha : p.IsHomLift f a) (hb : p.IsHomLift f b)
    (heq : q ≫ a = q ≫ b) : a = b := by
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp i q hq
  let : p.IsHomLift (i ≫ f) (q ≫ a) := by
    let := ha
    infer_instance
  obtain ⟨t, ⟨ht, hfac⟩, huniq⟩ :=
    Functor.IsStronglyCocartesian.universal_property p i q f (i ≫ f) rfl (q ≫ a)
  exact (huniq a ⟨ha, rfl⟩).trans (huniq b ⟨hb, heq.symm⟩).symm

/-- Gluing squares commute once the apex square does, by cancelling a cocartesian arrow. -/
private theorem gluing_square_comm
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {P A' A : ArtinianLocalAlgCat.{u, v, w} Λ k} (p' : P ⟶ A') (f : A' ⟶ A)
    {z z' : p.Fiber P} {x' y' : p.Fiber A'} {x y : p.Fiber A} (e : z ≅ z')
    (q : z.1 ⟶ x'.1) (r : z'.1 ⟶ y'.1) (g : x'.1 ⟶ x.1) (h : y'.1 ⟶ y.1)
    (hq : p.IsHomLift p' q) (hg : p.IsHomLift f g) (hh : p.IsHomLift f h)
    (b' : x' ≅ y') (b : x ≅ y) (hb' : q ≫ b'.hom.1 = e.hom.1 ≫ r)
    (hb : q ≫ g ≫ b.hom.1 = e.hom.1 ≫ r ≫ h) : b'.hom.1 ≫ h = g ≫ b.hom.1 := by
  let : p.IsHomLift (𝟙 A') b'.hom.1 := b'.hom.2
  let : p.IsHomLift (𝟙 A) b.hom.1 := b.hom.2
  refine cofibered_cancel_cocartesian p hp p' f q hq _ _ (by infer_instance) (by infer_instance) ?_
  rw [← Category.assoc, hb', Category.assoc, hb]

private theorem cofibered_gluing_iso_of_apex_iso
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (x₁ y₁ : p.Fiber A₁) (x₂ y₂ : p.Fiber A₂) (x y : p.Fiber A)
    (g₁ : x₁.1 ⟶ x.1) (g₂ : x₂.1 ⟶ x.1) (h₁ : y₁.1 ⟶ y.1) (h₂ : y₂.1 ⟶ y.1)
    (hg₁ : p.IsHomLift f₁ g₁) (hg₂ : p.IsHomLift f₂ g₂)
    (hh₁ : p.IsHomLift f₁ h₁) (hh₂ : p.IsHomLift f₂ h₂)
    {z z' : p.Fiber P}
    (q₁ : z.1 ⟶ x₁.1) (q₂ : z.1 ⟶ x₂.1) (r₁ : z'.1 ⟶ y₁.1) (r₂ : z'.1 ⟶ y₂.1)
    (hq₁ : p.IsHomLift p₁ q₁) (hq₂ : p.IsHomLift p₂ q₂)
    (hr₁ : p.IsHomLift p₁ r₁) (hr₂ : p.IsHomLift p₂ r₂)
    (hq : q₁ ≫ g₁ = q₂ ≫ g₂) (hr : r₁ ≫ h₁ = r₂ ≫ h₂)
    (_hbase : p₁ ≫ f₁ = p₂ ≫ f₂) (e : z ≅ z') :
    ∃ (b₁ : x₁ ≅ y₁) (b₂ : x₂ ≅ y₂) (b : x ≅ y),
      (b₁.hom.1 ≫ h₁ = g₁ ≫ b.hom.1) ∧ (b₂.hom.1 ≫ h₂ = g₂ ≫ b.hom.1) := by
  obtain ⟨b₁, hb₁⟩ := cofibered_iso_compare_lifts p hp p₁ z z' x₁ y₁ e q₁ hq₁ r₁ hr₁
  obtain ⟨b₂, hb₂⟩ := cofibered_iso_compare_lifts p hp p₂ z z' x₂ y₂ e q₂ hq₂ r₂ hr₂
  have htLift : p.IsHomLift (p₁ ≫ f₁) (q₁ ≫ g₁) := by
    let := hq₁
    let := hg₁
    infer_instance
  have huLift : p.IsHomLift (p₁ ≫ f₁) (r₁ ≫ h₁) := by
    let := hr₁
    let := hh₁
    infer_instance
  obtain ⟨b, hb⟩ :=
    cofibered_iso_compare_lifts p hp (p₁ ≫ f₁) z z' x y e _ htLift _ huLift
  refine ⟨b₁, b₂, b, ?_, ?_⟩
  · exact gluing_square_comm p hp p₁ f₁ e q₁ r₁ g₁ h₁ hq₁ hg₁ hh₁ b₁ b hb₁
      (by simpa only [Category.assoc] using hb)
  · refine gluing_square_comm p hp p₂ f₂ e q₂ r₂ g₂ h₂ hq₂ hg₂ hh₂ b₂ b hb₂ ?_
    rw [hq, hr] at hb
    simpa only [Category.assoc] using hb

private theorem completion_over_pullback
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hS : SchlessingerConditionS1 p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hP : IsPullback p₁ p₂ f₁ f₂) (hf : Function.Surjective f₂.hom)
    (x₁ : p.Fiber A₁) (x₂ : p.Fiber A₂) (x : p.Fiber A)
    (g₁ : x₁.1 ⟶ x.1) (g₂ : x₂.1 ⟶ x.1)
    (hg₁ : p.IsHomLift f₁ g₁) (hg₂ : p.IsHomLift f₂ g₂) :
    ∃ (z : p.Fiber P) (q₁ : z.1 ⟶ x₁.1) (q₂ : z.1 ⟶ x₂.1),
      p.IsHomLift p₁ q₁ ∧ p.IsHomLift p₂ q₂ ∧ q₁ ≫ g₁ = q₂ ≫ g₂ := by
  rcases x₁ with ⟨x₁, rfl⟩
  rcases x₂ with ⟨x₂, rfl⟩
  rcases x with ⟨x, rfl⟩
  have he₁ := IsHomLift.eq_of_isHomLift p f₁ g₁
  have he₂ := IsHomLift.eq_of_isHomLift p f₂ g₂
  subst f₁ f₂
  obtain ⟨c⟩ := hS.completion g₁ g₂ hf p₁ p₂ hP.flip
  refine ⟨⟨c.apex, c.apex_eq⟩, c.toFirst, c.toSecond, ?_, ?_, c.comm.symm⟩
  · apply IsHomLift.of_fac p p₁ c.toFirst c.apex_eq rfl
    simp [c.map_toFirst]
  · apply IsHomLift.of_fac p p₂ c.toSecond c.apex_eq rfl
    simp [c.map_toSecond]

private theorem fiber_cone_isLimit
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : SatisfiesRS p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hP : IsPullback p₁ p₂ f₁ f₂) (hf : Function.Surjective f₂.hom)
    (z : p.Fiber P) (x₁ : p.Fiber A₁) (x₂ : p.Fiber A₂) (x : p.Fiber A)
    (q₁ : z.1 ⟶ x₁.1) (q₂ : z.1 ⟶ x₂.1) (g₁ : x₁.1 ⟶ x.1) (g₂ : x₂.1 ⟶ x.1)
    (hq₁ : p.IsHomLift p₁ q₁) (hq₂ : p.IsHomLift p₂ q₂)
    (hg₁ : p.IsHomLift f₁ g₁) (hg₂ : p.IsHomLift f₂ g₂)
    (h : q₁ ≫ g₁ = q₂ ≫ g₂) : Nonempty (IsLimit (PullbackCone.mk q₁ q₂ h)) := by
  rcases z with ⟨z, rfl⟩
  rcases x₁ with ⟨x₁, rfl⟩
  rcases x₂ with ⟨x₂, rfl⟩
  rcases x with ⟨x, rfl⟩
  have he₁ := IsHomLift.eq_of_isHomLift p p₁ q₁
  have he₂ := IsHomLift.eq_of_isHomLift p p₂ q₂
  have he₃ := IsHomLift.eq_of_isHomLift p f₁ g₁
  have he₄ := IsHomLift.eq_of_isHomLift p f₂ g₂
  subst p₁ p₂ f₁ f₂
  refine isLimit_of_map_isLimit hp g₁ g₂ _ ?_ ⟨hP.isLimit⟩
  simpa using hf

/-- If `m ≫ r = q ≫ b` with `b` over an identity, then `m` lies over an identity in the
base direction of `q` and `r`. -/
private theorem map_comp_base_eq
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    {P A' : ArtinianLocalAlgCat.{u, v, w} Λ k} (p' : P ⟶ A')
    {z z' : p.Fiber P} {x' y' : p.Fiber A'} (q : z.1 ⟶ x'.1) (r : z'.1 ⟶ y'.1)
    (b : x'.1 ⟶ y'.1) (hb : p.IsHomLift (𝟙 A') b) (m : z.1 ⟶ z'.1)
    (hq : p.IsHomLift p' q) (hr : p.IsHomLift p' r) (hm : m ≫ r = q ≫ b) :
    𝟙 P ≫ p' = (eqToHom z.2.symm ≫ p.map m ≫ eqToHom z'.2) ≫ p' := by
  have ht := congrArg (fun t => eqToHom z.2.symm ≫ t ≫ eqToHom y'.2)
    (by rw [← p.map_comp, ← p.map_comp, hm] : p.map m ≫ p.map r = p.map q ≫ p.map b)
  simp only [IsHomLift.fac' p p' r, IsHomLift.fac' p p' q, IsHomLift.fac' p (𝟙 A') b] at ht
  simpa [Category.assoc] using ht.symm

private theorem apex_iso_of_gluing_iso
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : SatisfiesRS p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hP : IsPullback p₁ p₂ f₁ f₂) (hf : Function.Surjective f₂.hom)
    (z z' : p.Fiber P)
    (x₁ y₁ : p.Fiber A₁) (x₂ y₂ : p.Fiber A₂) (x y : p.Fiber A)
    (q₁ : z.1 ⟶ x₁.1) (q₂ : z.1 ⟶ x₂.1) (r₁ : z'.1 ⟶ y₁.1) (r₂ : z'.1 ⟶ y₂.1)
    (g₁ : x₁.1 ⟶ x.1) (g₂ : x₂.1 ⟶ x.1) (h₁ : y₁.1 ⟶ y.1) (h₂ : y₂.1 ⟶ y.1)
    (hq₁ : p.IsHomLift p₁ q₁) (hq₂ : p.IsHomLift p₂ q₂)
    (hr₁ : p.IsHomLift p₁ r₁) (hr₂ : p.IsHomLift p₂ r₂)
    (hh₁ : p.IsHomLift f₁ h₁) (hh₂ : p.IsHomLift f₂ h₂)
    (hq : q₁ ≫ g₁ = q₂ ≫ g₂) (hr : r₁ ≫ h₁ = r₂ ≫ h₂)
    (b₁ : x₁ ≅ y₁) (b₂ : x₂ ≅ y₂) (b : x ≅ y)
    (hb₁ : b₁.hom.1 ≫ h₁ = g₁ ≫ b.hom.1)
    (hb₂ : b₂.hom.1 ≫ h₂ = g₂ ≫ b.hom.1) : Nonempty (z ≅ z') := by
  obtain ⟨hc⟩ := fiber_cone_isLimit p hp p₁ p₂ f₁ f₂ hP hf
    z' y₁ y₂ y r₁ r₂ h₁ h₂ hr₁ hr₂ hh₁ hh₂ hr
  have hs : (q₁ ≫ b₁.hom.1) ≫ h₁ = (q₂ ≫ b₂.hom.1) ≫ h₂ := by
    simp only [Category.assoc, hb₁, hb₂]
    rw [← Category.assoc, ← Category.assoc, hq]
  let m : z.1 ⟶ z'.1 := PullbackCone.IsLimit.lift hc (q₁ ≫ b₁.hom.1) (q₂ ≫ b₂.hom.1) hs
  have hbase₁ : m ≫ r₁ = q₁ ≫ b₁.hom.1 :=
    PullbackCone.IsLimit.lift_fst hc (q₁ ≫ b₁.hom.1) (q₂ ≫ b₂.hom.1) hs
  have hbase₂ : m ≫ r₂ = q₂ ≫ b₂.hom.1 :=
    PullbackCone.IsLimit.lift_snd hc (q₁ ≫ b₁.hom.1) (q₂ ≫ b₂.hom.1) hs
  have hm : p.IsHomLift (𝟙 P) m := by
    apply IsHomLift.of_fac p (𝟙 P) m z.2 z'.2
    apply hP.hom_ext
    · exact map_comp_base_eq p p₁ q₁ r₁ b₁.hom.1 b₁.hom.2 m hq₁ hr₁ hbase₁
    · exact map_comp_base_eq p p₂ q₂ r₂ b₂.hom.1 b₂.hom.2 m hq₂ hr₂ hbase₂
  obtain ⟨e, -⟩ := exists_fiber_iso_of_isHomLift p hp.1 m hm
  exact ⟨e⟩

private theorem cofibered_square_from_apex
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hP : p₁ ≫ f₁ = p₂ ≫ f₂) (z : p.Fiber P) :
    ∃ (x₁ : p.Fiber A₁) (x₂ : p.Fiber A₂) (x : p.Fiber A)
      (q₁ : z.1 ⟶ x₁.1) (q₂ : z.1 ⟶ x₂.1) (g₁ : x₁.1 ⟶ x.1) (g₂ : x₂.1 ⟶ x.1),
      p.IsHomLift p₁ q₁ ∧ p.IsHomLift p₂ q₂ ∧
      p.IsHomLift f₁ g₁ ∧ p.IsHomLift f₂ g₂ ∧ q₁ ≫ g₁ = q₂ ≫ g₂ := by
  obtain ⟨x₁, q₁, hq₁⟩ := cofibered_exists_lift p hp p₁ z
  obtain ⟨x, g₁, hg₁⟩ := cofibered_exists_lift p hp f₁ x₁
  have hm : p.IsHomLift (p₂ ≫ f₂) (q₁ ≫ g₁) := by
    rw [← hP]
    let := hq₁
    let := hg₁
    infer_instance
  obtain ⟨x₂, q₂, g₂, hq₂, hg₂, he⟩ := exists_factor_of_isHomLift_comp hp p₂ f₂ (q₁ ≫ g₁) hm
  exact ⟨x₁, ⟨x₂, IsHomLift.codomain_eq p p₂ q₂⟩, x, q₁, q₂, g₁, g₂,
    hq₁, hq₂, hg₁, hg₂, he.symm⟩

private theorem associatedFiberValue_surjective
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p)
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    Function.Surjective (fun x : p.Fiber A => elementsFiberValue
      (isomorphismClassesData (BasedCategory.ofFunctor p) hp).classes A
      ((fiberFunctor
        (isomorphismClassesData (BasedCategory.ofFunctor p) hp).projection A).obj x)) := by
  intro a
  let d := isomorphismClassesData (BasedCategory.ofFunctor p) hp
  let T := fiberFunctor d.projection A
  let z : Functor.Fiber (Functor.Elements.π d.classes) A := ⟨d.classes.elementsMk A a, rfl⟩
  let : T.EssSurj := d.quotient.fiber_essSurj A
  have he : T.obj (T.objPreimage z) = z :=
    d.quotient.fiber_skeletal A ⟨T.objObjPreimageIso z⟩
  refine ⟨T.objPreimage z, ?_⟩
  change elementsFiberValue d.classes A (T.obj (T.objPreimage z)) = a
  rw [he]
  have hid : ∀ {B : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : B = B) (y : d.classes.obj B),
      d.classes.map (eqToHom h) y = y := fun _ _ => by simp
  exact hid _ a

private theorem elements_pullback_isLimit {𝒞 : Type u} [Category.{v} 𝒞] (G : 𝒞 ⥤ Type u₁)
    {X₁ X₂ X : 𝒞} {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (x₁ : G.obj X₁) (x₂ : G.obj X₂) (x : G.obj X)
    (hx₁ : G.map f₁ x₁ = x) (hx₂ : G.map f₂ x₂ = x)
    (z : G.obj c.pt) (hz₁ : G.map c.fst z = x₁) (hz₂ : G.map c.snd z = x₂)
    (hinj : Function.Injective (fun z : G.obj c.pt => (G.map c.fst z, G.map c.snd z))) :
    let e₁ : G.Elements := G.elementsMk X₁ x₁
    let e₂ : G.Elements := G.elementsMk X₂ x₂
    let e : G.Elements := G.elementsMk X x
    let a₁ : e₁ ⟶ e := Functor.Elements.homMk (x := e₁) (y := e) f₁ hx₁
    let a₂ : e₂ ⟶ e := Functor.Elements.homMk (x := e₂) (y := e) f₂ hx₂
    Nonempty (IsLimit (PullbackCone.mk (f := a₁) (g := a₂)
      (Functor.Elements.homMk (x := G.elementsMk c.pt z) (y := e₁) c.fst hz₁)
      (Functor.Elements.homMk (x := G.elementsMk c.pt z) (y := e₂) c.snd hz₂) (by
        apply Functor.Elements.hom_ext
        change c.fst ≫ f₁ = c.snd ≫ f₂
        exact c.condition))) := by
  let e₁ : G.Elements := G.elementsMk X₁ x₁
  let e₂ : G.Elements := G.elementsMk X₂ x₂
  let e : G.Elements := G.elementsMk X x
  let a₁ : e₁ ⟶ e := Functor.Elements.homMk (x := e₁) (y := e) f₁ hx₁
  let a₂ : e₂ ⟶ e := Functor.Elements.homMk (x := e₂) (y := e) f₂ hx₂
  let ez : G.Elements := G.elementsMk c.pt z
  let q₁ : ez ⟶ e₁ := Functor.Elements.homMk (x := ez) (y := e₁) c.fst hz₁
  let q₂ : ez ⟶ e₂ := Functor.Elements.homMk (x := ez) (y := e₂) c.snd hz₂
  let ce : PullbackCone a₁ a₂ := PullbackCone.mk (f := a₁) (g := a₂) q₁ q₂ (by
    apply Functor.Elements.hom_ext
    change c.fst ≫ f₁ = c.snd ≫ f₂
    exact c.condition)
  let sC (s : PullbackCone a₁ a₂) : PullbackCone f₁ f₂ :=
    PullbackCone.mk s.fst.hom s.snd.hom (by
      simpa [Functor.Elements.comp_hom, a₁, a₂] using congrArg Functor.Elements.Hom.hom s.condition)
  have key (s : PullbackCone a₁ a₂) : G.map (hc.lift (sC s)) s.pt.val = z := by
    refine hinj (Prod.ext ?_ ?_)
    · dsimp only
      rw [hz₁]
      erw [← Functor.map_comp_apply, hc.fac _ WalkingCospan.left]
      exact s.fst.map_val
    · dsimp only
      rw [hz₂]
      erw [← Functor.map_comp_apply, hc.fac _ WalkingCospan.right]
      exact s.snd.map_val
  refine ⟨PullbackCone.isLimitAux ce
    (fun s => Functor.Elements.homMk (x := s.pt) (y := ez) (hc.lift (sC s)) (key s))
    (fun s => ?_) (fun s => ?_) (fun s mArb hw => ?_)⟩
  · apply Functor.Elements.hom_ext
    exact hc.fac (sC s) WalkingCospan.left
  · apply Functor.Elements.hom_ext
    exact hc.fac (sC s) WalkingCospan.right
  · apply Functor.Elements.hom_ext
    refine PullbackCone.IsLimit.hom_ext hc ?_ ?_
    · have h := hw WalkingCospan.left
      change mArb ≫ ce.fst = s.fst at h
      have hv : mArb.hom ≫ c.fst = s.fst.hom := congrArg Functor.Elements.Hom.hom h
      exact hv.trans (hc.fac (sC s) WalkingCospan.left).symm
    · have h := hw WalkingCospan.right
      change mArb ≫ ce.snd = s.snd at h
      have hv : mArb.hom ≫ c.snd = s.snd.hom := congrArg Functor.Elements.Hom.hom h
      exact hv.trans (hc.fac (sC s) WalkingCospan.right).symm

private theorem elements_pullback_value_unique_of_rs
    (G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type u₁)
    (hRS : SatisfiesRS (Functor.Elements.π G))
    {X₁ X₂ X : ArtinianLocalAlgCat.{u, v, w} Λ k} {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
    (hf₂ : Function.Surjective f₂.hom)
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (x₁ : G.obj X₁) (x₂ : G.obj X₂) (x : G.obj X)
    (hx₁ : G.map f₁ x₁ = x) (hx₂ : G.map f₂ x₂ = x)
    (z z' : G.obj c.pt)
    (hz₁ : G.map c.fst z = x₁) (hz₂ : G.map c.snd z = x₂)
    (hz₁' : G.map c.fst z' = x₁) (hz₂' : G.map c.snd z' = x₂) :
    z = z' := by
  let e₁ : G.Elements := G.elementsMk X₁ x₁
  let e₂ : G.Elements := G.elementsMk X₂ x₂
  let e : G.Elements := G.elementsMk X x
  let a₁ : e₁ ⟶ e := Functor.Elements.homMk (x := e₁) (y := e) f₁ hx₁
  let a₂ : e₂ ⟶ e := Functor.Elements.homMk (x := e₂) (y := e) f₂ hx₂
  obtain ⟨d, ⟨hd⟩, ⟨hdBase⟩⟩ := hRS.2 a₁ a₂ hf₂
  let u := PullbackCone.IsLimit.lift hdBase c.fst c.snd c.condition
  let v := PullbackCone.IsLimit.lift hc (d.map (Functor.Elements.π G)).fst
    (d.map (Functor.Elements.π G)).snd (d.map (Functor.Elements.π G)).condition
  have hu₁ : u ≫ (d.map (Functor.Elements.π G)).fst = c.fst :=
    PullbackCone.IsLimit.lift_fst hdBase c.fst c.snd c.condition
  have hu₂ : u ≫ (d.map (Functor.Elements.π G)).snd = c.snd :=
    PullbackCone.IsLimit.lift_snd hdBase c.fst c.snd c.condition
  have hv₁ : v ≫ c.fst = (d.map (Functor.Elements.π G)).fst :=
    PullbackCone.IsLimit.lift_fst hc _ _ (d.map (Functor.Elements.π G)).condition
  have hv₂ : v ≫ c.snd = (d.map (Functor.Elements.π G)).snd :=
    PullbackCone.IsLimit.lift_snd hc _ _ (d.map (Functor.Elements.π G)).condition
  have huv : u ≫ v = 𝟙 c.pt := by
    apply PullbackCone.IsLimit.hom_ext hc
    · rw [Category.assoc, hv₁]
      exact hu₁.trans (Category.id_comp _).symm
    · rw [Category.assoc, hv₂]
      exact hu₂.trans (Category.id_comp _).symm
  have hval : ∀ w : G.obj c.pt, G.map c.fst w = x₁ → G.map c.snd w = x₂ →
      G.map u w = d.pt.val := by
    intro w hw₁ hw₂
    let ew : G.Elements := G.elementsMk c.pt w
    let q₁ : ew ⟶ e₁ := Functor.Elements.homMk (x := ew) (y := e₁) c.fst hw₁
    let q₂ : ew ⟶ e₂ := Functor.Elements.homMk (x := ew) (y := e₂) c.snd hw₂
    let s : PullbackCone a₁ a₂ := PullbackCone.mk q₁ q₂ (by
      apply Functor.Elements.hom_ext
      exact c.condition)
    have hm₁ : (hd.lift s).hom ≫ (d.map (Functor.Elements.π G)).fst = c.fst := by
      have h := hd.fac s WalkingCospan.left
      change hd.lift s ≫ d.fst = q₁ at h
      have hv := congrArg (fun q => q.hom) h
      change (hd.lift s).hom ≫ d.fst.hom = c.fst at hv
      simpa [Functor.Elements.π] using hv
    have hm₂ : (hd.lift s).hom ≫ (d.map (Functor.Elements.π G)).snd = c.snd := by
      have h := hd.fac s WalkingCospan.right
      change hd.lift s ≫ d.snd = q₂ at h
      have hv := congrArg (fun q => q.hom) h
      change (hd.lift s).hom ≫ d.snd.hom = c.snd at hv
      simpa [Functor.Elements.π] using hv
    have hm : (hd.lift s).hom = u := PullbackCone.IsLimit.hom_ext hdBase
      (hm₁.trans hu₁.symm) (hm₂.trans hu₂.symm)
    have hpp := (hd.lift s).map_val
    change G.map (hd.lift s).hom w = d.pt.val at hpp
    rwa [hm] at hpp
  have hinj : Function.Injective (G.map u) := by
    intro a b hab
    have hab' := congrArg (G.map v) hab
    simpa only [← Functor.map_comp_apply, huv, Functor.map_id_apply] using hab'
  exact hinj ((hval z hz₁ hz₂).trans (hval z' hz₁' hz₂').symm)

private theorem associated_pullback_injective
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : SatisfiesRS p) (hinj : IsInjectiveOnGluingClasses p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hP : IsPullback p₁ p₂ f₁ f₂) (hf : Function.Surjective f₂.hom) :
    let G := (isomorphismClassesData (BasedCategory.ofFunctor p) hp.1).classes
    Function.Injective (fun z : G.obj P => (G.map p₁ z, G.map p₂ z)) := by
  let d := isomorphismClassesData (BasedCategory.ofFunctor p) hp.1
  let G := d.classes
  let V (A) (x : p.Fiber A) := elementsFiberValue G A ((fiberFunctor d.projection A).obj x)
  change Function.Injective (fun z : G.obj P => (G.map p₁ z, G.map p₂ z))
  intro a a' ha
  obtain ⟨z, rfl⟩ := associatedFiberValue_surjective p hp.1 P a
  obtain ⟨z', rfl⟩ := associatedFiberValue_surjective p hp.1 P a'
  obtain ⟨x₁, x₂, x, q₁, q₂, g₁, g₂, hq₁, hq₂, hg₁, hg₂, hq⟩ :=
    cofibered_square_from_apex p hp.1 p₁ p₂ f₁ f₂ hP.w z
  obtain ⟨y₁, y₂, y, r₁, r₂, h₁, h₂, hr₁, hr₂, hh₁, hh₂, hr⟩ :=
    cofibered_square_from_apex p hp.1 p₁ p₂ f₁ f₂ hP.w z'
  have he₁ : V A₁ x₁ = V A₁ y₁ :=
    (associatedFiberValue_map p hp.1 p₁ z x₁ q₁ hq₁).symm.trans
      ((congrArg Prod.fst ha).trans (associatedFiberValue_map p hp.1 p₁ z' y₁ r₁ hr₁))
  have he₂ : V A₂ x₂ = V A₂ y₂ :=
    (associatedFiberValue_map p hp.1 p₂ z x₂ q₂ hq₂).symm.trans
      ((congrArg Prod.snd ha).trans (associatedFiberValue_map p hp.1 p₂ z' y₂ r₂ hr₂))
  obtain ⟨b₁, b₂, b, hb₁, hb₂⟩ := hinj f₁ f₂ hf x₁ y₁ x₂ y₂ x y
    g₁ g₂ h₁ h₂ hg₁ hg₂ hh₁ hh₂
    (associatedFiberIsoOfValueEq p hp.1 x₁ y₁ he₁)
    (associatedFiberIsoOfValueEq p hp.1 x₂ y₂ he₂)
  have hz := apex_iso_of_gluing_iso p hp p₁ p₂ f₁ f₂ hP hf z z'
    x₁ y₁ x₂ y₂ x y q₁ q₂ r₁ r₂ g₁ g₂ h₁ h₂ hq₁ hq₂ hr₁ hr₂ hh₁ hh₂
    hq hr b₁ b₂ b hb₁ hb₂
  exact congrArg (elementsFiberValue G P) (associatedFiberEqOfIso p hp.1 z z' hz)

private theorem gluingClassesInjective_of_associatedSatisfiesRS
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : SatisfiesRS p)
    (hRS : SatisfiesRS (Functor.Elements.π
      (isomorphismClassesData (BasedCategory.ofFunctor p) hp.1).classes)) :
    IsInjectiveOnGluingClasses p := by
  intro A₁ A₂ A f₁ f₂ hf x₁ y₁ x₂ y₂ x y g₁ g₂ h₁ h₂ hg₁ hg₂ hh₁ hh₂ he₁ he₂
  let d := isomorphismClassesData (BasedCategory.ofFunctor p) hp.1
  let G := d.classes
  let V (A) (x : p.Fiber A) := elementsFiberValue G A ((fiberFunctor d.projection A).obj x)
  let H := (ArtinianLocalAlgCat.hasPullback_of_surjective f₁ f₂ (Or.inr hf)).1
  have hP := H.isPullback
  have hS := schlessingerConditionS1_of_satisfiesRS hp
  obtain ⟨z, q₁, q₂, hq₁, hq₂, hq⟩ :=
    completion_over_pullback p hS H.fst H.snd f₁ f₂ hP hf x₁ x₂ x g₁ g₂ hg₁ hg₂
  obtain ⟨z', r₁, r₂, hr₁, hr₂, hr⟩ :=
    completion_over_pullback p hS H.fst H.snd f₁ f₂ hP hf y₁ y₂ y h₁ h₂ hh₁ hh₂
  have hv₁ : V A₁ x₁ = V A₁ y₁ :=
    congrArg (elementsFiberValue G A₁) (associatedFiberEqOfIso p hp.1 x₁ y₁ he₁)
  have hv₂ : V A₂ x₂ = V A₂ y₂ :=
    congrArg (elementsFiberValue G A₂) (associatedFiberEqOfIso p hp.1 x₂ y₂ he₂)
  have hz : V H.obj z = V H.obj z' :=
    elements_pullback_value_unique_of_rs G hRS hf hP.cone hP.isLimit
      (V A₁ x₁) (V A₂ x₂) (V A x)
      (associatedFiberValue_map p hp.1 f₁ x₁ x g₁ hg₁)
      (associatedFiberValue_map p hp.1 f₂ x₂ x g₂ hg₂)
      (V H.obj z) (V H.obj z')
      (associatedFiberValue_map p hp.1 H.fst z x₁ q₁ hq₁)
      (associatedFiberValue_map p hp.1 H.snd z x₂ q₂ hq₂)
      ((associatedFiberValue_map p hp.1 H.fst z' y₁ r₁ hr₁).trans hv₁.symm)
      ((associatedFiberValue_map p hp.1 H.snd z' y₂ r₂ hr₂).trans hv₂.symm)
  obtain ⟨e⟩ := associatedFiberIsoOfValueEq p hp.1 z z' hz
  exact cofibered_gluing_iso_of_apex_iso p hp.1 H.fst H.snd f₁ f₂
    x₁ y₁ x₂ y₂ x y g₁ g₂ h₁ h₂ hg₁ hg₂ hh₁ hh₂
    q₁ q₂ r₁ r₂ hq₁ hq₂ hr₁ hr₂ hq hr hP.w e

private theorem associatedSatisfiesRS_of_gluingClassesInjective
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : SatisfiesRS p)
    (hinj : IsInjectiveOnGluingClasses p) :
    SatisfiesRS (Functor.Elements.π
      (isomorphismClassesData (BasedCategory.ofFunctor p) hp.1).classes) := by
  let d := isomorphismClassesData (BasedCategory.ofFunctor p) hp.1
  let G := d.classes
  let π := Functor.Elements.π G
  have hS : SchlessingerConditionS1 π :=
    schlessingerConditionS1_of_isIsomorphismClasses d.projection d.quotient
      (schlessingerConditionS1_of_satisfiesRS hp)
  refine ⟨isCofiberedInGroupoids_elementsProjection G, ?_⟩
  intro x₁ x₂ x g₁ g₂ hf
  let H := (ArtinianLocalAlgCat.hasPullback_of_surjective g₁.hom g₂.hom (Or.inr hf)).1
  have hP := H.isPullback
  obtain ⟨z, q₁, q₂, hq₁, hq₂, hq⟩ := completion_over_pullback π hS
    H.fst H.snd g₁.hom g₂.hom hP hf ⟨x₁, rfl⟩ ⟨x₂, rfl⟩ ⟨x, rfl⟩ g₁ g₂
    (IsHomLift.map π g₁) (IsHomLift.map π g₂)
  let a := elementsFiberValue G H.obj z
  have hid : ∀ {B : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : B = B) (y : G.obj B),
      G.map (eqToHom h) y = y := fun _ _ => by simp
  have ha₁ : G.map H.fst a = x₁.val :=
    (elementsFiberValue_map G H.fst z ⟨x₁, rfl⟩ q₁ hq₁).trans (hid _ _)
  have ha₂ : G.map H.snd a = x₂.val :=
    (elementsFiberValue_map G H.snd z ⟨x₂, rfl⟩ q₂ hq₂).trans (hid _ _)
  let c : PullbackCone g₁ g₂ := PullbackCone.mk
    (Functor.Elements.homMk (x := G.elementsMk H.obj a) (y := x₁) H.fst ha₁)
    (Functor.Elements.homMk (x := G.elementsMk H.obj a) (y := x₂) H.snd ha₂) (by
      apply Functor.Elements.hom_ext
      exact hP.w)
  refine ⟨c, ?_, ⟨hP.isLimit⟩⟩
  exact elements_pullback_isLimit G hP.cone hP.isLimit
    x₁.val x₂.val x.val g₁.map_val g₂.map_val a ha₁ ha₂
    (associated_pullback_injective p hp hinj H.fst H.snd g₁.hom g₂.hom hP hf)

/-- For a category cofibered in groupoids satisfying (RS), the associated functor of isomorphism
classes satisfies (RS) exactly when the comparison on isomorphism classes of gluing data is
injective. -/
@[stacks 06J8 "conditions (1) and (2)", sga "7 VI 2.7" "(i) <=> injectivity"]
theorem associatedSatisfiesRS_iff_gluingClassesInjective
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : SatisfiesRS p) :
    SatisfiesRS (Functor.Elements.π
        (isomorphismClassesData (BasedCategory.ofFunctor p) hp.1).classes) ↔
      IsInjectiveOnGluingClasses p :=
  ⟨gluingClassesInjective_of_associatedSatisfiesRS p hp,
    associatedSatisfiesRS_of_gluingClassesInjective p hp⟩

/-- For a category cofibered in groupoids, injectivity on isomorphism classes of gluing data is
equivalent to lifting automorphisms along every surjection of Artinian local algebras. -/
@[stacks 06J8 "conditions (2) and (3)", sga "7 VI 2.7" "inj <=> aut surjective"]
theorem gluingClassesInjective_iff_automorphismsLift
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    IsInjectiveOnGluingClasses p ↔
      (∀ {A' A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A' ⟶ A),
        Function.Surjective f.hom → AutomorphismsLiftAlong p f) := by
  constructor
  · intro hinj A' A f hf x' x g hg a
    let : p.IsHomLift (𝟙 A) a.hom.1 := a.hom.2
    let : p.IsHomLift f g := hg
    have hga : p.IsHomLift f (g ≫ a.hom.1) := by infer_instance
    obtain ⟨b₁, b₂, b, h₁, h₂⟩ := hinj f f hf
      x' x' x' x' x x g g g (g ≫ a.hom.1) hg hg hg hga ⟨Iso.refl x'⟩ ⟨Iso.refl x'⟩
    refine ⟨b₂.symm ≪≫ b₁, ?_⟩
    have hb₂ : b₂.inv.1 ≫ b₂.hom.1 = 𝟙 x'.1 := congrArg Subtype.val b₂.inv_hom_id
    have h := congrArg (b₂.inv.1 ≫ ·) h₂
    rw [← Category.assoc, hb₂, Category.id_comp] at h
    change (b₂.inv.1 ≫ b₁.hom.1) ≫ g = g ≫ a.hom.1
    rw [Category.assoc, h₁, h]
  · intro hlift A₁ A₂ A f₁ f₂ hf₂ x₁ y₁ x₂ y₂ x y g₁ g₂ h₁ h₂ hg₁ hg₂ hh₁ hh₂ hxy₁ hxy₂
    obtain ⟨b₁⟩ := hxy₁
    obtain ⟨b₂⟩ := hxy₂
    let : p.IsHomLift (𝟙 A₁) b₁.hom.1 := b₁.hom.2
    let : p.IsHomLift f₁ h₁ := hh₁
    let : p.IsHomLift f₁ (b₁.hom.1 ≫ h₁) := by infer_instance
    let := isStronglyCocartesian_of_isCofiberedInGroupoids hp f₁ g₁ hg₁
    obtain ⟨b, ⟨hb, hfac₁⟩, _⟩ :=
      Functor.IsStronglyCocartesian.universal_property p f₁ g₁ (𝟙 A) f₁
        (by simp) (b₁.hom.1 ≫ h₁)
    obtain ⟨bIso, hbIso⟩ := exists_fiber_iso_of_isHomLift p hp b hb
    let : p.IsHomLift (𝟙 A₂) b₂.inv.1 := b₂.inv.2
    let : p.IsHomLift f₂ g₂ := hg₂
    let : p.IsHomLift f₂ (b₂.inv.1 ≫ g₂ ≫ b) := by
      let : p.IsHomLift (𝟙 A) b := hb
      infer_instance
    let := isStronglyCocartesian_of_isCofiberedInGroupoids hp f₂ h₂ hh₂
    obtain ⟨c, ⟨hc, hfac₂⟩, _⟩ :=
      Functor.IsStronglyCocartesian.universal_property p f₂ h₂ (𝟙 A) f₂
        (by simp) (b₂.inv.1 ≫ g₂ ≫ b)
    obtain ⟨cIso, hcIso⟩ := exists_fiber_iso_of_isHomLift p hp c hc
    obtain ⟨d, hd⟩ := hlift f₂ hf₂ y₂ y h₂ hh₂ cIso
    refine ⟨b₁, b₂ ≪≫ d, bIso, ?_, ?_⟩
    · rw [hbIso]
      exact hfac₁.symm
    · change (b₂.hom.1 ≫ d.hom.1) ≫ h₂ = g₂ ≫ bIso.hom.1
      have hb₂ : b₂.hom.1 ≫ b₂.inv.1 = 𝟙 x₂.1 := congrArg Subtype.val b₂.hom_inv_id
      rw [Category.assoc, hd, hcIso, hfac₂, ← Category.assoc b₂.hom.1, hb₂, hbIso,
        Category.id_comp]

/-- For a category cofibered in groupoids, automorphisms lift along every surjection of Artinian
local algebras exactly when they lift along every small extension. -/
@[stacks 06J8 "conditions (3) and (4)", sga "7 VI 2.7" "(ii) vs surjections"]
theorem automorphismsLift_iff_smallExtensions
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    (∀ {A' A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A' ⟶ A),
      Function.Surjective f.hom → AutomorphismsLiftAlong p f) ↔
      (∀ {A' A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A' ⟶ A),
        InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom f.hom.toRingHom) → AutomorphismsLiftAlong p f) := by
  constructor
  · intro hsurj A' A f hsmall
    exact hsurj f hsmall.2.2.2.2.1
  · intro hsmall A' A f hf
    obtain ⟨n, D, hleft, e, hfactor, hedge⟩ := surjective_factors_into_smallExtensions f hf
    have hstep : ∀ (i : ℕ) (hi : i < n),
        AutomorphismsLiftAlong p (D.map' i (i + 1)) := fun i hi => hsmall _ (hedge i hi)
    have hD := automorphismsLiftAlong_composable p hp D hstep
    let e₀ : A' ≅ D.left := eqToIso hleft.symm
    have hstart := automorphismsLiftAlong_iso p hp e₀
    have hmid := automorphismsLiftAlong_comp p hp e₀.hom D.hom hstart hD
    have hend := automorphismsLiftAlong_iso p hp e
    have hfinal := automorphismsLiftAlong_comp p hp (e₀.hom ≫ D.hom) e.hom hmid hend
    have hfactor' : (e₀.hom ≫ D.hom) ≫ e.hom = f := by
      simpa [e₀, Category.assoc] using hfactor
    exact hfactor' ▸ hfinal

end

end Deformation
