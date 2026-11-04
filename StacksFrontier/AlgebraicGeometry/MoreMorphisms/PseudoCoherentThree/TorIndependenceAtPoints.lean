module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceBaseChange

/-!
# Tor independence at a pair of points

Tor independence of two morphisms `f : X ⟶ S` and `g : Y ⟶ S` (Stacks 08IA) is a condition at
every pair of points `x`, `y` with `f x = g y`: the local rings `𝒪_{X,x}` and `𝒪_{Y,y}` are Tor
independent over `𝒪_{S,f x}`. This file names that pointwise condition and proves that it only
depends on the three local rings: it is transported along morphisms of the three schemes which
are compatible with `f` and `g` and induce isomorphisms of local rings at the points in question,
such as open immersions and isomorphisms.

## Main definitions

* `AlgebraicGeometry.TorIndependentAt`: Tor independence of `f` and `g` at a pair of points.

## Main results

* `AlgebraicGeometry.torIndependentAt_iff_of_isIso_stalkMap`: transport of the pointwise
  condition along morphisms inducing isomorphisms on the relevant local rings.
* `AlgebraicGeometry.torIndependentAt_symm`: the pointwise condition is symmetric.

## References

* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Tor independence of `f : X ⟶ S` and `g : Y ⟶ S` at points `x` and `y` with the same image:
the local rings `𝒪_{X,x}` and `𝒪_{Y,y}` are Tor independent over `𝒪_{S,f x}`. -/
def TorIndependentAt {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (h : f.base x = g.base y) : Prop :=
  letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  letI : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
  Algebra.TorIndependent (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
    (Y.presheaf.stalk y)

/-- Tor independence is Tor independence at every pair of points with the same image. -/
theorem torIndependent_iff_forall_torIndependentAt {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) : TorIndependent f g ↔ ∀ x y h, TorIndependentAt f g x y h :=
  Iff.rfl

/-- Tor independence of algebras is transported along isomorphisms of the base ring and of the
two algebras which commute with the structure maps. -/
theorem algebraTorIndependent_iff_of_isIso {R A B R₁ A₁ B₁ : CommRingCat.{u}}
    (φA : R ⟶ A) (φB : R ⟶ B) (φA₁ : R₁ ⟶ A₁) (φB₁ : R₁ ⟶ B₁)
    (eR : R₁ ⟶ R) (eA : A₁ ⟶ A) (eB : B₁ ⟶ B) [IsIso eR] [IsIso eA] [IsIso eB]
    (hA : φA₁ ≫ eA = eR ≫ φA) (hB : φB₁ ≫ eB = eR ≫ φB) :
    (letI := φA₁.hom.toAlgebra; letI := φB₁.hom.toAlgebra; Algebra.TorIndependent R₁ A₁ B₁) ↔
      (letI := φA.hom.toAlgebra; letI := φB.hom.toAlgebra; Algebra.TorIndependent R A B) := by
  let := φA₁.hom.toAlgebra
  let := φB₁.hom.toAlgebra
  let := φA.hom.toAlgebra
  let := φB.hom.toAlgebra
  show Algebra.TorIndependent R₁ A₁ B₁ ↔ Algebra.TorIndependent R A B
  rw [Algebra.torIndependent_iff, Algebra.torIndependent_iff,
    ← RingTheory.TorIndependence.torIndependent_iff_isZero_tor,
    ← RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  exact torIndependent_congr R₁ A₁ B₁ R A B (asIso eR).commRingCatIsoToRingEquiv
    (asIso eA).commRingCatIsoToRingEquiv (asIso eB).commRingCatIsoToRingEquiv
    (fun r => congrArg (fun k => k.hom r) hA) (fun r => congrArg (fun k => k.hom r) hB)

/-- The transport along an equality of points is the isomorphism of stalks of inseparable
points. -/
theorem eqToHom_stalk_eq_stalkCongr {S : Scheme.{u}} {p q : S} (h : p = q) :
    eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) =
      (S.presheaf.stalkCongr (.of_eq h)).hom := by
  subst h
  simp

/-- The stalk maps of two factorizations of one morphism agree, up to the isomorphism of stalks
at the two (equal) images of the point. -/
theorem stalkMap_comp_eq_of_comp_eq {X Y Y' Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z)
    (u' : X ⟶ Y') (v' : Y' ⟶ Z) (e : u ≫ v = u' ≫ v') (x : X)
    (hx : v.base (u.base x) = v'.base (u'.base x)) :
    v.stalkMap (u.base x) ≫ u.stalkMap x =
      (Z.presheaf.stalkCongr (.of_eq hx)).hom ≫
        v'.stalkMap (u'.base x) ≫ u'.stalkMap x := by
  have key := Scheme.Hom.stalkMap_congr_hom (u ≫ v) (u' ≫ v') e x
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at key
  exact key

/-- For a commutative square `b ≫ g₁ = g ≫ c`, the two maps `𝒪_{S₁,f₁(a x)} ⟶ 𝒪_{Y,y}` built
from stalk maps and isomorphisms of stalks at equal points, one through `𝒪_{Y₁,b y}` and one
through `𝒪_{S,f x}`, agree. -/
theorem stalkMap_square_of_comp_eq {S X Y S₁ X₁ Y₁ : Scheme.{u}} {f : X ⟶ S}
    {g : Y ⟶ S} {f₁ : X₁ ⟶ S₁} {g₁ : Y₁ ⟶ S₁} {a : X ⟶ X₁} (b : Y ⟶ Y₁) (c : S ⟶ S₁)
    (hb : b ≫ g₁ = g ≫ c) {x : X} {y : Y} (h : f.base x = g.base y)
    (h₁ : f₁.base (a.base x) = g₁.base (b.base y)) (h₂ : f₁.base (a.base x) = c.base (f.base x))
    (h₃ : g₁.base (b.base y) = c.base (g.base y)) :
    ((S₁.presheaf.stalkCongr (.of_eq h₁)).hom ≫ g₁.stalkMap (b.base y)) ≫ b.stalkMap y =
      ((S₁.presheaf.stalkCongr (.of_eq h₂)).hom ≫ c.stalkMap (f.base x)) ≫
        (S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap y := by
  have hcomp {p q r : S₁} (e₁ : Inseparable p q) (e₂ : Inseparable q r) :
      (S₁.presheaf.stalkCongr e₁).hom ≫ (S₁.presheaf.stalkCongr e₂).hom =
        (S₁.presheaf.stalkCongr (e₁.trans e₂)).hom :=
    TopCat.Presheaf.stalkSpecializes_comp _ e₂.ge e₁.ge
  rw [Category.assoc, stalkMap_comp_eq_of_comp_eq b g₁ g c hb y h₃, Category.assoc,
    Scheme.Hom.stalkMap_congr_point_assoc c (f.base x) (g.base y) h, reassoc_of% hcomp,
    reassoc_of% hcomp]

/-- **Transport of Tor independence at a point.** Let `a`, `b`, `c` be morphisms from the data
`f : X ⟶ S`, `g : Y ⟶ S` to the data `f₁ : X₁ ⟶ S₁`, `g₁ : Y₁ ⟶ S₁`, compatible with the
structure morphisms, and inducing isomorphisms of local rings at `x`, `y` and `f x`. Then `f₁`
and `g₁` are Tor independent at `a x`, `b y` exactly when `f` and `g` are Tor independent at
`x`, `y`. -/
theorem torIndependentAt_iff_of_isIso_stalkMap {S X Y S₁ X₁ Y₁ : Scheme.{u}} {f : X ⟶ S}
    {g : Y ⟶ S} {f₁ : X₁ ⟶ S₁} {g₁ : Y₁ ⟶ S₁} (a : X ⟶ X₁) (b : Y ⟶ Y₁) (c : S ⟶ S₁)
    (ha : a ≫ f₁ = f ≫ c) (hb : b ≫ g₁ = g ≫ c) {x : X} {y : Y} (h : f.base x = g.base y)
    (h₁ : f₁.base (a.base x) = g₁.base (b.base y))
    [IsIso (a.stalkMap x)] [IsIso (b.stalkMap y)] [IsIso (c.stalkMap (f.base x))] :
    TorIndependentAt f₁ g₁ (a.base x) (b.base y) h₁ ↔ TorIndependentAt f g x y h := by
  have h₂ : f₁.base (a.base x) = c.base (f.base x) := by
    simpa using congrArg (fun k : X ⟶ S₁ => k.base x) ha
  have h₃ : g₁.base (b.base y) = c.base (g.base y) := by
    simpa using congrArg (fun k : Y ⟶ S₁ => k.base y) hb
  unfold TorIndependentAt
  rw [eqToHom_stalk_eq_stalkCongr h₁, eqToHom_stalk_eq_stalkCongr h]
  refine algebraTorIndependent_iff_of_isIso _ _ _ _
    ((S₁.presheaf.stalkCongr (.of_eq h₂)).hom ≫ c.stalkMap (f.base x)) (a.stalkMap x)
    (b.stalkMap y) ?_ ?_
  · rw [stalkMap_comp_eq_of_comp_eq a f₁ f c ha x h₂]
    simp only [Category.assoc]
  · exact stalkMap_square_of_comp_eq b c hb h h₁ h₂ h₃

/-- Tor independence at a pair of points is symmetric. -/
theorem torIndependentAt_symm {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {x : X} {y : Y}
    (h : f.base x = g.base y) (H : TorIndependentAt f g x y h) :
    TorIndependentAt g f y x h.symm := by
  unfold TorIndependentAt at H ⊢
  refine (algebraTorIndependent_iff_of_isIso
    (g.stalkMap y) (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h.symm) ≫ f.stalkMap x)
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ g.stalkMap y) (f.stalkMap x)
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h)) (𝟙 _) (𝟙 _)
    (by simp) (by simp)).1 ?_
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
  intro p hp
  obtain ⟨e⟩ := _root_.tor_symm_canonically_iso (S.presheaf.stalk (f.base x)) p
  exact (H p hp).of_iso ((e.app (ModuleCat.of _ _)).app (ModuleCat.of _ _))

end AlgebraicGeometry

end
