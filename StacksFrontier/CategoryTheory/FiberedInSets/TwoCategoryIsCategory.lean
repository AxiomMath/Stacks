module


public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# The 2-category of categories fibred in sets is a category

The only 2-morphisms between categories fibred in sets over `𝒞` are the identities: if
`F, G : 𝒮 ⥤ 𝒮'` are 1-morphisms over `𝒞` into a functor `p'` fibred in sets
(`CategoryTheory.Functor.IsFiberedInSets`) and `η : F ⟶ G` is vertical, meaning each
`p'.map (η.app x)` is an identity of `𝒞`, then `F = G`.

## Main definitions

* `CategoryTheory.Functor.IsFiberedInSets`: a functor is fibred in sets if every morphism of the
  base has a unique lift with a prescribed target.

## Main results

* `CategoryTheory.Functor.IsFiberedInSets.map_eq_of_obj_eq` and
  `CategoryTheory.Functor.IsFiberedInSets.eq_of_obj_eq`: a 1-morphism over `𝒞` into a category
  fibred in sets is determined by its action on objects.
* `CategoryTheory.Functor.twoMorphisms_are_identity`: a vertical 2-morphism between 1-morphisms
  into a category fibred in sets is an identity.

## Implementation notes

Only the target is asked to be fibred in sets, and the source and the target live in independent
universes.

## References

* [Stacks Project, Tag 02Y2](https://stacks.math.columbia.edu/tag/02Y2)
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- A functor `p : 𝒮 ⥤ 𝒞` is *fibred in sets* iff for every morphism
`f : V ⟶ U` in `𝒞` and every object `x ∈ 𝒮` with `p.obj x = U`, there exists a unique
pair `(y, φ)` of an object `y ∈ 𝒮` with `p.obj y = V` and a morphism `φ : y ⟶ x` in
`𝒮` whose image under `p` equals `f` (after transporting along the propositional
equalities `p.obj y = V` and `p.obj x = U` via `eqToHom`). -/
class IsFiberedInSets {𝒮 : Type u₂} [Category.{v₂} 𝒮] (p : 𝒮 ⥤ 𝒞) : Prop where
  existsUnique_lift : ∀ {U V : 𝒞} (f : V ⟶ U) (x : 𝒮) (hx : p.obj x = U),
    ∃! yφ : Σ y : 𝒮, y ⟶ x,
      ∃ hy : p.obj yφ.1 = V,
        p.map yφ.2 = eqToHom hy ≫ f ≫ eqToHom hx.symm

section Helpers

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮] {𝒮' : Type u₃} [Category.{v₃} 𝒮']

/-- Two lifts of the same morphism with the same target in a category fibred in sets have equal
sources and heterogeneously equal morphisms. -/
private lemma lift_unique (p' : 𝒮' ⥤ 𝒞) [p'.IsFiberedInSets] {U V : 𝒞} (f : V ⟶ U)
    {x y z : 𝒮'} (hx : p'.obj x = U) (φ : y ⟶ x) (ψ : z ⟶ x) (hy : p'.obj y = V)
    (hz : p'.obj z = V) (hφ : p'.map φ = eqToHom hy ≫ f ≫ eqToHom hx.symm)
    (hψ : p'.map ψ = eqToHom hz ≫ f ≫ eqToHom hx.symm) : y = z ∧ HEq φ ψ :=
  Sigma.mk.inj_iff.mp
    ((IsFiberedInSets.existsUnique_lift (p := p') f x hx).unique ⟨hy, hφ⟩ ⟨hz, hψ⟩)

/-- Two functors over `𝒞` into a category fibred in sets related by a vertical natural
transformation agree on objects. -/
private lemma obj_eq_of_vertical
    (p : 𝒮 ⥤ 𝒞) (p' : 𝒮' ⥤ 𝒞) [p'.IsFiberedInSets]
    (F G : 𝒮 ⥤ 𝒮') (hF : F ⋙ p' = p) (hG : G ⋙ p' = p) (η : F ⟶ G)
    (hη : ∀ x, HEq (p'.map (η.app x)) (𝟙 (p.obj x))) (x : 𝒮) :
    F.obj x = G.obj x :=
  (lift_unique p' (𝟙 (p.obj x)) (Functor.congr_obj hG x) (η.app x) (𝟙 (G.obj x))
    (Functor.congr_obj hF x) (Functor.congr_obj hG x)
    (by grind only [comp_eqToHom_heq, eqToHom_comp_heq]) (by simp)).1

/-- Two 1-morphisms over `𝒞` into a category fibred in sets which agree on objects agree on
morphisms, modulo the `eqToHom` transport along the object equalities. -/
lemma IsFiberedInSets.map_eq_of_obj_eq
    (p : 𝒮 ⥤ 𝒞) (p' : 𝒮' ⥤ 𝒞) [p'.IsFiberedInSets]
    (F G : 𝒮 ⥤ 𝒮') (hF : F ⋙ p' = p) (hG : G ⋙ p' = p)
    (hobj : ∀ x, F.obj x = G.obj x) {x y : 𝒮} (φ : x ⟶ y) :
    F.map φ = eqToHom (hobj x) ≫ G.map φ ≫ eqToHom (hobj y).symm :=
  eq_of_heq (lift_unique p' (p.map φ) (Functor.congr_obj hF y) (F.map φ)
    (eqToHom (hobj x) ≫ G.map φ ≫ eqToHom (hobj y).symm) (Functor.congr_obj hF x)
    (Functor.congr_obj hF x) (Functor.congr_hom hF φ)
    (by grind only [comp_eqToHom_heq, eqToHom_comp_heq, = comp_map])).2

/-- A 1-morphism over `𝒞` into a category fibred in sets is determined by its action on
objects. -/
lemma IsFiberedInSets.eq_of_obj_eq
    (p : 𝒮 ⥤ 𝒞) (p' : 𝒮' ⥤ 𝒞) [p'.IsFiberedInSets]
    (F G : 𝒮 ⥤ 𝒮') (hF : F ⋙ p' = p) (hG : G ⋙ p' = p)
    (hobj : ∀ x, F.obj x = G.obj x) : F = G :=
  Functor.ext hobj fun _ _ φ ↦ IsFiberedInSets.map_eq_of_obj_eq p p' F G hF hG hobj φ

end Helpers

/-- A 2-morphism over `𝒞` between two 1-morphisms into a category fibred in sets is an
identity: the two 1-morphisms are equal. -/
@[stacks 02Y2]
theorem twoMorphisms_are_identity
    {𝒮 : Type u₂} [Category.{v₂} 𝒮] {𝒮' : Type u₃} [Category.{v₃} 𝒮']
    (p : 𝒮 ⥤ 𝒞) (p' : 𝒮' ⥤ 𝒞) [p'.IsFiberedInSets]
    (F G : 𝒮 ⥤ 𝒮') (hF : F ⋙ p' = p) (hG : G ⋙ p' = p)
    (η : F ⟶ G)
    (hη : ∀ x, HEq (p'.map (η.app x)) (𝟙 (p.obj x))) :
    F = G :=
  IsFiberedInSets.eq_of_obj_eq p p' F G hF hG (obj_eq_of_vertical p p' F G hF hG η hη)

end CategoryTheory.Functor
