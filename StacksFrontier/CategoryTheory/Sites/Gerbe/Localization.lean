module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Sites.Over

public import StacksFrontier.CategoryTheory.Sites.Gerbe.Defs
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localizing a category fibred in groupoids at an object

Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` be a category fibred in groupoids and let `x` be an
object of `𝒳`. Then `p` induces an equivalence of the localizations, `𝒳/x ⥤ 𝒞/p x`, and it
matches the coverings on the two sides when `𝒳` carries the topology inherited from `(𝒞, J)`. This
is Stacks 0CN0.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_overPost`: the functor
  `Over.post p : Over x ⥤ Over (p.obj x)` is an equivalence of categories — the first half of
  **Stacks 0CN0**.
* `CategoryTheory.Functor.IsInheritedTopology.mem_over_iff_functorPushforward`: a sieve on an
  object of `𝒳/x` is covering for the topology induced by `J𝒳` exactly when its image is
  covering for the topology induced by `J` — the second half of **Stacks 0CN0**.
* `CategoryTheory.Functor.IsInheritedTopology.mem_iff_functorPushforward`: the same statement one
  level down, on `𝒳` itself.

## Implementation notes

`Over.post p` lands in `Over (p.obj x)` rather than in `Over U` for an object `U` of `𝒞` given
with an equality `p.obj x = U`; writing the target as `p.obj x` is the same statement with no
`eqToHom` transport in it.

The inherited topology is a hypothesis, `IsInheritedTopology p J J𝒳`, rather than a
construction: Stacks 06NU, which builds the site, is not available here — see
`StacksFrontier.CategoryTheory.Sites.InheritedTopology.Defs`.
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒞}

/-! ### The equivalence of categories `𝒳/x ⥤ 𝒞/p x` -/

/-- For `p` fibred in groupoids, `Over.post p : 𝒳/x ⥤ 𝒞/p x` is faithful. -/
theorem IsFiberedInGroupoids.faithful_overPost (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    (Over.post (X := x) p).Faithful where
  map_injective {A B} f g h := by
    have hfac : p.map (Over.Hom.left f) = p.map (Over.Hom.left g) := congrArg Over.Hom.left h
    obtain ⟨χ, -, huniq⟩ := hp.unique_lift B.hom A.hom (p.map (Over.Hom.left f))
      (by rw [← p.map_comp, Over.w f])
    exact Over.OverMorphism.ext ((huniq (Over.Hom.left f) ⟨rfl, Over.w f⟩).trans
      (huniq (Over.Hom.left g) ⟨hfac.symm, Over.w g⟩).symm)

/-- For `p` fibred in groupoids, `Over.post p : 𝒳/x ⥤ 𝒞/p x` is full. -/
theorem IsFiberedInGroupoids.full_overPost (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    (Over.post (X := x) p).Full where
  map_surjective {A B} h := by
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, -⟩ := hp.unique_lift B.hom A.hom (Over.Hom.left h) (Over.w h)
    exact ⟨Over.homMk χ hχ₂, Over.OverMorphism.ext hχ₁⟩

/-- For `p` fibred in groupoids, `Over.post p : 𝒳/x ⥤ 𝒞/p x` is essentially surjective. -/
@[sga "4 I 6.5" "(i)⇒(iii)"]
theorem IsFiberedInGroupoids.essSurj_overPost (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    (Over.post (X := x) p).EssSurj where
  mem_essImage B := by
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift B.hom x rfl
    have := hφ
    have hy : p.obj y = B.left := IsHomLift.domain_eq p B.hom φ
    refine ⟨Over.mk φ, ⟨Over.isoMk (eqToIso hy) ?_⟩⟩
    show (eqToIso hy).hom ≫ B.hom = p.map φ
    rw [IsHomLift.fac' p B.hom φ]
    simp

/-- For `p : 𝒳 ⥤ 𝒞` fibred in groupoids and `x` an object of `𝒳`, the functor
`Over.post p : 𝒳/x ⥤ 𝒞/p x` induced by `p` is an equivalence of categories. -/
@[stacks 0CN0 "the equivalence of categories 𝒳/x ⥤ 𝒞/U"]
theorem IsFiberedInGroupoids.isEquivalence_overPost (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    (Over.post (X := x) p).IsEquivalence where
  faithful := hp.faithful_overPost x
  full := hp.full_overPost x
  essSurj := hp.essSurj_overPost x

/-- `𝒳/x ≌ 𝒞/p x`, the equivalence of `IsFiberedInGroupoids.isEquivalence_overPost` as a bundled
equivalence of categories. -/
noncomputable def IsFiberedInGroupoids.overPostEquivalence (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    Over x ≌ Over (p.obj x) :=
  have := hp.isEquivalence_overPost x
  (Over.post (X := x) p).asEquivalence

/-! ### The correspondence of coverings -/

/-- For `p` fibred in groupoids, a sieve on an object `x` of `𝒳` is covering for the topology
inherited from `(𝒞, J)` exactly when its image sieve is covering in `𝒞`. -/
theorem IsInheritedTopology.mem_iff_functorPushforward (hp : p.IsFiberedInGroupoids)
    {J : GrothendieckTopology 𝒞} {J𝒳 : GrothendieckTopology 𝒳}
    (hJ : _root_.CategoryTheory.Functor.IsInheritedTopology.{max u₂ v₂} p J J𝒳)
    {x : 𝒳} (T : Sieve x) :
    T ∈ J𝒳 x ↔ Sieve.functorPushforward p T ∈ J (p.obj x) := by
  have key := hJ (Y := x) (I := Σ z : 𝒳, {φ : z ⟶ x // T.arrows φ})
    (fun i => i.1) (fun i => i.2.val) (fun i => hp.isStronglyCartesian i.2.val)
  rw [CategoryTheory.Sieve.ofArrows_sigma_arrows] at key
  rw [key]
  congr! 1
  ext Z g
  rw [Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨i, a, rfl⟩
    exact ⟨i.1, i.2.val, a, i.2.property, rfl⟩
  · rintro ⟨z, φ, k, hφ, rfl⟩
    exact ⟨⟨z, φ, hφ⟩, k, rfl⟩

/-- For `p` fibred in groupoids and `J𝒳` inherited from `(𝒞, J)`, a sieve on an object of `𝒳/x` is
covering for the topology that `J𝒳` induces on `𝒳/x` exactly when its image under `Over.post p` is
covering for the topology that `J` induces on `𝒞/p x`. -/
@[stacks 0CN0 "coverings of x' in 𝒳/x correspond to coverings of p x' in 𝒞/U"]
theorem IsInheritedTopology.mem_over_iff_functorPushforward (hp : p.IsFiberedInGroupoids)
    {J : GrothendieckTopology 𝒞} {J𝒳 : GrothendieckTopology 𝒳}
    (hJ : _root_.CategoryTheory.Functor.IsInheritedTopology.{max u₂ v₂} p J J𝒳)
    {x : 𝒳} (Y : Over x) (S : Sieve Y) :
    S ∈ (J𝒳.over x) Y ↔
      Sieve.functorPushforward (Over.post p) S ∈
        (J.over (p.obj x)) ((Over.post (X := x) p).obj Y) := by
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_functorPushforward_post]
  exact IsInheritedTopology.mem_iff_functorPushforward hp hJ _

/-- The localization functor `Over.post p : 𝒳/x ⥤ 𝒞/p x` preserves coverings, the forward half of
`IsInheritedTopology.mem_over_iff_functorPushforward`. -/
theorem IsInheritedTopology.coverPreserving_overPost (hp : p.IsFiberedInGroupoids)
    {J : GrothendieckTopology 𝒞} {J𝒳 : GrothendieckTopology 𝒳}
    (hJ : _root_.CategoryTheory.Functor.IsInheritedTopology.{max u₂ v₂} p J J𝒳) (x : 𝒳) :
    CoverPreserving (J𝒳.over x) (J.over (p.obj x)) (Over.post (X := x) p) where
  cover_preserve {Y S} hS :=
    (IsInheritedTopology.mem_over_iff_functorPushforward hp hJ Y S).1 hS

end CategoryTheory.Functor
