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
public import Mathlib.Algebra.Category.Grp.Basic

public import StacksFrontier.CategoryTheory.Sites.Gerbe.Defs
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing

/-! # The band of a gerbe with abelian automorphism sheaves

Let `p : 𝒮 ⥤ 𝒞` be a gerbe over the site `(𝒞, J)` all of whose automorphism sheaves are abelian.
Stacks 0CJY produces one sheaf of abelian groups `𝒢` on `𝒞` together with isomorphisms
`𝒢|_U ≅ Aut(x)` for every object `x` of every fibre, compatible with conjugation. This file builds
the object that carries it, the *band*: a section of the inertia of `p` over `V` is a family
assigning to every object `x` of `𝒮` and every morphism `h : p x ⟶ V` an endomorphism of `x` lying
over an identity, naturally in `x` — that is, commuting with every morphism of `𝒮` over `V`.

The band is a presheaf of groups on `𝒞` on the nose: restriction along `k : V' ⟶ V` precomposes the
second argument with `k`, so functoriality is associativity of composition and no choices and no
gluing enter its definition. The group law is composition, and it is commutative exactly because
the endomorphisms of the objects of the fibres are. The comparison with `Aut(x) = Mor(x, x)` reads
a section of the inertia at the chosen pullbacks of `x`; it is multiplicative by construction, and
the conjugation square of Stacks 0CJY is its naturality in the object of the fibre, so the source's
per-`U` gluing of the local comparisons — and with it the compatibility "over varying `U`" that the
source leaves out — is absorbed into the definition.

## Main results

* `CategoryTheory.Gerbe.Band.fiberHom_mul` and
  `CategoryTheory.Gerbe.Band.fiberHom_pullbackFiber_conj`: the two clauses of the conclusion of
  Stacks 0CJY, for the band.
* `CategoryTheory.Gerbe.Band.eq_of_fiberHom_eq` and
  `CategoryTheory.Gerbe.Band.exists_band_fiberHom_eq`: the comparison is injective, and surjective,
  on sections, so it is a bijection.
* `CategoryTheory.Gerbe.Band.existsUnique_band_of_compatible`: the band is a sheaf.
* `CategoryTheory.Gerbe.Band.small_band`: the band is small, with no hypothesis on the universes.
* `CategoryTheory.Gerbe.conj_eq_conj_of_comm`: the computation in the source's proof — conjugation
  by an isomorphism of a fibre with commuting endomorphisms does not depend on the isomorphism.

## Implementation notes

The band over `V` is a family indexed by the objects of `𝒮` lying over `V`, so its sections are a
type in `Type (max u₂ v₁ v₂)`, while a sheaf valued in `CommGrpCat.{v₂}` has its sections in
`Type v₂`. Passing between the two is a smallness statement, and it is the one step of Stacks 0CJY
that does not follow from the hypotheses as they stand: over an object `V` whose fibre is empty no
comparison constrains the sections at `V`, while the sheaf axiom puts them in bijection with the
matching families over a covering sieve of `V`, a type in `Type (max u₁ v₁)`. `Type 0`-many copies
of a nontrivial `ℤ/2`-gerbe give sections of cardinality `2 ^ |Type 0|` at the top object, which is
the cardinality of no `Type 0`, so no sheaf valued in `CommGrpCat.{0}` can carry them.

What *is* true with no hypothesis is `Band.small_band`: the band is small in `Type (max u₁ v₁ v₂)`,
the universe of the objects of `𝒮` dropping out. Local nonemptiness gives a covering sieve of `V`
all of whose members carry an object of `𝒮`, the band is separated for that sieve, and over an
object carrying an object of `𝒮` a section is determined by its single value there
(`Band.eq_of_fiberHom_eq`); so the band embeds into a product indexed by the arrows of the sieve —
a type in `Type (max u₁ v₁)` — of endomorphism groups, which are types in `Type v₂`. Under the
further hypothesis `UnivLE.{max u₁ v₁, v₂}` the same injection gives `Band.small_band_of_univLE`,
smallness in `Type v₂` itself, which is what a sheaf valued in `CommGrpCat.{v₂}` needs.

`Aut(x)` is `CategoryTheory.Functor.morPresheaf p x x` and not the subpresheaf `Isom(x, x)`: over a
category fibred in groupoids every morphism of a fibre is invertible, so the two presheaves are the
same one. The two halves of condition (2) of Stacks 026F that the arguments here consume are
`CategoryTheory.Functor.eq_of_pullbackFiberHom_locally_eq` and
`CategoryTheory.Functor.exists_fiberHom_of_locally`. The bridge between the band and those is
`Band.pullbackFiberHom_fiberHom`: the value of a section of the inertia at a chosen pullback is the
base change of its value, so a section of the inertia gives a section of `Mor(x, x)` and the sheaf
property applies to it verbatim.

## References

* [Stacks 0CJY](https://stacks.math.columbia.edu/tag/0CJY)
-/

@[expose] public section

-- The chosen pullbacks and the inclusion of a fibre are semireducible, so the endpoints of the
-- composites below agree only up to unfolding them, as in
-- `StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated`.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Gerbe

open CategoryTheory Opposite CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- A section over `V` of the inertia of `p` — a *band section*: an endomorphism `hom x h` of every
object `x` of `𝒮` given with a morphism `h : p x ⟶ V`, lying over an identity and natural in `x`,
that is commuting with every morphism of `𝒮` compatible with the two given morphisms to `V`. -/
private structure Band (p : 𝒮 ⥤ 𝒞) (V : 𝒞) where
  /-- The endomorphism attached to an object over `V`. -/
  hom : ∀ (x : 𝒮), (p.obj x ⟶ V) → (x ⟶ x)
  /-- Every value lies over an identity, so it is an endomorphism of a fibre. -/
  map_hom : ∀ (x : 𝒮) (h : p.obj x ⟶ V), p.map (hom x h) = 𝟙 (p.obj x)
  /-- The values commute with every morphism of `𝒮` over `V`. -/
  natural : ∀ {x y : 𝒮} (hx : p.obj x ⟶ V) (hy : p.obj y ⟶ V) (φ : x ⟶ y),
    p.map φ ≫ hy = hx → hom x hx ≫ φ = φ ≫ hom y hy

/-! ### Independence of the conjugating isomorphism -/

section Conjugation

variable {p : 𝒮 ⥤ 𝒞}

/-- **The computation in the source's proof of Stacks 0CJY.** When the endomorphisms of the objects
of a fibre commute, conjugation by an isomorphism `z ≅ z'` of that fibre does not depend on the
isomorphism: if `e` and `f` are two of them then `e⁻¹ α e = f⁻¹ α f`, because `e f⁻¹` is an
endomorphism of `z` and so commutes with `α`. This is what makes the comparisons of Stacks 0CJY
canonical, and hence what makes them glue. -/
private lemma conj_eq_conj_of_comm
    (habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α)
    {W : 𝒞} {z z' : p.Fiber W} (e f : z ≅ z') (α : z ⟶ z) :
    e.inv ≫ α ≫ e.hom = f.inv ≫ α ≫ f.hom := by
  calc e.inv ≫ α ≫ e.hom
      = e.inv ≫ (α ≫ (e.hom ≫ f.inv)) ≫ f.hom := by simp
    _ = e.inv ≫ ((e.hom ≫ f.inv) ≫ α) ≫ f.hom := by rw [habel W z α (e.hom ≫ f.inv)]
    _ = f.inv ≫ α ≫ f.hom := by simp

end Conjugation

namespace Band

variable {p : 𝒮 ⥤ 𝒞} {V : 𝒞}

/-- Two band sections with the same values are equal. -/
private lemma ext {a b : Band p V} (h : a.hom = b.hom) : a = b := by
  cases a
  cases b
  simp_all

attribute [local ext] ext

/-- Every value of a band section lies over the identity of any object it lies over. -/
private lemma isHomLift (a : Band p V) {W : 𝒞} {x : 𝒮} (hx : p.obj x = W) (h : p.obj x ⟶ V) :
    p.IsHomLift (𝟙 W) (a.hom x h) :=
  IsHomLift.of_fac p (𝟙 W) _ hx hx (by subst hx; simp [a.map_hom])

/-- A morphism of `𝒮` over `k` transports the canonical morphism to `V` of its target to the one
of its source. -/
private lemma map_eqToHom {W Z : 𝒞} (k : Z ⟶ W) {x y : 𝒮} (φ : x ⟶ y) (hφ : p.IsHomLift k φ)
    (hx : p.obj x = Z) (hy : p.obj y = W) :
    p.map φ ≫ eqToHom hy = eqToHom hx ≫ k := by
  have := hφ
  subst hx hy
  rw [IsHomLift.eq_of_isHomLift p k φ]
  simp

/-- `Band.map_eqToHom` composed with a morphism `W ⟶ V`: the form in which the naturality of a band
section is applied. -/
private lemma map_comp_eqToHom {W Z : 𝒞} (k : Z ⟶ W) {x y : 𝒮} (φ : x ⟶ y) (hφ : p.IsHomLift k φ)
    (hx : p.obj x = Z) (hy : p.obj y = W) (h : W ⟶ V) :
    p.map φ ≫ eqToHom hy ≫ h = eqToHom hx ≫ k ≫ h := by
  rw [← Category.assoc, map_eqToHom k φ hφ hx hy, Category.assoc]

/-! ### The group of band sections and its restriction maps -/

/-- The trivial band section. -/
private instance : One (Band p V) where
  one := { hom := fun x _ => 𝟙 x
           map_hom := fun x _ => p.map_id x
           natural := by intros; simp }

/-- Band sections are multiplied by composing their values. -/
private instance : Mul (Band p V) where
  mul a b := { hom := fun x h => a.hom x h ≫ b.hom x h
               map_hom := fun x h => by rw [p.map_comp, a.map_hom, b.map_hom, Category.comp_id]
               natural := fun hx hy φ hφ => by
                 rw [Category.assoc, b.natural hx hy φ hφ, ← Category.assoc,
                   a.natural hx hy φ hφ, Category.assoc] }

/-- The values of the trivial band section are identities. -/
private lemma hom_one (x : 𝒮) (h : p.obj x ⟶ V) : (1 : Band p V).hom x h = 𝟙 x := rfl

/-- The values of a product of band sections are the composites of the values. -/
private lemma hom_mul (a b : Band p V) (x : 𝒮) (h : p.obj x ⟶ V) :
    (a * b).hom x h = a.hom x h ≫ b.hom x h := rfl

attribute [local simp] hom_one hom_mul

private instance : Monoid (Band p V) where
  mul_assoc a b c := by ext x h; simp
  one_mul a := by ext x h; simp
  mul_one a := by ext x h; simp

section Inv

variable (hp : p.IsFiberedInGroupoids)

include hp in
/-- Every value of a band section is invertible: it lies over an identity, and the fibres of a
category fibred in groupoids are groupoids. -/
private lemma isIso_hom (a : Band p V) (x : 𝒮) (h : p.obj x ⟶ V) : IsIso (a.hom x h) :=
  isIso_of_isHomLift_id p hp _ (a.isHomLift rfl h)

/-- The pointwise inverse of a value of a band section. -/
private noncomputable def invHom (a : Band p V) (x : 𝒮) (h : p.obj x ⟶ V) : x ⟶ x :=
  @CategoryTheory.inv _ _ _ _ (a.hom x h) (isIso_hom hp a x h)

private lemma hom_invHom_id (a : Band p V) (x : 𝒮) (h : p.obj x ⟶ V) :
    a.hom x h ≫ invHom hp a x h = 𝟙 x :=
  @IsIso.hom_inv_id _ _ _ _ (a.hom x h) (isIso_hom hp a x h)

private lemma invHom_hom_id (a : Band p V) (x : 𝒮) (h : p.obj x ⟶ V) :
    invHom hp a x h ≫ a.hom x h = 𝟙 x :=
  @IsIso.inv_hom_id _ _ _ _ (a.hom x h) (isIso_hom hp a x h)

attribute [local simp] hom_invHom_id invHom_hom_id

/-- The pointwise inverse again lies over an identity. -/
private lemma map_invHom (a : Band p V) (x : 𝒮) (h : p.obj x ⟶ V) :
    p.map (invHom hp a x h) = 𝟙 (p.obj x) := by
  have h1 : p.map (a.hom x h) ≫ p.map (invHom hp a x h) = 𝟙 (p.obj x) := by
    rw [← p.map_comp, hom_invHom_id, p.map_id]
  rwa [a.map_hom, Category.id_comp] at h1

/-- The inverse of a band section. Naturality of the inverse is naturality of the section
conjugated: `α⁻¹ φ = α⁻¹ (φ α) α⁻¹ = α⁻¹ (α φ) α⁻¹ = φ α⁻¹`. -/
private noncomputable def inv (a : Band p V) : Band p V where
  hom x h := invHom hp a x h
  map_hom x h := map_invHom hp a x h
  natural {x y} hx hy φ hφ := by
    calc invHom hp a x hx ≫ φ
        = invHom hp a x hx ≫ (φ ≫ a.hom y hy) ≫ invHom hp a y hy := by
          rw [Category.assoc, hom_invHom_id, Category.comp_id]
      _ = invHom hp a x hx ≫ (a.hom x hx ≫ φ) ≫ invHom hp a y hy := by rw [a.natural hx hy φ hφ]
      _ = φ ≫ invHom hp a y hy := by
          rw [← Category.assoc, ← Category.assoc, invHom_hom_id, Category.id_comp]

private lemma hom_inv (a : Band p V) (x : 𝒮) (h : p.obj x ⟶ V) :
    (inv hp a).hom x h = invHom hp a x h := rfl

attribute [local simp] hom_inv

include hp in
private lemma inv_mul_cancel (a : Band p V) : inv hp a * a = 1 := by
  ext x h
  simp

/-- The group of band sections over `V`. -/
@[instance_reducible] private noncomputable def group : Group (Band p V) :=
  { (inferInstance : Monoid (Band p V)) with
    inv := inv hp
    inv_mul_cancel := inv_mul_cancel hp }

end Inv

section Comm

variable (habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α)

include habel in
/-- Band sections commute when the endomorphisms of the objects of the fibres do: their values at
one object are two endomorphisms of one object of a fibre. -/
private lemma mul_comm (a b : Band p V) : a * b = b * a := by
  ext x h
  have := habel (p.obj x) (Fiber.mk (rfl : p.obj x = p.obj x))
    ⟨a.hom x h, a.isHomLift rfl h⟩ ⟨b.hom x h, b.isHomLift rfl h⟩
  exact congrArg Fiber.fiberInclusion.map this

/-- The group of band sections over `V` is commutative when the endomorphisms of the objects of the
fibres are. -/
@[instance_reducible] private noncomputable def commGroup (hp : p.IsFiberedInGroupoids) :
    CommGroup (Band p V) :=
  { group hp with mul_comm := mul_comm habel }

end Comm

section Restrict

/-- Restriction of a band section along `k : V' ⟶ V`: precompose the morphism to `V` with `k`. -/
private def restrict (a : Band p V) {V' : 𝒞} (k : V' ⟶ V) : Band p V' where
  hom x h := a.hom x (h ≫ k)
  map_hom x h := a.map_hom x (h ≫ k)
  natural hx hy φ hφ := a.natural _ _ φ (by rw [← Category.assoc, hφ])

private lemma hom_restrict (a : Band p V) {V' : 𝒞} (k : V' ⟶ V) (x : 𝒮) (h : p.obj x ⟶ V') :
    (a.restrict k).hom x h = a.hom x (h ≫ k) := rfl

attribute [local simp] hom_restrict

/-- Restriction along an identity does nothing. -/
private lemma restrict_id (a : Band p V) : a.restrict (𝟙 V) = a := by ext x h; simp

/-- Restriction is functorial. -/
private lemma restrict_restrict (a : Band p V) {V' V'' : 𝒞} (k : V' ⟶ V) (k' : V'' ⟶ V') :
    (a.restrict k).restrict k' = a.restrict (k' ≫ k) := by ext x h; simp

/-- Restriction is multiplicative. -/
private lemma restrict_mul (a b : Band p V) {V' : 𝒞} (k : V' ⟶ V) :
    (a * b).restrict k = a.restrict k * b.restrict k := by ext x h; simp

/-- Restriction preserves the trivial section. -/
private lemma restrict_one {V' : 𝒞} (k : V' ⟶ V) : (1 : Band p V).restrict k = 1 := by
  ext x h; simp

end Restrict

/-! ### The comparison with `Aut(x) = Mor(x, x)` -/

/-- The value of a band section at an object of the fibre over `W`, read as an endomorphism of that
fibre. For `z` a chosen pullback of `x` this is the comparison `𝒢|_U ⟶ Aut(x)` of Stacks 0CJY on
sections. -/
private def fiberHom (a : Band p V) {W : 𝒞} (z : p.Fiber W) (h : W ⟶ V) : z ⟶ z :=
  ⟨a.hom z.1 (eqToHom z.2 ≫ h), a.isHomLift z.2 _⟩

private lemma fiberInclusion_map_fiberHom (a : Band p V) {W : 𝒞} (z : p.Fiber W) (h : W ⟶ V) :
    Fiber.fiberInclusion.map (a.fiberHom z h) = a.hom z.1 (eqToHom z.2 ≫ h) := rfl

attribute [local simp] fiberInclusion_map_fiberHom

/-- The value of a band section at an object of `𝒮` is its value in the fibre over `p z`. -/
private lemma hom_eq_fiberInclusion_map_fiberHom (a : Band p V) (z : 𝒮) (h : p.obj z ⟶ V) :
    a.hom z h = Fiber.fiberInclusion.map (a.fiberHom (Fiber.mk (rfl : p.obj z = p.obj z)) h) := by
  show a.hom z h = a.hom z (eqToHom (rfl : p.obj z = p.obj z) ≫ h)
  simp

/-- The comparison depends on the morphism to `V` only through its value. -/
private lemma fiberHom_congr (a : Band p V) {W : 𝒞} (z : p.Fiber W) {h h' : W ⟶ V} (e : h = h') :
    a.fiberHom z h = a.fiberHom z h' := by rw [e]

/-- **The comparison is natural in the object of the fibre**: a band section commutes with every
morphism of the fibre over `W`. This is the conjugation square of Stacks 0CJY. -/
private lemma fiberHom_naturality (a : Band p V) {W : 𝒞} {z z' : p.Fiber W} (e : z ⟶ z')
    (h : W ⟶ V) : a.fiberHom z h ≫ e = e ≫ a.fiberHom z' h := by
  refine Fiber.hom_ext ?_
  simp only [Functor.map_comp, fiberInclusion_map_fiberHom]
  refine a.natural _ _ (Fiber.fiberInclusion.map e) ?_
  have h2 := map_comp_eqToHom (V := V) (𝟙 W) (Fiber.fiberInclusion.map e) e.2 z.2 z'.2 h
  rwa [Category.id_comp] at h2

/-- **The comparison is compatible with base change**: the base change along `k` of the value of a
band section at `z` is its value at the chosen pullback of `z` along `k`. This is what lets the
sheaf property of `Mor(z, z)` be applied to a band section. -/
private lemma pullbackFiberHom_fiberHom [p.IsFibered] (a : Band p V) {W Z : 𝒞} (z : p.Fiber W)
    (h : W ⟶ V) (k : Z ⟶ W) :
    pullbackFiberHom (a.fiberHom z h) k = a.fiberHom (pullbackFiber p z k) (k ≫ h) := by
  refine (pullbackFiberHom_uniq (a.fiberHom z h) k _ ?_).symm
  simp only [fiberInclusion_map_fiberHom]
  refine a.natural _ _ (IsPreFibered.pullbackMap z.2 k) ?_
  exact map_comp_eqToHom k _ inferInstance (pullbackFiber p z k).2 z.2 h

/-- **Clause (1) of Stacks 0CJY**: the comparison is multiplicative. -/
private lemma fiberHom_mul (a b : Band p V) {W : 𝒞} (z : p.Fiber W) (h : W ⟶ V) :
    (a * b).fiberHom z h = a.fiberHom z h ≫ b.fiberHom z h :=
  Fiber.hom_ext rfl

/-- Conjugation by an isomorphism of the fibre carries the comparison at `z` to the comparison at
`z'`. -/
private lemma fiberHom_conj (a : Band p V) {W : 𝒞} {z z' : p.Fiber W} (e : z ⟶ z') [IsIso e]
    (h : W ⟶ V) : a.fiberHom z' h = CategoryTheory.inv e ≫ a.fiberHom z h ≫ e := by
  rw [a.fiberHom_naturality e h, IsIso.inv_hom_id_assoc]

/-- Base change preserves being an isomorphism. -/
private lemma isIso_pullbackFiberHom [p.IsFibered] {W : 𝒞} {z z' : p.Fiber W} (φ : z ⟶ z')
    [IsIso φ] {Z : 𝒞} (b : Z ⟶ W) : IsIso (pullbackFiberHom φ b) :=
  ⟨pullbackFiberHom (CategoryTheory.inv φ) b, by
    rw [← pullbackFiberHom_comp, IsIso.hom_inv_id, pullbackFiberHom_id], by
    rw [← pullbackFiberHom_comp, IsIso.inv_hom_id, pullbackFiberHom_id]⟩

/-- The base change of the inverse is the inverse of the base change. -/
private lemma pullbackFiberHom_inv [p.IsFibered] {W : 𝒞} {z z' : p.Fiber W} (φ : z ⟶ z') [IsIso φ]
    {Z : 𝒞} (b : Z ⟶ W) :
    have := isIso_pullbackFiberHom φ b
    pullbackFiberHom (CategoryTheory.inv φ) b = CategoryTheory.inv (pullbackFiberHom φ b) := by
  have := isIso_pullbackFiberHom φ b
  refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
  rw [← pullbackFiberHom_comp, IsIso.hom_inv_id, pullbackFiberHom_id]

/-- **Clause (2) of Stacks 0CJY**: for a morphism `φ : x ⟶ y` of the fibre over `U` and an object
`g` of `𝒞/U`, the comparison at `y` on sections over `g` is the comparison at `x` conjugated by the
base change of `φ` along `g`. -/
private lemma fiberHom_pullbackFiber_conj [p.IsFibered] {U : 𝒞} {x y : p.Fiber U} (φ : x ⟶ y)
    [IsIso φ] (g : Over U) (a : Band p g.left) :
    a.fiberHom (pullbackFiber p y g.hom) (𝟙 g.left) =
      pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
        a.fiberHom (pullbackFiber p x g.hom) (𝟙 g.left) ≫ pullbackFiberHom φ g.hom := by
  have := isIso_pullbackFiberHom φ g.hom
  rw [pullbackFiberHom_inv φ g.hom]
  exact a.fiberHom_conj (pullbackFiberHom φ g.hom) (𝟙 g.left)

/-- **The comparisons of Stacks 0CJY agree over varying base object.** The comparison attached to
`y` over `U`, read on sections over `g : Over U`, is the comparison attached to the chosen pullback
`y|_g` over `g.left`, read on sections over the identity of `g.left`, conjugated by the contraction
of the chosen pullback of `y|_g` along that identity.

Both sides are a value of the same band section over `g.left`; the identity is the naturality of
that section at the isomorphism `Functor.pullbackFiberIdIso`. This is the compatibility of the
local comparisons "over varying `U`" that the source's proof of Stacks 0CJY leaves out. -/
private lemma fiberHom_pullbackFiber_base [p.IsFibered] {U : 𝒞} (y : p.Fiber U) (g : Over U)
    (a : Band p g.left) :
    a.fiberHom (pullbackFiber p y g.hom) (𝟙 g.left) =
      (pullbackFiberIdIso (pullbackFiber p y g.hom)).inv ≫
        a.fiberHom (pullbackFiber p (pullbackFiber p y g.hom) (𝟙 g.left)) (𝟙 g.left) ≫
          (pullbackFiberIdIso (pullbackFiber p y g.hom)).hom := by
  have h := a.fiberHom_conj (pullbackFiberIdIso (pullbackFiber p y g.hom)).hom (𝟙 g.left)
  rwa [IsIso.Iso.inv_hom] at h

/-! ### Rigidity: a band section is determined by one of its values -/

section Rigidity

variable (hp : p.IsFiberedInGroupoids)

include hp in
/-- Two band sections agreeing at `w` agree at the source of every morphism into `w`: every
morphism of a category fibred in groupoids is cartesian, so the value at the source is the unique
fill-in of the value at the target. -/
private lemma hom_eq_of_hom_eq {a b : Band p V} {w w' : 𝒮} (ζ : w' ⟶ w) (hw : p.obj w ⟶ V)
    (hw' : p.obj w' ⟶ V) (hcomp : p.map ζ ≫ hw = hw')
    (hab : a.hom w hw = b.hom w hw) : a.hom w' hw' = b.hom w' hw' := by
  have hc : p.IsStronglyCartesian (p.map ζ) ζ := hp.isStronglyCartesian ζ
  have hA := a.isHomLift (rfl : p.obj w' = p.obj w') hw'
  have hB := b.isHomLift (rfl : p.obj w' = p.obj w') hw'
  exact IsCartesian.ext p (p.map ζ) ζ _ _
    (by rw [a.natural hw' hw ζ hcomp, b.natural hw' hw ζ hcomp, hab])

include hp in
/-- `Band.hom_eq_of_hom_eq` in the shape a chain of morphisms uses it: the morphisms to `V` stay in
the canonical form `eqToHom _ ≫ (morphism of the base) ≫ t`. -/
private lemma hom_eq_of_hom_eq_base {a b : Band p V} {w w' : 𝒮} {W W' : 𝒞} (ζ : w' ⟶ w)
    (k : W' ⟶ W) (hζ : p.IsHomLift k ζ) (hw : p.obj w = W) (hw' : p.obj w' = W') (t : W ⟶ V)
    (hab : a.hom w (eqToHom hw ≫ t) = b.hom w (eqToHom hw ≫ t)) :
    a.hom w' (eqToHom hw' ≫ k ≫ t) = b.hom w' (eqToHom hw' ≫ k ≫ t) :=
  hom_eq_of_hom_eq hp ζ _ _ (map_comp_eqToHom k ζ hζ hw' hw t) hab

end Rigidity

section Injective

variable [p.IsFibered] (hp : p.IsFiberedInGroupoids) {J : GrothendieckTopology 𝒞}

include hp in
/-- **A band section over `V` is determined by its value at a single object of the fibre over
`V`**, so the comparison of Stacks 0CJY is injective on sections. Locally on `𝒞` every object over
`V` is isomorphic to a restriction of the given one — this is local connectedness — and a morphism
of a fibre is determined by its base changes along a covering because `Mor` is a sheaf. -/
private theorem eq_of_fiberHom_eq (hst : p.IsStack J) (hlc : p.LocallyConnected J) {V : 𝒞}
    (x : p.Fiber V) {a b : Band p V} (hab : a.fiberHom x (𝟙 V) = b.fiberHom x (𝟙 V)) : a = b := by
  have habh : a.hom x.1 (eqToHom x.2 ≫ 𝟙 V) = b.hom x.1 (eqToHom x.2 ≫ 𝟙 V) :=
    congrArg Fiber.fiberInclusion.map hab
  ext z hz
  -- Agreement propagates to the chosen restriction of `x` along `hz`.
  have hA := hom_eq_of_hom_eq_base hp (IsPreFibered.pullbackMap x.2 hz) hz inferInstance x.2
    (pullbackFiber p x hz).2 (𝟙 V) habh
  -- It suffices to prove the goal in the fibre over `p.obj z`.
  rw [hom_eq_fiberInclusion_map_fiberHom a, hom_eq_fiberInclusion_map_fiberHom b]
  refine congrArg _ ?_
  obtain ⟨S, hS, hiso⟩ := hlc z (pullbackFiber p x hz).1 rfl (pullbackFiber p x hz).2
  refine eq_of_pullbackFiberHom_locally_eq p (hst.isMorSheaf _ _ _) hS ?_
  intro W' k hk
  obtain ⟨z₁, y₁, ξ, υ, e, hξ, hυ, he⟩ := hiso k hk
  -- Down to `y₁` along `υ`, across to `z₁` along `e`, and then to the chosen restriction of `z`.
  have hB := hom_eq_of_hom_eq_base hp υ k hυ (pullbackFiber p x hz).2
    (IsHomLift.domain_eq p k υ) (hz ≫ 𝟙 V) hA
  have hC := hom_eq_of_hom_eq_base hp e.hom (𝟙 W') he (IsHomLift.domain_eq p k υ)
    (IsHomLift.domain_eq p (𝟙 W') e.hom) (k ≫ hz ≫ 𝟙 V) hB
  rw [Category.id_comp] at hC
  have hξs : p.IsStronglyCartesian k ξ := hp.isStronglyCartesian_homLift k ξ
  have hD := hom_eq_of_hom_eq_base hp
    (IsStronglyCartesian.map p k ξ (g := 𝟙 W') (f' := k) (Category.id_comp k).symm
      (IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj z = p.obj z)).2 k))
    (𝟙 W') inferInstance (IsHomLift.domain_eq p (𝟙 W') e.hom)
    (pullbackFiber p (Fiber.mk (rfl : p.obj z = p.obj z)) k).2 (k ≫ hz ≫ 𝟙 V) hC
  rw [pullbackFiberHom_fiberHom, pullbackFiberHom_fiberHom]
  refine Fiber.hom_ext ?_
  simp only [fiberInclusion_map_fiberHom]
  simp only [Category.comp_id, Category.id_comp] at hD
  exact hD

end Injective

end Band


namespace Band

/-- The conjugate of an endomorphism of `x` by an isomorphism `z ≅ x` of the fibre, which by
`conj_eq_conj_of_comm` does not depend on the isomorphism, only on its existence. -/
private noncomputable def canonConj {p : 𝒮 ⥤ 𝒞}
    (_habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α) {W : 𝒞} (z x : p.Fiber W)
    (h : Nonempty (z ≅ x)) (α : x ⟶ x) : z ⟶ z :=
  h.some.hom ≫ α ≫ h.some.inv

/-- `Band.canonConj` is computed by any isomorphism of the fibre. -/
private lemma canonConj_eq {p : 𝒮 ⥤ 𝒞}
    (habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α) {W : 𝒞} {z x : p.Fiber W}
    {h : Nonempty (z ≅ x)} (e : z ≅ x) (α : x ⟶ x) :
    canonConj habel z x h α = e.hom ≫ α ≫ e.inv :=
  conj_eq_conj_of_comm habel h.some.symm e.symm α

/-! ### Recognizing a band section by its values in the fibres

A band section is a family of endomorphisms of the objects of `𝒮` over `V`; reading it in the
fibres, `Band.fiberHom`, loses nothing, and the two conditions that a fibrewise family of
endomorphisms is a band section are compatibility with base change and commutation with the
morphisms of the fibres. `Band.exists_band_of_local` builds a band section from local fibrewise
data satisfying those two conditions, which is how both the surjectivity of the comparison and the
sheaf property of the band are proved. -/

section Fibrewise

variable {p : 𝒮 ⥤ 𝒞} {V : 𝒞}

attribute [local ext] ext
attribute [local simp] fiberInclusion_map_fiberHom hom_restrict

/-- A band section is determined by its values in the fibres. -/
private lemma ext_of_fiberHom {a b : Band p V}
    (h : ∀ ⦃W : 𝒞⦄ (z : p.Fiber W) (j : W ⟶ V), a.fiberHom z j = b.fiberHom z j) : a = b := by
  ext z j
  rw [hom_eq_fiberInclusion_map_fiberHom, hom_eq_fiberInclusion_map_fiberHom, h]

/-- The comparison of a restricted band section is the comparison of the section itself, at the
composed morphism to `V`. -/
private lemma fiberHom_restrict (a : Band p V) {V' : 𝒞} (k : V' ⟶ V) {W : 𝒞} (z : p.Fiber W)
    (j : W ⟶ V') : (a.restrict k).fiberHom z j = a.fiberHom z (j ≫ k) := by
  refine Fiber.hom_ext ?_
  simp

end Fibrewise

section Separated

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered] {J : GrothendieckTopology 𝒞} {V : 𝒞}

/-- **Two band sections whose values in the fibres agree locally agree.** The values of a band
section at the chosen restrictions of `z` are the base changes of its value at `z`, so this is the
separatedness half of condition (2) of Stacks 026F for `Mor(z, z)`. -/
private lemma fiberHom_eq_of_locally (hst : p.IsStack J) {a b : Band p V} {W : 𝒞} (z : p.Fiber W)
    (h : W ⟶ V) {R : Sieve W} (hR : R ∈ J W)
    (hab : ∀ ⦃W' : 𝒞⦄ (f : W' ⟶ W), R.arrows f →
      a.fiberHom (pullbackFiber p z f) (f ≫ h) = b.fiberHom (pullbackFiber p z f) (f ≫ h)) :
    a.fiberHom z h = b.fiberHom z h := by
  refine eq_of_pullbackFiberHom_locally_eq p (hst.isMorSheaf _ _ _) hR ?_
  intro W' f hf
  rw [pullbackFiberHom_fiberHom, pullbackFiberHom_fiberHom]
  exact hab f hf

/-- **A band section is determined by its restrictions to a covering sieve.** -/
private lemma eq_of_restrict_eq (hst : p.IsStack J) {S : Sieve V} (hS : S ∈ J V) {a b : Band p V}
    (h : ∀ ⦃W : 𝒞⦄ (f : W ⟶ V) (_ : S.arrows f), a.restrict f = b.restrict f) : a = b := by
  refine ext_of_fiberHom fun {W} z j => ?_
  refine fiberHom_eq_of_locally hst z j (J.pullback_stable j hS) ?_
  intro W' f hf
  have h1 := congrArg (fun c : Band p W' => c.fiberHom (pullbackFiber p z f) (𝟙 W'))
    (h (f ≫ j) hf)
  simpa [fiberHom_restrict] using h1

end Separated

/-! ### Base change along an identity -/

section IdBase

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered]

/-- **The canonical isomorphism `pullbackFiberIdIso` is natural**: base change along an identity
is, up to it, the morphism itself. The library states the compatibility of base change with a
composite of base morphisms, `CategoryTheory.Functor.pullbackFiberHom_comp_base`, but not this one
for the identity. -/
private lemma pullbackFiberHom_id_base {W : 𝒞} {y y' : p.Fiber W} (α : y ⟶ y') :
    pullbackFiberHom α (𝟙 W) ≫ (pullbackFiberIdIso y').hom = (pullbackFiberIdIso y).hom ≫ α := by
  refine Fiber.hom_ext ?_
  rw [Functor.map_comp, Functor.map_comp, pullbackFiberIdIso_hom_fac, pullbackFiberIdIso_hom_fac,
    pullbackFiberHom_fac]

/-- `Band.pullbackFiberHom_id_base` as a conjugation: base change along an identity is conjugation
by `CategoryTheory.Functor.pullbackFiberIdIso`. -/
private lemma eq_conj_pullbackFiberHom_id_base {W : 𝒞} (y : p.Fiber W) (α : y ⟶ y) :
    α = (pullbackFiberIdIso y).inv ≫ pullbackFiberHom α (𝟙 W) ≫ (pullbackFiberIdIso y).hom := by
  rw [pullbackFiberHom_id_base α]
  simp

end IdBase

/-! ### A fibrewise family of endomorphisms as a band section -/

section Fiberwise

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered] {V : 𝒞}

/-- **A fibrewise family of endomorphisms, compatible with base change and commuting with the
morphisms of the fibres, commutes with every morphism of `𝒮`.** A morphism `φ` of `𝒮` over
`k : W ⟶ T` factors as an isomorphism of the fibre over `W` followed by the chosen cartesian lift
of `k`, and the two hypotheses dispose of the two factors in turn. -/
private lemma comp_eq_of_fiberwise (hp : p.IsFiberedInGroupoids)
    (m : ∀ (W : 𝒞) (z : p.Fiber W), (W ⟶ V) → (z ⟶ z))
    (hmbase : ∀ (W Z : 𝒞) (z : p.Fiber W) (h : W ⟶ V) (k : Z ⟶ W),
      pullbackFiberHom (m W z h) k = m Z (pullbackFiber p z k) (k ≫ h))
    (hmnat : ∀ (W : 𝒞) (z z' : p.Fiber W) (e : z ⟶ z') (h : W ⟶ V),
      m W z h ≫ e = e ≫ m W z' h)
    {W T : 𝒞} (z : p.Fiber W) (y : p.Fiber T) (k : W ⟶ T) (φ : z.1 ⟶ y.1)
    (hφ : p.IsHomLift k φ) (h : T ⟶ V) :
    Fiber.fiberInclusion.map (m W z (k ≫ h)) ≫ φ =
      φ ≫ Fiber.fiberInclusion.map (m T y h) := by
  have hcart : p.IsStronglyCartesian k φ := hp.isStronglyCartesian_homLift k φ
  obtain ⟨χ, hχ⟩ : ∃ χ : z ≅ pullbackFiber p y k,
      Fiber.fiberInclusion.map χ.hom ≫ IsPreFibered.pullbackMap y.2 k = φ :=
    ⟨fiberIsoOfCartesian k φ (IsPreFibered.pullbackMap y.2 k) inferInstance
      (IsPreFibered.pullbackMap.IsCartesian y.2 k), fiberIsoOfCartesian_hom_fac _ _ _ _ _⟩
  calc Fiber.fiberInclusion.map (m W z (k ≫ h)) ≫ φ
      = Fiber.fiberInclusion.map (m W z (k ≫ h) ≫ χ.hom) ≫
          IsPreFibered.pullbackMap y.2 k := by
        rw [Functor.map_comp, Category.assoc, hχ]
    _ = Fiber.fiberInclusion.map (χ.hom ≫ m W (pullbackFiber p y k) (k ≫ h)) ≫
          IsPreFibered.pullbackMap y.2 k := by
        rw [hmnat]
    _ = Fiber.fiberInclusion.map χ.hom ≫
          Fiber.fiberInclusion.map (pullbackFiberHom (m T y h) k) ≫
          IsPreFibered.pullbackMap y.2 k := by
        rw [← hmbase, Functor.map_comp, Category.assoc]
    _ = φ ≫ Fiber.fiberInclusion.map (m T y h) := by
        rw [pullbackFiberHom_fac, ← Category.assoc, hχ]

/-- **A fibrewise family of endomorphisms is a band section**, as soon as it is compatible with
base change and commutes with the morphisms of the fibres. -/
private lemma exists_band_of_fiberwise (hp : p.IsFiberedInGroupoids)
    (m : ∀ (W : 𝒞) (z : p.Fiber W), (W ⟶ V) → (z ⟶ z))
    (hmbase : ∀ (W Z : 𝒞) (z : p.Fiber W) (h : W ⟶ V) (k : Z ⟶ W),
      pullbackFiberHom (m W z h) k = m Z (pullbackFiber p z k) (k ≫ h))
    (hmnat : ∀ (W : 𝒞) (z z' : p.Fiber W) (e : z ⟶ z') (h : W ⟶ V),
      m W z h ≫ e = e ≫ m W z' h) :
    ∃ a : Band p V, ∀ (W : 𝒞) (z : p.Fiber W) (h : W ⟶ V), a.fiberHom z h = m W z h := by
  refine ⟨{ hom := fun z h => Fiber.fiberInclusion.map (m (p.obj z) (Fiber.mk rfl) h)
            map_hom := ?_
            natural := ?_ }, ?_⟩
  · intro z h
    have := (m (p.obj z) (Fiber.mk (rfl : p.obj z = p.obj z)) h).2
    exact (IsHomLift.eq_of_isHomLift p (𝟙 (p.obj z)) _).symm
  · intro x y hx hy φ hφ
    obtain rfl := hφ
    exact comp_eq_of_fiberwise hp m hmbase hmnat (Fiber.mk rfl) (Fiber.mk rfl) (p.map φ) φ
      (IsHomLift.of_fac p (p.map φ) φ rfl rfl (by simp)) hy
  · intro W z h
    obtain ⟨z, rfl⟩ := z
    refine Fiber.hom_ext ?_
    simp only [fiberInclusion_map_fiberHom, eqToHom_refl, Category.id_comp]
    rfl

end Fiberwise

/-! ### Constructing a band section from local data -/

section Construction

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered] {J : GrothendieckTopology 𝒞} {V : 𝒞}

/-- **A band section from local fibrewise data.** Let `P h z β` be a property of an endomorphism
`β` of an object `z` of the fibre over `W`, relative to a morphism `h : W ⟶ V`, which is preserved
by base change (`hbase`), transported by the isomorphisms of a fibre (`hconj`), determines `β`
(`huniq`), and holds locally on `𝒞`, for some `β`, at every `z` and every `h` (`hlocal`). Then
there is a band section over `V` whose value at `z` and `h` is the endomorphism satisfied by
`P h z` whenever there is one.

The values are glued from the local data by the sheaf property of `Mor(z, z)`,
`CategoryTheory.Functor.exists_fiberHom_of_locally`, and the two hypotheses of
`Band.exists_band_of_fiberwise` are then verified for the glued family by separatedness, the local
data being canonical. -/
private theorem exists_band_of_local (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (P : ∀ ⦃W : 𝒞⦄, (W ⟶ V) → ∀ z : p.Fiber W, (z ⟶ z) → Prop)
    (hbase : ∀ ⦃W Z : 𝒞⦄ (h : W ⟶ V) (z : p.Fiber W) (β : z ⟶ z) (k : Z ⟶ W),
      P h z β → P (k ≫ h) (pullbackFiber p z k) (pullbackFiberHom β k))
    (hconj : ∀ ⦃W : 𝒞⦄ (h : W ⟶ V) {z z' : p.Fiber W} (β : z ⟶ z) (e : z ≅ z'),
      P h z β → P h z' (e.inv ≫ β ≫ e.hom))
    (huniq : ∀ ⦃W : 𝒞⦄ (h : W ⟶ V) (z : p.Fiber W) (β β' : z ⟶ z), P h z β → P h z β' → β = β')
    (hlocal : ∀ (W : 𝒞) (z : p.Fiber W) (h : W ⟶ V), ∃ R ∈ J W,
      ∀ (W' : 𝒞) (f : W' ⟶ W), R.arrows f → ∃ β, P (f ≫ h) (pullbackFiber p z f) β) :
    ∃ a : Band p V,
      ∀ ⦃W : 𝒞⦄ (z : p.Fiber W) (h : W ⟶ V) (β : z ⟶ z), P h z β → a.fiberHom z h = β := by
  -- `P` depends on the morphism to `V` only through its value.
  have hPcongr : ∀ (W : 𝒞) (h h' : W ⟶ V) (z : p.Fiber W) (β : z ⟶ z), h = h' →
      P h z β → P h' z β := by
    intro W h h' z β e
    subst e
    exact id
  -- Glue the local data at every object of every fibre.
  have hglue : ∀ (W : 𝒞) (z : p.Fiber W) (h : W ⟶ V), ∃ β : z ⟶ z, ∃ R ∈ J W,
      ∀ (W' : 𝒞) (f : W' ⟶ W), R.arrows f →
        P (f ≫ h) (pullbackFiber p z f) (pullbackFiberHom β f) := by
    intro W z h
    obtain ⟨R, hR, hex⟩ := hlocal W z h
    choose θ hθ using hex
    have hcompat : ∀ ⦃V' W' : 𝒞⦄ (f : V' ⟶ W) (hf : R.arrows f) (γ : W' ⟶ V') (b : W' ⟶ W)
        (hb : γ ≫ f = b) (hb' : R.arrows b),
        θ W' b hb' = (pullbackFiberCompIso' z f γ b hb).inv ≫
          pullbackFiberHom (θ V' f hf) γ ≫ (pullbackFiberCompIso' z f γ b hb).hom := by
      intro V' W' f hf γ b hb hb'
      refine huniq (b ≫ h) _ _ _ (hθ W' b hb') ?_
      refine hPcongr _ _ _ _ _ (by rw [← hb, Category.assoc]) ?_
      exact hconj (γ ≫ f ≫ h) _ (pullbackFiberCompIso' z f γ b hb)
        (hbase (f ≫ h) _ _ γ (hθ V' f hf))
    obtain ⟨β, hβ⟩ := exists_fiberHom_of_locally p (hst.isMorSheaf _ _ _) hR
      (fun {W'} f hf => θ W' f hf) hcompat
    exact ⟨β, R, hR, fun W' f hf => by rw [hβ f hf]; exact hθ W' f hf⟩
  choose loc R hR hlocP using hglue
  -- The glued value is the unique one satisfying `P`, when `P` holds globally.
  have hdet : ∀ (W : 𝒞) (z : p.Fiber W) (h : W ⟶ V) (β : z ⟶ z), P h z β → loc W z h = β := by
    intro W z h β hβ
    refine eq_of_pullbackFiberHom_locally_eq p (hst.isMorSheaf _ _ _) (hR W z h) ?_
    intro W' f hf
    exact huniq (f ≫ h) _ _ _ (hlocP W z h W' f hf) (hbase h z β f hβ)
  -- The glued values are compatible with base change.
  have hlocbase : ∀ (W Z : 𝒞) (z : p.Fiber W) (h : W ⟶ V) (k : Z ⟶ W),
      pullbackFiberHom (loc W z h) k = loc Z (pullbackFiber p z k) (k ≫ h) := by
    intro W Z z h k
    refine eq_of_pullbackFiberHom_locally_eq p (hst.isMorSheaf _ _ _)
      (J.intersection_covering (J.pullback_stable k (hR W z h))
        (hR Z (pullbackFiber p z k) (k ≫ h))) ?_
    intro W'' γ hγ
    obtain ⟨hγ1, hγ2⟩ := hγ
    have h1 := hlocP W z h W'' (γ ≫ k) hγ1
    rw [pullbackFiberHom_comp_base (loc W z h) k γ] at h1
    have h2 := hconj ((γ ≫ k) ≫ h) _ (pullbackFiberCompIso z k γ).symm h1
    simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] at h2
    exact huniq _ _ _ _ h2 (hlocP Z (pullbackFiber p z k) (k ≫ h) W'' γ hγ2)
  -- The glued values commute with the morphisms of the fibres.
  have hlocnat : ∀ (W : 𝒞) (z z' : p.Fiber W) (e : z ⟶ z') (h : W ⟶ V),
      loc W z h ≫ e = e ≫ loc W z' h := by
    intro W z z' e h
    have : IsGroupoid (p.Fiber W) := hp.fiber_isGroupoid W
    have : IsIso e := inferInstance
    refine eq_of_pullbackFiberHom_locally_eq p (hst.isMorSheaf _ _ _)
      (J.intersection_covering (hR W z h) (hR W z' h)) ?_
    intro W' f hf
    obtain ⟨hf1, hf2⟩ := hf
    have : IsIso (pullbackFiberHom e f) := isIso_pullbackFiberHom e f
    have h4 := huniq (f ≫ h) _ _ _ (hlocP W z' h W' f hf2)
      (hconj (f ≫ h) _ (asIso (pullbackFiberHom e f)) (hlocP W z h W' f hf1))
    rw [pullbackFiberHom_comp, pullbackFiberHom_comp, h4]
    simp
  obtain ⟨a, ha⟩ := exists_band_of_fiberwise hp loc hlocbase hlocnat
  exact ⟨a, fun {W} z h β hβ => by rw [ha W z h]; exact hdet W z h β hβ⟩

end Construction

/-! ### Local connectedness in terms of chosen pullbacks -/

section LocallyConnected

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered] {J : GrothendieckTopology 𝒞}

/-- **Local connectedness, read at the chosen pullbacks.** For two objects `z`, `x'` of the fibre
over `W` there is a covering sieve of `W` along every member `f` of which the chosen pullbacks
`f^* z` and `f^* x'` are isomorphic in the fibre.

`CategoryTheory.Functor.LocallyConnected` supplies *some* restrictions `z₁`, `y₁` of `z` and `x'`
together with an isomorphism between them; every morphism of a category fibred in groupoids is
strongly cartesian, so `z₁` and `y₁` are compared with the chosen pullbacks by
`CategoryTheory.Functor.fiberIsoOfCartesian`. -/
private lemma exists_iso_pullbackFiber_locally (hp : p.IsFiberedInGroupoids)
    (hlc : p.LocallyConnected J) {W : 𝒞} (z x' : p.Fiber W) :
    ∃ R ∈ J W, ∀ ⦃W' : 𝒞⦄ (f : W' ⟶ W), R.arrows f →
      Nonempty (pullbackFiber p z f ≅ pullbackFiber p x' f) := by
  obtain ⟨S, hS, hiso⟩ := hlc z.1 x'.1 z.2 x'.2
  refine ⟨S, hS, ?_⟩
  intro W' f hf
  obtain ⟨z₁, y₁, ξ, υ, e, hξ, hυ, he⟩ := hiso f hf
  have := hξ
  have := hυ
  have hξc : p.IsStronglyCartesian f ξ := hp.isStronglyCartesian_homLift f ξ
  have hυc : p.IsStronglyCartesian f υ := hp.isStronglyCartesian_homLift f υ
  have i₁ : pullbackFiber p z f ≅ (Fiber.mk (IsHomLift.domain_eq p f ξ) : p.Fiber W') :=
    fiberIsoOfCartesian f (IsPreFibered.pullbackMap z.2 f) ξ
      (IsPreFibered.pullbackMap.IsCartesian _ _) inferInstance
  have i₂ : (Fiber.mk (IsHomLift.domain_eq p f υ) : p.Fiber W') ≅ pullbackFiber p x' f :=
    fiberIsoOfCartesian f υ (IsPreFibered.pullbackMap x'.2 f) inferInstance
      (IsPreFibered.pullbackMap.IsCartesian _ _)
  have e' : (Fiber.mk (IsHomLift.domain_eq p f ξ) : p.Fiber W') ≅
      (Fiber.mk (IsHomLift.domain_eq p f υ) : p.Fiber W') := Fiber.isoMk e he
  exact ⟨i₁ ≪≫ e' ≪≫ i₂⟩

end LocallyConnected

/-! ### The comparison is surjective, the band is a sheaf, and the band is small -/

section Open

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered] {J : GrothendieckTopology 𝒞}

/-- **The comparison of Stacks 0CJY is surjective on sections.** Given an endomorphism `α` of an
object `x` of the fibre over `V`, there is a band section over `V` whose value at `x` is `α`: for
every object `z` over `V`, local connectedness gives a covering of `p z` along which `z` becomes
isomorphic to a restriction of `x`, conjugating the restriction of `α` gives an endomorphism of
each of those restrictions of `z` — one not depending on the conjugating isomorphism, by
`conj_eq_conj_of_comm` — and those glue by the sheaf property of `Mor(z, z)`,
`CategoryTheory.Functor.exists_fiberHom_of_locally`. -/
private theorem exists_band_fiberHom_eq (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (hlc : p.LocallyConnected J)
    (habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α)
    {V : 𝒞} (x : p.Fiber V) (α : x ⟶ x) : ∃ a : Band p V, a.fiberHom x (𝟙 V) = α := by
  -- `β` is the conjugate of the base change of `α` by *some* — hence by every — isomorphism
  -- identifying `z` with the chosen pullback of `x`.
  set P : ∀ ⦃W : 𝒞⦄, (W ⟶ V) → ∀ z : p.Fiber W, (z ⟶ z) → Prop :=
    fun ⦃W⦄ h z β => ∃ e : z ≅ pullbackFiber p x h,
      β = e.hom ≫ pullbackFiberHom α h ≫ e.inv with hPdef
  have hbase : ∀ ⦃W Z : 𝒞⦄ (h : W ⟶ V) (z : p.Fiber W) (β : z ⟶ z) (k : Z ⟶ W),
      P h z β → P (k ≫ h) (pullbackFiber p z k) (pullbackFiberHom β k) := by
    rintro W Z h z β k ⟨e, rfl⟩
    refine ⟨pullbackFiberIso e k ≪≫ pullbackFiberCompIso x h k, ?_⟩
    have hc := pullbackFiberHom_comp_base (p := p) α h k
    simp only [Iso.trans_hom, Iso.trans_inv, pullbackFiberIso_hom, pullbackFiberIso_inv,
      pullbackFiberHom_comp, hc, Category.assoc]
    simp [← Category.assoc]
  have hconj : ∀ ⦃W : 𝒞⦄ (h : W ⟶ V) {z z' : p.Fiber W} (β : z ⟶ z) (e : z ≅ z'),
      P h z β → P h z' (e.inv ≫ β ≫ e.hom) := by
    rintro W h z z' β e ⟨ε, rfl⟩
    exact ⟨e.symm ≪≫ ε, by simp⟩
  have huniq : ∀ ⦃W : 𝒞⦄ (h : W ⟶ V) (z : p.Fiber W) (β β' : z ⟶ z),
      P h z β → P h z β' → β = β' := by
    rintro W h z β β' ⟨e, rfl⟩ ⟨f, rfl⟩
    exact conj_eq_conj_of_comm habel e.symm f.symm (pullbackFiberHom α h)
  have hlocal : ∀ (W : 𝒞) (z : p.Fiber W) (h : W ⟶ V), ∃ R ∈ J W,
      ∀ (W' : 𝒞) (f : W' ⟶ W), R.arrows f → ∃ β, P (f ≫ h) (pullbackFiber p z f) β := by
    intro W z h
    obtain ⟨R, hR, hiso⟩ := exists_iso_pullbackFiber_locally hp hlc z (pullbackFiber p x h)
    refine ⟨R, hR, ?_⟩
    intro W' f hf
    obtain ⟨e⟩ := hiso f hf
    exact ⟨_, ⟨e ≪≫ pullbackFiberCompIso x h f, rfl⟩⟩
  obtain ⟨a, ha⟩ := exists_band_of_local hp hst P hbase hconj huniq hlocal
  exact ⟨a, ha x (𝟙 V) α ⟨(pullbackFiberIdIso x).symm, eq_conj_pullbackFiberHom_id_base x α⟩⟩

/-- **The band is a sheaf.** A family of band sections over the members of a covering sieve of `V`,
compatible with restriction, comes from a unique band section over `V`: at an object `z` over `V`
the values of the family give a family of endomorphisms of the restrictions of `z` along the
covering sieve of `p z` obtained by base change, and that family glues by the sheaf property of
`Mor(z, z)`. Only the stack condition is used, not the two local conditions on a gerbe. -/
private theorem existsUnique_band_of_compatible (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    {V : 𝒞} {S : Sieve V} (hS : S ∈ J V) (t : ∀ ⦃W : 𝒞⦄ (f : W ⟶ V), S.arrows f → Band p W)
    (ht : ∀ ⦃W W' : 𝒞⦄ (f : W ⟶ V) (hf : S.arrows f) (γ : W' ⟶ W) (hγ : S.arrows (γ ≫ f)),
      (t f hf).restrict γ = t (γ ≫ f) hγ) :
    ∃! a : Band p V, ∀ ⦃W : 𝒞⦄ (f : W ⟶ V) (hf : S.arrows f), a.restrict f = t f hf := by
  -- `β` is the value at `z` of the member of the family at `h`, when `h` is in the sieve.
  set P : ∀ ⦃W : 𝒞⦄, (W ⟶ V) → ∀ z : p.Fiber W, (z ⟶ z) → Prop :=
    fun ⦃W⦄ h z β => ∃ hh : S.arrows h, β = (t h hh).fiberHom z (𝟙 W) with hPdef
  have hbase : ∀ ⦃W Z : 𝒞⦄ (h : W ⟶ V) (z : p.Fiber W) (β : z ⟶ z) (k : Z ⟶ W),
      P h z β → P (k ≫ h) (pullbackFiber p z k) (pullbackFiberHom β k) := by
    rintro W Z h z β k ⟨hh, rfl⟩
    refine ⟨S.downward_closed hh k, ?_⟩
    rw [pullbackFiberHom_fiberHom, ← ht h hh k (S.downward_closed hh k), fiberHom_restrict]
    simp
  have hconj : ∀ ⦃W : 𝒞⦄ (h : W ⟶ V) {z z' : p.Fiber W} (β : z ⟶ z) (e : z ≅ z'),
      P h z β → P h z' (e.inv ≫ β ≫ e.hom) := by
    rintro W h z z' β e ⟨hh, rfl⟩
    refine ⟨hh, ?_⟩
    rw [fiberHom_conj (t h hh) e.hom (𝟙 W)]
    simp
  have huniq : ∀ ⦃W : 𝒞⦄ (h : W ⟶ V) (z : p.Fiber W) (β β' : z ⟶ z),
      P h z β → P h z β' → β = β' := by
    rintro W h z β β' ⟨hh, rfl⟩ ⟨hh', rfl⟩
    rfl
  have hlocal : ∀ (W : 𝒞) (z : p.Fiber W) (h : W ⟶ V), ∃ R ∈ J W,
      ∀ (W' : 𝒞) (f : W' ⟶ W), R.arrows f → ∃ β, P (f ≫ h) (pullbackFiber p z f) β := by
    intro W z h
    exact ⟨S.pullback h, J.pullback_stable h hS, fun W' f hf => ⟨_, ⟨hf, rfl⟩⟩⟩
  obtain ⟨a, ha⟩ := exists_band_of_local hp hst P hbase hconj huniq hlocal
  have hA : ∀ ⦃W : 𝒞⦄ (f : W ⟶ V) (hf : S.arrows f), a.restrict f = t f hf := by
    intro W f hf
    refine ext_of_fiberHom fun {W'} z j => ?_
    rw [fiberHom_restrict]
    refine ha z (j ≫ f) _ ⟨S.downward_closed hf j, ?_⟩
    rw [← ht f hf j (S.downward_closed hf j), fiberHom_restrict]
    simp
  have huq : ∀ b : Band p V,
      (∀ ⦃W : 𝒞⦄ (f : W ⟶ V) (hf : S.arrows f), b.restrict f = t f hf) → b = a := by
    intro b hb
    refine eq_of_restrict_eq hst hS ?_
    intro W f hf
    rw [hb f hf, hA f hf]
  exact ⟨a, hA, huq⟩

/-- **A band section over `V` is determined by a family of values indexed by a covering sieve.**
Local nonemptiness gives a covering sieve of `V` all of whose members carry an object of `𝒮`, and
over such an object a band section is determined by its single value there, by
`Band.eq_of_fiberHom_eq`. So the band embeds into a product, indexed by the arrows of that sieve —
a type in `Type (max u₁ v₁)` — of endomorphism groups of objects of `𝒮`, which are types in
`Type v₂`. This is the whole smallness content of Stacks 0CJY. -/
private theorem exists_injection_band (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (hne : p.LocallyNonempty J) (hlc : p.LocallyConnected J) (V : 𝒞) :
    ∃ (ι : Type (max u₁ v₁)) (κ : ι → Type v₂) (F : Band p V → ∀ i, κ i),
      Function.Injective F := by
  classical
  obtain ⟨S, hS, hobj⟩ := hne V
  refine ⟨Σ W : 𝒞, {g : W ⟶ V // S.arrows g},
    fun i => ((hobj i.2.1 i.2.2).some ⟶ (hobj i.2.1 i.2.2).some),
    fun a i => a.fiberHom (hobj i.2.1 i.2.2).some i.2.1, ?_⟩
  intro a b hab
  refine eq_of_restrict_eq hst hS fun {W} f hf => ?_
  refine eq_of_fiberHom_eq hp hst hlc (hobj f hf).some ?_
  have := congrFun hab ⟨W, f, hf⟩
  rw [fiberHom_restrict, fiberHom_restrict, Category.id_comp]
  exact this

/-- **The band is small**, with no hypothesis on the universes: the band sections over `V` are a
type in `Type (max u₂ v₁ v₂)`, being indexed by the objects of `𝒮` over `V`, and they are in
bijection with a type in `Type (max u₁ v₁ v₂)`, where the objects of `𝒮` no longer appear. -/
private theorem small_band (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (hne : p.LocallyNonempty J) (hlc : p.LocallyConnected J) (V : 𝒞) :
    Small.{max u₁ v₁ v₂} (Band p V) := by
  obtain ⟨ι, κ, F, hF⟩ := exists_injection_band hp hst hne hlc V
  exact small_of_injective hF

/-- **The band is small in the universe of the morphisms of `𝒮`**, under the smallness hypothesis
`UnivLE.{max u₁ v₁, v₂}`. Without it the conclusion is false: `Type 0`-many copies of a nontrivial
`ℤ/2`-gerbe give a band whose sections over the top object have cardinality `2 ^ |Type 0|`, which
is the cardinality of no `Type 0`. -/
private theorem small_band_of_univLE [UnivLE.{max u₁ v₁, v₂}] (hp : p.IsFiberedInGroupoids)
    (hst : p.IsStack J) (hne : p.LocallyNonempty J) (hlc : p.LocallyConnected J) (V : 𝒞) :
    Small.{v₂} (Band p V) := by
  obtain ⟨ι, κ, F, hF⟩ := exists_injection_band hp hst hne hlc V
  exact small_of_injective hF

end Open

/-! ### The band as a sheaf of abelian groups on the base -/

section Assembly

open Limits

universe w

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered] {J : GrothendieckTopology 𝒞}

/-- Restriction of band sections along `k : V' ⟶ V`, as a homomorphism of monoids. -/
private def restrictMonoidHom {V V' : 𝒞} (k : V' ⟶ V) : Band p V →* Band p V' where
  toFun a := a.restrict k
  map_one' := restrict_one k
  map_mul' a b := restrict_mul a b k

/-- **The comparison is natural in the object of `𝒞/U`**: restricting a band section along an
arrow of `𝒞/U` corresponds to restricting a section of `Mor(x, x)`. -/
private lemma fiberHom_morRestrict {U : 𝒞} (x : p.Fiber U) {g g' : Over U} (k : g' ⟶ g)
    (a : Band p g.left) :
    (a.restrict k.left).fiberHom (pullbackFiber p x g'.hom) (𝟙 g'.left) =
      morRestrict p x x k (a.fiberHom (pullbackFiber p x g.hom) (𝟙 g.left)) := by
  rw [morRestrict_eq_pullbackFiberHom, pullbackFiberHom_fiberHom, fiberHom_restrict,
    Category.id_comp, Category.comp_id]
  have h := a.fiberHom_conj (pullbackFiberCompIso' x g.hom k.left g'.hom (Over.w k)).hom k.left
  simpa using h

variable (hp : p.IsFiberedInGroupoids)
  (habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α)

include hp habel

/-- **The band as a presheaf of commutative groups on `𝒞`.** Its sections over `V` are the band
sections over `V`, carried into `Type w` along `hsm`; the group law is composition, commutative by
`Band.mul_comm`, and the restriction maps are `Band.restrict`. -/
private noncomputable def bandPresheaf (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) :
    𝒞ᵒᵖ ⥤ CommGrpCat.{w} :=
  letI : ∀ V : 𝒞, Small.{w} (Band p V) := hsm
  letI : ∀ V : 𝒞, CommGroup (Band p V) := fun _ => commGroup habel hp
  { obj := fun V => CommGrpCat.of (Shrink.{w} (Band p V.unop))
    map := fun {V V'} k => CommGrpCat.ofHom
      ((Shrink.mulEquiv).symm.toMonoidHom.comp
        ((restrictMonoidHom k.unop).comp (Shrink.mulEquiv).toMonoidHom))
    map_id := fun V => by
      ext a
      simp [restrictMonoidHom, restrict_id]
    map_comp := fun k k' => by
      ext a
      simp [restrictMonoidHom, restrict_restrict] }

/-- The sections of the band presheaf over `V` are the band sections over `V`. -/
private noncomputable def bandSections (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) (V : 𝒞) :
    ToType ((bandPresheaf hp habel hsm).obj (op V)) ≃ Band p V :=
  letI : Small.{w} (Band p V) := hsm V
  (equivShrink (Band p V)).symm

omit [p.IsFibered] in
/-- The restriction maps of the band presheaf are `Band.restrict`. -/
private lemma bandSections_map (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) {V V' : 𝒞} (k : V' ⟶ V)
    (a : ToType ((bandPresheaf hp habel hsm).obj (op V))) :
    bandSections hp habel hsm V' ((bandPresheaf hp habel hsm).map k.op a) =
      (bandSections hp habel hsm V a).restrict k := by
  simp [bandSections, bandPresheaf, restrictMonoidHom]

omit [p.IsFibered] in
/-- The group law of the band presheaf is composition of band sections. -/
private lemma bandSections_mul (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) (V : 𝒞)
    (a b : ToType ((bandPresheaf hp habel hsm).obj (op V))) :
    bandSections hp habel hsm V (a * b) =
      bandSections hp habel hsm V a * bandSections hp habel hsm V b := by
  unfold bandSections
  exact equivShrink_symm_mul a b

/-- **The band presheaf is a sheaf**, by `Band.existsUnique_band_of_compatible`. -/
private theorem isSheaf_bandPresheaf (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) (hst : p.IsStack J)
    [ReflectsLimitsOfSize.{v₁, max v₁ u₁} (forget CommGrpCat.{w})] :
    Presheaf.IsSheaf J (bandPresheaf hp habel hsm) := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (forget CommGrpCat.{w}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  intro V S hS fam hfam
  rw [Presieve.compatible_iff_sieveCompatible] at hfam
  have hrestr : ∀ ⦃W W' : 𝒞⦄ (f : W ⟶ V) (hf : S.arrows f) (γ : W' ⟶ W)
      (hγ : S.arrows (γ ≫ f)),
      (bandSections hp habel hsm W (fam f hf)).restrict γ =
        bandSections hp habel hsm W' (fam (γ ≫ f) hγ) := by
    intro W W' f hf γ hγ
    rw [← bandSections_map hp habel hsm γ (fam f hf)]
    congr 1
    exact (hfam f γ hf).symm
  obtain ⟨a, ha, hauniq⟩ := existsUnique_band_of_compatible hp hst hS
    (fun {W} f hf => bandSections hp habel hsm W (fam f hf)) hrestr
  refine ⟨(bandSections hp habel hsm V).symm a, ?_, ?_⟩
  · intro W f hf
    apply (bandSections hp habel hsm W).injective
    have h1 := bandSections_map hp habel hsm f ((bandSections hp habel hsm V).symm a)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.trans (ha f hf)
  · intro b hb
    apply (bandSections hp habel hsm V).injective
    rw [Equiv.apply_symm_apply]
    refine hauniq (bandSections hp habel hsm V b) fun {W} f hf => ?_
    exact (bandSections_map hp habel hsm f b).symm.trans
      (congrArg (bandSections hp habel hsm W) (hb f hf))

/-- **The band, as a sheaf of abelian groups on `𝒞`.** This is the sheaf `𝒢` of Stacks 0CJY. -/
private noncomputable def bandSheaf (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) (hst : p.IsStack J)
    [ReflectsLimitsOfSize.{v₁, max v₁ u₁} (forget CommGrpCat.{w})] :
    Sheaf J CommGrpCat.{w} :=
  ⟨bandPresheaf hp habel hsm, isSheaf_bandPresheaf hp habel hsm hst⟩

/-! ### The comparison isomorphism `𝒢|_U ≅ Aut(x)` -/

variable (hst : p.IsStack J) (hlc : p.LocallyConnected J)

/-- The comparison of Stacks 0CJY on sections over an object `g` of `𝒞/U`: the value of a band
section at the chosen pullback of `x` along `g`. -/
private noncomputable def compFun (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) {U : 𝒞} (x : p.Fiber U)
    (g : Over U) :
    ToType ((bandPresheaf hp habel hsm).obj (op g.left)) →
      (pullbackFiber p x g.hom ⟶ pullbackFiber p x g.hom) :=
  fun a => (bandSections hp habel hsm g.left a).fiberHom (pullbackFiber p x g.hom) (𝟙 g.left)

/-- The comparison is multiplicative. -/
private lemma compFun_mul (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) {U : 𝒞} (x : p.Fiber U)
    (g : Over U) (a b : ToType ((bandPresheaf hp habel hsm).obj (op g.left))) :
    compFun hp habel hsm x g (a * b) = compFun hp habel hsm x g a ≫ compFun hp habel hsm x g b := by
  unfold compFun
  rw [bandSections_mul, fiberHom_mul]

/-- The comparison is natural in the object of `𝒞/U`. -/
private lemma compFun_map (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) {U : 𝒞} (x : p.Fiber U)
    {g g' : Over U} (k : g' ⟶ g) (a : ToType ((bandPresheaf hp habel hsm).obj (op g.left))) :
    compFun hp habel hsm x g' ((bandPresheaf hp habel hsm).map k.left.op a) =
      morRestrict p x x k (compFun hp habel hsm x g a) := by
  unfold compFun
  rw [bandSections_map]
  exact fiberHom_morRestrict x k _

include hst hlc

/-- **The comparison is bijective on sections**: injective by `Band.eq_of_fiberHom_eq` and
surjective by `Band.exists_band_fiberHom_eq`. -/
private lemma compFun_bijective (hsm : ∀ V : 𝒞, Small.{w} (Band p V)) {U : 𝒞} (x : p.Fiber U)
    (g : Over U) : Function.Bijective (compFun hp habel hsm x g) := by
  constructor
  · intro a b hab
    exact (bandSections hp habel hsm g.left).injective
      (eq_of_fiberHom_eq hp hst hlc (pullbackFiber p x g.hom) hab)
  · intro α
    obtain ⟨c, hc⟩ := exists_band_fiberHom_eq hp hst hlc habel (pullbackFiber p x g.hom) α
    refine ⟨(bandSections hp habel hsm g.left).symm c, ?_⟩
    unfold compFun
    rwa [Equiv.apply_symm_apply]

/-- **The comparison isomorphism `𝒢|_U ≅ Aut(x)` of Stacks 0CJY**, for a band valued in the
universe `v₂` of the morphisms of `𝒮`. Its components are `Band.compFun`, bijective by
`Band.compFun_bijective`, and its naturality is `Band.fiberHom_morRestrict`. -/
private noncomputable def bandCompIso (hsm : ∀ V : 𝒞, Small.{v₂} (Band p V)) {U : 𝒞}
    (x : p.Fiber U) :
    (Over.forget U).op ⋙ bandPresheaf hp habel hsm ⋙ forget CommGrpCat.{v₂} ≅
      p.morPresheaf x x :=
  NatIso.ofComponents
    (fun g => (Equiv.ofBijective _ (compFun_bijective hp habel hst hlc hsm x g.unop)).toIso)
    (by
      intro g g' k
      ext a
      exact compFun_map hp habel hsm x k.unop a)

/-- **The comparison isomorphism `𝒢|_U ≅ Aut(x)` of Stacks 0CJY**, for the band valued in
`Type (max u₁ v₁ v₂)`, where it exists with no hypothesis on the universes: the target is then the
universe lift of `Aut(x)`. -/
private noncomputable def bandCompIsoULift (hsm : ∀ V : 𝒞, Small.{max u₁ v₁ v₂} (Band p V))
    {U : 𝒞} (x : p.Fiber U) :
    (Over.forget U).op ⋙ bandPresheaf hp habel hsm ⋙ forget CommGrpCat.{max u₁ v₁ v₂} ≅
      p.morPresheaf x x ⋙ uliftFunctor.{max u₁ v₁, v₂} :=
  NatIso.ofComponents
    (fun g => ((Equiv.ofBijective _ (compFun_bijective hp habel hst hlc hsm x g.unop)).trans
      Equiv.ulift.symm).toIso)
    (by
      intro g g' k
      ext a
      exact ULift.ext (compFun_map hp habel hsm x k.unop a))

end Assembly

end Band

/-! ### Stacks 0CJY -/

open Limits

/-- **Stacks 0CJY, with no hypothesis on the universes.** Let `p : 𝒮 ⥤ 𝒞` be a gerbe over the site
`(𝒞, J)`: fibred in groupoids, a stack, locally nonempty and locally connected. Assume that for
every `U` and every object `x` of the fibre `𝒮_U` the sheaf of groups
`Aut(x) = Isom(x, x) = Mor(x, x)` on `𝒞/U` is abelian, that is that the endomorphisms of every
object of every fibre commute. Then there are

1. a sheaf `𝒢` of abelian groups on `𝒞`, and
2. for every `U` and every object `x` of `𝒮_U` an isomorphism `θ x : 𝒢|_U ≅ Aut(x)` of sheaves of
   groups on `𝒞/U`, that is an isomorphism of presheaves whose components are multiplicative,

such that for every `U` and every morphism `φ : x ⟶ y` of `𝒮_U` conjugation by `φ` carries `θ x` to
`θ y`: on sections over `g : V ⟶ U` one has `θ y a = φ|_V ∘ θ x a ∘ (φ|_V)⁻¹`.

`𝒢` is the band, `CategoryTheory.Gerbe.Band`, which lives in `Type (max u₁ v₁ v₂)` and not in the
universe `v₂` of `Aut(x)`; the isomorphism of (2) is therefore stated against the universe lift of
`Aut(x)`, which is what makes the statement true in every universe. See
`CategoryTheory.Gerbe.exists_sheaf_iso_morPresheaf_self` for the unlifted form, which needs
`UnivLE.{max u₁ v₁, v₂}` and is false without it. -/
@[stacks 0CJY]
public theorem exists_sheaf_iso_morPresheaf_self_uliftFunctor (p : 𝒮 ⥤ 𝒞)
    (J : GrothendieckTopology 𝒞) (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (hne : p.LocallyNonempty J) (hlc : p.LocallyConnected J)
    (habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α) :
    haveI : p.IsFibered := hp.isFibered
    haveI : ∀ U : 𝒞, IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid
    ∃ (𝒢 : Sheaf J CommGrpCat.{max u₁ v₁ v₂})
      (θ : ∀ (U : 𝒞) (x : p.Fiber U),
        (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{max u₁ v₁ v₂} ≅
          p.morPresheaf x x ⋙ uliftFunctor.{max u₁ v₁, v₂}),
      (∀ (U : 𝒞) (x : p.Fiber U) (g : Over U) (a b : 𝒢.obj.obj (op g.left)),
          ((θ U x).hom.app (op g) (a * b)).down =
            ((θ U x).hom.app (op g) a).down ≫ ((θ U x).hom.app (op g) b).down) ∧
        ∀ (U : 𝒞) (x y : p.Fiber U) (φ : x ⟶ y) (g : Over U) (a : 𝒢.obj.obj (op g.left)),
          ((θ U y).hom.app (op g) a).down =
            pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫ ((θ U x).hom.app (op g) a).down ≫
              pullbackFiberHom φ g.hom := by
  have : p.IsFibered := hp.isFibered
  have : ∀ U : 𝒞, IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid
  refine ⟨Band.bandSheaf hp habel (Band.small_band hp hst hne hlc) hst,
    fun U x => Band.bandCompIsoULift hp habel hst hlc (Band.small_band hp hst hne hlc) x,
    fun U x g a b => ?_, fun U x y φ g a => ?_⟩
  · exact Band.compFun_mul hp habel (Band.small_band hp hst hne hlc) x g a b
  · exact Band.fiberHom_pullbackFiber_conj φ g
      (Band.bandSections hp habel (Band.small_band hp hst hne hlc) g.left a)

/-- **Stacks 0CJY.** Let `p : 𝒮 ⥤ 𝒞` be a gerbe over the site `(𝒞, J)` whose automorphism sheaves
are abelian. Then there are a sheaf `𝒢` of abelian groups on `𝒞` and, for every `U` and every
object `x` of the fibre `𝒮_U`, an isomorphism `θ x : 𝒢|_U ≅ Aut(x)` of sheaves of groups on `𝒞/U`,
and these are compatible with conjugation.

The hypothesis `UnivLE.{max u₁ v₁, v₂}` is what makes `𝒢` exist in the universe `v₂` of the
morphisms of `𝒮`, and it cannot be dropped: `Type 0`-many copies of a nontrivial `ℤ/2`-gerbe give a
band whose sections at the top object have cardinality `2 ^ |Type 0|`, which is the cardinality of
no `Type 0`. Without it the statement still holds in the form
`CategoryTheory.Gerbe.exists_sheaf_iso_morPresheaf_self_uliftFunctor`, with `Aut(x)` lifted into
the universe `𝒢` is valued in. -/
@[stacks 0CJY]
public theorem exists_sheaf_iso_morPresheaf_self [UnivLE.{max u₁ v₁, v₂}] (p : 𝒮 ⥤ 𝒞)
    (J : GrothendieckTopology 𝒞) (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (hne : p.LocallyNonempty J) (hlc : p.LocallyConnected J)
    (habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α) :
    haveI : p.IsFibered := hp.isFibered
    haveI : ∀ U : 𝒞, IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid
    ∃ (𝒢 : Sheaf J CommGrpCat.{v₂})
      (θ : ∀ (U : 𝒞) (x : p.Fiber U),
        (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{v₂} ≅ p.morPresheaf x x),
      (∀ (U : 𝒞) (x : p.Fiber U) (g : Over U) (a b : 𝒢.obj.obj (op g.left)),
          (θ U x).hom.app (op g) (a * b) =
            (θ U x).hom.app (op g) a ≫ (θ U x).hom.app (op g) b) ∧
        ∀ (U : 𝒞) (x y : p.Fiber U) (φ : x ⟶ y) (g : Over U) (a : 𝒢.obj.obj (op g.left)),
          (θ U y).hom.app (op g) a =
            pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫ (θ U x).hom.app (op g) a ≫
              pullbackFiberHom φ g.hom := by
  have : p.IsFibered := hp.isFibered
  have : ∀ U : 𝒞, IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid
  refine ⟨Band.bandSheaf hp habel (Band.small_band_of_univLE hp hst hne hlc) hst,
    fun U x => Band.bandCompIso hp habel hst hlc (Band.small_band_of_univLE hp hst hne hlc) x,
    fun U x g a b => ?_, fun U x y φ g a => ?_⟩
  · exact Band.compFun_mul hp habel (Band.small_band_of_univLE hp hst hne hlc) x g a b
  · exact Band.fiberHom_pullbackFiber_conj φ g
      (Band.bandSections hp habel (Band.small_band_of_univLE hp hst hne hlc) g.left a)

/-- **Stacks 0CJY, with the compatibility of the comparisons over varying base object.** Let
`p : 𝒮 ⥤ 𝒞` be a gerbe over the site `(𝒞, J)` whose automorphism sheaves are abelian. Then there
are a sheaf `𝒢` of abelian groups on `𝒞` and, for every `U` and every object `x` of the fibre
`𝒮_U`, an isomorphism `θ x : 𝒢|_U ≅ Aut(x)` of sheaves of groups on `𝒞/U`, such that

1. each `θ x` is multiplicative on sections,
2. for `φ : x ⟶ y` in `𝒮_U`, conjugation by `φ` carries `θ x` to `θ y`, and
3. `θ x` read on sections over `g : Over U` is `θ (x|_g)` read on sections over the identity of
   `g.left`, conjugated by the contraction of the chosen pullback along that identity.

Clauses (1) and (2) are the conclusion of Stacks 0CJY as the source states it, so this is
`CategoryTheory.Gerbe.exists_sheaf_iso_morPresheaf_self_uliftFunctor` with (3) added. Clause (3)
is the compatibility of the local comparisons over varying `U` whose verification the source's
proof omits; for the band it is `CategoryTheory.Gerbe.Band.fiberHom_pullbackFiber_base`, the
naturality of a band section. It is what makes "the sheaf of abelian groups constructed in Stacks
0CJY" pin `𝒢` down well enough to use it as the coefficient sheaf of Stacks 0CK0, so that no
hypothesis of
`CategoryTheory.Gerbe.exists_band_nonempty_fiber_of_cohomology_vanishing` has to be assumed. -/
@[stacks 0CJY]
public theorem exists_sheaf_iso_morPresheaf_self_uliftFunctor_base (p : 𝒮 ⥤ 𝒞)
    (J : GrothendieckTopology 𝒞) (hp : p.IsFiberedInGroupoids) (hst : p.IsStack J)
    (hne : p.LocallyNonempty J) (hlc : p.LocallyConnected J)
    (habel : ∀ (U : 𝒞) (x : p.Fiber U) (α β : x ⟶ x), α ≫ β = β ≫ α) :
    haveI : p.IsFibered := hp.isFibered
    haveI : ∀ U : 𝒞, IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid
    ∃ (𝒢 : Sheaf J CommGrpCat.{max u₁ v₁ v₂})
      (θ : ∀ (U : 𝒞) (x : p.Fiber U),
        (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{max u₁ v₁ v₂} ≅
          p.morPresheaf x x ⋙ uliftFunctor.{max u₁ v₁, v₂}),
      (∀ (U : 𝒞) (x : p.Fiber U) (g : Over U) (a b : 𝒢.obj.obj (op g.left)),
          ((θ U x).hom.app (op g) (a * b)).down =
            ((θ U x).hom.app (op g) a).down ≫ ((θ U x).hom.app (op g) b).down) ∧
        (∀ (U : 𝒞) (x y : p.Fiber U) (φ : x ⟶ y) (g : Over U) (a : 𝒢.obj.obj (op g.left)),
          ((θ U y).hom.app (op g) a).down =
            pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫ ((θ U x).hom.app (op g) a).down ≫
              pullbackFiberHom φ g.hom) ∧
        ∀ (U : 𝒞) (x : p.Fiber U) (g : Over U) (a : 𝒢.obj.obj (op g.left)),
          ((θ U x).hom.app (op g) a).down =
            (pullbackFiberIdIso (pullbackFiber p x g.hom)).inv ≫
              ((θ g.left (pullbackFiber p x g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
                (pullbackFiberIdIso (pullbackFiber p x g.hom)).hom := by
  have : p.IsFibered := hp.isFibered
  have : ∀ U : 𝒞, IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid
  refine ⟨Band.bandSheaf hp habel (Band.small_band hp hst hne hlc) hst,
    fun U x => Band.bandCompIsoULift hp habel hst hlc (Band.small_band hp hst hne hlc) x,
    fun U x g a b => ?_, fun U x y φ g a => ?_, fun U x g a => ?_⟩
  · exact Band.compFun_mul hp habel (Band.small_band hp hst hne hlc) x g a b
  · exact Band.fiberHom_pullbackFiber_conj φ g
      (Band.bandSections hp habel (Band.small_band hp hst hne hlc) g.left a)
  · exact Band.fiberHom_pullbackFiber_base x g
      (Band.bandSections hp habel (Band.small_band hp hst hne hlc) g.left a)


end CategoryTheory.Gerbe

end
