module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity

/-!
# The restriction map on Chow cohomology is a map of `ℤ`-algebras

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : Y' ⟶ Y` be a
morphism of schemes locally of finite type over `S`. **Stacks 0B7F** asserts that the special case
of the restriction map of Stacks 0F9Z along `f` is a canonical map of `ℤ`-algebras

  `res : A^*(Y) ⟶ A^*(Y')`,   often written `f^*`.

The map itself, degreewise and on the graded groups, and the cap formula characterizing it are
`Stacks.Chow.chowCohomologyRestriction`, `Stacks.Chow.chowCohomologyTotalRestriction` and
`Stacks.Chow.chowCohomologyRestriction_cap` in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology`, where additivity is the
`AddMonoidHom` structure. What is added here is the remaining content of the tag — that the map
respects the multiplication and the unit of the ring structure on Chow cohomology — and the whole
tag at the Gysin system where it is unconditional.

The multiplication on `A^*(Y)` is composition of bivariant classes, Stacks 0B75, at the two
identity morphisms of `Y`; the unit is the identity class `1 ∈ A^0(Y)`. Both are
constructed in this repository, as `Stacks.Chow.bivariantComposite` and
`Stacks.Chow.bivariantIdentityClass`, so the two assertions are statable and are proved here —
degreewise, and on the graded group `A^*(Y)`, which is given that multiplication and that unit
here too.

## Main definitions

* `Stacks.Chow.chowCohomologyMul` — the multiplication `A^p(Y) × A^q(Y) ⟶ A^{p+q}(Y)` of the
  graded ring `A^*(Y)`: the composite bivariant class of Stacks 0B75 for the two identity
  morphisms of `Y`, read for `𝟙 Y`.
* `Stacks.Chow.chowCohomologyMulBilinear` — that multiplication as the bilinear map it is,
  through `Stacks.Chow.BivariantClass.copyAddHom`.
* `Stacks.Chow.chowCohomologyMulOfInvertible`,
  `Stacks.Chow.chowCohomologyMulBilinearOfInvertible` — that multiplication at the Gysin system
  of the genuine first Chern class, with nothing assumed.
* `Stacks.Chow.chowCohomologyGradedOne`, `Stacks.Chow.chowCohomologyGradedMul` — the unit and the
  multiplication of `A^*(Y)` as the graded structure Mathlib's `DirectSum` machinery takes, which
  is what gives the graded group `A^*(Y)` its `1` and its multiplication.
* `Stacks.Chow.chowCohomologyRestrictionOfInvertible`,
  `Stacks.Chow.chowCohomologyTotalRestrictionOfInvertible` — **Stacks 0B7F**, the restriction
  maps `A^p(Y) ⟶ A^p(Y')` and `A^*(Y) ⟶ A^*(Y')` at that Gysin system, with nothing assumed.
* `Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible` — **Stacks 0B7F**, that map on the
  graded groups as a homomorphism for addition and for the multiplication of `A^*`, with nothing
  assumed.

## Main results

* `Stacks.Chow.chowCohomologyMul_cap` — the cap operation of a product: `(a ⬝ b) ∩ α` is
  `a ∩ (b ∩ α)`, the inner class being read on the test scheme `Y ×_Y T` and the result pushed
  forward along `Y ×_Y (Y ×_Y T) ≅ Y ×_Y T`.
* `Stacks.Chow.chowCohomologyRestriction_mul` — the restriction map is multiplicative:
  `res(a ⬝ b) = res(a) ⬝ res(b)` in `A^{p+q}(Y')`.
* `Stacks.Chow.chowCohomologyRestriction_bivariantIdentityClass` — the restriction map is unital:
  `res(1) = 1` in `A^0(Y')`.
* `Stacks.Chow.chowCohomologyRestrictionOfInvertible_cap`,
  `Stacks.Chow.chowCohomologyRestrictionOfInvertible_mul`,
  `Stacks.Chow.chowCohomologyRestrictionOfInvertible_bivariantIdentityClass` — **Stacks 0B7F**,
  the cap formula, the multiplicativity and the unitality at the Gysin system of the genuine
  first Chern class, with nothing assumed.
* `Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible_map_one` — **Stacks 0B7F**, the
  restriction map carries the unit of `A^*(Y)` to the unit of `A^*(Y')`, with nothing assumed.
* `Stacks.Chow.copy_bivariantComposite_cap` — the cap operation of a composite bivariant class
  read for a morphism `m` presented by an equality `f ≫ g = m`, which is what specializes to the
  product on Chow cohomology.
* `Stacks.Chow.BivariantClass.copy_zero`, `Stacks.Chow.BivariantClass.copy_add` — reading a
  bivariant class for an equal morphism in an equal degree is a homomorphism of groups.

## Implementation notes

### Why the composite has to be read for an equal morphism

`Stacks.Chow.bivariantComposite` produces a class for `f ≫ g`, so at `f = g = 𝟙 Y` a class for
`𝟙 Y ≫ 𝟙 Y`, while `A^{p+q}(Y)` is the group of classes for `𝟙 Y`. The two morphisms are equal
but not the same term, and the cap operations land in the fibre products `Y ×_{𝟙 Y ≫ 𝟙 Y} T` and
`Y ×_{𝟙 Y} T` accordingly. `Stacks.Chow.chowCohomologyMul` therefore transports the composite
along `Category.id_comp (𝟙 Y)` with `Stacks.Chow.BivariantClass.copy`, which is what gives it the
declared type `A^{p+q}(Y)`; `Stacks.Chow.copy_bivariantComposite_cap` reads off the cap operation
of such a transport for a general presentation `f ≫ g = m` of the morphism, with the comparison
isomorphism of the two iterated fibre products carried as a parameter characterized by its two
projections. Taking `m = 𝟙 Y` and the comparison isomorphism to be the identity base change
`Y ×_Y (Y ×_Y T) ≅ Y ×_Y T` gives `Stacks.Chow.chowCohomologyMul_cap`.

### The two layers, and why the tag sits on the second

The whole bivariant development is stated against an arbitrary `Stacks.Chow.GysinSystem`, whose
`chern` field is unconstrained data. Three naturality properties of that system are therefore
side conditions of the general statements:

* `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`, carried already by the restriction map
  of Stacks 0F9Z, hence by `Stacks.Chow.chowCohomologyRestriction`;
* `Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`, carried by the composition of
  Stacks 0B75, hence by `Stacks.Chow.bivariantComposite`;
* `Stacks.Chow.IdentityCapRule.TransportGysinNaturality` for `Y` and for `Y'`, carried by the
  identity class of Stacks 0FBS, hence by `Stacks.Chow.bivariantIdentityClass`.

Each is the isomorphism or iterated-pullback case of Stacks 02TA for a Gysin system, which an
arbitrary one does not satisfy; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction` and of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class`. They are `Prop`s, so none of
them changes the group `A^p(Y)` or the map `res`.

None of them is a hypothesis of the tag: the source derives all three. And none of them is a
hypothesis at the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the genuine first Chern
class, where all three are theorems —
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward` and, for the third,
`Stacks.Chow.IdentityCapRule.transportGysinNaturality` fed with the unconditional
`Stacks.Chow.identityCapRule_gysinNaturality` and
`Stacks.Chow.GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso` (the combination
already used by `Stacks.Chow.bivariantIdentityClassOfInvertible`).

So Stacks 0B7F is carried by the `…OfInvertible` layer, which instantiates each general
statement at that Gysin system and discharges every side condition: nothing beyond the
hypotheses of the tag — `Y` and `Y'` locally of finite type over `S` and a morphism `f : Y' ⟶ Y`
over `S` — is assumed there. The general layer survives untagged for the consumers that work
with an abstract Gysin system, such as
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyRestrictionInjective` and
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.SplittingPrinciple`.

### "Map of `ℤ`-algebras", and what of the algebra structure `A^*` carries

A map of `ℤ`-algebras is a map that respects addition, the multiplication and the unit; over `ℤ`
there is nothing else to respect, since an additive map between abelian groups is `ℤ`-linear
automatically. All three are asserted of `res` here, and each twice over: degreewise as
`Stacks.Chow.chowCohomologyRestrictionOfInvertible` (additivity, as its `AddMonoidHom`
structure), `Stacks.Chow.chowCohomologyRestrictionOfInvertible_mul` and
`Stacks.Chow.chowCohomologyRestrictionOfInvertible_bivariantIdentityClass`; and on the graded
group `A^*(Y)` itself as `Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible`, a
`NonUnitalRingHom` carrying addition and the multiplication together, and
`Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible_map_one`.

For the second of those readings `A^*(Y)` needs a multiplication and a unit, and
`Stacks.Chow.chowCohomologyGradedMul` and `Stacks.Chow.chowCohomologyGradedOne` install them: the
multiplication is composition of bivariant classes, Stacks 0B75, and the unit is the identity
class `Stacks.Chow.bivariantIdentityClass` in degree `0`. Stacks 0FBS is a lemma that *uses* that
unit — it asserts `Δ^! ∘ prᵢ^! = 1` in `A⁰(X)` — rather than one that defines it or states a unit
law, so it is not cited for either here. They are stated at the Gysin system of the genuine first
Chern class, because at an arbitrary `Stacks.Chow.GysinSystem` the composition of Stacks 0B75 is
not available at all (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ChowCohomology`).

What `A^*(Y)` carries from that is `Mul`, `One` and the `NonUnitalNonAssocRing` structure
Mathlib's `DirectSum` machinery derives from a `DirectSum.GNonUnitalNonAssocSemiring`, which is
exactly the bilinearity of the composition. It is not a `Ring`, and `res` is not a `RingHom`,
because `DirectSum.GSemiring` additionally wants `GradedMonoid.GMonoid`, whose fields are the two
unit laws `1 ∘ a = a` and `a ∘ 1 = a` and the associativity `(a ∘ b) ∘ c = a ∘ (b ∘ c)` of the
composition.

What is missing is that *packaging* on the `DirectSum`, not the mathematics. For the product form
`∏_{p ≥ 0} Aᵖ(Y)` all three laws are proved, from the same Stacks 0B75 composites, by
`Stacks.Chow.TotalChowClass.instRing` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass` — `mul_assoc`, `one_mul` and `mul_one`
are among its fields — and this module imports that file.

Either way all three belong to the ring structure of `A^*` — Stacks 0B7E and Stacks 0B75 — rather
than to any assertion Stacks 0B7F makes about `res`, and so none of them is needed for, nor
supplied by, the declarations here.

### The degrees

A product of classes of degrees `p` and `q` caps a class of degree `k` into degree `k - q - p`,
while a class of degree `p + q` caps it into `k - (p + q)`. These are the same integer and not the
same term, whence the transport `Stacks.Chow.chowGroupDegreeEquiv` in
`Stacks.Chow.chowCohomologyMul_cap`, exactly as in `Stacks.Chow.bivariantComposite_cap`.

## References

* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The cap operation of a composite read for an equal morphism -/

/-- The cap operation of the composite of `a ∈ A^p(X ⟶ Y)` and `b ∈ A^q(Y ⟶ Z)`, read as a class
for a morphism `m : X ⟶ Z` presented by an equality `f ≫ g = m`: it is cap with `b`, cap with
`a`, and pushforward along a comparison isomorphism `w : X ×_Y (Y ×_Z T) ≅ X ×_Z T` of the
iterated fibre products, up to the transport of the degree.

The comparison isomorphism is a parameter, characterized by its two projections; for `m = f ≫ g`
it is `CategoryTheory.Limits.pullbackRightPullbackFstIso` and the statement is
`Stacks.Chow.bivariantComposite_cap` together with
`Stacks.Chow.bivariantCompositeCap_apply`. -/
theorem copy_bivariantComposite_cap (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX)
    (hg : g ≫ sZ = sY) (p q : ℤ) (a : BivariantClass C G sX sY f hf p)
    (b : BivariantClass C G sY sZ g hg q) (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) (m : X ⟶ Z) [LocallyOfFiniteType m]
    (hm : f ≫ g = m) (hmb : m ≫ sZ = sX) {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t]
    (k : ℤ) (w : pullback f (pullback.fst g t) ⟶ pullback m t) [IsIso w]
    (hwb : w ≫ (pullback.fst m t ≫ sX) = pullback.fst f (pullback.fst g t) ≫ sX)
    (hw1 : w ≫ pullback.fst m t = pullback.fst f (pullback.fst g t))
    (hw2 : w ≫ pullback.snd m t = pullback.snd f (pullback.fst g t) ≫ pullback.snd g t)
    (α : chowGroup C (t ≫ sZ) k) :
    (BivariantClass.copy C G sX sZ hm (comp_comp_structureMorphism_eq hf hg) hmb
          (rfl : p + q = p + q)
          (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc)).cap t k α =
      chowGroupDegreeEquiv C (pullback.fst m t ≫ sX) (by ring : k - q - p = k - (p + q))
        (chowPushforwardOfIso C (pullback.fst f (pullback.fst g t) ≫ sX)
          (pullback.fst m t ≫ sX) w hwb (k - q - p)
          (a.cap (pullback.fst g t) (k - q) (b.cap t k α))) := by
  subst hm
  have hw : w = (pullbackRightPullbackFstIso g t f).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [hw1, pullbackRightPullbackFstIso_hom_fst]
    · rw [hw2, pullbackRightPullbackFstIso_hom_snd]
  subst hw
  rfl

/-! ### Reading a bivariant class for an equal morphism is additive -/

section Copy

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f f' : X ⟶ Y}
  [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff' : f = f') (hf : f ≫ sY = sX)
  (hf' : f' ≫ sY = sX) {p p' : ℤ} (hpp' : p = p')

/-- Reading the zero class for an equal morphism in an equal degree gives the zero class: once
the two morphisms and the two degrees are identified the transport is the identity. -/
theorem BivariantClass.copy_zero :
    BivariantClass.copy C G sX sY hff' hf hf' hpp' 0 = 0 := by
  subst hff'
  subst hpp'
  rfl

/-- Reading a bivariant class for an equal morphism in an equal degree is additive, for the same
reason. -/
theorem BivariantClass.copy_add (c d : BivariantClass C G sX sY f hf p) :
    BivariantClass.copy C G sX sY hff' hf hf' hpp' (c + d) =
      BivariantClass.copy C G sX sY hff' hf hf' hpp' c +
        BivariantClass.copy C G sX sY hff' hf hf' hpp' d := by
  subst hff'
  subst hpp'
  rfl

/-- `Stacks.Chow.BivariantClass.copy` as a homomorphism of the groups `A^p(X ⟶ Y)` of Stacks
0B76, which is what makes the multiplication on Chow cohomology bilinear. -/
def BivariantClass.copyAddHom :
    BivariantClass C G sX sY f hf p →+ BivariantClass C G sX sY f' hf' p' where
  toFun := BivariantClass.copy C G sX sY hff' hf hf' hpp'
  map_zero' := BivariantClass.copy_zero C G sX sY hff' hf hf' hpp'
  map_add' := BivariantClass.copy_add C G sX sY hff' hf hf' hpp'

end Copy

/-! ### The multiplication on Chow cohomology -/

section Mul

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (p q : ℤ) (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- The multiplication `A^p(Y) × A^q(Y) ⟶ A^{p+q}(Y)` of the graded ring `A^*(Y)` of Stacks
0B7E: the composite bivariant class of Stacks 0B75 of two classes for the identity of `Y`, read
for `𝟙 Y` rather than for `𝟙 Y ≫ 𝟙 Y`.

It carries the two cases of Stacks 02TA for the Gysin system that the composition of Stacks 0B75
carries; see the implementation notes. -/
def chowCohomologyMul (a : chowCohomologyComponent C G sY p)
    (b : chowCohomologyComponent C G sY q) : chowCohomologyComponent C G sY (p + q) :=
  BivariantClass.copy C G sY sY (Category.id_comp (𝟙 Y))
    (comp_comp_structureMorphism_eq (Category.id_comp sY) (Category.id_comp sY))
    (Category.id_comp sY) (rfl : p + q = p + q)
    (bivariantComposite C G sY sY sY (𝟙 Y) (𝟙 Y) (Category.id_comp sY) (Category.id_comp sY)
      p q a b hgys hgysc)

/-- **The cap operation of a product is the composite operation.** On a test scheme `t : T ⟶ Y`
the product `a ⬝ b` caps by `a ∩ (b ∩ -)`, the class `b ∩ α` being read on the test scheme
`Y ×_Y T` and the result pushed forward along the identity base change
`Y ×_Y (Y ×_Y T) ≅ Y ×_Y T`, up to the transport of the degree. -/
theorem chowCohomologyMul_cap (a : chowCohomologyComponent C G sY p)
    (b : chowCohomologyComponent C G sY q) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (chowCohomologyMul C G sY p q hgys hgysc a b).cap t k α =
      chowGroupDegreeEquiv C (pullback.fst (𝟙 Y) t ≫ sY) (by ring : k - q - p = k - (p + q))
        (chowPushforwardOfIso C (pullback.fst (𝟙 Y) (pullback.fst (𝟙 Y) t) ≫ sY)
          (pullback.fst (𝟙 Y) t ≫ sY) (identityBaseChangeIso (pullback.fst (𝟙 Y) t)).hom
          (identityBaseChangeIso_hom_comp_base C sY (pullback.fst (𝟙 Y) t)) (k - q - p)
          (a.cap (pullback.fst (𝟙 Y) t) (k - q) (b.cap t k α))) :=
  copy_bivariantComposite_cap C G sY sY sY (𝟙 Y) (𝟙 Y) (Category.id_comp sY)
    (Category.id_comp sY) p q a b hgys hgysc (𝟙 Y) (Category.id_comp (𝟙 Y))
    (Category.id_comp sY) t k (identityBaseChangeIso (pullback.fst (𝟙 Y) t)).hom
    (identityBaseChangeIso_hom_comp_base C sY (pullback.fst (𝟙 Y) t))
    (by simpa using (fst_eq_identityBaseChangeIso_hom (pullback.fst (𝟙 Y) t)).symm) rfl α

/-- The multiplication `A^p(Y) × A^q(Y) ⟶ A^{p+q}(Y)` of the graded ring `A^*(Y)` of Stacks
0B7E as the bilinear map it is: the bilinear composition of Stacks 0B75 at the two identity
morphisms of `Y`, read for `𝟙 Y` through the homomorphism
`Stacks.Chow.BivariantClass.copyAddHom`.

It carries the two cases of Stacks 02TA for the Gysin system that the composition of Stacks 0B75
carries; see the implementation notes. -/
def chowCohomologyMulBilinear :
    chowCohomologyComponent C G sY p →+ chowCohomologyComponent C G sY q →+
      chowCohomologyComponent C G sY (p + q) :=
  (BivariantClass.copyAddHom C G sY sY (Category.id_comp (𝟙 Y))
        (comp_comp_structureMorphism_eq (Category.id_comp sY) (Category.id_comp sY))
        (Category.id_comp sY) (rfl : p + q = p + q)).compHom.comp
    (bivariantCompositeBilinear C G sY sY sY (𝟙 Y) (𝟙 Y) (Category.id_comp sY)
      (Category.id_comp sY) p q hgys hgysc)

/-- The bilinear multiplication is the multiplication. -/
@[simp]
theorem chowCohomologyMulBilinear_apply (a : chowCohomologyComponent C G sY p)
    (b : chowCohomologyComponent C G sY q) :
    chowCohomologyMulBilinear C G sY p q hgys hgysc a b =
      chowCohomologyMul C G sY p q hgys hgysc a b :=
  rfl

end Mul

/-! ### Stacks 0B7F: the restriction map is a map of `ℤ`-algebras -/

section Restriction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : Y' ⟶ Y) [LocallyOfFiniteType f] (p q : ℤ)
  (hgys : G.IsNaturalUnderBaseChangeIso) (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- The restriction map `res : A^*(Y) ⟶ A^*(Y')` along `f : Y' ⟶ Y` is multiplicative:
`res(a ⬝ b) = res(a) ⬝ res(b)` for `a ∈ A^p(Y)` and `b ∈ A^q(Y)`, the multiplication being
composition of bivariant classes, Stacks 0B75.

Stated against an arbitrary Gysin system, hence under the two cases of Stacks 02TA for it;
**Stacks 0B7F** is the unconditional
`Stacks.Chow.chowCohomologyRestrictionOfInvertible_mul`, below at line 543.

The proof is the source's: a bivariant class for the identity of `Y'` is determined by the
operation it induces on the Chow groups of the test schemes
(`Stacks.Chow.BivariantClass.eq_of_pushforward_cap_eq`), and on a test scheme `g : T ⟶ Y'` both
sides induce `a ∩ (b ∩ -)` read along `g ≫ f` by the cap formula
`Stacks.Chow.chowCohomologyRestriction_cap` of Stacks 0F9Z, applied to `b` on `T` and to `a` on
`Y' ×_{Y'} T`. The two readings differ by the identifications of `Y ×_Y T` and `Y' ×_{Y'} T` with
`T`, and the proper-pushforward axiom of `a` for an isomorphism of test schemes
(`Stacks.Chow.BivariantClass.cap_chowPushforwardOfIso`) moves one to the other. -/
theorem chowCohomologyRestriction_mul (a : chowCohomologyComponent C G sY p)
    (b : chowCohomologyComponent C G sY q) :
    chowCohomologyRestriction C G sY f (p + q) hgys
        (chowCohomologyMul C G sY p q hgys hgysc a b) =
      chowCohomologyMul C G (f ≫ sY) p q hgys hgysc
        (chowCohomologyRestriction C G sY f p hgys a)
        (chowCohomologyRestriction C G sY f q hgys b) := by
  refine BivariantClass.eq_of_pushforward_cap_eq C (f ≫ sY) (p + q) G _ _ fun {T} g _ k α ↦ ?_
  rw [chowCohomologyRestriction_cap C G sY f (p + q) hgys
      (chowCohomologyMul C G sY p q hgys hgysc a b) g k α,
    chowCohomologyMul_cap C G sY p q hgys hgysc a b (g ≫ f) k
      (chowGroupCongr C (Category.assoc g f sY).symm k α),
    chowCohomologyMul_cap C G (f ≫ sY) p q hgys hgysc
      (chowCohomologyRestriction C G sY f p hgys a)
      (chowCohomologyRestriction C G sY f q hgys b) g k α,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso, ← chowGroupDegreeEquiv_chowPushforwardOfIso]
  refine DFunLike.congr_arg _ ?_
  -- the comparison `Y' ×_{Y'} T ≅ Y ×_Y T` of the two identity base changes of the test scheme
  have h1 : (identityBaseChangeIso (g ≫ f)).inv ≫ pullback.fst (𝟙 Y) (g ≫ f) = g ≫ f := by
    rw [fst_eq_identityBaseChangeIso_hom (g ≫ f), Iso.inv_hom_id_assoc]
  have h2 : pullback.fst (𝟙 Y') g ≫ f = (identityBaseChangeIso g).hom ≫ (g ≫ f) := by
    rw [fst_eq_identityBaseChangeIso_hom g, Category.assoc]
  have hθfst : ((identityBaseChangeIso g).hom ≫ (identityBaseChangeIso (g ≫ f)).inv) ≫
      pullback.fst (𝟙 Y) (g ≫ f) = pullback.fst (𝟙 Y') g ≫ f := by
    rw [Category.assoc, h1, h2]
  have hθbase : ((identityBaseChangeIso g).hom ≫ (identityBaseChangeIso (g ≫ f)).inv) ≫
      (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) = pullback.fst (𝟙 Y') g ≫ (f ≫ sY) := by
    rw [← Category.assoc, hθfst, Category.assoc]
  have hθibc : ((identityBaseChangeIso g).hom ≫ (identityBaseChangeIso (g ≫ f)).inv) ≫
      (identityBaseChangeIso (g ≫ f)).hom = (identityBaseChangeIso g).hom := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hbaseL : (identityBaseChangeIso (g ≫ f)).hom ≫ (g ≫ f ≫ sY) =
      pullback.fst (𝟙 Y) (g ≫ f) ≫ sY := by
    rw [← Category.assoc]; exact identityBaseChangeIso_hom_comp_base C sY (g ≫ f)
  have hinj : Function.Injective (chowPushforwardOfIso C
      (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) (g ≫ f ≫ sY)
      (identityBaseChangeIso (g ≫ f)).hom hbaseL (k - q)) := fun x y hxy ↦
    (chowGroupEquivOfIso C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) (g ≫ f ≫ sY)
      (identityBaseChangeIso (g ≫ f)).hom hbaseL (k - q)).injective (by simpa using hxy)
  -- `b ∩ α` read on `Y ×_Y T` is `res(b) ∩ α` read on `Y' ×_{Y'} T`
  have hβ : b.cap (g ≫ f) k (chowGroupCongr C (Category.assoc g f sY).symm k α) =
      chowPushforwardOfIso C (pullback.fst (𝟙 Y') g ≫ (f ≫ sY))
        (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY)
        ((identityBaseChangeIso g).hom ≫ (identityBaseChangeIso (g ≫ f)).inv) hθbase (k - q)
        ((chowCohomologyRestriction C G sY f q hgys b).cap g k α) := by
    refine hinj ?_
    rw [chowPushforwardOfIso_comp_apply C _ _ _ _ _ hθbase hbaseL (k - q),
      chowPushforwardOfIso_congr_apply C _ _ _ _ hθibc _
        (identityBaseChangeIso_hom_comp_base C (f ≫ sY) g) (k - q),
      ← chowCohomologyRestriction_cap C G sY f q hgys b g k α]
  -- the proper-pushforward axiom of `a` along that comparison, and the cap formula for `res(a)`
  have ha := BivariantClass.cap_chowPushforwardOfIso a (pullback.fst (𝟙 Y) (g ≫ f))
    ((identityBaseChangeIso g).hom ≫ (identityBaseChangeIso (g ≫ f)).inv)
    (pullback.fst (𝟙 Y') g ≫ f) hθfst (pullback.fst (𝟙 Y') g ≫ (f ≫ sY))
    (Category.assoc (pullback.fst (𝟙 Y') g) f sY).symm (k - q) hθbase
    ((chowCohomologyRestriction C G sY f q hgys b).cap g k α) _ rfl
  have hres_a := chowCohomologyRestriction_cap C G sY f p hgys a (pullback.fst (𝟙 Y') g) (k - q)
    ((chowCohomologyRestriction C G sY f q hgys b).cap g k α)
  rw [hβ, ha, hres_a]
  simp only [chowPushforwardOfIso_comp_apply]
  have hW : ((testBaseChangeIso (𝟙 Y) (pullback.fst (𝟙 Y) (g ≫ f))
          ((identityBaseChangeIso g).hom ≫ (identityBaseChangeIso (g ≫ f)).inv)
          (pullback.fst (𝟙 Y') g ≫ f) hθfst).hom ≫
        (identityBaseChangeIso (pullback.fst (𝟙 Y) (g ≫ f))).hom) ≫
      (identityBaseChangeIso (g ≫ f)).hom =
      (identityBaseChangeIso (pullback.fst (𝟙 Y') g ≫ f)).hom ≫ (identityBaseChangeIso g).hom := by
    have h : ((testBaseChangeIso (𝟙 Y) (pullback.fst (𝟙 Y) (g ≫ f))
            ((identityBaseChangeIso g).hom ≫ (identityBaseChangeIso (g ≫ f)).inv)
            (pullback.fst (𝟙 Y') g ≫ f) hθfst).hom ≫
          pullback.snd (𝟙 Y) (pullback.fst (𝟙 Y) (g ≫ f))) ≫ pullback.snd (𝟙 Y) (g ≫ f) =
        pullback.snd (𝟙 Y) (pullback.fst (𝟙 Y') g ≫ f) ≫ pullback.snd (𝟙 Y') g := by
      rw [testBaseChangeIso_hom_snd, Category.assoc]
      exact congrArg (_ ≫ ·) hθibc
    exact h
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ hW _ _ (k - q - p) _

/-- The restriction map `res : A^*(Y) ⟶ A^*(Y')` along `f : Y' ⟶ Y` is unital: it carries the
identity class `1 ∈ A^0(Y)` of Stacks 0FBS to the identity class `1 ∈ A^0(Y')`.

Stated against an arbitrary Gysin system, hence under the isomorphism case of Stacks 02TA for it
and under the Gysin axiom for the transported identity cap rule on `Y` and on `Y'`; **Stacks
0B7F** is the unconditional
`Stacks.Chow.chowCohomologyRestrictionOfInvertible_bivariantIdentityClass`, below at line 568.

The proof is the source's: a class of degree `0` for `𝟙 Y'` is the identity class exactly when
it acts as the identity on the Chow groups of every test scheme
(`Stacks.Chow.eq_bivariantIdentityClass_iff`), and `res(1)` acts on a test scheme `g : T ⟶ Y'` the
way `1` acts along `g ≫ f`, by the cap formula of Stacks 0F9Z, namely as the identity. -/
theorem chowCohomologyRestriction_bivariantIdentityClass
    (hone : IdentityCapRule.TransportGysinNaturality C sY 0 (identityCapRule C sY) G)
    (hone' : IdentityCapRule.TransportGysinNaturality C (f ≫ sY) 0
      (identityCapRule C (f ≫ sY)) G) :
    chowCohomologyRestriction C G sY f 0 hgys (bivariantIdentityClass C sY G hone) =
      bivariantIdentityClass C (f ≫ sY) G hone' := by
  rw [eq_bivariantIdentityClass_iff]
  intro T g _ k α
  rw [chowCohomologyRestriction_cap C G sY f 0 hgys (bivariantIdentityClass C sY G hone) g k α,
    ← chowGroupCongr_chowPushforwardOfIso_target C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY)
      (Category.assoc g f sY) (identityBaseChangeIso (g ≫ f)).hom
      (identityBaseChangeIso_hom_comp_base C sY (g ≫ f)),
    bivariantIdentityClass_cap_pushforward C sY G hone (g ≫ f) k]
  refine eq_of_heq (HEq.trans ?_
    (chowGroupDegreeEquiv_heq C (g ≫ f ≫ sY) (sub_zero k).symm α).symm)
  refine (chowGroupCongr_heq C (Category.assoc g f sY) (k - 0) _).trans ?_
  refine (chowGroupDegreeEquiv_heq C ((g ≫ f) ≫ sY) (sub_zero k).symm _).trans ?_
  exact chowGroupCongr_heq C (Category.assoc g f sY).symm k α

/-- The graded restriction map is the degreewise one on each summand: it carries the image of
`c ∈ A^p(Y)` in `A^*(Y)` to the image of `res(c) ∈ A^p(Y')` in `A^*(Y')`. -/
theorem chowCohomologyTotalRestriction_of (c : chowCohomologyComponent C G sY p) :
    chowCohomologyTotalRestriction C G sY f hgys (DirectSum.of _ p c) =
      DirectSum.of _ p (chowCohomologyRestriction C G sY f p hgys c) :=
  DirectSum.map_of _ p c

end Restriction

/-! ### Stacks 0B7F at the Gysin system of the first Chern class rule -/

section Unconditional

variable (C : ChowSituation.{u}) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : Y' ⟶ Y) [LocallyOfFiniteType f] (p q : ℤ)

/-- **Stacks 0B7F.** The restriction map `res : A^p(Y) ⟶ A^p(Y')` along a morphism `f : Y' ⟶ Y`
of schemes locally of finite type over the base, a homomorphism of groups, at the Gysin system of
the first Chern class rule of an invertible module. It is often written `f^*`.

This is `Stacks.Chow.chowCohomologyRestriction` with its case of Stacks 02TA discharged, by
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`. Nothing is assumed: the Gysin
system itself carries no hypothesis either, so the only hypotheses are those of the tag. -/
@[stacks 0B7F "the canonical map, at the Gysin system of the first Chern class rule, with \
nothing assumed beyond the tag's own hypotheses"]
def chowCohomologyRestrictionOfInvertible :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sY p →+
      chowCohomologyComponent C (gysinSystemOfInvertible C) (f ≫ sY) p :=
  chowCohomologyRestriction C (gysinSystemOfInvertible C) sY f p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)

/-- **Stacks 0B7F.** The restriction map on Chow cohomology satisfies the cap formula of Stacks
0F9Z: `res(c) ∩ α = c ∩ α` for every `α ∈ CH_k(T)` and every test scheme `g : T ⟶ Y'`, both
sides read in `CH_{k-p}(T)` through the canonical identifications `Y' ×_{Y'} T ≅ T` and
`Y ×_Y T ≅ T`. Nothing is assumed. -/
@[stacks 0B7F "the cap formula for the canonical map, at the Gysin system of the first Chern \
class rule, with nothing assumed beyond the tag's own hypotheses"]
theorem chowCohomologyRestrictionOfInvertible_cap
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) {T : Scheme.{u}}
    (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ (f ≫ sY)) k) :
    chowPushforwardOfIso C (pullback.fst (𝟙 Y') g ≫ (f ≫ sY)) (g ≫ (f ≫ sY))
        (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C (f ≫ sY) g) (k - p)
        ((chowCohomologyRestrictionOfInvertible C sY f p c).cap g k α) =
      chowPushforwardOfIso C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) (g ≫ (f ≫ sY))
        (identityBaseChangeIso (g ≫ f)).hom
        (by rw [← Category.assoc]; exact identityBaseChangeIso_hom_comp_base C sY (g ≫ f))
        (k - p) (c.cap (g ≫ f) k (chowGroupCongr C (Category.assoc g f sY).symm k α)) :=
  chowCohomologyRestriction_cap C (gysinSystemOfInvertible C) sY f p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c g k α

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` of the graded Chow cohomology
groups along `f : Y' ⟶ Y`, a homomorphism of graded groups, at the Gysin system of the first
Chern class rule: the degreewise restriction map. Nothing is assumed.

That this graded map is a map of `ℤ`-algebras is the `AddMonoidHom` structure here and in each
degree, together with `Stacks.Chow.chowCohomologyRestrictionOfInvertible_mul` and
`Stacks.Chow.chowCohomologyRestrictionOfInvertible_bivariantIdentityClass`. -/
@[stacks 0B7F "the canonical map of graded groups, at the Gysin system of the first Chern class \
rule, with nothing assumed beyond the tag's own hypotheses"]
def chowCohomologyTotalRestrictionOfInvertible :
    chowCohomology C (gysinSystemOfInvertible C) sY →+
      chowCohomology C (gysinSystemOfInvertible C) (f ≫ sY) :=
  chowCohomologyTotalRestriction C (gysinSystemOfInvertible C) sY f
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)

/-- The multiplication `A^p(Y) × A^q(Y) ⟶ A^{p+q}(Y)` of the graded ring `A^*(Y)` of Stacks
0B7E at the Gysin system of the first Chern class rule: `Stacks.Chow.chowCohomologyMul` with both
of its cases of Stacks 02TA discharged, by
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso` and
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward`. Nothing is
assumed. -/
def chowCohomologyMulOfInvertible
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sY (p + q) :=
  chowCohomologyMul C (gysinSystemOfInvertible C) sY p q
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) a b

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` along `f : Y' ⟶ Y` is
multiplicative: `res(a ⬝ b) = res(a) ⬝ res(b)` for `a ∈ A^p(Y)` and `b ∈ A^q(Y)`, the
multiplication being composition of bivariant classes, Stacks 0B75. Nothing is assumed.

This is `Stacks.Chow.chowCohomologyRestriction_mul` with both of its cases of Stacks 02TA
discharged, by `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso` and
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward`. -/
@[stacks 0B7F "the canonical map is multiplicative: res(a ⬝ b) = res(a) ⬝ res(b), the \
multiplication on Chow cohomology being composition of bivariant classes -- at the Gysin system \
of the first Chern class rule, with nothing assumed beyond the tag's own hypotheses"]
theorem chowCohomologyRestrictionOfInvertible_mul
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q) :
    chowCohomologyRestrictionOfInvertible C sY f (p + q)
        (chowCohomologyMulOfInvertible C sY p q a b) =
      chowCohomologyMulOfInvertible C (f ≫ sY) p q
        (chowCohomologyRestrictionOfInvertible C sY f p a)
        (chowCohomologyRestrictionOfInvertible C sY f q b) :=
  chowCohomologyRestriction_mul C (gysinSystemOfInvertible C) sY f p q
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) a b

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` along `f : Y' ⟶ Y` is unital:
it carries the identity class `1 ∈ A^0(Y)` of Stacks 0FBS to the identity class `1 ∈ A^0(Y')`.
Nothing is assumed.

This is `Stacks.Chow.chowCohomologyRestriction_bivariantIdentityClass` with its case of Stacks
02TA discharged by `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso` and its two
Gysin axioms for the transported identity cap rule discharged by
`Stacks.Chow.IdentityCapRule.transportGysinNaturality` — exactly the proofs
`Stacks.Chow.bivariantIdentityClassOfInvertible` is built from, so the two identity classes in
the statement are the unconditional ones. -/
@[stacks 0B7F "the canonical map is unital: it carries the identity class 1 of A^0(Y) to the \
identity class of A^0(Y') -- at the Gysin system of the first Chern class rule, with nothing \
assumed beyond the tag's own hypotheses"]
theorem chowCohomologyRestrictionOfInvertible_bivariantIdentityClass :
    chowCohomologyRestrictionOfInvertible C sY f 0 (bivariantIdentityClassOfInvertible C sY) =
      bivariantIdentityClassOfInvertible C (f ≫ sY) :=
  chowCohomologyRestriction_bivariantIdentityClass C (gysinSystemOfInvertible C) sY f
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (IdentityCapRule.transportGysinNaturality C sY 0 (identityCapRule C sY)
      (gysinSystemOfInvertible C) (identityCapRule_gysinNaturality C sY _)
      (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C))
    (IdentityCapRule.transportGysinNaturality C (f ≫ sY) 0 (identityCapRule C (f ≫ sY))
      (gysinSystemOfInvertible C) (identityCapRule_gysinNaturality C (f ≫ sY) _)
      (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C))

/-- The restriction map carries the degree `p` summand of `A^*(Y)` to the degree `p` summand of
`A^*(Y')` by the degreewise map. -/
theorem chowCohomologyTotalRestrictionOfInvertible_of
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    chowCohomologyTotalRestrictionOfInvertible C sY f (DirectSum.of _ p c) =
      DirectSum.of _ p (chowCohomologyRestrictionOfInvertible C sY f p c) :=
  chowCohomologyTotalRestriction_of C (gysinSystemOfInvertible C) sY f p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c

/-- The multiplication `A^p(Y) × A^q(Y) ⟶ A^{p+q}(Y)` of the graded ring `A^*(Y)` of Stacks
0B7E as a bilinear map, at the Gysin system of the first Chern class rule:
`Stacks.Chow.chowCohomologyMulBilinear` with both of its cases of Stacks 02TA discharged.
Nothing is assumed. -/
def chowCohomologyMulBilinearOfInvertible :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sY p →+
      chowCohomologyComponent C (gysinSystemOfInvertible C) sY q →+
        chowCohomologyComponent C (gysinSystemOfInvertible C) sY (p + q) :=
  chowCohomologyMulBilinear C (gysinSystemOfInvertible C) sY p q
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- The bilinear multiplication is the multiplication. -/
@[simp]
theorem chowCohomologyMulBilinearOfInvertible_apply
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q) :
    chowCohomologyMulBilinearOfInvertible C sY p q a b =
      chowCohomologyMulOfInvertible C sY p q a b :=
  rfl

/-- The unit of the graded ring `A^*(Y)` of Stacks 0B7E, as the graded `1` of `A^0(Y)`: the
identity class of Stacks 0FBS at the Gysin system of the first Chern class rule. Nothing is
assumed. -/
instance chowCohomologyGradedOne :
    GradedMonoid.GOne (chowCohomologyComponent C (gysinSystemOfInvertible C) sY) where
  one := bivariantIdentityClassOfInvertible C sY

/-- The multiplication of the graded ring `A^*(Y)` of Stacks 0B7E, as a graded multiplication
with its distributive laws: composition of bivariant classes, Stacks 0B75, at the Gysin system of
the first Chern class rule, with its bilinearity supplying the four laws. Nothing is assumed.

Through this and `Stacks.Chow.chowCohomologyGradedOne`, Mathlib's `DirectSum` machinery equips
the graded group `A^*(Y)` with `1`, with the multiplication of Stacks 0B75, and with the
`NonUnitalNonAssocRing` structure those satisfy. The remaining laws of a graded ring — the two
unit laws and associativity — are not among them; see the implementation notes. -/
instance chowCohomologyGradedMul : DirectSum.GNonUnitalNonAssocSemiring
    (chowCohomologyComponent C (gysinSystemOfInvertible C) sY) where
  mul {p q} a b := chowCohomologyMulBilinearOfInvertible C sY p q a b
  mul_zero a := map_zero (chowCohomologyMulBilinearOfInvertible C sY _ _ a)
  zero_mul b := by
    change chowCohomologyMulBilinearOfInvertible C sY _ _ 0 b = 0
    rw [map_zero]
    rfl
  mul_add a b c := map_add (chowCohomologyMulBilinearOfInvertible C sY _ _ a) b c
  add_mul a b c := by
    change chowCohomologyMulBilinearOfInvertible C sY _ _ (a + b) c = _
    rw [map_add]
    rfl

/-- The graded `1` of `A^*(Y)` is the identity class of Stacks 0FBS. -/
@[simp]
theorem chowCohomologyGradedOne_eq :
    (GradedMonoid.GOne.one : chowCohomologyComponent C (gysinSystemOfInvertible C) sY 0) =
      bivariantIdentityClassOfInvertible C sY :=
  rfl

/-- The graded multiplication of `A^*(Y)` is the composition of Stacks 0B75. -/
@[simp]
theorem chowCohomologyGradedMul_eq
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q) :
    GradedMonoid.GMul.mul a b = chowCohomologyMulOfInvertible C sY p q a b :=
  rfl

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` along `f : Y' ⟶ Y` as a map of
the ring structures of the graded Chow cohomology: a homomorphism for addition and for the
multiplication of Stacks 0B75, at the Gysin system of the first Chern class rule. It is often
written `f^*`.

Its underlying additive map is `Stacks.Chow.chowCohomologyTotalRestrictionOfInvertible`, and that
it also carries `1` to `1` is `Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible_map_one`
just below; since an additive map between abelian groups is `ℤ`-linear, the two together are the
whole of the tag's "map of `ℤ`-algebras". Nothing is assumed.

The proof reduces to the degreewise statement
`Stacks.Chow.chowCohomologyRestrictionOfInvertible_mul`: multiplication on a `DirectSum` is
bilinear, so both sides of `res(x ⬝ y) = res(x) ⬝ res(y)` are additive in `x` and in `y` and it
is enough to check them on the summands. -/
@[stacks 0B7F "the canonical map res : A^*(Y) → A^*(Y') on the graded groups is a homomorphism \
for addition and for the multiplication of Stacks 0B75 -- at the Gysin system of the first Chern \
class rule, with nothing assumed beyond the tag's own hypotheses"]
def chowCohomologyTotalRestrictionRingOfInvertible :
    chowCohomology C (gysinSystemOfInvertible C) sY →ₙ+*
      chowCohomology C (gysinSystemOfInvertible C) (f ≫ sY) where
  toFun := chowCohomologyTotalRestrictionOfInvertible C sY f
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p a =>
        induction y using DirectSum.induction_on with
        | zero => simp
        | of q b =>
            rw [DirectSum.of_mul_of]
            show chowCohomologyTotalRestrictionOfInvertible C sY f _ = _
            rw [chowCohomologyTotalRestrictionOfInvertible_of,
              chowCohomologyTotalRestrictionOfInvertible_of,
              chowCohomologyTotalRestrictionOfInvertible_of, DirectSum.of_mul_of]
            congr 1
            exact chowCohomologyRestrictionOfInvertible_mul C sY f p q a b
        | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
    | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` carries the unit `1` of
`A^*(Y)` to the unit of `A^*(Y')`: the unit of the graded ring is the identity class of Stacks
0FBS sitting in degree `0`, and `res` carries it to the identity class of `A^0(Y')` by
`Stacks.Chow.chowCohomologyRestrictionOfInvertible_bivariantIdentityClass`. Nothing is
assumed. -/
@[stacks 0B7F "the canonical map res : A^*(Y) → A^*(Y') on the graded groups carries the unit 1 \
of A^*(Y) to the unit of A^*(Y') -- at the Gysin system of the first Chern class rule, with \
nothing assumed beyond the tag's own hypotheses"]
theorem chowCohomologyTotalRestrictionRingOfInvertible_map_one :
    chowCohomologyTotalRestrictionRingOfInvertible C sY f 1 = 1 := by
  show chowCohomologyTotalRestrictionOfInvertible C sY f
      (DirectSum.of _ 0 (bivariantIdentityClassOfInvertible C sY)) = _
  rw [chowCohomologyTotalRestrictionOfInvertible_of,
    chowCohomologyRestrictionOfInvertible_bivariantIdentityClass]
  rfl

end Unconditional

end Stacks.Chow

end
