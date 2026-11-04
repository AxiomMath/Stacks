module

public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# The naive cotangent complex of an arbitrary extension

For an extension `P → S` of an `R`-algebra `S`, that is a surjection of `R`-algebras onto `S`
with kernel `I`, the two-term complex `I/I² ⟶ Ω[P/R] ⊗[P] S` is the naive cotangent complex
`NL(P)`.  A morphism of extensions over `R` and `S` induces a chain map of these complexes, any
two morphisms induce homotopic chain maps, and a morphism admitting a morphism in the other
direction therefore induces a homotopy equivalence, hence a quasi-isomorphism.

This is Stacks 00S1 for extensions rather than for polynomial presentations.  It is what makes
the statement usable when the underlying ring of the extension is not literally a polynomial
ring — for instance a stalk of a free algebra sheaf, which is only isomorphic to one.

## Main definitions

* `NaiveCotangent.nlOfExtension`: the naive cotangent complex of an extension, as a
  `NaiveCotangent.TwoTerm`.
* `NaiveCotangent.nlExtensionMap`: the chain map induced by a morphism of extensions.

## Main results

* `NaiveCotangent.nlExtensionMap_homotopic`: any two morphisms of extensions induce homotopic
  chain maps.
* `NaiveCotangent.nlExtensionMap_isHomotopyEquiv` and
  `NaiveCotangent.nlExtensionMap_isQuasiIso`: a morphism of extensions which admits a morphism
  in the other direction induces a homotopy equivalence, hence a quasi-isomorphism.

## Implementation notes

Both extensions are extensions of the same algebra `S` over the same base `R`, so the induced
maps are already `S`-linear and no restriction of scalars is needed; the `restrictScalars S`
appearing in Mathlib's `Algebra.Extension.Cotangent.map_comp` and
`Algebra.Extension.CotangentSpace.map_sub_map` is restriction along the identity of `S`, and the
statements below are therefore matched with it pointwise rather than by rewriting.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 07BM](https://stacks.math.columbia.edu/tag/07BM)
-/

@[expose] public section

namespace NaiveCotangent

open Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The chain map `NL(P) ⟶ NL(P')` induced by a morphism of extensions of `S` over `R`. -/
noncomputable def nlExtensionMap {P P' : Extension R S} (f : P.Hom P') :
    ChainMap (nlOfExtension P) (nlOfExtension P') where
  f₁ := Extension.Cotangent.map f
  f₀ := Extension.CotangentSpace.map f
  comm := LinearMap.ext fun y => (Extension.CotangentSpace.map_cotangentComplex f y).symm

/-- The degree-one component of `nlExtensionMap f` is `Algebra.Extension.Cotangent.map f`. -/
@[simp] lemma nlExtensionMap_f₁ {P P' : Extension R S} (f : P.Hom P') :
    (nlExtensionMap f).f₁ = Extension.Cotangent.map f := rfl

/-- The degree-zero component of `nlExtensionMap f` is
`Algebra.Extension.CotangentSpace.map f`. -/
@[simp] lemma nlExtensionMap_f₀ {P P' : Extension R S} (f : P.Hom P') :
    (nlExtensionMap f).f₀ = Extension.CotangentSpace.map f := rfl

/-- The identity morphism of extensions induces the identity chain map. -/
theorem nlExtensionMap_id (P : Extension R S) :
    nlExtensionMap (Extension.Hom.id P) = ChainMap.id (nlOfExtension P) :=
  ChainMap.ext Extension.Cotangent.map_id Extension.CotangentSpace.map_id

/-- The chain map induced by a composite of morphisms of extensions is the composite of the
induced chain maps. -/
theorem nlExtensionMap_comp {P P' P'' : Extension R S} (f : P.Hom P') (g : P'.Hom P'') :
    nlExtensionMap (g.comp f) = (nlExtensionMap g).comp (nlExtensionMap f) :=
  ChainMap.ext
    (LinearMap.ext fun y => congr($(Extension.Cotangent.map_comp P'' f g) y))
    (LinearMap.ext fun y => congr($(Extension.CotangentSpace.map_comp f g) y))

/-- **Homotopy uniqueness.**  Any two morphisms of extensions induce homotopic chain maps; the
homotopy is `Algebra.Extension.Hom.sub` of the two morphisms. -/
theorem nlExtensionMap_homotopic {P P' : Extension R S} (f g : P.Hom P') :
    Homotopic (nlExtensionMap f) (nlExtensionMap g) :=
  ⟨Extension.Hom.sub f g, Extension.Cotangent.map_sub_map f g,
    LinearMap.ext fun y => congr($(Extension.CotangentSpace.map_sub_map f g) y)⟩

/-- **A morphism of extensions with a morphism back induces a homotopy equivalence.**  The two
composites are morphisms of extensions from an extension to itself, hence homotopic to the
identity. -/
theorem nlExtensionMap_isHomotopyEquiv {P P' : Extension R S} (f : P.Hom P') (g : P'.Hom P) :
    IsHomotopyEquiv (nlExtensionMap f) := by
  refine ⟨nlExtensionMap g, ?_, ?_⟩ <;> rw [← nlExtensionMap_comp, ← nlExtensionMap_id] <;>
    exact nlExtensionMap_homotopic _ _

/-- **Stacks 00S1(4) for extensions.**  A morphism of extensions of `S` over `R` which admits a
morphism in the other direction induces a quasi-isomorphism of naive cotangent complexes. -/
theorem nlExtensionMap_isQuasiIso {P P' : Extension R S} (f : P.Hom P') (g : P'.Hom P) :
    IsQuasiIso (nlExtensionMap f) :=
  isQuasiIso_of_isHomotopyEquiv (nlExtensionMap_isHomotopyEquiv f g)

end NaiveCotangent

end
