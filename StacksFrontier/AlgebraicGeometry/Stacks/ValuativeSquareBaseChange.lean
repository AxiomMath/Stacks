module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterion
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Base changing a valuative square to its own valuation ring

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `q` be a valuative square
for it (**Stacks 0CLK**): a valuation ring `A` with fraction field `K`, both of whose spectra lie
in the chosen big fppf site, a generic point `x : Spec K ⟶ 𝒳`, a special point `y : Spec A ⟶ 𝒴`
and a 2-morphism filling the square.

The special point makes `Spec A` an algebraic stack over `S` and `y` a 1-morphism of algebraic
stacks, so `f` can be base changed along it. This module assembles that base change together
with the data the first paragraph of the proof of **Stacks 0CLX** uses on it: the *generic
section*, the 1-morphism `Spec K ⟶ Spec A ×_𝒴 𝒳` determined by the solid square, whose
composites with the two projections are the left edge and the generic point **on the nose**; the
closedness of the projection to `Spec A`, which is universal closedness of `f` read at this one
base change; the quasi-separatedness of that projection; and the quasi-compactness of the generic
section.

## Main definitions

* `AlgebraicGeometry.Stack.ValuativeSquare.specialStack`,
  `AlgebraicGeometry.Stack.ValuativeSquare.genericStack`: the spectra of the valuation ring and of
  its fraction field, as algebraic stacks over `S`.
* `AlgebraicGeometry.Stack.ValuativeSquare.solidSquare`: the solid part of the valuative square,
  as a 2-commutative square of algebraic stacks over the cospan `(y, f)`.
* `AlgebraicGeometry.Stack.ValuativeSquare.baseChangeSquare`: the canonical base change of `f`
  along `y`.
* `AlgebraicGeometry.Stack.ValuativeSquare.genericSection`: the strict comparison of the solid
  square with that base change.

## Main results

* `AlgebraicGeometry.Stack.ValuativeSquare.genericSection_comp_fst`,
  `genericSection_comp_snd`: the two composites of the generic section are the left edge and the
  generic point, both by `rfl`.
* `AlgebraicGeometry.Stack.ValuativeSquare.isClosed_baseChange`: the projection to `Spec A` is
  closed when `f` is universally closed.
* `AlgebraicGeometry.Stack.ValuativeSquare.isQuasiSeparated_baseChange`: it is quasi-separated
  when `f` is.
* `AlgebraicGeometry.Stack.ValuativeSquare.isQuasiCompact_yoneda_map_genericMap`: the left edge is
  quasi-compact as a morphism of representable algebraic spaces.
* `AlgebraicGeometry.Stack.ValuativeSquare.isQuasiCompactMorphism_genericSection`: the generic
  section is quasi-compact as soon as `f` is quasi-separated.

## Implementation notes

**No transport along a 2-isomorphism is needed anywhere here, and that is the point of the
file.** The comparison of the solid square with the canonical base change is
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks`, whose two comparison 2-cells are
identities, so `genericSection ≫ baseChangeSquare.fst` is the left edge of the valuative square
and `genericSection ≫ baseChangeSquare.snd` is its generic point, both definitionally. That is
what lets **Stacks 050Y** be applied to the generic section against the projection with no
bookkeeping: the quasi-compactness hypothesis it wants about the composite is literally
quasi-compactness of the left edge.

Three further economies are worth recording, because each replaces something that looks like
work.

* Closedness of the base change is **not** a base-change stability theorem for universal
  closedness. `AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyClosed` quantifies over every
  1-morphism of algebraic stacks into the target, so instantiating it at the special point *is*
  the statement.
* Quasi-separatedness of the base change is `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isQuasiSeparated_baseChange_of_isTwoFibreProduct`, **Stacks 050F** at an arbitrary 2-fibre
  product of the cospan, applied to the exchanged square: universal closedness is stated at the
  projection to the *test* stack and Stacks 050F at the projection to the *second* factor, and
  `CategoryTheory.Bicategory.TwoCommSq.swap` reconciles the two on the nose.
* The left edge of a valuative square **is** the 1-morphism induced by the morphism of the site
  it names: the `j_canonical` field says the two underlying functors agree, and a based functor
  is determined by its functor, the compatibility with the structure functors being a
  proposition. So `AlgebraicGeometry.Stack.isQuasiCompactMorphism_schemeAlgebraicStackMap`
  applies to it directly.
* Quasi-compactness of the left edge as a morphism of *representable algebraic spaces* — the one
  hypothesis that remained — needs no hypothesis either. Both ends of the left edge are spectra
  of rings, so the morphism of schemes is affine, and
  `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_isAffineHom` turns an affine morphism of
  the site into a quasi-compact morphism of algebraic spaces.

Reading the filler of a valuative square as a 2-isomorphism — which the 2-commutative square
needs and which the valuative square does not carry — is
`CategoryTheory.CatFiberedInGroupoids.twoIso`, available because the 2-category of categories
fibred in groupoids is a `(2,1)`-category.

No declaration here carries a `@[stacks]` attribute: this is the first paragraph of the proof of
Stacks 0CLX, not an assertion of the Stacks Project.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLX](https://stacks.math.columbia.edu/tag/0CLX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.ValuativeSquare

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}

/-- The spectrum of the valuation ring of a valuative square, as an algebraic stack over `S`. -/
noncomputable abbrev specialStack (q : ValuativeSquare B S hS f) :
    AlgebraicStacks.{u, w} B S hS :=
  schemeAlgebraicStack.{u, w} B S hS (siteObject B S hS q.ring_mem q.base)

/-- The spectrum of the fraction field of a valuative square, as an algebraic stack over `S`. -/
noncomputable abbrev genericStack (q : ValuativeSquare B S hS f) :
    AlgebraicStacks.{u, w} B S hS :=
  schemeAlgebraicStack.{u, w} B S hS (siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))

/-- The special point of a valuative square, as a 1-morphism of algebraic stacks. -/
noncomputable abbrev specialMor (q : ValuativeSquare B S hS f) :
    specialStack.{u, w} B S hS q ⟶ 𝒴 :=
  Bicategory.InducedBicategory.mkHom q.y

/-- The left edge of a valuative square, as a 1-morphism of algebraic stacks. -/
noncomputable abbrev leftMor (q : ValuativeSquare B S hS f) :
    genericStack.{u, w} B S hS q ⟶ specialStack.{u, w} B S hS q :=
  Bicategory.InducedBicategory.mkHom q.j

/-- The generic point of a valuative square, as a 1-morphism of algebraic stacks. -/
noncomputable abbrev sourceMor (q : ValuativeSquare B S hS f) :
    genericStack.{u, w} B S hS q ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom q.x

/-- **The solid part of a valuative square, as a 2-commutative square of algebraic stacks** over
the cospan of the special point and `f`. The filler is the filler of the valuative square, read
as a 2-isomorphism. -/
noncomputable def solidSquare (q : ValuativeSquare B S hS f) :
    Bicategory.TwoCommSq (specialMor.{u, w} B S hS q) f where
  pt := genericStack.{u, w} B S hS q
  fst := leftMor.{u, w} B S hS q
  snd := sourceMor.{u, w} B S hS q
  iso := Bicategory.InducedBicategory.isoMk (CatFiberedInGroupoids.twoIso q.γ)

/-- **The canonical base change of `f` along the special point of a valuative square**
(**Stacks 04T2**). Its first projection is the 1-morphism `Spec A ×_𝒴 𝒳 ⟶ Spec A` and its second
projection is `Spec A ×_𝒴 𝒳 ⟶ 𝒳`. -/
noncomputable abbrev baseChangeSquare (q : ValuativeSquare B S hS f) :
    Bicategory.TwoCommSq (specialMor.{u, w} B S hS q) f :=
  twoFibreProductSquareAlgebraicStacks B S hS (specialMor.{u, w} B S hS q) f

/-- **The generic section of a valuative square**: the 1-morphism
`Spec K ⟶ Spec A ×_𝒴 𝒳` determined by the solid square, namely the strict comparison
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks` of the solid square with the canonical
base change. -/
noncomputable abbrev genericSection (q : ValuativeSquare B S hS f) :
    genericStack.{u, w} B S hS q ⟶ (baseChangeSquare.{u, w} B S hS q).pt :=
  (canonicalPreHomAlgebraicStacks B S hS (specialMor.{u, w} B S hS q) f
    (solidSquare.{u, w} B S hS q)).hom

/-- The generic section followed by the projection to `Spec A` is the left edge of the valuative
square, on the nose. -/
theorem genericSection_comp_fst (q : ValuativeSquare B S hS f) :
    genericSection.{u, w} B S hS q ≫ (baseChangeSquare.{u, w} B S hS q).fst =
      leftMor.{u, w} B S hS q :=
  rfl

/-- The generic section followed by the projection to `𝒳` is the generic point of the valuative
square, on the nose. -/
theorem genericSection_comp_snd (q : ValuativeSquare B S hS f) :
    genericSection.{u, w} B S hS q ≫ (baseChangeSquare.{u, w} B S hS q).snd =
      sourceMor.{u, w} B S hS q :=
  rfl

/-- **The base change of a universally closed 1-morphism along the special point of a valuative
square is closed** (**Stacks 0513**, part (2)). This is not a base-change stability theorem:
universal closedness quantifies over every 1-morphism of algebraic stacks into the target, so
this is that quantifier instantiated at the special point. -/
theorem isClosed_baseChange (q : ValuativeSquare B S hS f)
    (hclosed : AlgebraicStacks.UniversallyClosed B S hS f) :
    AlgebraicStacks.IsClosed B S hS (baseChangeSquare.{u, w} B S hS q).fst :=
  hclosed (specialStack.{u, w} B S hS q) (specialMor.{u, w} B S hS q)

/-- **The base change of a quasi-separated 1-morphism along the special point of a valuative
square is quasi-separated** (**Stacks 050F**, the quasi-separated case, at the exchanged
square). -/
theorem isQuasiSeparated_baseChange (q : ValuativeSquare B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    AlgebraicStacks.IsQuasiSeparated B S hS (baseChangeSquare.{u, w} B S hS q).fst :=
  AlgebraicStacks.isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS f
    (specialMor.{u, w} B S hS q) (baseChangeSquare.{u, w} B S hS q).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (specialMor.{u, w} B S hS q) f)) hqs

/-- **The left edge of a valuative square is the 1-morphism of algebraic stacks induced by the
morphism of the site it names.** The `j_canonical` field of the valuative square says the two
underlying functors agree, and a based functor is determined by its underlying functor. -/
theorem leftMor_eq (q : ValuativeSquare B S hS f) :
    leftMor.{u, w} B S hS q = schemeAlgebraicStackMap.{u, w} B S hS q.genericMap := by
  refine congrArg Bicategory.InducedBicategory.mkHom ?_
  refine congrArg Bicategory.InducedBicategory.mkHom ?_
  exact BasedFunctor.eq_of_toFunctor_eq q.j_canonical

/-- **The left edge of a valuative square is quasi-compact as a morphism of representable
algebraic spaces** (**Stacks 03HE**). Both of its ends are spectra of rings, so the morphism of
schemes it induces is affine, and an affine morphism of the site is quasi-compact as a morphism of
algebraic spaces. -/
theorem isQuasiCompact_yoneda_map_genericMap (q : ValuativeSquare B S hS f) :
    Space.IsQuasiCompact B S hS (yoneda.map q.genericMap) := by
  have hK : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of q.K)))
  have hR : IsAffine ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS q.ring_mem q.base)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of q.R)))
  exact Space.isQuasiCompact_yoneda_map_of_isAffineHom B S hS q.genericMap
    (isAffineHom_of_isAffine _)

/-- **The generic section of a valuative square is quasi-compact** as soon as `f` is
quasi-separated.

This is **Stacks 050Y** applied to the factorisation of the generic section through the
projection to `Spec A`: that projection is quasi-separated by Stacks 050F, the composite is the
left edge — on the nose, the comparison being strict — and the left edge is quasi-compact in the
sense of Stacks 050U by
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_schemeAlgebraicStackMap`, whose hypothesis is
`isQuasiCompact_yoneda_map_genericMap`. -/
theorem isQuasiCompactMorphism_genericSection (q : ValuativeSquare B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    IsQuasiCompactMorphism.{u, w} B S hS (genericSection.{u, w} B S hS q) := by
  have hleft : IsQuasiCompactMorphism.{u, w} B S hS (leftMor.{u, w} B S hS q) := by
    rw [leftMor_eq]
    exact isQuasiCompactMorphism_schemeAlgebraicStackMap.{u, w} B S hS q.genericMap
      (isQuasiCompact_yoneda_map_genericMap.{u, w} B S hS q)
  exact isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS
    (genericSection.{u, w} B S hS q) (baseChangeSquare.{u, w} B S hS q).fst hleft
    (isQuasiSeparated_baseChange.{u, w} B S hS q hqs)

end AlgebraicGeometry.Stack.ValuativeSquare

end
