module

public import StacksFrontier.Cotangent.Triangle.FundamentalDisplay

/-!
# A vanishing vertex of the fundamental triangle

For ring maps `A → B → C` the fundamental triangle of Equation 92.7.0.1 displays

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`. When its third vertex `L_{C/B}` vanishes the first arrow of any distinguished triangle
on these vertices is an isomorphism. This file proves that triangle-level step, which is the whole
of the proof of [Stacks, Tag 08R3]. Lemma 08R3 itself, for arbitrary ring maps, is
`CommAlgCat.isIso_fundamentalMor₁_of_isZero_fundamentalVertex₃` and
`CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero_fundamentalVertex₃` in
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, which apply the results here to the
distinguished triangle of Proposition 08QX, `CommAlgCat.productFundamentalTriangle_distinguished`.

## Main results

* `CommAlgCat.isIso_of_isZero_fundamentalVertex₃` and
  `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero`: for a distinguished
  triangle on the three vertices of the display, the vanishing of `L_{C/B}` makes the first arrow
  an isomorphism.
* `CommAlgCat.nonempty_derivedBaseChange_iso_cotangentComplexDerived_of_isZero_obj₃`: the same
  step applied to the triangle of Tag 08SD for an injective map of `A`-algebras, whose third
  vertex is the complex of the base-changed relative differentials.

## Implementation notes

*The vanishing hypothesis is the real one.* In the first form the hypothesis is
`IsZero (CommAlgCat.fundamentalVertex₃ B C)`, and `CommAlgCat.fundamentalVertex₃` is
`L_{C/B} = DerivedCategory.Q.obj (CommAlgCat.cotangentComplex B (CommAlgCat.of B C))`, the
cotangent complex of `B → C` as an object of `D(C)`. It is the input to
`CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁`, which is the source's proof ("a
trivial consequence of the distinguished triangle").

*Why the triangle is an argument here.* These statements are proved before the triangle of
Proposition 08QX is constructed (`StacksFrontier/Cotangent/Triangle/ProductDescent.lean` imports this
file), so they take a distinguished triangle on the display's vertices as an argument; several
files apply them to towers whose triangle they obtain elsewhere.

## References

* [Stacks Project, Tag 08R3](https://stacks.math.columbia.edu/tag/08R3)
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), the display.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), that it is distinguished.
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD), the triangle of the
  differential sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v wB wC

namespace CommAlgCat

section Display

variable (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B] [Algebra A B]
  (C : Type (max u v)) [CommRing C] [Algebra A C] [Algebra B C]
  [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
  [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]

/-- **A vanishing third vertex makes the first arrow invertible.** Let `A → B → C` be ring maps
and let `α, β, γ` form a distinguished triangle on the three vertices of the display 92.7.0.1.
If `L_{C/B} = 0`, then `α : L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A}` is an isomorphism.

This is the step of the proof of [Stacks, Tag 08R3]; the lemma itself, with the triangle of
Proposition 08QX supplied, is `CommAlgCat.isIso_fundamentalMor₁_of_isZero_fundamentalVertex₃`. -/
theorem isIso_of_isZero_fundamentalVertex₃
    {α : fundamentalVertex₁.{u, v, wB, wC} A B C ⟶ fundamentalVertex₂.{u, v, wC} A C}
    {β : fundamentalVertex₂.{u, v, wC} A C ⟶ fundamentalVertex₃.{u, v, wC} B C}
    {γ : fundamentalVertex₃.{u, v, wC} B C ⟶ (fundamentalVertex₁.{u, v, wB, wC} A B C)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{max u v} C)))
    (h : IsZero (fundamentalVertex₃.{u, v, wC} B C)) : IsIso α :=
  (Triangle.isZero₃_iff_isIso₁ _ hT).1 h

/-- **A vanishing third vertex identifies the first two.** For a distinguished triangle on the
three vertices of the display 92.7.0.1, if `L_{C/B} = 0` then `L_{B/A} ⊗^𝐋_B C ≅ L_{C/A}` in
`D(C)`. The lemma [Stacks, Tag 08R3] in this form, with the triangle supplied, is
`CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero_fundamentalVertex₃`. -/
theorem nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero
    {α : fundamentalVertex₁.{u, v, wB, wC} A B C ⟶ fundamentalVertex₂.{u, v, wC} A C}
    {β : fundamentalVertex₂.{u, v, wC} A C ⟶ fundamentalVertex₃.{u, v, wC} B C}
    {γ : fundamentalVertex₃.{u, v, wC} B C ⟶ (fundamentalVertex₁.{u, v, wB, wC} A B C)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{max u v} C)))
    (h : IsZero (fundamentalVertex₃.{u, v, wC} B C)) :
    Nonempty (fundamentalVertex₁.{u, v, wB, wC} A B C ≅ fundamentalVertex₂.{u, v, wC} A C) :=
  have := isIso_of_isZero_fundamentalVertex₃.{u, v, wB, wC} A B C hT h
  ⟨asIso α⟩

end Display

section Injective

variable (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A}
  [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
  [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]

/-- **The vanishing step on the triangle of Tag 08SD.** Let `f : B ⟶ C` be an injective map of
`A`-algebras and suppose the third vertex of `CommAlgCat.cotangentTriangle` — the complex of the
base-changed relative differentials — vanishes. Then `L_{B/A} ⊗^𝐋_B C ≅ L_{C/A}` in `D(C)`, the
derived base change being taken along `f`. The triangle is
`CommAlgCat.exists_distinguished_derivedBaseChange_cotangentTriangle`. -/
theorem nonempty_derivedBaseChange_iso_cotangentComplexDerived_of_isZero_obj₃
    (f : B ⟶ C) (hf : Function.Injective f.hom)
    (h : IsZero ((cotangentTriangle A f hf).obj₃)) :
    Nonempty
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            f.hom.toRingHom).functor.obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, v} A B)) ≅
        DerivedCategory.Q.obj (cotangentComplex.{u, v} A C)) := by
  obtain ⟨α, β, γ, hT⟩ :=
    exists_distinguished_derivedBaseChange_cotangentTriangle.{u, v, wB, wC} A f hf
  have : IsIso α := (Triangle.isZero₃_iff_isIso₁ _ hT).1 h
  exact ⟨asIso α⟩

end Injective

end CommAlgCat

end
