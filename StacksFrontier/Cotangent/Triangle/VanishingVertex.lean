module

public import StacksFrontier.Cotangent.Triangle.FundamentalDisplay

/-!
# A vanishing vertex of the fundamental triangle

For ring maps `A → B → C` the fundamental triangle of Equation 92.7.0.1 displays

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`. When its third vertex `L_{C/B}` vanishes the first arrow is an isomorphism, which is
Lemma 08R3: `L_{C/A} = L_{B/A} ⊗^𝐋_B C`. This file proves that in two forms, one for each
triangle the library can offer.

## Main results

* `CommAlgCat.isIso_of_isZero_fundamentalVertex₃` and
  `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero`: **Tag 08R3** in the
  spelling of the display, with the distinguished triangle of Proposition 08QX carried as a
  hypothesis.
* `CommAlgCat.nonempty_derivedBaseChange_iso_cotangentComplexDerived_of_isZero_obj₃`: **Tag 08R3**
  for an injective map of `A`-algebras, from the triangle of Tag 08SD that this library proves,
  with `L_{C/B}` read as the third vertex of that triangle.

## Implementation notes

*The vanishing hypothesis is the real one.* In the first form the hypothesis is
`IsZero (CommAlgCat.fundamentalVertex₃ B C)`, and `CommAlgCat.fundamentalVertex₃` is
`L_{C/B} = DerivedCategory.Q.obj (CommAlgCat.cotangentComplex B (CommAlgCat.of B C))`, the
cotangent complex of `B → C` as an object of `D(C)`; so the hypothesis is the vanishing of that
object in the derived category and not of some auxiliary zero object. It is load-bearing: it is
the input to `CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁`, which is the whole of
the source's proof ("a trivial consequence of the distinguished triangle"). The conclusion is
stronger than an abstract isomorphism, being that *the first arrow of the given triangle* is
invertible.

*Why the triangle is a hypothesis in the first form.* Proposition 08QX — that the three vertices
of the display form a distinguished triangle for arbitrary ring maps `A → B → C` — is not
formalized in this library; see the `No @[stacks 08QX]` section of
`StacksFrontier.Cotangent.Triangle.Distinguished` for the three steps that are missing. It is
therefore carried as the hypothesis `hT`, in the shape Proposition 08QX gives it. This is the
pattern `CommAlgCat.exists_tensorProduct_nine_diagram` already uses for Tag 09D9 in
`StacksFrontier.Cotangent.TensorProduct`: the fundamental triangles of the two towers are
hypotheses, and what is proved is the consequence drawn from them.

*What the second form costs instead.* The triangle the library does prove, Tag 08SD
(`CommAlgCat.exists_distinguished_derivedBaseChange_cotangentTriangle`), needs `f : B ⟶ C` to be
injective and has as its third vertex the complex of the base-changed relative differentials
rather than `L_{C/B}`; identifying the two is the "key fact" of Tag 08SD, which rests on Tag 08RX
and is not available. So the second form assumes injectivity and reads the source's hypothesis
`L_{C/B} = 0` as the vanishing of `(CommAlgCat.cotangentTriangle A f hf).obj₃`. Nothing is
carried: the triangle comes from the library. The two forms are the same statement of Tag 08R3
under the two hypothesis shapes, and neither subsumes the other.

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
  (C : Type (max u v)) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
  [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]

/-- **Stacks Project, Tag 08R3.**

Let `A → B → C` be ring maps with `L_{C/B} = 0`. Then the first arrow
`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A}` of the fundamental triangle of Equation 92.7.0.1 is an isomorphism,
so that `L_{C/A} = L_{B/A} ⊗^𝐋_B C` in `D(C)`.

The distinguished triangle itself is the hypothesis `hT`, since Proposition 08QX is not
formalized in this library; see the module docstring. The source's proof is the remaining step:
a distinguished triangle whose third vertex vanishes has invertible first arrow. -/
@[stacks 08R3 "the lemma in the spelling of the display 92.7.0.1, with the distinguished \
triangle of Proposition 08QX carried as the hypothesis `hT` because Stacks 08QX is not \
formalized in this library (see the `No @[stacks 08QX]` section of \
`StacksFrontier.Cotangent.Triangle.Distinguished`). The source's hypothesis `L_{C/B} = 0` is the \
vanishing of `CommAlgCat.fundamentalVertex₃`, which is `L_{C/B}` as an object of `D(C)`, and the \
conclusion is that the first arrow `L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A}` of the given triangle is an \
isomorphism"]
theorem isIso_of_isZero_fundamentalVertex₃
    {α : fundamentalVertex₁.{u, v, wB, wC} A B C ⟶ fundamentalVertex₂.{u, v, wC} A C}
    {β : fundamentalVertex₂.{u, v, wC} A C ⟶ fundamentalVertex₃.{u, v, wC} B C}
    {γ : fundamentalVertex₃.{u, v, wC} B C ⟶ (fundamentalVertex₁.{u, v, wB, wC} A B C)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{max u v} C)))
    (h : IsZero (fundamentalVertex₃.{u, v, wC} B C)) : IsIso α :=
  (Triangle.isZero₃_iff_isIso₁ _ hT).1 h

/-- **Stacks Project, Tag 08R3**, as an isomorphism. Let `A → B → C` be ring maps with
`L_{C/B} = 0`. Then `L_{C/A} = L_{B/A} ⊗^𝐋_B C` in `D(C)`. -/
@[stacks 08R3 "the equality of the lemma read as an isomorphism `L_{B/A} ⊗^𝐋_B C ≅ L_{C/A}` in \
`D(C)`, under the same carried hypothesis `hT` as \
`CommAlgCat.isIso_of_isZero_fundamentalVertex₃`"]
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

/-- **Stacks Project, Tag 08R3**, from the triangle of Tag 08SD.

Let `f : B ⟶ C` be an injective map of `A`-algebras and suppose the third vertex of
`CommAlgCat.cotangentTriangle` vanishes. Then `L_{C/A} = L_{B/A} ⊗^𝐋_B C` in `D(C)`, the derived
base change being taken along `f`.

The third vertex of the triangle of Tag 08SD is the complex of the base-changed relative
differentials; identifying it with `L_{C/B}` is the "key fact" of Tag 08SD, which rests on Tag
08RX and is not available in this library, so the source's hypothesis `L_{C/B} = 0` is read as
the vanishing of that vertex. Nothing else is assumed: the triangle is the one the library
proves. -/
@[stacks 08R3 "the lemma for an INJECTIVE map `f : B ⟶ C` of `A`-algebras, with `L_{C/B}` read \
as the third vertex of the triangle of Tag 08SD — the complex of the base-changed relative \
differentials, which Tag 08RX (not formalized in this library) would identify with `L_{C/B}`. \
NO triangle is carried: it is \
`CommAlgCat.exists_distinguished_derivedBaseChange_cotangentTriangle`, proved in this library. \
The conclusion is the source's, `L_{C/A} = L_{B/A} ⊗^𝐋_B C` in `D(C)`, with the derived base \
change taken along `f`"]
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
