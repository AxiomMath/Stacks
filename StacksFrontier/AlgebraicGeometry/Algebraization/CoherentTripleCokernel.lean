module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedPointReduction

/-!
# The cokernel of a monomorphism of coherent triples

The induction step of [Stacks, Tag 0F27] produces, for every integer `n`, the short exact
sequence

`0 → T ⊗ L^{⊗ n} → T ⊗ L^{⊗ n+1} → G ⊗ L^{⊗ n} → 0`

whose left-hand map is multiplication by a global section `s` of the invertible triple
(`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`) and whose right-hand term is the
cokernel of that map. This file builds the quotient: given a morphism of coherent triples both
of whose members are monomorphisms, and given that the cokernel of its punctured-spectrum member
is again `f`-torsion-free, the two cokernels form a coherent triple and the sequence is short
exact.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.cokernelAlpha`: the gluing datum of the quotient --
  the two inverse-image functors preserve cokernels, and the compatibility square of the
  morphism identifies the two cokernels so produced.
* `Stacks.Algebraization.CoherentTriple.cokernelTriple`: **the quotient of a morphism of
  coherent triples, as a coherent triple.**
* `Stacks.Algebraization.CoherentTriple.cokernelHom`: the quotient map onto it.

## Main results

* `Stacks.Algebraization.CoherentTriple.shortExact_cokernelHom`: **a morphism of coherent
  triples both of whose members are monomorphisms sits in a short exact sequence with the
  quotient map onto its cokernel triple.**
* `Stacks.Algebraization.CoherentTriple.exists_shortExact_cokernel`: the same, packaged as an
  existence statement.

## Implementation notes

The `f`-torsion-freeness of the quotient's punctured-spectrum member is a *hypothesis* here, not
a consequence. In [Stacks, Tag 0F27] it is the snake-lemma output of the choice of `s`: the
section is chosen to vanish at no point of `Ass(F) ∪ Ass(F/fF)`, and the second half of that
union is exactly what makes multiplication by `f` injective on the cokernel. Nothing of that
choice is visible at this level of generality, so it is carried as an argument.

`Stacks.Algebraization.CoherentTriple.cokernelTriple` is `@[reducible]`, for the reason recorded
in `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedPointReduction`: a morphism
into it is written with members that have to be recognised as morphisms into a cokernel, and the
recognition is definitional only.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.Algebraization

section

variable {A : Type u} [CommRing A] [IsLocalRing A] {f : A}

/-! ### The gluing datum of the quotient -/

/-- **The gluing datum of the quotient of a morphism of coherent triples.** Both inverse-image
functors of the square of a coherent triple are left adjoints, so they carry a cokernel to the
cokernel of the image; the compatibility square of the morphism is then an isomorphism of the two
morphisms whose cokernels those are. -/
public def CoherentTriple.cokernelAlpha {T S : CoherentTriple A f} (φ : T.Hom S) :
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).obj (cokernel φ.onPunctured) ≅
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj (cokernel φ.onClosedFibre) :=
  PreservesCokernel.iso _ φ.onPunctured ≪≫
    cokernel.mapIso _ _ T.alpha S.alpha φ.compatible ≪≫
      (PreservesCokernel.iso _ φ.onClosedFibre).symm

/-! ### The quotient triple -/

/-- **The quotient of a morphism of coherent triples, as a coherent triple.** Its two members are
the cokernels of the two members of the morphism; they are coherent as cokernels of morphisms of
coherent modules, and they are glued by
`Stacks.Algebraization.CoherentTriple.cokernelAlpha`. -/
@[reducible]
public def CoherentTriple.cokernelTriple {T S : CoherentTriple A f} (φ : T.Hom S)
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) : CoherentTriple A f where
  F := cokernel φ.onPunctured
  F₀ := cokernel φ.onClosedFibre
  coherent_F := by
    have := T.coherent_F
    have := S.coherent_F
    exact _root_.SheafOfModules.cokernel_isCoherent φ.onPunctured
  coherent_F₀ := by
    have := T.coherent_F₀
    have := S.coherent_F₀
    exact _root_.SheafOfModules.cokernel_isCoherent φ.onClosedFibre
  torsionFree := htf
  alpha := CoherentTriple.cokernelAlpha φ

/-- **The quotient map onto the cokernel triple.** Its two members are the two cokernel
projections; that they are compatible is the construction of
`Stacks.Algebraization.CoherentTriple.cokernelAlpha` read off on the two projections. -/
public def CoherentTriple.cokernelHom {T S : CoherentTriple A f} (φ : T.Hom S)
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) :
    S.Hom (CoherentTriple.cokernelTriple φ htf) where
  onPunctured := cokernel.π φ.onPunctured
  onClosedFibre := cokernel.π φ.onClosedFibre
  compatible := by
    change (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map (cokernel.π φ.onPunctured) ≫
        (CoherentTriple.cokernelAlpha φ).hom = _
    rw [CoherentTriple.cokernelAlpha]
    simp only [Iso.trans_hom, Iso.symm_hom, cokernel.mapIso_hom]
    rw [PreservesCokernel.π_iso_hom_assoc, cokernel.π_desc_assoc,
      ← PreservesCokernel.π_iso_hom]
    simp

/-! ### The short exact sequence -/

/-- **A morphism of coherent triples both of whose members are monomorphisms sits in a short
exact sequence with the quotient map onto its cokernel triple.** This is the shape the second
clause of `Stacks.Algebraization.HasHilbertInductionStep` asks for, once the morphism is
multiplication by a global section of the invertible triple. -/
public theorem CoherentTriple.shortExact_cokernelHom {T S : CoherentTriple A f} (φ : T.Hom S)
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) (hmono : Mono φ.onPunctured)
    (hmono₀ : Mono φ.onClosedFibre) :
    CoherentTriple.ShortExact φ (CoherentTriple.cokernelHom φ htf) where
  zero_punctured := cokernel.condition φ.onPunctured
  zero_closedFibre := cokernel.condition φ.onClosedFibre
  punctured := by
    have := hmono
    exact ShortComplex.shortExact_mk_cokernel_π φ.onPunctured
  closedFibre := by
    have := hmono₀
    exact ShortComplex.shortExact_mk_cokernel_π φ.onClosedFibre

/-- `Stacks.Algebraization.CoherentTriple.shortExact_cokernelHom` as an existence statement: a
monomorphism of coherent triples with `f`-torsion-free quotient on the punctured spectrum has a
cokernel in the category of coherent triples. -/
public theorem CoherentTriple.exists_shortExact_cokernel {T S : CoherentTriple A f} (φ : T.Hom S)
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) (hmono : Mono φ.onPunctured)
    (hmono₀ : Mono φ.onClosedFibre) :
    ∃ (G : CoherentTriple A f) (ψ : S.Hom G), CoherentTriple.ShortExact φ ψ :=
  ⟨CoherentTriple.cokernelTriple φ htf, CoherentTriple.cokernelHom φ htf,
    CoherentTriple.shortExact_cokernelHom φ htf hmono hmono₀⟩

end

end Stacks.Algebraization

end
