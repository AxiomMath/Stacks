module

public import StacksFrontier.Deformation.SquareZero.NaiveCotangentUlifted
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.Perfect.Local

/-!
# Stacks 0A6A at the naive cotangent complex

Let `B` be a `k`-algebra of finite type over a Noetherian ring and let `B → Bʰ` be flat.
Stacks 0A6A (`Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange`) says that the
derived-Hom base-change morphism of Stacks 0E1X

`RHom_B(K, M) ⊗ᴸ_B Bʰ ⟶ RHom_{Bʰ}(K ⊗ᴸ_B Bʰ, M ⊗ᴸ_B Bʰ)`

is invertible in four cases.  The third of them is the one the proof of Stacks 0DZC appeals to:
the ring map is flat, `K` is pseudo-coherent and `M` is bounded below.  This file instantiates
that case at `K = NL_{B/k}`, which is what pulls a flat base change out of
`Ext¹_B(NL_{B/k}, -)`.

## Main results

* `Stacks.Deformation.isIso_derivedHomBaseChange_naiveCotangentCochainComplex`: the derived-Hom
  base-change morphism along a flat `B → Bʰ` is invertible at the naive cotangent complex of `B`
  over `k`, for every bounded-below coefficient object.

## Implementation notes

The two hypotheses of case (3) of Stacks 0A6A that are about the data rather than about the
coefficients are discharged here.  Flatness of the ring map is `RingHom.flat_algebraMap_iff`
applied to `Module.Flat B Bʰ`, which for the henselization of a pair is
`flat_henselization_and_bijective_quotientMap` (Stacks 0AGU).  Pseudo-coherence of the naive
cotangent complex is `Stacks.Deformation.isPseudoCoherent_naiveCotangentCochainComplex`; it is
*not* readable off the terms of the complex, see the implementation notes there.  Boundedness
below of the coefficients stays a hypothesis, because it depends on the coefficient object: for
a module placed in degree `0` it holds with bound `0`.

The derived functor `F` of termwise extension of scalars, its comparison and the
left-derived-functor property are taken as arguments rather than fixed to a model, exactly as
Stacks 0A6A itself takes them: the statement is then an instantiation of that theorem with
nothing added or chosen, and a caller which already has a
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` bundle — as
`Stacks.Deformation.naiveCotangentDerivedBaseChangeExtOneEquiv` does — passes its three fields.
The three `letI`s on adjointness are the ones Stacks 0A6A's own statement carries, in the same
form and with the same universe instantiation.

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0E1V](https://stacks.math.columbia.edu/tag/0E1V)
* [Stacks Project, Tag 0DZC](https://stacks.math.columbia.edu/tag/0DZC)
-/

@[expose] public section

open CategoryTheory Category Limits
open StacksDraft.PseudoCoherence

universe uk uB v

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (k : Type uk) [CommRing k] [IsNoetherianRing k] (B : Type uB) [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B] (Bh : Type uB) [CommRing Bh] [Algebra B Bh]

/-- **Stacks 0A6A, case (3), at the naive cotangent complex.**  For `B` of finite type over a
Noetherian ring `k` and a flat `B`-algebra `Bʰ`, the derived-Hom base-change morphism

`RHom_B(NL_{B/k}, M) ⊗ᴸ_B Bʰ ⟶ RHom_{Bʰ}(NL_{B/k} ⊗ᴸ_B Bʰ, M ⊗ᴸ_B Bʰ)`

is an isomorphism for every object `M` of `D(B)` that is bounded below.  The naive cotangent
complex is pseudo-coherent by
`Stacks.Deformation.isPseudoCoherent_naiveCotangentCochainComplex`, and the ring map is flat, so
the third disjunct of Stacks 0A6A applies. -/
public theorem isIso_derivedHomBaseChange_naiveCotangentCochainComplex
    (hflat : Module.Flat B Bh) :
    letI : (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uk uB v, uB, uB}
        (algebraMap B Bh)).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uk uB v, uB, uB} (algebraMap B Bh)).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uk uB v, uB, uB}
        (algebraMap B Bh)).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uk uB v, uB, uB} (algebraMap B Bh)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uk uB v, uB, uB}
        (algebraMap B Bh)).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uk uB v} B) ⥤
        DerivedCategory (ModuleCat.{max uk uB v} Bh))
      (comparison : DerivedCategory.Q ⋙ F ⟶
        (ModuleCat.extendScalars.{uB, uB, max uk uB v}
          (algebraMap B Bh)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      [F.IsLeftDerivedFunctor comparison
        (HomologicalComplex.quasiIso (ModuleCat.{max uk uB v} B) (ComplexShape.up ℤ))]
      (M : DerivedCategory (ModuleCat.{max uk uB v} B)) (b : ℤ),
      DerivedCategory.IsGE M b →
      IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uB, uB, max uk v}
        (algebraMap B Bh) F comparison
        (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{uk, uB, v} k B)) M) := by
  intro F comparison _ M b hM
  exact Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{uB, uB, max uk v}
    (algebraMap B Bh) F comparison _ M
    (Or.inr (Or.inr (Or.inl ⟨RingHom.flat_algebraMap_iff.mpr hflat,
      isPseudoCoherent_naiveCotangentCochainComplex.{uk, uB, v} k B, ⟨b, hM⟩⟩)))

end

end Stacks.Deformation

end
