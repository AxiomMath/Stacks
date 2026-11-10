module

public import StacksFrontier.RingTheory.Dualizing.RelativeComposition
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionAssembly
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionDiagonalOverC
public import StacksFrontier.RingTheory.Dualizing.RelativePerfectionTransitivity
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composing relative dualizing complexes: [stacks 0E2H]

Let `R → A → B` be flat ring maps of finite presentation, let `K_{A/R}` be a relative dualizing
complex for `R → A` and `K_{B/A}` one for `A → B`, both in the sense of [stacks 0E2C],
`Dualizing.IsRelativeDualizingComplex`.  [stacks 0E2H] asserts that
`K = K_{A/R} ⊗ᴸ_A K_{B/A}` is a relative dualizing complex for `R → B`.  This file proves it,
at the object `Dualizing.derivedTensorProductOver (algebraMap A B) K_{B/A} |>.obj K_{A/R}`.

The source reduces to a Noetherian base and identifies `K` with `(ψ ∘ φ)^!(R)`.  The proof here
goes straight from the definition [stacks 0E2C] instead.

## Clause (1)

That `K` is `R`-perfect is transitivity of relative perfection,
`Dualizing.isRelativelyPerfect_derivedTensorProductOver` of
`StacksFrontier.RingTheory.Dualizing.RelativePerfectionTransitivity`.

## Clause (2)

Write `C = B ⊗[R] B`, `C' = B ⊗[A] B` and `i : C → C'` for `Dualizing.diagonalQuotient`.  The
diagonal of `R → B` factors through `i`, so clause (2) for `K` follows from clause (2) for
`K_{B/A}` and the isomorphism

  (★)  `RHom_C(C', K ⊗ᴸ_B C) ≅ K_{B/A} ⊗ᴸ_B C'`

of `D(C')`, `Dualizing.DiagonalQuotientDerivedHom`
(`Dualizing.diagonalDerivedHom_of_diagonalQuotientIso`).  (★) is proved in
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionAssembly`: its right-hand side is the
derived extension of scalars `i^* W` of `W = K_{B/A} ⊗ᴸ_B C`, the unit `W ⟶ i_* i^* W` is
surjective on
cohomology, and so (`Dualizing.nonempty_iso_of_restrictScalars_iso_of_epi_unit`) it suffices to
identify the *restrictions* of the two sides to `D(C)` by any isomorphism at all.  That
identification is `Dualizing.restrictExtendScalarsIsoDerivedHomTensor`, which consumes the
untwisted half `RHom_C(C', K_{A/R} ⊗ᴸ_A C) ≅ C'` and the invertibility of the tensor--Hom diagonal
of the single ring `C` at `(W, K_{A/R} ⊗ᴸ_A C, C')`.  The latter is
`Dualizing.isIso_derivedTensorHomDiagonalOverRing_diagonalQuotient_composite`: the restriction of
`W` to `A ⊗[R] A` is K-flat, and the other two arguments are base changes along the flat map
`A ⊗[R] A → C`.

## Main definitions

* `Dualizing.RelativelyPerfectOverBase` -- clause (1) of [stacks 0E2C], named.
* `Dualizing.DiagonalQuotientDerivedHom` -- the isomorphism (★), named.

## Main results

* `Dualizing.relativelyPerfectOverBase_derivedTensorProductOver` -- clause (1) for the composite.
* `Dualizing.diagonalQuotientDerivedHom_derivedTensorProductOver` -- (★) for the composite.
* `Dualizing.isRelativeDualizingComplex_derivedTensorProductOver` -- **[stacks 0E2H]**.

## References

* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0DHV](https://stacks.math.columbia.edu/tag/0DHV)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

/-- **Clause (1) of [stacks 0E2C], named.**  That `K` is perfect relative to the base `R`, in
the spelling the field `relativelyPerfect` of `Dualizing.IsRelativeDualizingComplex` uses. -/
@[sga "6 IV 3.3.1" "special case"]
def RelativelyPerfectOverBase (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    (K : DerivedCategory (ModuleCat.{u} B)) : Prop :=
  PseudoCoherence.IsRelativelyPerfect
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- **The isomorphism (★) of the module documentation, named.**  Writing `C = B ⊗[R] B` and
`C' = B ⊗[A] B`, this says that derived Hom along the surjection
`Dualizing.diagonalQuotient : C → C'` carries the derived base change of `K` along the left
coprojection `B → C` to the derived base change of `L` along the left coprojection `B → C'`.

It is the hypothesis `e` of `Dualizing.diagonalDerivedHom_of_diagonalQuotientIso`, and it holds
for the composite of two relative dualizing complexes by
`Dualizing.diagonalQuotientDerivedHom_derivedTensorProductOver`. -/
def DiagonalQuotientDerivedHom [Module.Flat R A] [Module.Flat A B]
    (K L : DerivedCategory (ModuleCat.{u} B)) : Prop :=
  letI : Module.Flat R B := Module.Flat.trans R A B
  Nonempty
    ((derivedHom.{u, u} (diagonalQuotient R A B).toRingHom).obj
        ((diagonalDerivedExtension R B).obj K) ≅
      (diagonalDerivedExtension A B).obj L)

variable [Module.Flat R A] [Module.Flat A B]
  [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B]

/-- **Clause (1) of [stacks 0E2C] for the composite, proved.**  Let `R → A → B` be flat and of
finite presentation, let `KA` be a relative dualizing complex for `R → A` and `KB` one for
`A → B`.  Then `KA ⊗ᴸ_A KB` is `R`-perfect in `D(B)`.

This is `Dualizing.RelativelyPerfectOverBase` at the object of [stacks 0E2H], and it carries
nothing.  Only the relative perfectness of the two given complexes is used, so the diagonal
conditions of `hKA` and `hKB` are not consumed here.  The content is transitivity of relative
perfection, `Dualizing.isRelativelyPerfect_derivedTensorProductOver`. -/
theorem relativelyPerfectOverBase_derivedTensorProductOver
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA) (hKB : IsRelativeDualizingComplex A B KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    letI : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R A B
    RelativelyPerfectOverBase R B
      ((derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA) :=
  isRelativelyPerfect_derivedTensorProductOver R A B KA KB hKA.relativelyPerfect
    hKB.relativelyPerfect

/-- **The isomorphism (★) for the composite.**  Let `R → A → B` be flat and of finite
presentation, let `KA` be a relative dualizing complex for `R → A` and `KB` one for `A → B`.
Then derived Hom along `B ⊗[R] B → B ⊗[A] B` carries `(KA ⊗ᴸ_A KB) ⊗ᴸ_B (B ⊗[R] B)` to
`KB ⊗ᴸ_B (B ⊗[A] B)`. -/
theorem diagonalQuotientDerivedHom_derivedTensorProductOver
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA) (hKB : IsRelativeDualizingComplex A B KB) :
    DiagonalQuotientDerivedHom R A B
      ((derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA) KB :=
  nonempty_diagonalQuotientDerivedHom_of_isIso_of_epi R A B KA KB hKA
    (isIso_derivedTensorHomDiagonalOverRing_diagonalQuotient_composite R A B KA KB
      hKA.relativelyPerfect hKB.relativelyPerfect)
    (epi_homologyFunctor_map_unit_diagonalDerivedExtension R A B KB)

/-- **[stacks 0E2H], at a general object.**  Let `R → A → B` be flat and of finite presentation,
let `KA` be a relative dualizing complex for `R → A` and `KB` one for `A → B`.  An object `K` of
`D(B)` isomorphic to `KA ⊗ᴸ_A KB` which satisfies the isomorphism (★) of
`Dualizing.DiagonalQuotientDerivedHom` relative to `KB` is a relative dualizing complex for
`R → B`. -/
theorem isRelativeDualizingComplex_of_relativelyPerfectOverBase
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB K : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA)
    (hKB : IsRelativeDualizingComplex A B KB)
    (e : K ≅ (derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA)
    (hstar : DiagonalQuotientDerivedHom R A B K KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    letI : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R A B
    IsRelativeDualizingComplex R B K := by
  let : Module.Flat R B := Module.Flat.trans R A B
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R A B
  exact ⟨isRelativelyPerfect_of_iso _ _ _ e.symm
      (relativelyPerfectOverBase_derivedTensorProductOver R A B KA KB hKA hKB),
    diagonalDerivedHom_of_diagonalQuotientIso R A B K KB hstar.some hKB.diagonalDerivedHom⟩

/-- **Stacks 0E2H.**  Let `R → A → B` be ring maps which are flat and of finite presentation,
let `K_{A/R}` be a relative dualizing complex for `R → A` and `K_{B/A}` one for `A → B`.  Then
`K = K_{A/R} ⊗ᴸ_A K_{B/A}` is a relative dualizing complex for `R → B`.

Clause (1) of [stacks 0E2C] is `Dualizing.relativelyPerfectOverBase_derivedTensorProductOver`
and clause (2) follows from the isomorphism (★),
`Dualizing.diagonalQuotientDerivedHom_derivedTensorProductOver`; see the module
documentation. -/
@[stacks 0E2H]
theorem isRelativeDualizingComplex_derivedTensorProductOver
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA)
    (hKB : IsRelativeDualizingComplex A B KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    letI : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R A B
    IsRelativeDualizingComplex R B
      ((derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA) :=
  isRelativeDualizingComplex_of_relativelyPerfectOverBase R A B KA KB _ hKA hKB (Iso.refl _)
    (diagonalQuotientDerivedHom_derivedTensorProductOver R A B KA KB hKA hKB)

end

end Dualizing

end
