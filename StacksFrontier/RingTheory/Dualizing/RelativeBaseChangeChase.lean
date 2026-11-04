module

public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssembly
public import StacksFrontier.RingTheory.Flat.DegreewiseChaseComplex

/-!
# [stacks 0E2F] (2) from the Noetherian case at the residue fields

With the notation of `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssembly` — `R → A` flat
of finite presentation, `R → R'` arbitrary, `A' = A ⊗[R] R'`, `B = A ⊗[R] A`, `B' = A' ⊗[R'] A'`,
`K` a relative dualizing complex for `R → A` and `Y = K' ⊗ᴸ_{A'} B'` — the source's proof of
clause (2) runs the degreewise chase on the complex `E^•` of [stacks 0E1U], and the input the
chase consumes is the *Noetherian case of the clause read at the residue fields of `R`*: for every
prime `𝔭` the cohomology of `RHom_{B_𝔭}(A_𝔭, K_𝔭 ⊗ᴸ_{A_𝔭} B_𝔭)` vanishes outside degree zero,
where the subscript is base change along `R → κ(𝔭)`.  Each `κ(𝔭)` is Noetherian, so that case is
the one [stacks 0BZV] and [stacks 0E2E] settle.

This file closes the gap between the two: the chase's output is turned into clause (2), with the
residue-field vanishing going in as the hypothesis and nothing else about `E^•` surviving beyond
the data [stacks 0E1U] produces.

## Main results

* `Dualizing.subsingleton_hom_restrictedUnitSingle_of_isZero_homology_derivedHom` — the converse of
  `Dualizing.isZero_homology_derivedHom_of_subsingleton`: a vanishing cohomology module of a
  derived-Hom object kills the morphisms out of the restricted unit.
* `Dualizing.exact_rTensor_residueField_of_isZero_homology` — the residue-field vanishing, read in
  the shape the chase consumes it.
* `Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldHomology` — **clause (2) from
  the residue-field vanishing**, together with the degree-zero generator.

## What is carried, and what is not

The hypothesis `hE` is the base-change clause of [stacks 0E1U] in its own shape, at the left
coprojection `B → B ⊗[R] S'` and quantified over `S'`: the chase needs it at every residue field
`κ(𝔭)` as well as at `R'`, and [stacks 0E1U] states it for every `S'` at once, so nothing is
restated.  The remaining hypotheses `hEflat` and `hEfin` are the two finiteness clauses of the
same statement — the terms of `E^•` are `R`-flat and finitely presented over `B` — which is what
makes the local criterion [stacks 00ME] inside the chase applicable.

Two things are **not** supplied here.

*The residue-field vanishing itself.*  It is the Noetherian case of the clause, which the source
gets from [stacks 0BZV] and [stacks 0E2E]; in this library both carry
`Dualizing.PolynomialPresentation.ProjectionCompatibility`, the projection-formula compatibility
of [stacks 0E2A] at the square of a presentation, through
`Dualizing.PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq`.  That is the
same proposition `Dualizing.UpperShriekInputs` already bundles, so a consumer that holds the
bundle — `Dualizing.exists_isRelativeDualizingComplex` does — has it; it remains the keystone of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange`.

At the upper shriek complex `φ^!(R)` the vanishing is itself a theorem of this library, namely
`Dualizing.isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek` of
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian`, which gets it from
[stacks 0BZV] with [stacks 0E2E] and asks for nothing past that one compatibility.  What is *not*
available is the vanishing at the arbitrary `K` the statement below is written at: to transport
it from `φ^!(R)` to `K` one needs `K ≅ φ^!(R)`, which is [stacks 0E2D].  That tag is in this
library as `Dualizing.nonempty_iso_of_isRelativeDualizingComplex`, whose hypothesis — the
invertibility of the two diagonals of [stacks 0BYN] — is *false* at the witness of
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation`, and is discharged outright only
when the diagonal or the two derived base changes are perfect, or under the Tor-amplitude bound
of [stacks 0ATK] (3).  So `hres` stays a hypothesis here, and the degreewise chase of this file
is what a general `K` has to be reached through.

*The degree-zero generator `h0`.*  The assembly
`Dualizing.nonempty_homologyAddEquiv_restrictedUnitSingle` used here is additive, so it says
nothing about the `A'`-action the clause needs in degree zero; the generator is therefore a
hypothesis of the statement below, in the shape
`Dualizing.homRestrictedUnitSingleLinearEquiv` converts.  It is **not** a residue of the proof:
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero` discharges it from the degree-zero
output of the same chase, through the `B'`-linear reading of the assembly in
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssemblyLinear`, and
`Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldHomology_of_isIso_cyclesComparison`
is the statement below with `h0` gone.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
* [Stacks Project, Tag 00ME](https://stacks.math.columbia.edu/tag/00ME)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DegreewiseChase (ResidueFieldAt)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Dualizing.smulHomRestrictedUnitSingle

universe u

namespace Dualizing

noncomputable section

section Corepresented

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- **The vanishing form, read the other way.**  If `H^j(RHom_S(T, Y))` is zero then there are no
nonzero morphisms from `T[0]` into `Y⟦j⟧`.

This is the converse of `Dualizing.isZero_homology_derivedHom_of_subsingleton`, by the same
additive identification `Dualizing.nonempty_derivedHomHomologyAddEquiv`: the cohomology module and
the morphism group are isomorphic as additive groups, and being a subsingleton passes along an
additive isomorphism in either direction.  It is what lets a vanishing of cohomology — the form in
which the Noetherian case of [stacks 0E2F] (2) is available — be fed to the assembly, which reads
its hypothesis on the morphism groups. -/
theorem subsingleton_hom_restrictedUnitSingle_of_isZero_homology_derivedHom
    (Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ)
    (h : Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
      ((derivedHom.{u, u, u} f).obj Y))) :
    Subsingleton (restrictedUnitSingle f 0 ⟶
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y) := by
  obtain ⟨e⟩ := nonempty_derivedHomHomologyAddEquiv f Y j
  have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
      ((derivedHom.{u, u, u} f).obj Y)) := ModuleCat.isZero_iff_subsingleton.1 h
  exact Function.Injective.subsingleton e.symm.injective

end Corepresented

section Chase

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R'] [Module.Flat R A] [Algebra.FinitePresentation R A]
  (K : DerivedCategory (ModuleCat.{u} A))
  (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
  [∀ i : ℤ, Projective (P.X i)] (hP : CochainComplex.KFlat.{u, u} P)
  (eP : DerivedCategory.Q.obj P ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
  (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
  (hflat : ∀ i : ℤ, Module.Flat R
    ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
  (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K)
  (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
  (hE : ∀ (S' : Type u) [CommRing S'] [Algebra R S'],
    Nonempty ((diagonalIncludeLeftExtend R A S').obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] S')
        ((diagonalIncludeLeftExtend R A S').obj P)
        ((diagonalIncludeLeftExtend R A S').obj F)))

include dP hP eP d hflat eF hE

omit [Algebra.FinitePresentation R A] in
/-- Fix a prime `𝔭` of `R`, put `κ = κ(𝔭)` and let `j` be a degree. If the cohomology of
`RHom_{B_κ}(A_κ, K_κ ⊗ᴸ_{A_κ} B_κ)` vanishes in degree `j`, then
`E^{j-1} ⊗_R κ → E^j ⊗_R κ → E^{j+1} ⊗_R κ` is exact in the middle. -/
theorem exact_rTensor_residueField_of_isZero_homology (p : Ideal R) [p.IsPrime] (j : ℤ)
    (hvan : Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] ResidueFieldAt R p)) j).obj
        ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul' (ResidueFieldAt R p) :
              (A ⊗[R] ResidueFieldAt R p) ⊗[ResidueFieldAt R p]
                (A ⊗[R] ResidueFieldAt R p) →ₐ[ResidueFieldAt R p]
                (A ⊗[R] ResidueFieldAt R p)).toRingHom).obj
          (diagonalBaseChangeTarget R A (ResidueFieldAt R p) K)))) :
    Function.Exact
      (LinearMap.rTensor (ResidueFieldAt R p)
        (((diagonalRestrictR R A).obj E).d (j - 1) j).hom)
      (LinearMap.rTensor (ResidueFieldAt R p)
        (((diagonalRestrictR R A).obj E).d j (j + 1)).hom) := by
  obtain ⟨e⟩ := nonempty_homologyAddEquiv_restrictedUnitSingle R A (ResidueFieldAt R p) K P dP
    hP eP F d hflat eF E
    (nonempty_diagonalBaseChangeExtend_iso_homComplexR R A (ResidueFieldAt R p) E P F
      (hE (ResidueFieldAt R p))) j
  have := subsingleton_hom_restrictedUnitSingle_of_isZero_homology_derivedHom
    (Algebra.TensorProduct.lmul' (ResidueFieldAt R p) :
      (A ⊗[R] ResidueFieldAt R p) ⊗[ResidueFieldAt R p]
        (A ⊗[R] ResidueFieldAt R p) →ₐ[ResidueFieldAt R p]
        (A ⊗[R] ResidueFieldAt R p)).toRingHom
    (diagonalBaseChangeTarget R A (ResidueFieldAt R p) K) j hvan
  have hzero : Limits.IsZero
      (((diagonalBaseChangeExtend R A (ResidueFieldAt R p)).obj E).homology j) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact Function.Injective.subsingleton e.injective
  exact (StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor
      ((diagonalRestrictR R A).obj E) (ModuleCat.of R (ResidueFieldAt R p)) j).1
    ((StacksDraft.BaseChangeCancellation.isZero_homology_extendScalars_includeLeft_iff E j).1
      ((isZero_homology_diagonalBaseChangeExtend_iff R A (ResidueFieldAt R p) E j).1 hzero))

/-- **Stacks Project, Tag 0E2F (2), from the Noetherian case at the residue fields of `R`.**  Let
`R → A` be flat of finite presentation, let `K` be a relative dualizing complex for `R → A` and
let `R → R'` be any ring map.  Suppose given the data of [stacks 0E1U] at the diagonal square —
the two representatives `P^•` and `F^•`, the complex `E^•` with `R`-flat finite `B`-modules as
terms, and the base-change clause at every target ring.  If for every prime `𝔭` of `R` the
cohomology of `RHom_{B_𝔭}(A_𝔭, K_𝔭 ⊗ᴸ_{A_𝔭} B_𝔭)` vanishes outside degree zero, and if in degree
zero some morphism `A'[0] ⟶ Y` generates the morphism group freely over `A'`, then `K'` is a
relative dualizing complex for `R' → A'`.

This is the source's Step 3 and Step 4 made into one statement.  Step 3 is the degreewise chase:
the residue-field vanishing is exactly its input, and
`StacksDraft.DegreewiseChase.exact_rTensor_of_exact_rTensor_residueField_complex` runs it at each
degree, delivering exactness after `⊗_R R'` for the arbitrary — in particular non-Noetherian —
ring `R'`, which is the whole point of passing through the residue fields.  Step 4, the degree-zero
computation, is the hypothesis `h0`; it is obtained from the chase in
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero`, which needs the assembly read
`B'`-linearly rather than additively.

The residue-field vanishing is the Noetherian case of this very clause, and in this library it
carries the projection-formula compatibility of [stacks 0E2A] through [stacks 0BZV] and
[stacks 0E2E] — the proposition `Dualizing.UpperShriekInputs` bundles.  It is **not** discharged
here. -/
theorem isRelativeDualizingComplex_baseChange_of_residueFieldHomology
    [IsNoetherianRing (A ⊗[R] A)]
    (hEflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (E.X i)))
    (hEfin : ∀ i : ℤ, Module.Finite (A ⊗[R] A) (E.X i))
    (hK : IsRelativeDualizingComplex R A K)
    (hres : ∀ (p : Ideal R) [p.IsPrime] (j : ℤ), j ≠ 0 → Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] ResidueFieldAt R p)) j).obj
        ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul' (ResidueFieldAt R p) :
              (A ⊗[R] ResidueFieldAt R p) ⊗[ResidueFieldAt R p]
                (A ⊗[R] ResidueFieldAt R p) →ₐ[ResidueFieldAt R p]
                (A ⊗[R] ResidueFieldAt R p)).toRingHom).obj
          (diagonalBaseChangeTarget R A (ResidueFieldAt R p) K))))
    (h0 : ∃ g : restrictedUnitSingle
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
        (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) (0 : ℤ)).obj
          (diagonalBaseChangeTarget R A R' K),
      Function.Bijective fun a : A ⊗[R] R' =>
        smulRestrictedUnitSingle
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom a 0 ≫ g) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) :=
  isRelativeDualizingComplex_baseChange_of_exact_rTensor R A R' K P dP hP eP F d hflat eF E
    (hE R') hK
    (fun j hj => by
      have := hEfin j
      exact StacksDraft.DegreewiseChase.exact_rTensor_of_exact_rTensor_residueField_complex
        R (A ⊗[R] A) E j (hEflat (j + 1))
        (fun p _ => exact_rTensor_residueField_of_isZero_homology R A K P dP hP eP F d hflat eF
          E hE p j (hres p j hj)) (ModuleCat.of R R'))
    h0

end Chase

end

end Dualizing

end
