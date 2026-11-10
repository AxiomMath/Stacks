module

public import StacksFrontier.Homology.ExtendScalars.BaseChangeCancellation
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.RingEquivTransport
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeRepresentatives
public import StacksFrontier.RingTheory.Flat.DegreewiseChase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The assembly of [stacks 0E2F] (2): [stacks 0E1U] read on the morphism groups

With the notation of `StacksFrontier/RingTheory/Dualizing/RelativeBaseChangeTorIndependence.lean` --
`R → A` flat of finite presentation, `R → R'` arbitrary, `A' = A ⊗[R] R'`, `B = A ⊗[R] A`,
`B' = A' ⊗[R'] A'`, and `Δ : B → A`, `Δ' : B' → A'` the two multiplication maps -- the proof of
[stacks 0E2F] (2) applies [stacks 0E1U] at the flat ring map `R → B`, to the diagonal `A` and to
`X = K ⊗ᴸ_A B`.  That produces two representatives `P^•` and `F^•` and the Hom complex
`E^• = Hom^•_B(P^•, F^•)`, *compatibly with base change along `R → R'`*: the naive base change
`E^• ⊗_B B'` is `Hom^•_{B'}(P^• ⊗_B B', F^• ⊗_B B')`.  The source then computes the cohomology of
`E^• ⊗_B B'` degree by degree.

This file is the last step before the chase: it turns that computation into the two hypotheses of
`Dualizing.isRelativeDualizingComplex_baseChange_of_hom`, which are read on the morphism groups
`Hom_{D(B')}(A'[0], Y⟦j⟧)` for `Y = (K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'`.

## Main definitions

* `Dualizing.diagonalBaseChangeExtend` -- termwise extension of scalars along the map of
  diagonals, on complexes.
* `Dualizing.homComplexRHomologyAddEquiv` -- the representability clause of [stacks 0E1U], which
  is [stacks 0A66], read on the derived category: `H^n(Hom^•_S(P, L)) ≃+ Hom_{D(S)}(P, L⟦n⟧)`.
* `Dualizing.homRestrictedUnitSingleLinearEquiv` -- **the `A'`-linearity of the degree-zero
  identification**: the morphisms `A'[0] ⟶ Y` are `A'` as an `A'`-module as soon as one of them
  generates the group freely.

## Main results

* `Dualizing.nonempty_homologyAddEquiv_restrictedUnitSingle` -- **the assembly**:
  `H^j(E^• ⊗_B B') ≃+ Hom_{D(B')}(A'[0], Y⟦j⟧)`, and
  `Dualizing.nonempty_homologyFunctorAddEquiv_restrictedUnitSingle`, the same read through
  `DerivedCategory.homologyFunctor`.
* `Dualizing.subsingleton_hom_restrictedUnitSingle_of_isZero_homology` -- **the hypothesis `hvan`
  discharged** from the chase's vanishing.
* `Dualizing.nonempty_linearEquiv_hom_diagonalDerivedExtension` -- the diagonal condition of
  [stacks 0E2C] read in degree zero, `A`-linearly: `Hom_{D(B)}(A[0], K ⊗ᴸ_A B) ≃ₗ[A] A`.  This
  is the statement whose base change the chase's degree-zero step computes.
* `Dualizing.isRelativeDualizingComplex_baseChange_of_homComplexHomology` -- clause (2) from the
  chase's output: the vanishing of `H^j(E^• ⊗_B B')` for `j ≠ 0` and a free `A'`-generator of
  `Hom_{D(B')}(A'[0], Y)`.
* `Dualizing.nonempty_diagonalBaseChangeExtend_iso_homComplexR` and
  `Dualizing.isZero_homology_diagonalBaseChangeExtend_iff` -- the two hypotheses about `E^•` read
  at the left coprojection `B → B ⊗[R] R'` instead of at the map of diagonals, and
  `Dualizing.isRelativeDualizingComplex_baseChange_of_homComplexHomology_includeLeft`, clause (2)
  in that form, which is the tagged statement.
* `Dualizing.isZero_homology_diagonalIncludeLeftExtend_iff_exact_rTensor` -- the vanishing read at
  the degreewise chase's own statement, by the base-change cancellation
  `(B ⊗_R R') ⊗_B M = M ⊗_R R'`, and
  `Dualizing.isRelativeDualizingComplex_baseChange_of_exact_rTensor`, clause (2) with the chase's
  output going in verbatim and nothing but the degree-zero generator left.

## The two hypotheses and the two readings of the assembly

The assembly below is **additive**, which is all the vanishing hypothesis needs: `Subsingleton`
transports along an `AddEquiv`, so
`Dualizing.subsingleton_hom_restrictedUnitSingle_of_isZero_homology` needs nothing more.

In degree zero the conclusion asked for is an isomorphism of `A'`-modules, and there the additive
form is not enough.  The `A'`-action on `Hom_{D(B')}(A'[0], Y⟦j⟧)` is
`Dualizing.smulHomRestrictedUnitSingle`, precomposition with multiplication on the source; it
exists only through the source object, restriction of scalars along `Δ'`, which is why the
corepresentability of the cohomology of derived Hom is `A'`-linear only after that action is
written down by hand (`Dualizing.derivedHomHomologyAddEquiv_smul`).  The degree-zero statement is
therefore stated here on the morphism group, as a **free generator**: a morphism `g : A'[0] ⟶ Y`
for which `a ↦ a • g` is bijective.  That map is `A'`-linear by construction
(`LinearMap.toSpanSingleton`), so `Dualizing.homRestrictedUnitSingleLinearEquiv` is exactly the
`≃ₗ[A']` the clause consumes.  `Dualizing.nonempty_linearEquiv_hom_diagonalDerivedExtension`
produces such a generator before base change, from the defining condition of `K`, which is an
isomorphism in `D(A)` and hence `A`-linear on cohomology.

The generator is **not** an irreducible residue of the architecture.  `E^• ⊗_B B'` is a complex of
`B'`-modules and `D(B')` is a `B'`-linear category, so all three steps of the assembly are
`B'`-linear; that reading is
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssemblyLinear`, and since `Δ' : B' → A'` is
surjective a `B'`-linear identification of two modules that both carry an `A'`-structure is
automatically `A'`-linear.  `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero`
discharges the generator that way, from the degree-zero output of the degreewise chase.

## The crossing from the left coprojection to the map of diagonals

The three identifications of
`StacksFrontier/RingTheory/Dualizing/RelativeBaseChangeRepresentatives.lean`, and hence the
assembly,
are stated at the *map of diagonals* `Dualizing.diagonalBaseChangeMap : B → B'`, whereas
[stacks 0E1U] states its base-change clause, and the chase its vanishing, on the base change
`B ⊗[R] R'`, i.e. at the left coprojection `Algebra.TensorProduct.includeLeftRingHom`.  The two
ring maps differ by the ring isomorphism `Dualizing.diagonalBaseChangeEquiv` -- the map of
diagonals *is* the left coprojection followed by it -- and the crossing is now available:
`StacksDraft.ScalarTransport.nonempty_extendScalars_iso_homComplexR_comp` transports a termwise
extension-of-scalars functor together with a Hom complex along a ring isomorphism of the target,
and `StacksDraft.ScalarTransport.isZero_homology_extendScalars_comp_iff` transports a vanishing
of cohomology.  Both hypotheses about `E^•` are therefore read at the left coprojection in
`Dualizing.isRelativeDualizingComplex_baseChange_of_homComplexHomology_includeLeft`, by
`Dualizing.nonempty_diagonalBaseChangeExtend_iso_homComplexR` and
`Dualizing.isZero_homology_diagonalBaseChangeExtend_iff`.

## What this still carries

* The base-change clause of [stacks 0E1U] is taken as the hypothesis `hE`.  It is no longer
  restated at the map of diagonals: in the tagged form it is read at [stacks 0E1U]'s own left
  coprojection, so the clause goes in verbatim.
* The vanishing hypothesis is no longer restated either: the cancellation
  `(B ⊗_R R') ⊗_B M = M ⊗_R R'` -- no ring isomorphism occurs in it --
  (`StacksDraft.BaseChangeCancellation.isZero_homology_extendScalars_includeLeft_iff`) carries the
  chase's `StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor`,
  stated at `tensorModuleRight R'` over `R`, to `E^• ⊗_B (B ⊗_R R')`, so in
  `Dualizing.isRelativeDualizingComplex_baseChange_of_exact_rTensor` the chase's output goes in
  verbatim as well.
* The degree-zero generator is a hypothesis of the statements below and is discharged in
  `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero`, from the base change of the
  generator of `Dualizing.nonempty_linearEquiv_hom_diagonalDerivedExtension` and the chase's
  degree-zero step, read through the `B'`-linear assembly of
  `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssemblyLinear`.
* Beneath the chase, the residue-field input still carries `Dualizing.KFlatAlgebraActionEq`
  through `Dualizing.PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq`.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Dualizing.smulHomRestrictedUnitSingle

universe u

namespace Dualizing

noncomputable section

section Representability

variable {S : Type u} [CommRing S]

/-- **[stacks 0A66] read on the derived category.**  For `P` a bounded above complex of projective
`S`-modules and `L` any complex, the degree-`n` cohomology of the `S`-linear Hom complex
`Hom^•_S(P, L)` is the group of morphisms `P ⟶ L⟦n⟧` in `D(S)`.

This is `cohomologyClassRHomAddEquiv` with two translations folded in: the homology of
`CochainComplex.HomComplexR`, a complex of `S`-modules, is the homology of the underlying complex
of abelian groups `CochainComplex.HomComplex` (restriction of scalars to `Ab` is exact), and
morphisms in the homotopy category localize through `DerivedCategory.quotientCompQhIso` and
`DerivedCategory.Q.commShiftIso`.  It is the form in which the representability clause of
[stacks 0E1U] is consumed. -/
@[sga "4½ Etat_0 3.2.3" "special case"]
def homComplexRHomologyAddEquiv (P L : CochainComplex (ModuleCat.{u} S) ℤ) (d n : ℤ)
    [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] :
    ((CochainComplex.HomComplexR S P L).homology n : Type u) ≃+
      (DerivedCategory.Q.obj P ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) n).obj
          (DerivedCategory.Q.obj L)) :=
  ((((CochainComplex.HomComplexR S P L).sc n).mapHomologyIso
          (forget₂ (ModuleCat.{u} S) Ab)).symm.addCommGroupIsoToAddEquiv.trans
      ((CochainComplex.HomComplex.homologyAddEquiv P L n).trans
        (cohomologyClassRHomAddEquiv P L d n))).trans
    ((postcompAddEquiv _
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)).app (L⟦n⟧) ≪≫
            (DerivedCategory.Q.commShiftIso n).app L)).trans
      (precompAddEquiv ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)).app P).symm _))

end Representability

section Linearity

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
  (Z : DerivedCategory (ModuleCat.{u} S))

/-- **The `T`-linearity of the degree-zero identification.**  The morphisms `T[0] ⟶ Z` in `D(S)`
are `T` itself, `T`-linearly, as soon as one of them is a free generator: the `T`-module structure
is `Dualizing.smulHomRestrictedUnitSingle`, precomposition with multiplication, so the map
`t ↦ t • g` out of `T` is `T`-linear by construction and the hypothesis is exactly that it is
bijective.

This is the step at which the `A'`-linearity enters the proof of [stacks 0E2F] (2) in the
statements below: the additive assembly of this file says nothing about the `A'`-action, the
`A'`-structure of `H^0(RHom_{B'}(A', Y))` existing only through the adjunction
(`Dualizing.derivedHomHomologyAddEquiv_smul`), so the linearity is supplied here, where that
action lives, in the shape of a free generator. -/
def homRestrictedUnitSingleLinearEquiv (g : restrictedUnitSingle f 0 ⟶ Z)
    (hg : Function.Bijective fun t : T => smulRestrictedUnitSingle f t 0 ≫ g) :
    (restrictedUnitSingle f 0 ⟶ Z) ≃ₗ[T] T :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton T (restrictedUnitSingle f 0 ⟶ Z) g)
    hg).symm

/-- A free generator makes the morphisms out of `T[0]` a subsingleton-free rank one module; the
pointwise form of `Dualizing.homRestrictedUnitSingleLinearEquiv`, with the generator existentially
quantified. -/
theorem nonempty_homRestrictedUnitSingleLinearEquiv
    (h : ∃ g : restrictedUnitSingle f 0 ⟶ Z,
      Function.Bijective fun t : T => smulRestrictedUnitSingle f t 0 ≫ g) :
    Nonempty ((restrictedUnitSingle f 0 ⟶ Z) ≃ₗ[T] T) :=
  ⟨homRestrictedUnitSingleLinearEquiv f Z h.choose h.choose_spec⟩

end Linearity

section Assembly

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- Termwise extension of scalars along the map of diagonals `B → B'`, on complexes. -/
abbrev diagonalBaseChangeExtend :
    CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ ⥤
      CochainComplex (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))) ℤ :=
  (ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R')).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Extension of scalars preserves projective modules: it is the left adjoint of a functor
preserving epimorphisms. -/
theorem projective_extendScalars {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    (φ : B₁ →+* B₂) (P : ModuleCat.{u} B₁) [Projective P] :
    Projective ((ModuleCat.extendScalars.{u, u, u} φ).obj P) := by
  let : (ModuleCat.restrictScalars.{u, u, u} φ).PreservesEpimorphisms :=
    ⟨fun f hf => (ModuleCat.epi_iff_surjective _).2 ((ModuleCat.epi_iff_surjective f).1 hf)⟩
  exact (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).map_projective P inferInstance

variable [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A))

/-- **The diagonal condition of [stacks 0E2C] in degree zero, `A`-linearly.**  For `K` a relative
dualizing complex for `R → A`, the morphisms `A[0] ⟶ K ⊗ᴸ_A B` in `D(B)` are `A` itself as an
`A`-module, `A` acting on the source by multiplication
(`Dualizing.smulHomRestrictedUnitSingle`).

This is the degree-zero statement whose base change along `R → R'` the degreewise chase computes,
and it is where the `A`-linearity comes from: the defining condition of a relative dualizing
complex is an isomorphism in `D(A)`, so its degree-zero cohomology is an isomorphism of
`A`-modules, and `Dualizing.derivedHomHomologyLinearEquiv` carries that to the morphism group.
A free generator of the base-changed group is what
`Dualizing.isRelativeDualizingComplex_baseChange_of_homComplexHomology` asks for. -/
theorem nonempty_linearEquiv_hom_diagonalDerivedExtension [Algebra.FinitePresentation R A]
    (hK : IsRelativeDualizingComplex R A K) :
    Nonempty ((restrictedUnitSingle
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom 0 ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) (0 : ℤ)).obj
          ((diagonalDerivedExtension R A).obj K)) ≃ₗ[A] A) := by
  obtain ⟨e⟩ := nonempty_derivedHomHomologyLinearEquiv
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
    ((diagonalDerivedExtension R A).obj K) 0
  exact ⟨e.symm.trans (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
      hK.diagonalDerivedHom.some ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
      (ModuleCat.of A A)).toLinearEquiv)⟩

/-- A linear identification of a module with the free rank-one module exhibits a free generator:
`e.symm 1`. -/
theorem bijective_smul_symm_one {T : Type u} {M : Type*} [CommRing T] [AddCommGroup M]
    [Module T M]
    (e : M ≃ₗ[T] T) : Function.Bijective fun t : T => t • e.symm (1 : T) := by
  convert e.symm.bijective using 1
  funext t
  rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one]

variable (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
  [∀ i : ℤ, Projective (P.X i)] (hP : CochainComplex.KFlat.{u, u} P)
  (eP : DerivedCategory.Q.obj P ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
  (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
  (hflat : ∀ i : ℤ, Module.Flat R
    ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
  (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K)
  (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
  (hE : Nonempty ((diagonalBaseChangeExtend R A R').obj E ≅
    CochainComplex.HomComplexR ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
      ((diagonalBaseChangeExtend R A R').obj P) ((diagonalBaseChangeExtend R A R').obj F)))

include dP d hP eP hflat eF hE

/-- **The assembly of [stacks 0E2F] (2).**  Let `P^•` be a bounded above complex of projective
`B`-modules representing the diagonal `A[0]`, let `F^•` be a bounded above complex of `R`-flat
`B`-modules representing `K ⊗ᴸ_A B`, and let `E^•` be a complex of `B`-modules whose termwise base
change along the map of diagonals is `Hom^•_{B'}(P^• ⊗_B B', F^• ⊗_B B')` -- which is the
base-change clause of [stacks 0E1U] at the diagonal square.  Then the degree-`j` cohomology of
`E^• ⊗_B B'` is the group of morphisms `A'[0] ⟶ Y⟦j⟧` in `D(B')`, where
`Y = (K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'`.

These are the groups on which the hypotheses of
`Dualizing.isRelativeDualizingComplex_baseChange_of_hom` are read, and the left-hand side is what
the degreewise chase of `StacksFrontier.RingTheory.Flat.DegreewiseChase` computes.  The three steps
are the representability clause of [stacks 0E1U] (`Dualizing.homComplexRHomologyAddEquiv`, which
is [stacks 0A66]) and the two identifications of the base-changed representatives
(`Dualizing.nonempty_homAddEquiv_restrictedUnitSingle`).

The identification here is additive, which is what the vanishing hypothesis consumes; the
`A'`-linearity needed in degree zero is `Dualizing.homRestrictedUnitSingleLinearEquiv`.  The same
three steps are read `B'`-linearly in
`Dualizing.nonempty_homologyLinearEquiv_restrictedUnitSingle`. -/
theorem nonempty_homologyAddEquiv_restrictedUnitSingle (j : ℤ) :
    Nonempty (((((diagonalBaseChangeExtend R A R').obj E).homology j) : Type u) ≃+
      (restrictedUnitSingle
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
        (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
          (diagonalBaseChangeTarget R A R' K))) := by
  have : ((diagonalBaseChangeExtend R A R').obj P).IsStrictlyLE dP := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R'))
      (P.isZero_of_isStrictlyLE dP i hi)
  have : ∀ i : ℤ, Projective (((diagonalBaseChangeExtend R A R').obj P).X i) := fun i =>
    projective_extendScalars (diagonalBaseChangeMap R A R') (P.X i)
  obtain ⟨e₁⟩ := hE
  obtain ⟨e₃⟩ := nonempty_homAddEquiv_restrictedUnitSingle R A R' K P hP eP F d hflat eF j
  refine ⟨AddEquiv.trans ?_ ((homComplexRHomologyAddEquiv
    ((diagonalBaseChangeExtend R A R').obj P)
    ((diagonalBaseChangeExtend R A R').obj F) dP j).trans e₃)⟩
  exact ((forget₂ (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))) Ab).mapIso
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).mapIso
      e₁)).addCommGroupIsoToAddEquiv

/-- `Dualizing.nonempty_homologyAddEquiv_restrictedUnitSingle` read through
`DerivedCategory.homologyFunctor`, which is the functor the hypotheses of
`Dualizing.isRelativeDualizingComplex_baseChange_of_homology` are stated with.  The translation is
`DerivedCategory.homologyFunctorFactors`. -/
theorem nonempty_homologyFunctorAddEquiv_restrictedUnitSingle (j : ℤ) :
    Nonempty ((((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))) j).obj
        (DerivedCategory.Q.obj ((diagonalBaseChangeExtend R A R').obj E)) : Type u)) ≃+
      (restrictedUnitSingle
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
        (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
          (diagonalBaseChangeTarget R A R' K))) := by
  obtain ⟨e⟩ := nonempty_homologyAddEquiv_restrictedUnitSingle R A R' K P dP hP eP F d hflat eF
    E hE j
  exact ⟨AddEquiv.trans
    ((forget₂ (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))) Ab).mapIso
      ((DerivedCategory.homologyFunctorFactors
        (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))) j).app
          ((diagonalBaseChangeExtend R A R').obj E))).addCommGroupIsoToAddEquiv e⟩

/-- **The vanishing hypothesis of [stacks 0E2F] (2), from the chase.**  If the degree-`j`
cohomology of `E^• ⊗_B B'` vanishes then there is no nonzero morphism `A'[0] ⟶ Y⟦j⟧` in `D(B')`.

Being a subsingleton transports along the additive identification
`Dualizing.nonempty_homologyAddEquiv_restrictedUnitSingle`, so this half needs no linearity. -/
theorem subsingleton_hom_restrictedUnitSingle_of_isZero_homology (j : ℤ)
    (hvan : Limits.IsZero (((diagonalBaseChangeExtend R A R').obj E).homology j)) :
    Subsingleton
      (restrictedUnitSingle
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
        (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
          (diagonalBaseChangeTarget R A R' K)) := by
  obtain ⟨e⟩ := nonempty_homologyAddEquiv_restrictedUnitSingle R A R' K P dP hP eP F d hflat eF
    E hE j
  have : Subsingleton ((((diagonalBaseChangeExtend R A R').obj E).homology j) : Type u) :=
    ModuleCat.isZero_iff_subsingleton.1 hvan
  exact Function.Injective.subsingleton e.symm.injective

/-- **Stacks Project, Tag 0E2F (2), from the degreewise chase.**  Let `R → A` be flat of finite
presentation, let `K` be a relative dualizing complex for `R → A`, let `R → R'` be any ring map
and put `A' = A ⊗[R] R'`, `B = A ⊗[R] A`, `B' = A' ⊗[R'] A'`, `K' = K ⊗ᴸ_A A'` and
`Y = K' ⊗ᴸ_{A'} B'`.  Suppose given the two representatives of [stacks 0E1U] at the diagonal
square — `P^•` bounded above with projective terms and `P^• ≅ A[0]` in `D(B)`, `F^•` bounded above
with `R`-flat terms and `F^• ≅ K ⊗ᴸ_A B` in `D(B)` — together with a complex `E^•` of `B`-modules
whose termwise base change along the map of diagonals is `Hom^•_{B'}(P^• ⊗_B B', F^• ⊗_B B')`,
which is the base-change clause of [stacks 0E1U].  If the cohomology of `E^• ⊗_B B'` vanishes
outside degree zero, and in degree zero some morphism `A'[0] ⟶ Y` generates the morphism group
freely over `A'`, then `K'` is a relative dualizing complex for `R' → A'`.

These two hypotheses are what the degreewise flatness chase of
`StacksFrontier.RingTheory.Flat.DegreewiseChase` computes: the vanishing is read off from the
`R`-flatness of the cokernels of `E^•`, and the degree-zero group is `H^0(E^•) ⊗_R R' = A ⊗_R R'`.
The vanishing crosses to the morphism groups additively
(`Dualizing.subsingleton_hom_restrictedUnitSingle_of_isZero_homology`); the degree-zero statement
is read on the morphism group instead, as a free generator, and converted by
`Dualizing.homRestrictedUnitSingleLinearEquiv`.  It is discharged in
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero`.

The hypothesis `hE` is here stated at the map of diagonals, which is the form the three
identifications of the base-changed representatives are stated at; [stacks 0E1U] states its
base-change clause at its own left coprojection `B → B ⊗[R] R'`, and
`Dualizing.isRelativeDualizingComplex_baseChange_of_homComplexHomology_includeLeft` is this
statement with `hE` in that shape, which is the tagged form. -/
theorem isRelativeDualizingComplex_baseChange_of_homComplexHomology
    [Algebra.FinitePresentation R A] (hK : IsRelativeDualizingComplex R A K)
    (hvan : ∀ j : ℤ, j ≠ 0 →
      Limits.IsZero (((diagonalBaseChangeExtend R A R').obj E).homology j))
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
  isRelativeDualizingComplex_baseChange_of_hom R A R' K hK
    (fun j hj => subsingleton_hom_restrictedUnitSingle_of_isZero_homology R A R' K P dP hP eP
      F d hflat eF E hE j (hvan j hj))
    (homRestrictedUnitSingleLinearEquiv _ _ h0.choose h0.choose_spec)

end Assembly

section IncludeLeft

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- Termwise extension of scalars along the left coprojection `B → B ⊗[R] R'`, on complexes:
the functor at which [stacks 0E1U] states its base-change clause. -/
abbrev diagonalIncludeLeftExtend :
    CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ ⥤
      CochainComplex (ModuleCat.{u} ((A ⊗[R] A) ⊗[R] R')) ℤ :=
  (ModuleCat.extendScalars.{u, u, u}
    (Algebra.TensorProduct.includeLeftRingHom :
      (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R')).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The base-change clause of [stacks 0E1U] moved to the map of diagonals.**  [stacks 0E1U]
states it at the left coprojection `B → B ⊗[R] R'`, while the three identifications of the
base-changed representatives, and hence the assembly, are stated at the map of diagonals
`Dualizing.diagonalBaseChangeMap : B → B'`.  The two ring maps differ by the ring isomorphism
`Dualizing.diagonalBaseChangeEquiv` -- the map of diagonals *is* the left coprojection followed by
it -- so the crossing is the transport of a termwise extension-of-scalars functor and of a Hom
complex along a ring isomorphism of the target,
`StacksDraft.ScalarTransport.nonempty_extendScalars_iso_homComplexR_comp`. -/
theorem nonempty_diagonalBaseChangeExtend_iso_homComplexR
    (E P F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hE : Nonempty ((diagonalIncludeLeftExtend R A R').obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] R')
        ((diagonalIncludeLeftExtend R A R').obj P)
        ((diagonalIncludeLeftExtend R A R').obj F))) :
    Nonempty ((diagonalBaseChangeExtend R A R').obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
        ((diagonalBaseChangeExtend R A R').obj P)
        ((diagonalBaseChangeExtend R A R').obj F)) :=
  StacksDraft.ScalarTransport.nonempty_extendScalars_iso_homComplexR_comp
    (diagonalBaseChangeEquiv R A R').toRingEquiv
    (Algebra.TensorProduct.includeLeftRingHom :
      (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R') E P F hE

/-- **The vanishing hypothesis of clause (2) read at the left coprojection.**  The cohomology of
`E^• ⊗_B B'` vanishes in a degree exactly when that of `E^• ⊗_B (B ⊗_R R')` does: the two
complexes differ by the relabelling along `Dualizing.diagonalBaseChangeEquiv`, which does not
change the underlying modules, and restriction of scalars is exact.  This is
`StacksDraft.ScalarTransport.isZero_homology_extendScalars_comp_iff`.

It is the ring-isomorphism half of the crossing the degreewise chase needs: the chase delivers
the vanishing of the cohomology of `E^• ⊗_R R'`
(`StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor`, at
`tensorModuleRight R'` over `R`), and what separates that from the right-hand side here is the
cancellation `(B ⊗_R R') ⊗_B M = M ⊗_R R'`, in which no ring isomorphism occurs. -/
theorem isZero_homology_diagonalBaseChangeExtend_iff
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (j : ℤ) :
    Limits.IsZero (((diagonalBaseChangeExtend R A R').obj E).homology j) ↔
      Limits.IsZero (((diagonalIncludeLeftExtend R A R').obj E).homology j) :=
  StacksDraft.ScalarTransport.isZero_homology_extendScalars_comp_iff
    (diagonalBaseChangeEquiv R A R').toRingEquiv
    (Algebra.TensorProduct.includeLeftRingHom :
      (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R') E j

/-- `E^•` read as a complex of `R`-modules: the complex the degreewise chase runs on. -/
abbrev diagonalRestrictR :
    CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (ModuleCat.restrictScalars.{u, u, u}
    (algebraMap R (A ⊗[R] A))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The vanishing hypothesis of clause (2) read at the degreewise chase.**  The cohomology of
`E^• ⊗_B (B ⊗_R R')` vanishes in a degree exactly when the three terms
`E^{j-1} ⊗_R R' → E^j ⊗_R R' → E^{j+1} ⊗_R R'` are exact in the middle, which is the statement
the chase produces at every degree and for every `R → R'`.

The two halves are the base-change cancellation `(B ⊗_R R') ⊗_B M = M ⊗_R R'`,
`StacksDraft.BaseChangeCancellation.isZero_homology_extendScalars_includeLeft_iff` -- no ring
isomorphism occurs in it, the relabelling having already been done by
`Dualizing.isZero_homology_diagonalBaseChangeExtend_iff` -- and the chase's own bridge to a
complex, `StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor`.

Together with `Dualizing.isZero_homology_diagonalBaseChangeExtend_iff` this is the whole passage
from the chase's output to the vanishing read at the map of diagonals. -/
theorem isZero_homology_diagonalIncludeLeftExtend_iff_exact_rTensor
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (j : ℤ) :
    Limits.IsZero (((diagonalIncludeLeftExtend R A R').obj E).homology j) ↔
      Function.Exact
        (LinearMap.rTensor (ModuleCat.of R R')
          (((diagonalRestrictR R A).obj E).d (j - 1) j).hom)
        (LinearMap.rTensor (ModuleCat.of R R')
          (((diagonalRestrictR R A).obj E).d j (j + 1)).hom) :=
  (StacksDraft.BaseChangeCancellation.isZero_homology_extendScalars_includeLeft_iff E j).trans
    (StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor
      ((diagonalRestrictR R A).obj E) (ModuleCat.of R R') j)

variable [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A))
  (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
  [∀ i : ℤ, Projective (P.X i)] (hP : CochainComplex.KFlat.{u, u} P)
  (eP : DerivedCategory.Q.obj P ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
  (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
  (hflat : ∀ i : ℤ, Module.Flat R
    ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
  (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K)
  (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
  (hE : Nonempty ((diagonalIncludeLeftExtend R A R').obj E ≅
    CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] R')
      ((diagonalIncludeLeftExtend R A R').obj P)
      ((diagonalIncludeLeftExtend R A R').obj F)))

include dP d hP eP hflat eF hE

/-- **Stacks Project, Tag 0E2F (2), from the degreewise chase, with the base-change clause of
[stacks 0E1U] in its own shape.**  This is
`Dualizing.isRelativeDualizingComplex_baseChange_of_homComplexHomology` with the hypothesis `hE`
read at the left coprojection `B → B ⊗[R] R'` -- the ring map at which [stacks 0E1U] states its
base-change clause, so that the clause goes in verbatim and nothing has to be restated at the map
of diagonals.  The crossing is `Dualizing.nonempty_diagonalBaseChangeExtend_iso_homComplexR`.

What the statement still carries is the *output of the chase*, and nothing else of the Hom
complex: the vanishing of the cohomology of `E^• ⊗_B B'` outside degree zero, which the chase
delivers at `tensorModuleRight R'` over `R`
(`StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor`) and which
`Dualizing.isZero_homology_diagonalIncludeLeftExtend_iff_exact_rTensor` now reads here, so that
`Dualizing.isRelativeDualizingComplex_baseChange_of_exact_rTensor` takes it in the chase's own
shape; and, in degree zero, a free `A'`-generator of the morphisms `A'[0] ⟶ Y`, which
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero` produces from the `B'`-linear
reading of the assembly.  Beneath the chase the
residue-field input carries `Dualizing.KFlatAlgebraActionEq` through
`Dualizing.PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq`. -/
theorem isRelativeDualizingComplex_baseChange_of_homComplexHomology_includeLeft
    [Algebra.FinitePresentation R A] (hK : IsRelativeDualizingComplex R A K)
    (hvan : ∀ j : ℤ, j ≠ 0 →
      Limits.IsZero (((diagonalIncludeLeftExtend R A R').obj E).homology j))
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
  isRelativeDualizingComplex_baseChange_of_homComplexHomology R A R' K P dP hP eP F d hflat eF E
    (nonempty_diagonalBaseChangeExtend_iso_homComplexR R A R' E P F hE) hK
    (fun j hj => (isZero_homology_diagonalBaseChangeExtend_iff R A R' E j).2 (hvan j hj)) h0

/-- **Stacks Project, Tag 0E2F (2), with the vanishing read at the degreewise chase.**  This is
`Dualizing.isRelativeDualizingComplex_baseChange_of_homComplexHomology_includeLeft` with its
vanishing hypothesis in the shape the chase delivers it: the exactness in the middle of
`E^{j-1} ⊗_R R' → E^j ⊗_R R' → E^{j+1} ⊗_R R'`, for every degree `j ≠ 0`, which is what
`StacksDraft.DegreewiseChase.flat_cokernel_and_exact_rTensor_of_exact_rTensor_residueField`
produces at each degree from the residue-field test.  The crossing is
`Dualizing.isZero_homology_diagonalIncludeLeftExtend_iff_exact_rTensor`: the base-change
cancellation `(B ⊗_R R') ⊗_B M = M ⊗_R R'` followed by the chase's own bridge to a complex.

What the statement still carries is the degree-zero generator `h0` alone, together with the two
representatives and the base-change clause of [stacks 0E1U] going in verbatim.  The generator is
produced in `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero`, from the `B'`-linear
reading of the assembly and the chase's degree-zero output.  Beneath the chase the residue-field
input carries `Dualizing.KFlatAlgebraActionEq` through
`Dualizing.PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq`. -/
theorem isRelativeDualizingComplex_baseChange_of_exact_rTensor
    [Algebra.FinitePresentation R A] (hK : IsRelativeDualizingComplex R A K)
    (hvan : ∀ j : ℤ, j ≠ 0 → Function.Exact
      (LinearMap.rTensor (ModuleCat.of R R')
        (((diagonalRestrictR R A).obj E).d (j - 1) j).hom)
      (LinearMap.rTensor (ModuleCat.of R R')
        (((diagonalRestrictR R A).obj E).d j (j + 1)).hom))
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
  isRelativeDualizingComplex_baseChange_of_homComplexHomology_includeLeft R A R' K P dP hP eP F d
    hflat eF E hE hK
    (fun j hj =>
      (isZero_homology_diagonalIncludeLeftExtend_iff_exact_rTensor R A R' E j).2 (hvan j hj)) h0

end IncludeLeft

end

end Dualizing

end
