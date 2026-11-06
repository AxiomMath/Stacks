module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExt
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssembly

/-!
# The assembly of [stacks 0E2F] (2), `B'`-linearly

The assembly of `StacksFrontier/RingTheory/Dualizing/RelativeBaseChangeAssembly.lean` identifies the
degree-`j` cohomology of `E^• ⊗_B B'` with the morphisms `A'[0] ⟶ Y⟦j⟧` in `D(B')` *additively*.
That is enough for the vanishing hypothesis of clause (2), which only has to transport
`Subsingleton`, and it is not enough in degree zero, where the conclusion asked for is an
isomorphism of modules.

This file reads the same three steps as an isomorphism of `B'`-modules.  There is no obstruction:
`E^• ⊗_B B'` is a complex of `B'`-modules, `D(B')` is a `B'`-linear category
(`DerivedCategory.instLinear`), and all three steps are `B'`-linear.  Only the first of them --
[stacks 0A66], which identifies the cohomology of a Hom complex with morphisms in the derived
category -- needed an argument, because the comparison factors through the Hom complex of the
*underlying abelian groups*, where no scalar action is in sight.

The degree-zero conclusion the clause wants is `A'`-linear, not `B'`-linear.  The two are the same
demand: the multiplication map `Δ' : B' → A'` is surjective, so an `A'`-module structure
restricting to a given `B'`-module structure is unique, and a `B'`-linear map between two modules
that both carry one is automatically `A'`-linear.  That passage is
`Dualizing.linearEquivOfSurjective`, and the compatibility it consumes -- that the `A'`-action
`Dualizing.smulHomRestrictedUnitSingle` on `Hom_{D(B')}(A'[0], Z)` restricts along `Δ'` to the
`B'`-action of the linear structure of `D(B')` -- is
`Dualizing.smulRestrictedUnitSingle_comp_eq_smul`.

## Main definitions

* `Dualizing.homComplexRHomologyLinearEquiv` -- **[stacks 0A66] read on the derived category,
  `S`-linearly**: `H^n(Hom^•_S(P, L)) ≃ₗ[S] Hom_{D(S)}(P, L⟦n⟧)`.

## Main results

* `Dualizing.nonempty_homLinearEquiv_restrictedUnitSingle` -- the two identifications of the
  base-changed representatives, on the morphism groups, `B'`-linearly.
* `Dualizing.nonempty_homologyLinearEquiv_restrictedUnitSingle` -- **the assembly, `B'`-linearly**:
  `H^j(E^• ⊗_B B') ≃ₗ[B'] Hom_{D(B')}(A'[0], Y⟦j⟧)`.
* `Dualizing.smulRestrictedUnitSingle_comp_eq_smul` and `Dualizing.linearEquivOfSurjective` -- the
  passage from `B'`-linearity to the `A'`-linearity the clause consumes.

## Why [stacks 0A66] needs a proof here

`Dualizing.homComplexRHomologyAddEquiv` is built from `cohomologyClassRHomAddEquiv`, which is
stated on `CochainComplex.HomComplex.CohomologyClass`, a quotient of the group of cocycles of the
Hom complex of abelian groups.  The scalar action of `S` on `H^n(Hom^•_S(P, L))` lives on the other
side of `CochainComplex.HomComplexR`'s forgetful comparison with that complex, so the equivariance
has to be checked on representatives: a homology class is the class of a cocycle
(`Dualizing.LocalDuality.homComplexRHomologyAddEquiv_cyclesMk`), the action of `S` on classes of
cocycles is the action on cocycles, and the comparison to the homotopy category is `S`-linear
because `CochainComplex.HomComplex.Cocycle.equivHomShift` is and because the localization functors
are (`DerivedCategory.Qh` is `Functor.Linear`).  This is the same argument as the one in
`Dualizing.LocalDuality.homologyDerivedHomLinearEquiv`, at a bounded above complex of projectives
instead of a K-injective target.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
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

/-- **[stacks 0A66] read on the derived category, `S`-linearly.**  For `P` a bounded above complex
of projective `S`-modules and `L` any complex, the degree-`n` cohomology of the `S`-linear Hom
complex `Hom^•_S(P, L)` is the module of morphisms `P ⟶ L⟦n⟧` in `D(S)`, as `S`-modules.

This is `Dualizing.homComplexRHomologyAddEquiv` with the `S`-action checked.  The comparison runs
through the cohomology classes of the Hom complex of the underlying abelian groups, where no
`S`-action is available, so the equivariance is read on representatives: a class in
`H^n(Hom^•_S(P, L))` is the class of a cocycle
(`Dualizing.LocalDuality.homComplexRHomologyAddEquiv_cyclesMk`), the `S`-action on `H^n` is the
action on cocycles, and the passage from a cocycle to a morphism in the homotopy category is
`S`-linear because `CochainComplex.HomComplex.Cocycle.equivHomShift` is and because
`HomotopyCategory.quotient` and `DerivedCategory.Qh` are `S`-linear functors. -/
@[stacks 0A66]
def homComplexRHomologyLinearEquiv (P L : CochainComplex (ModuleCat.{u} S) ℤ) (d n : ℤ)
    [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] :
    ((CochainComplex.HomComplexR S P L).homology n : Type u) ≃ₗ[S]
      (DerivedCategory.Q.obj P ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) n).obj
          (DerivedCategory.Q.obj L)) := by
  classical
  haveI : P.IsKProjective := CochainComplex.isKProjective_of_projective P d
  let H := CochainComplex.HomComplexR S P L
  let q := HomotopyCategory.quotient (ModuleCat.{u} S) (ComplexShape.up ℤ)
  let eHC := Dualizing.LocalDuality.homComplexRHomologyAddEquiv P L n
  let eClassHom := CochainComplex.HomComplex.CohomologyClass.homAddEquiv
    (K := P) (L := L) (n := n)
  let eClassLinear := eClassHom.toLinearEquiv (R := S) (by
    intro r x
    obtain ⟨z, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective x
    change CochainComplex.HomComplex.CohomologyClass.toHom
        (r • CochainComplex.HomComplex.CohomologyClass.mk z) =
      r • CochainComplex.HomComplex.CohomologyClass.toHom
        (CochainComplex.HomComplex.CohomologyClass.mk z)
    rw [← CochainComplex.HomComplex.CohomologyClass.mk_smul,
      CochainComplex.HomComplex.CohomologyClass.toHom_mk,
      CochainComplex.HomComplex.CohomologyClass.toHom_mk, ← Functor.map_smul]
    have hshift : CochainComplex.HomComplex.Cocycle.equivHomShift.symm (r • z) =
        r • CochainComplex.HomComplex.Cocycle.equivHomShift.symm z := by
      apply CochainComplex.HomComplex.Cocycle.equivHomShift.injective
      ext p p' hpp' w
      rfl
    rw [hshift])
  let eHCLinear : H.homology n ≃ₗ[S]
      CochainComplex.HomComplex.CohomologyClass P L n :=
    eHC.toLinearEquiv (by
      intro r x
      let SC := H.sc n
      obtain ⟨z, hz⟩ :=
        CochainComplex.HomComplex.CohomologyClass.mk_surjective (eHC x)
      let cyc : H.cycles n := H.cyclesMk z.val (n + 1) (by simp)
        (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _)
      let y := H.homologyπ n cyc
      have hy := Dualizing.LocalDuality.homComplexRHomologyAddEquiv_cyclesMk P L n z
      have hx : x = y := eHC.injective (hz.symm.trans hy.symm)
      have hsmul : r • y = H.homologyπ n
          (H.cyclesMk (r • z).val (n + 1) (by simp)
            (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _)) := by
        dsimp [y, SC]
        change r • (H.homologyπ n).hom cyc =
          (H.homologyπ n).hom
            (SC.cyclesMk (r • z).val
              (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _))
        rw [← (H.homologyπ n).hom.map_smul]
        congr 1
        apply (ModuleCat.mono_iff_injective (H.iCycles n)).mp inferInstance
        rw [(H.iCycles n).hom.map_smul]
        have hzi := HomologicalComplex.i_cyclesMk H z.val (n + 1) (by simp)
          (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _)
        have hrzi := HomologicalComplex.i_cyclesMk H (r • z).val (n + 1) (by simp)
          (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _)
        have hz' : (H.iCycles n).hom cyc = z.val := by
          dsimp [cyc]
          simpa [HomologicalComplex.cyclesMk, ConcreteCategory.forget₂_comp_apply] using hzi
        have hrz' : (H.iCycles n).hom
              (H.cyclesMk (r • z).val (n + 1) (by simp)
                (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _)) = (r • z).val := by
          simpa [HomologicalComplex.cyclesMk, ConcreteCategory.forget₂_comp_apply] using hrzi
        change r • (H.iCycles n).hom cyc = (H.iCycles n).hom
          (H.cyclesMk (r • z).val (n + 1) (by simp)
            (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _))
        rw [hz', hrz', CochainComplex.HomComplex.Cocycle.coe_smul]
        rfl
      have hmk : r • CochainComplex.HomComplex.CohomologyClass.mk z =
          CochainComplex.HomComplex.CohomologyClass.mk (r • z) :=
        (CochainComplex.HomComplex.CohomologyClass.mk_smul r z).symm
      have hrep := Dualizing.LocalDuality.homComplexRHomologyAddEquiv_cyclesMk P L n (r • z)
      have hrep' : eHC (H.homologyπ n
          (H.cyclesMk (r • z).val (n + 1) (by simp)
            (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _))) =
          CochainComplex.HomComplex.CohomologyClass.mk (r • z) := by
        simpa [HomologicalComplex.cyclesMk] using hrep
      have hclass : eHC y = CochainComplex.HomComplex.CohomologyClass.mk z := by
        change Dualizing.LocalDuality.homComplexRHomologyAddEquiv P L n
          (H.homologyπ n
            (H.cyclesMk z.val (n + 1) (by simp)
              (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _))) = _
        exact Dualizing.LocalDuality.homComplexRHomologyAddEquiv_cyclesMk P L n z
      rw [hx, hsmul, hclass]
      exact hrep'.trans hmk.symm)
  let ePQh := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)).app P
  let eLQh := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)).app (L⟦n⟧) ≪≫
    (DerivedCategory.Q.commShiftIso n).app L
  let eQh : (q.obj P ⟶ q.obj (L⟦n⟧)) ≃ₗ[S]
      (DerivedCategory.Q.obj P ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
    (LinearEquiv.ofBijective (DerivedCategory.Qh.mapLinearMap S
        (X := q.obj P) (Y := q.obj (L⟦n⟧)))
      (CochainComplex.IsKProjective.Qh_map_bijective P (q.obj (L⟦n⟧)))).trans
      (Linear.homCongr S ePQh eLQh)
  exact eHCLinear.trans (eClassLinear.trans eQh)

end Representability

section Restriction

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- **The `T`-action on the morphisms out of `T[0]` restricts to the linear structure of `D(S)`.**
Precomposition with multiplication by `f b` on the source
(`Dualizing.smulRestrictedUnitSingle`) is the scalar multiplication by `b` of the `S`-linear
structure of `D(S)`.

The source `T[0]` is `T` restricted along `f` and placed in degree zero, so multiplication by
`f b` on it *is* multiplication by `b`, and `DerivedCategory.singleFunctor` is an `S`-linear
functor. -/
theorem smulRestrictedUnitSingle_comp_eq_smul (b : S) (n : ℤ)
    {Z : DerivedCategory (ModuleCat.{u} S)} (g : restrictedUnitSingle f n ⟶ Z) :
    smulRestrictedUnitSingle f (f b) n ≫ g = b • g := by
  have h : (ModuleCat.restrictScalars.{u} f).map ((f b) • 𝟙 (ModuleCat.of T T)) =
      b • 𝟙 ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of T T)) := rfl
  rw [smulRestrictedUnitSingle, h, Functor.map_smul, CategoryTheory.Functor.map_id,
    Linear.smul_comp, Category.id_comp]

end Restriction

section SurjectiveScalars

/-- **A `B`-linear equivalence between two `A`-modules whose `B`-actions are the restrictions along
a surjective ring map is `A`-linear.**  The `A`-action is then determined by the `B`-action, so
nothing has to be checked twice.

This is the passage from the `B'`-linearity the assembly has to the `A'`-linearity clause (2)
consumes: the multiplication map `Δ' : B' → A'` is surjective. -/
def linearEquivOfSurjective {B A : Type u} [CommRing B] [CommRing A] (φ : B →+* A)
    (hφ : Function.Surjective φ)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    [Module A M] [Module A N]
    (hM : ∀ (b : B) (m : M), φ b • m = b • m) (hN : ∀ (b : B) (x : N), φ b • x = b • x)
    (e : M ≃ₗ[B] N) : M ≃ₗ[A] N :=
  { toFun := e
    map_add' := e.map_add
    map_smul' := fun a m => by
      obtain ⟨b, rfl⟩ := hφ a
      change e (φ b • m) = φ b • e m
      rw [hM b m, hN b (e m)]
      exact e.map_smul b m
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

end SurjectiveScalars

section Assembly

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R'] [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A))

/-- **The two identifications of the base-changed representatives, `B'`-linearly.**  The morphism
groups `Hom_{D(B')}(P^• ⊗_B B', (F^• ⊗_B B')⟦j⟧)`, which the representability clause of
[stacks 0E1U] computes after base change, are the morphism groups
`Hom_{D(B')}(A'[0], Y⟦j⟧)`, as `B'`-modules.

This is `Dualizing.nonempty_homAddEquiv_restrictedUnitSingle` with the `B'`-action: the two
identifications enter as pre- and postcomposition with isomorphisms of `D(B')`, which is a
`B'`-linear category, so `CategoryTheory.Linear.homCongr` replaces the two additive
equivalences. -/
theorem nonempty_homLinearEquiv_restrictedUnitSingle
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K) (j : ℤ) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    Nonempty
      ((DerivedCategory.Q.obj ((diagonalBaseChangeExtend R A R').obj P) ⟶
            (CategoryTheory.shiftFunctor
                (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
              (DerivedCategory.Q.obj ((diagonalBaseChangeExtend R A R').obj F)))
        ≃ₗ[(A ⊗[R] R') ⊗[R'] (A ⊗[R] R')]
          (restrictedUnitSingle
              (Algebra.TensorProduct.lmul' R' :
                (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
            (CategoryTheory.shiftFunctor
                (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
              (diagonalBaseChangeTarget R A R' K))) := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  obtain ⟨e₂⟩ := nonempty_restrictedUnitSingle_iso_extendScalars R A R' P hP eP
  obtain ⟨e₃⟩ := nonempty_diagonalBaseChangeTarget_iso_extendScalars R A R' K F d hflat eF
  exact ⟨Linear.homCongr ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) e₂
    ((CategoryTheory.shiftFunctor
      (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).mapIso e₃)⟩

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

/-- **The assembly of [stacks 0E2F] (2), `B'`-linearly.**  In the situation of
`Dualizing.nonempty_homologyAddEquiv_restrictedUnitSingle`, the degree-`j` cohomology of
`E^• ⊗_B B'` is the module of morphisms `A'[0] ⟶ Y⟦j⟧` in `D(B')`, as `B'`-modules.

The three steps are `Dualizing.homComplexRHomologyLinearEquiv` -- the representability clause of
[stacks 0E1U], which is [stacks 0A66] -- and the two identifications of the base-changed
representatives, `Dualizing.nonempty_homLinearEquiv_restrictedUnitSingle`; the hypothesis `hE` is
an isomorphism of complexes of `B'`-modules, so the cohomology functor carries it to an
isomorphism of `B'`-modules.

The `A'`-linearity the clause consumes in degree zero follows, `Δ' : B' → A'` being surjective;
see `Dualizing.linearEquivOfSurjective`. -/
theorem nonempty_homologyLinearEquiv_restrictedUnitSingle (j : ℤ) :
    Nonempty ((((((diagonalBaseChangeExtend R A R').obj E).homology j) : Type u)
        ≃ₗ[(A ⊗[R] R') ⊗[R'] (A ⊗[R] R')]
          (restrictedUnitSingle
              (Algebra.TensorProduct.lmul' R' :
                (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
            (CategoryTheory.shiftFunctor
                (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
              (diagonalBaseChangeTarget R A R' K)))) := by
  have : ((diagonalBaseChangeExtend R A R').obj P).IsStrictlyLE dP := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R'))
      (P.isZero_of_isStrictlyLE dP i hi)
  have : ∀ i : ℤ, Projective (((diagonalBaseChangeExtend R A R').obj P).X i) := fun i =>
    projective_extendScalars (diagonalBaseChangeMap R A R') (P.X i)
  obtain ⟨e₁⟩ := hE
  obtain ⟨e₃⟩ := nonempty_homLinearEquiv_restrictedUnitSingle R A R' K P hP eP F d hflat eF j
  exact ⟨(((HomologicalComplex.homologyFunctor
      (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))) (ComplexShape.up ℤ) j).mapIso
        e₁).toLinearEquiv.trans
    ((homComplexRHomologyLinearEquiv ((diagonalBaseChangeExtend R A R').obj P)
      ((diagonalBaseChangeExtend R A R').obj F) dP j).trans e₃))⟩

end Assembly

end

end Dualizing

end
