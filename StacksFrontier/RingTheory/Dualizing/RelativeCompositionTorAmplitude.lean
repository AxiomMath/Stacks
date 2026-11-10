module

public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.Homology.RelativelyPerfect.FlatComplex
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.RingTheory.Dualizing.RelativeComposition
public import StacksFrontier.RingTheory.Dualizing.RelativeCoprojections

/-!
# The twisting factor of [stacks 0E2H] over the diagonal `A ⊗[R] A`

Let `R → A → B` be flat ring maps of finite presentation and write `C = B ⊗[R] B`,
`C' = B ⊗[A] B`, `D = A ⊗[R] A`.  The isomorphism (★) to which clause (2) of [stacks 0E2C] for
the composite reduces -- `Dualizing.DiagonalQuotientDerivedHom`, the one remaining antecedent of
[stacks 0E2H] -- is the invertibility of a tensor--Hom diagonal whose tensor factor is
`Y = K_{B/A} ⊗ᴸ_B C`.  Over `C` no criterion of [stacks 0ATK] applies to it, and the witness
recorded in the module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeComposition`
refutes each disjunct.  **Over `D` it does**, and that is what this file proves.

## Main results

* `Dualizing.flat_restrictScalars_diagonalExtendScalars` -- the degreewise step.  For `M` a
  `B`-module flat over `A`, the `C`-module `C ⊗_B M` is flat over `D`.  Indeed `C ⊗_B M` is
  `M ⊗[R] B` with `D = A ⊗[R] A` acting factorwise
  (`Dualizing.diagonalExtendScalarsEquiv`), an external tensor product of two `A`-flat modules,
  and such a module is `D`-flat by `Dualizing.flat_extTensor`.  This is the first consumer of
  that lemma, which `StacksFrontier.RingTheory.Dualizing.ExternalTensorFlat` proved for exactly
  this purpose.
* `Dualizing.exists_kFlat_flat_representative_restrictScalars_diagonalDerivedExtension` -- the
  complex-level step.  Choosing by [stacks 0DHV] a bounded complex `Q` representing `K_{B/A}`
  with terms flat over `A` and finitely presented over `B`, the complex `Q ⊗_B C` read over `D`
  is bounded with `D`-flat terms, hence `K`-flat over `D` by [stacks 064K]; and it represents
  `Y` read over `D`, because the left coprojection `B → C` is flat, so termwise extension of
  scalars along it already computes the derived one
  (`Dualizing.diagonalDerivedExtensionIso`).
* `Dualizing.torAmplitudeAbove_restrictScalars_diagonalDerivedExtension` -- **`Y` has Tor
  amplitude bounded below over `D`.**  This is [stacks 0BYL] at the representative above.
* `Dualizing.isIso_derivedTensorHomDiagonal_restrictScalars_diagonalDerivedExtension` --
  **[stacks 0ATK] (3) over `D`, at the tensor factor `Y`.**  For any pseudo-coherent `M` and any
  bounded below `L` in `D(D)` the tensor--Hom diagonal
  `Y_D ⊗ᴸ_D RHom_D(M, L) ⟶ RHom_D(M, Y_D ⊗ᴸ_D L)` is an isomorphism.
* `Dualizing.isGE_diagonalDerivedExtension` and
  `Dualizing.exists_isGE_diagonalDerivedExtension_of_relativelyPerfect` -- the internal-Hom
  target `X_D = K_{A/R} ⊗ᴸ_A D` is bounded below, which is the remaining hypothesis of
  [stacks 0ATK] (3).
* `Dualizing.isIso_derivedTensorHomDiagonal_diagonal_diagonalDerivedExtension` -- the same at
  `M` the diagonal `A`, pseudo-coherent over `D` by `Dualizing.isPseudoCoherent_diagonal`.  This
  is the instance of [stacks 0ATK] (3) that the route to (★) calls for.
* `Dualizing.isIso_derivedTensorHomDiagonal_diagonal_composite` -- **the settled mathematics of
  (★), proved and carrying nothing.**  For `K_{A/R}` perfect relative to `R` and `K_{B/A}`
  perfect relative to `A`, the diagonal
  `Y_D ⊗ᴸ_D RHom_D(A, X_D) ⟶ RHom_D(A, Y_D ⊗ᴸ_D X_D)` is an isomorphism.

## What this does and does not give

It gives the *mathematics* of (★) over `D`: the one disjunct of [stacks 0ATK] that the twisting
factor satisfies, at the ring where it satisfies it.  It does **not** give (★), because (★) is an
isomorphism in `D(C')` and what is proved here is a statement in `D(D)`.  Bridging them is the
pair of identifications recorded in the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeComposition` -- that restriction along
`Dualizing.diagonalQuotient` carries the along-ring-map diagonal
`Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom` to the single-ring diagonal
of `C`, and that the latter descends to the single-ring diagonal of `D` -- and neither is proved
here.

Nothing in this file carries a `@[stacks]` attribute: [stacks 0ATK] and [stacks 0BYL] are tagged
where they are proved, and [stacks 0E2H] is tagged in
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionTag`.

## References

* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0BYL](https://stacks.math.columbia.edu/tag/0BYL)
* [Stacks Project, Tag 0DHV](https://stacks.math.columbia.edu/tag/0DHV)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

/-! ### The untwisted tensor factor is bounded below

Both [stacks 0ATK] (3) and [stacks 0A6A] (3) ask the internal-Hom *target* to be bounded below,
and in the route to (★) that target is `X_D = K_{A/R} ⊗ᴸ_A D`.  Since the left coprojection
`A → D` is flat, a bounded below representative of `K_{A/R}` extends termwise to one of `X_D`,
and relative perfection supplies a bounded one by [stacks 0DHV]. -/

section BoundedBelow

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]

/-- A functor preserving zero morphisms, applied termwise, preserves strict boundedness
below. -/
private theorem isStrictlyGE_map_obj {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (.up ℤ)).obj K) a :=
  (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi =>
    F.map_isZero (K.isZero_of_isStrictlyGE a i hi)

/-- A functor preserving zero morphisms, applied termwise, preserves strict boundedness
above. -/
private theorem isStrictlyLE_map_obj {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyLE a] : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up ℤ)).obj K) a :=
  (CochainComplex.isStrictlyLE_iff _ a).mpr fun i hi =>
    F.map_isZero (K.isZero_of_isStrictlyLE a i hi)

/-- **Derived base change to the diagonal preserves boundedness below.**  The left coprojection
`A → A ⊗[R] A` is flat, so `Dualizing.diagonalDerivedExtensionIso` computes the derived base
change on a bounded below representative, and termwise extension of scalars does not lower
degrees. -/
theorem isGE_diagonalDerivedExtension (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ)
    (hK : DerivedCategory.IsGE K a) :
    DerivedCategory.IsGE ((diagonalDerivedExtension R A).obj K) a := by
  obtain ⟨F, hF, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  have : ((CochainComplex.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj F).IsStrictlyGE a :=
    isStrictlyGE_map_obj _ F a
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (diagonalDerivedExtensionIso R A K F e.symm).symm a

/-- The same for an object perfect relative to `R`: [stacks 0DHV] supplies a bounded
representative, so `K_{A/R} ⊗ᴸ_A (A ⊗[R] A)` is bounded below. -/
theorem exists_isGE_diagonalDerivedExtension_of_relativelyPerfect
    [Algebra.FinitePresentation R A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K) :
    ∃ a : ℤ, DerivedCategory.IsGE ((diagonalDerivedExtension R A).obj K) a := by
  obtain ⟨P, a, b, hPGE, -, -, -, ⟨eP⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ K).1 hK
  exact ⟨a, isGE_diagonalDerivedExtension R A K a
    (DerivedCategory.TStructure.t.isGE_of_iso eP.symm a)⟩

end BoundedBelow

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-! ### The degreewise step

The left coprojection `B → C = B ⊗[R] B` extends a `B`-module `M` to `C ⊗_B M`, and
`Dualizing.diagonalBaseMap` makes that a module over `D = A ⊗[R] A`.  As such it is the external
tensor product `M ⊗[R] B` of the `A`-modules `M` and `B`, so `Dualizing.flat_extTensor` applies
to it. -/

section Degreewise

variable (M : ModuleCat.{u} B) [Module R M] [Module A M]
  [IsScalarTower R A M] [IsScalarTower A B M] [IsScalarTower R B M]

/-- The `D = A ⊗[R] A`-action on the external tensor product `M ⊗[R] B` is the restriction along
`Dualizing.diagonalBaseMap` of the `C = B ⊗[R] B`-action.  Both send `a ⊗ a'` to `a` acting on
the left factor and `a'` on the right, which is what
`Dualizing.extTensorModule_smul_tmul` says of each of them. -/
theorem diagonalBaseMap_smul_extTensor (d : A ⊗[R] A) (x : M ⊗[R] B) :
    letI := extTensorModule R B B M B
    letI := extTensorModule R A A M B
    (diagonalBaseMap R A B d) • x = d • x := by
  let := extTensorModule R B B M B
  let := extTensorModule R A A M B
  induction d with
  | add u v hu hv => simp only [map_add, add_smul, hu, hv]
  | tmul a a' =>
      induction x with
      | add u v hu hv => simp only [smul_add, hu, hv]
      | tmul m b =>
          rw [diagonalBaseMap_tmul, extTensorModule_smul_tmul, extTensorModule_smul_tmul,
            algebraMap_smul, algebraMap_smul]

/-- **The base change of `M` to `C = B ⊗[R] B` is the external tensor product `M ⊗[R] B`,
`D`-linearly.**  Over `C` this is `Dualizing.extBaseChangeEquiv'` at `S = T = B`; the `D`-linear
form is that identity read through `Dualizing.diagonalBaseMap`, which
`Dualizing.diagonalBaseMap_smul_extTensor` identifies with the factorwise action of `D`. -/
def diagonalExtendScalarsEquiv :
    letI := extTensorModule R A A M B
    ((ModuleCat.restrictScalars (diagonalBaseMap R A B).toRingHom).obj
        ((ModuleCat.extendScalars
          (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)).obj M)) ≃ₗ[A ⊗[R] A]
      (M ⊗[R] B) :=
  letI := extTensorModule R B B M B
  letI := extTensorModule R A A M B
  letI e : ((ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)).obj M) ≃ₗ[B ⊗[R] B]
      (M ⊗[R] B) :=
    (PseudoCoherence.extendScalarsAlgebraMapObjIso (R := B) (S := B ⊗[R] B) M).toLinearEquiv.trans
      (extBaseChangeEquiv' R B B M)
  { e.toAddEquiv with
    map_smul' := fun d x =>
      (e.map_smul (diagonalBaseMap R A B d) x).trans
        (diagonalBaseMap_smul_extTensor R A B M d (e x)) }

end Degreewise

/-- **The degreewise Tor-amplitude step of [stacks 0E2H].**  Let `M` be a `B`-module which is
flat over `A`, and let `B` be flat over `A`.  Then the base change of `M` along the left
coprojection `B → B ⊗[R] B` is flat over the diagonal `D = A ⊗[R] A`.

By `Dualizing.diagonalExtendScalarsEquiv` that base change is the external tensor product
`M ⊗[R] B` of two `A`-flat modules, which is `D`-flat by `Dualizing.flat_extTensor`.  It is
*not* flat over `C = B ⊗[R] B`, and nothing weaker than flatness over `D` is available: see the
module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeComposition`. -/
theorem flat_restrictScalars_diagonalExtendScalars [Module.Flat A B] (M : ModuleCat.{u} B)
    (hM : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :
    Module.Flat (A ⊗[R] A)
      ((ModuleCat.restrictScalars (diagonalBaseMap R A B).toRingHom).obj
        ((ModuleCat.extendScalars
          (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)).obj M)) := by
  let : Module A (M : Type u) := ((ModuleCat.restrictScalars (algebraMap A B)).obj M).isModule
  let : Module R (M : Type u) := ((ModuleCat.restrictScalars (algebraMap R B)).obj M).isModule
  have : IsScalarTower A B (M : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R B (M : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R A (M : Type u) := IsScalarTower.of_algebraMap_smul fun r m => by
    change (algebraMap A B (algebraMap R A r)) • m = (algebraMap R B r) • m
    rw [← IsScalarTower.algebraMap_apply]
  have : Module.Flat A (M : Type u) := hM
  let := extTensorModule R A A (M : Type u) B
  have : Module.Flat (A ⊗[R] A) ((M : Type u) ⊗[R] B) := flat_extTensor R A A (M : Type u) B
  exact Module.Flat.of_linearEquiv (diagonalExtendScalarsEquiv R A B M)

/-! ### The complex-level step -/

section Complexes

variable [Module.Flat R A] [Module.Flat A B]
  [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B]

omit [Algebra.FinitePresentation R A] in
/-- **A bounded `K`-flat representative over `D` of the twisting factor of (★).**  Let `K_{B/A}`
be perfect relative to `A` in `D(B)`.  Then `Y = K_{B/A} ⊗ᴸ_B C`, read over the diagonal
`D = A ⊗[R] A` through `Dualizing.diagonalBaseMap`, is represented by a complex which is
`K`-flat over `D`, has `D`-flat terms, and is concentrated in degrees `≥ a` for some `a`.

The representative is `Q ⊗_B C` for `Q` a bounded complex with `A`-flat, `B`-finitely presented
terms chosen by [stacks 0DHV].  Three things make it work: the left coprojection `B → C` is
flat, so `Dualizing.diagonalDerivedExtensionIso` computes the derived base change on *any*
representative, in particular on `Q`, which is not `K`-flat over `B`; its terms are `D`-flat by
`Dualizing.flat_restrictScalars_diagonalExtendScalars`; and it is bounded above, so it is
`K`-flat over `D` by [stacks 064K]. -/
theorem exists_kFlat_flat_representative_restrictScalars_diagonalDerivedExtension
    (KB : DerivedCategory (ModuleCat.{u} B))
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    ∃ (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (a : ℤ),
      E.KFlat ∧ (∀ n : ℤ, Module.Flat (A ⊗[R] A) (E.X n)) ∧ E.IsStrictlyGE a ∧
        Nonempty
          ((ModuleCat.restrictScalars
              (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
            ((diagonalDerivedExtension R B).obj KB) ≅ DerivedCategory.Q.obj E) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨Q, a, b, hQGE, hQLE, hQflat, -, ⟨eQ⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ KB).1 hKB
  set p : B →+* B ⊗[R] B := Algebra.TensorProduct.includeLeftRingHom
  set g : (A ⊗[R] A) →+* B ⊗[R] B := (diagonalBaseMap R A B).toRingHom
  let QC := (CochainComplex.extendScalars p).obj Q
  let E := (CochainComplex.restrictScalarsLarge.{u, u, u} g).obj QC
  have hEflat : ∀ n : ℤ, Module.Flat (A ⊗[R] A) (E.X n) := fun n =>
    flat_restrictScalars_diagonalExtendScalars R A B (Q.X n) (hQflat n)
  let F := ModuleCat.extendScalars p ⋙ ModuleCat.restrictScalars g
  have hEGE : E.IsStrictlyGE a := isStrictlyGE_map_obj F Q a
  have : E.IsStrictlyLE b := isStrictlyLE_map_obj F Q b
  exact ⟨E, a, CochainComplex.KFlat.kFlat_of_flat.{u, u} E b, hEflat, hEGE,
    ⟨(ModuleCat.restrictScalars g).mapDerivedCategory.mapIso
        (diagonalDerivedExtensionIso R B KB Q eQ.symm) ≪≫
      (ModuleCat.restrictScalars g).mapDerivedCategoryFactors.app QC⟩⟩

omit [Algebra.FinitePresentation R A] in
/-- **The twisting factor of (★) has Tor amplitude bounded below over the diagonal
`D = A ⊗[R] A`.**  This is [stacks 0BYL] at the representative produced by
`Dualizing.exists_kFlat_flat_representative_restrictScalars_diagonalDerivedExtension`.

Over `C = B ⊗[R] B` the same object has *no* lower bound on its Tor amplitude -- the witness in
the module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeComposition` has
`Tor_i^B(K_{B/A}, k) ≠ 0` for every `i` -- so the descent to `D` is not a convenience. -/
theorem torAmplitudeAbove_restrictScalars_diagonalDerivedExtension
    (KB : DerivedCategory (ModuleCat.{u} B))
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    ∃ a : ℤ, ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (A ⊗[R] A)).tensor.obj
            ((ModuleCat.restrictScalars
                (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
              ((diagonalDerivedExtension R B).obj KB))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N))) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨E, a, hEK, hEflat, hEGE, ⟨e⟩⟩ :=
    exists_kFlat_flat_representative_restrictScalars_diagonalDerivedExtension R A B KB hKB
  exact ⟨a,
    (StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative_canonical
      _ a).2 ⟨E, hEK, hEflat, hEGE, ⟨e⟩⟩⟩

omit [Algebra.FinitePresentation R A] in
/-- **[stacks 0ATK] (3) over the diagonal `D = A ⊗[R] A`, at the twisting factor of (★).**  Let
`K_{B/A}` be perfect relative to `A` in `D(B)`, write `Y = K_{B/A} ⊗ᴸ_B (B ⊗[R] B)` and read it
over `D` through `Dualizing.diagonalBaseMap`.  Then for every pseudo-coherent `M` and every
bounded below `L` in `D(D)` the tensor--Hom diagonal

`Y_D ⊗ᴸ_D RHom_D(M, L) ⟶ RHom_D(M, Y_D ⊗ᴸ_D L)`

is an isomorphism.

The third disjunct of [stacks 0ATK] is the one that applies, and its Tor-amplitude hypothesis is
`Dualizing.torAmplitudeAbove_restrictScalars_diagonalDerivedExtension`.  No disjunct applies to
the same diagonal taken over `C = B ⊗[R] B`. -/
theorem isIso_derivedTensorHomDiagonal_restrictScalars_diagonalDerivedExtension
    (KB : DerivedCategory (ModuleCat.{u} B))
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    ∀ (L M : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))),
      StacksDraft.PseudoCoherence.IsPseudoCoherent M → (∃ b : ℤ, DerivedCategory.IsGE L b) →
      IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
        ((ModuleCat.restrictScalars
            (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
          ((diagonalDerivedExtension R B).obj KB)) L M) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  intro L M hM hL
  obtain ⟨a, ha⟩ :=
    torAmplitudeAbove_restrictScalars_diagonalDerivedExtension R A B KB hKB
  exact Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal _ L M a
    (Or.inr (Or.inr ⟨hM, hL, ha⟩))

/-- **[stacks 0ATK] (3) over `D = A ⊗[R] A` at the diagonal.**  The instance of
`Dualizing.isIso_derivedTensorHomDiagonal_restrictScalars_diagonalDerivedExtension` the route to
(★) calls for: the internal-Hom source is the diagonal `A`, pseudo-coherent over `D` by
`Dualizing.isPseudoCoherent_diagonal`, and the target is any bounded below object of `D(D)` --
in the application, `K_{A/R} ⊗ᴸ_A D`, which is bounded below because `K_{A/R}` is `R`-perfect. -/
theorem isIso_derivedTensorHomDiagonal_diagonal_diagonalDerivedExtension
    (KB : DerivedCategory (ModuleCat.{u} B))
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB)
    (L : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) (hL : ∃ b : ℤ, DerivedCategory.IsGE L b) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
      ((ModuleCat.restrictScalars
          (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
        ((diagonalDerivedExtension R B).obj KB)) L
      ((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))) :=
  isIso_derivedTensorHomDiagonal_restrictScalars_diagonalDerivedExtension R A B KB hKB _ _
    (isPseudoCoherent_diagonal R A) hL

/-- **The mathematics of (★), proved: [stacks 0ATK] (3) at the diagonal of the single ring
`D = A ⊗[R] A`.**  Let `R → A → B` be flat of finite presentation, let `K_{A/R}` be perfect
relative to `R` in `D(A)` and `K_{B/A}` perfect relative to `A` in `D(B)`.  Write
`X_D = K_{A/R} ⊗ᴸ_A D` and let `Y_D` be `K_{B/A} ⊗ᴸ_B (B ⊗[R] B)` read over `D`.  Then the
tensor--Hom diagonal

`Y_D ⊗ᴸ_D RHom_D(A, X_D) ⟶ RHom_D(A, Y_D ⊗ᴸ_D X_D)`

**is an isomorphism**, with nothing carried: the three hypotheses of the third disjunct of
[stacks 0ATK] are discharged by `Dualizing.isPseudoCoherent_diagonal`, by
`Dualizing.exists_isGE_diagonalDerivedExtension_of_relativelyPerfect`, and by
`Dualizing.torAmplitudeAbove_restrictScalars_diagonalDerivedExtension`.

This is the statement the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeComposition` calls the settled mathematics of (★).
It is *not* (★): (★) is an isomorphism in `D(B ⊗[A] B)`, and what stands between the two is the
pair of identifications recorded there, neither of which is proved. -/
theorem isIso_derivedTensorHomDiagonal_diagonal_composite
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) KA)
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
      ((ModuleCat.restrictScalars
          (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
        ((diagonalDerivedExtension R B).obj KB))
      ((diagonalDerivedExtension R A).obj KA)
      ((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨a, ha⟩ := exists_isGE_diagonalDerivedExtension_of_relativelyPerfect R A KA hKA
  exact isIso_derivedTensorHomDiagonal_diagonal_diagonalDerivedExtension R A B KB hKB _ ⟨a, ha⟩

end Complexes

end

end Dualizing

end
