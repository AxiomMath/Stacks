module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFlat
public import StacksFrontier.AlgebraicGeometry.Modules.TildeKFlat
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.AffineTensor
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.Termwise
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude on an affine scheme

Let `X = Spec R` and let `M` be an object of `D(R)`. Its image `M̃` under derived sheafification,
an object of `D(𝒪_X)`, has Tor amplitude in `[a, b]` exactly when `M` does, and has finite Tor
dimension exactly when `M` does.

## Main results

* `AlgebraicGeometry.hasTorAmplitude_tilde_iff` is **Stacks 08E9 (1)**: Tor amplitude in a fixed
  interval agrees on the two sides.
* `AlgebraicGeometry.hasFiniteTorDimension_tilde_iff` is **Stacks 08E9 (2)**: finite Tor dimension
  agrees on the two sides.
* `AlgebraicGeometry.hasTorAmplitude_tilde_iff_tilde_tests` is the **affine case of Stacks 08EA**:
  on `Spec R` the Tor amplitude of `M̃` is already detected by the derived tensor products with
  the associated sheaves `Ñ`, which by `AlgebraicGeometry.tildeEquiv` are exactly the
  quasi-coherent `𝒪_{Spec R}`-modules. Its substantive half is
  `AlgebraicGeometry.hasTorAmplitudeCanonical_of_tilde_tests`, which is the sheaf-to-module
  direction of Stacks 08E9 (1) with the test family cut down in this way — that direction never
  used any other sheaf, the one appeal to the structure sheaf being an appeal to `R̃`.

## Implementation notes

Both sides name a *pinned* derived tensor product, so neither is quantified over a certificate:
on the sheaf side `Stacks.Cohomology.TorAmplitude.HasTorAmplitude` is stated against
`Stacks.Cohomology.TorAmplitude.derTensor`, the canonical derived tensor product of Stacks 06YU
read at the site of opens of `Spec R`, and on the module side
`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` is stated against the canonical derived
tensor product of Stacks 0BYI. This is what makes the equivalence a theorem rather than a
hypothesis: for a certificate carrying only the universal property,
`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff` exhibits an instantiation
for which Tor amplitude sees nothing but the cohomology of the object, and no equivalence with a
condition on `M` can hold there.

The two directions use the two different descriptions of Tor amplitude.

* From `M` to `M̃`: Stacks 0654 produces a complex `P` of flat `R`-modules concentrated in
  `[a, b]` representing `M`; then `P̃` is a complex of flat `𝒪_X`-modules (Stacks 05P0)
  concentrated in `[a, b]` representing `M̃`, and Stacks 08CI concludes.
* From `M̃` to `M`: tensoring with the structure sheaf shows `M̃`, hence `M`, has no cohomology
  above `b`, so `M` is represented by a bounded above complex `P` of projective, hence flat,
  modules, and `StacksDraft.TorAmplitude.hasTorAmplitude_iff_termwise_of_flat` reduces Tor
  amplitude of `M` to the vanishing of `H^i(P ⊗_R N)`. Taking the sheaf-side hypothesis at `Ñ`
  and computing both derived tensor products from the K-flat complex `P̃` (Stacks 08DV) through
  `CochainComplex.KFlatBifunctor.totalSingleIso` identifies `H^i(M̃ ⊗^{L} Ñ)` with
  `(H^i(P ⊗_R N))~`, and the associated-sheaf functor is faithful and exact.

The affine tensor comparison of Stacks 01I8 enters only termwise, as
`AlgebraicGeometry.tildeRowIso`; the full derived comparison of Stacks 08DX is not needed, since
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonLeft` computes the sheaf-side
derived tensor product from a K-flat left factor alone.

The derived category of `R`-modules is the standard one, as it already is for
`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`, whose statement carries no
`HasDerivedCategory` argument. `StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical` is not
exposed, so the existential form of finite Tor dimension is read off it through
`StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical`.

## References

* [Stacks Project, Lemma 20.48.5 (Tag 08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open StrictlyPerfect

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The associated sheaf of an `R`-module on `Spec R` is zero exactly when the module is: the
associated-sheaf functor is additive and faithful. -/
private theorem isZero_tilde_iff (M : ModuleCat.{u} R) : IsZero (tilde M) ↔ IsZero M := by
  refine ⟨fun h => ?_, fun h => Functor.map_isZero (tilde.functor R) h⟩
  rw [IsZero.iff_id_eq_zero]
  refine Functor.map_injective (tilde.functor R) ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- The affine tensor comparison of Stacks 01I8 is functorial in its first variable through the
tensor product of sheaves of modules: tensoring the associated sheaves on the right by a fixed
`Ñ` is the map that `AlgebraicGeometry.tildeTensorSheafMap` induces from a module map and an
identity. -/
private theorem tildeTensorSheafMap_id {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (N : ModuleCat.{u} R) :
    tildeTensorSheafMap R f (𝟙 N) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)).map
        (tilde.map f)).app (tilde N) := by
  unfold tildeTensorSheafMap Stacks.SheafOfModules.Tensor.sheafTensor
  rw [tilde.map_id]
  rfl

/-- An integer lies outside `[a, b]` exactly when it is below `a` or above `b`. -/
private theorem notMem_Icc_iff_lt_or_lt {i a b : ℤ} : i ∉ Set.Icc a b ↔ i < a ∨ b < i := by
  simp only [Set.mem_Icc, not_and_or, not_le]

attribute [local instance] HasDerivedCategory.standard

/-- **The termwise affine tensor comparison on complexes.** The associated sheaf of the termwise
tensor product `P ⊗_R N` of a complex of `R`-modules with a module is the termwise tensor product
of `P̃` with `Ñ` over `𝒪_{Spec R}`. In each degree this is the comparison of Stacks 01I8, and the
squares commute by its naturality. -/
public def tildeTensorRowIso (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (N : ModuleCat.{u} R) :
    tildeComplexMod (StacksDraft.TorAmplitude.Termwise.tensorComplex P N) ≅
      CochainComplex.KFlatBifunctor.rowComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (specCommRingSheaf R))
        (tildeComplexMod P) (tilde N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tildeTensorIso R (P.X n) N)
    (fun i j _ => by
      refine Eq.trans ?_ (tildeTensorIso_natural R (P.d i j) (𝟙 N)).symm
      exact congrArg (fun g => (tildeTensorIso R (P.X i) N).hom ≫ g)
        (tildeTensorSheafMap_id (P.d i j) N).symm)

/-- **The derived tensor product of `P̃` with `Ñ` on an affine scheme.** For a K-flat complex `P`
of `R`-modules and an `R`-module `N`, the derived tensor product of `P̃` with `Ñ[0]` is the
associated sheaf of the termwise tensor complex `P ⊗_R N`.

A K-flat left factor computes the derived tensor product with any right factor, `P̃` is K-flat by
Stacks 08DV, and tensoring with a complex concentrated in degree zero is termwise tensoring. -/
private def derivedTensorTildeIso
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (N : ModuleCat.{u} R) :
    ((Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor.obj
          (DerivedCategory.Q.obj (tildeComplexMod P))).obj
        ((DerivedCategory.singleFunctor (OXMod.{u} (Spec R).toRingedSpace) 0).obj (tilde N)) ≅
      DerivedCategory.Q.obj
        (tildeComplexMod (StacksDraft.TorAmplitude.Termwise.tensorComplex P N)) :=
  ((Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor.obj
        (DerivedCategory.Q.obj (tildeComplexMod P))).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (tilde N)) ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).comparisonLeft
      (tildeComplexMod P) _ (kFlat_tilde P hP) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso _ _ _) ≪≫
    DerivedCategory.Q.mapIso (tildeTensorRowIso P N).symm

/-- **The sheaf side of Stacks 08E9 (1) implies the module side, testing only on quasi-coherent
sheaves.** If the derived tensor product of `M̃` with `Ñ` has no cohomology outside `[a, b]` for
every `R`-module `N`, then `M` has Tor amplitude in `[a, b]` over `R`.

The hypothesis is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude` with the test sheaf restricted
to the associated sheaves `Ñ` — that is, by `AlgebraicGeometry.tildeEquiv`, to the quasi-coherent
`𝒪_{Spec R}`-modules. Nothing more is needed: tensoring with the structure sheaf, itself `R̃`,
bounds the cohomology of `M̃` and hence of `M` above by `b`, so `M` is represented by a bounded
above complex `P` of projective modules; the hypothesis at `Ñ`, transported along
`AlgebraicGeometry.derivedTensorTildeIso`, says that `(H^i(P ⊗_R N))~` vanishes for `i` outside
`[a, b]`, and the associated-sheaf functor is faithful.

This is the affine half of [Stacks, Tag 08EA], which asserts the same restriction of the test
family on any quasi-separated scheme. -/
theorem hasTorAmplitudeCanonical_of_tilde_tests
    (M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hE : ∀ (N : ModuleCat.{u} R) (i : ℤ), i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u} (Spec R).toRingedSpace) i).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor.obj
            ((tilde.functor R).mapDerivedCategory.obj M)).obj
          ((DerivedCategory.singleFunctor (OXMod.{u} (Spec R).toRingedSpace) 0).obj (tilde N))))) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R M a b := by
  have hunit : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u} (Spec R).toRingedSpace) i).obj
        ((tilde.functor R).mapDerivedCategory.obj M)) := by
    intro i hi
    refine (hE (ModuleCat.of R R) i hi).of_iso
      ((DerivedCategory.homologyFunctor (OXMod.{u} (Spec R).toRingedSpace) i).mapIso ?_)
    exact (Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.derivedTensorUnitIso
        ((tilde.functor R).mapDerivedCategory.obj M)).symm ≪≫
      (((Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor.obj
        ((tilde.functor R).mapDerivedCategory.obj M)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (tilde (ModuleCat.of R R))).symm)
  have hMLE : M.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    refine (isZero_tilde_iff _).mp
      ((hunit i (notMem_Icc_iff_lt_or_lt.2 (by omega))).of_iso ?_)
    exact ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (tilde.functor R) i).app M).symm
  obtain ⟨C, hCLE, ⟨eC⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE M b
  have := hCLE
  obtain ⟨P, m, π, hPLE, hPproj, hπ⟩ :=
    StacksDraft.TorAmplitude.exists_projective_resolution C b
  have := hPLE
  have := hπ
  have hP : P.KFlat :=
    StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective P m hPproj
  have hflat : ∀ i : ℤ, Module.Flat R (P.X i) := fun i => by
    have := hPproj i; infer_instance
  have hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨m, fun i hi => P.isZero_of_isStrictlyLE m i hi⟩
  have eP : DerivedCategory.Q.obj P ≅ M := asIso (DerivedCategory.Q.map π) ≪≫ eC.symm
  refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
    R M a b).mpr ?_
  refine (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) M a b).mp ?_
  refine (StacksDraft.TorAmplitude.hasTorAmplitude_of_iso eP a b).mp ?_
  rw [StacksDraft.TorAmplitude.hasTorAmplitude_iff_termwise_of_flat
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) P hbounded hflat a b]
  intro N i hi
  have eT : (tilde.functor R).mapDerivedCategory.obj M ≅
      DerivedCategory.Q.obj (tildeComplexMod P) :=
    (tilde.functor R).mapDerivedCategory.mapIso eP.symm ≪≫
      (tilde.functor R).mapDerivedCategoryFactors.app P
  have hz := hE N i (notMem_Icc_iff_lt_or_lt.2 hi)
  have hz2 : IsZero ((DerivedCategory.homologyFunctor
      (OXMod.{u} (Spec R).toRingedSpace) i).obj
      (DerivedCategory.Q.obj
        (tildeComplexMod (StacksDraft.TorAmplitude.Termwise.tensorComplex P N)))) :=
    hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      ((derivedTensorTildeIso P hP N).symm ≪≫
        ((Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor.mapIso
          eT.symm).app ((DerivedCategory.singleFunctor _ 0).obj (tilde N))))
  refine (isZero_tilde_iff _).mp (hz2.of_iso ?_)
  exact ((DerivedCategory.homologyFunctorFactors (OXMod.{u} (Spec R).toRingedSpace) i).app
      (tildeComplexMod (StacksDraft.TorAmplitude.Termwise.tensorComplex P N)) ≪≫
    (StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso
      (tilde.functor R) i).app
        (StacksDraft.TorAmplitude.Termwise.tensorComplex P N)).symm

/-- **The module side of Stacks 08E9 (1) implies the sheaf side.** If `M` has Tor amplitude in
`[a, b]` over `R`, then `M̃` has Tor amplitude in `[a, b]` on `Spec R`.

Stacks 0654 represents `M` by a complex of flat `R`-modules concentrated in `[a, b]`; its
associated sheaf is a complex of flat `𝒪_X`-modules (Stacks 05P0) concentrated in `[a, b]`
representing `M̃`, which is what Stacks 08CI asks for. -/
private theorem hasTorAmplitude_tilde_of_hasTorAmplitudeCanonical
    (M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hM : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R M a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec R).toRingedSpace
      ((tilde.functor R).mapDerivedCategory.obj M) a b := by
  obtain ⟨P, hPflat, hPGE, hPLE, ⟨e⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative R M a b).mp hM
  refine Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative
    (X := (Spec R).toRingedSpace) _ a b (tildeComplexMod P) (fun i => ?_) (fun i hi => ?_)
    (((tilde.functor R).mapDerivedCategory.mapIso e) ≪≫
      (tilde.functor R).mapDerivedCategoryFactors.app P).symm
  · exact (isFlat_tilde_iff_flat (P.X i)).2 (hPflat i)
  · rcases notMem_Icc_iff_lt_or_lt.1 hi with h | h
    · exact Functor.map_isZero (tilde.functor R) (P.isZero_of_isStrictlyGE a i h)
    · exact Functor.map_isZero (tilde.functor R) (P.isZero_of_isStrictlyLE b i h)

/-- **The sheaf side of Stacks 08E9 (1) implies the module side.** If `M̃` has Tor amplitude in
`[a, b]` on `Spec R`, then so does `M` over `R`. This is
`AlgebraicGeometry.hasTorAmplitudeCanonical_of_tilde_tests` with its hypothesis read at the test
sheaves `Ñ`. -/
private theorem hasTorAmplitudeCanonical_of_hasTorAmplitude_tilde
    (M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hE : Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec R).toRingedSpace
      ((tilde.functor R).mapDerivedCategory.obj M) a b) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R M a b :=
  hasTorAmplitudeCanonical_of_tilde_tests M a b fun N i hi => hE (tilde N) i hi

/-- **Stacks 08E9 (1).** Let `X = Spec R` be an affine scheme and let `M` be an object of `D(R)`.
Then the associated object `M̃` of `D(𝒪_X)` has Tor amplitude in `[a, b]` if and only if `M` has
Tor amplitude in `[a, b]`. -/
@[stacks 08E9 "part (1)"]
theorem hasTorAmplitude_tilde_iff (M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec R).toRingedSpace
        ((tilde.functor R).mapDerivedCategory.obj M) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R M a b :=
  ⟨hasTorAmplitudeCanonical_of_hasTorAmplitude_tilde M a b,
    hasTorAmplitude_tilde_of_hasTorAmplitudeCanonical M a b⟩

/-- **Tor amplitude on an affine scheme is tested by the quasi-coherent sheaves alone.** For `M`
an object of `D(R)`, the object `M̃` of `D(𝒪_{Spec R})` has Tor amplitude in `[a, b]` — a
condition on its derived tensor product with *every* `𝒪_{Spec R}`-module — if and only if the
derived tensor product with `Ñ` has no cohomology outside `[a, b]` for every `R`-module `N`.

By `AlgebraicGeometry.tildeEquiv` the sheaves `Ñ` are exactly the quasi-coherent
`𝒪_{Spec R}`-modules, so this is the affine case of [Stacks, Tag 08EA]. The forward direction is
specialisation; the converse is
`AlgebraicGeometry.hasTorAmplitudeCanonical_of_tilde_tests` followed by Stacks 08E9. No relation
between `a` and `b` is assumed. -/
theorem hasTorAmplitude_tilde_iff_tilde_tests (M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec R).toRingedSpace
        ((tilde.functor R).mapDerivedCategory.obj M) a b ↔
      ∀ (N : ModuleCat.{u} R) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u} (Spec R).toRingedSpace) i).obj
          (((Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor.obj
              ((tilde.functor R).mapDerivedCategory.obj M)).obj
            ((DerivedCategory.singleFunctor (OXMod.{u} (Spec R).toRingedSpace) 0).obj
              (tilde N)))) :=
  ⟨fun hE N i hi => hE (tilde N) i hi,
    fun hE => hasTorAmplitude_tilde_of_hasTorAmplitudeCanonical M a b
      (hasTorAmplitudeCanonical_of_tilde_tests M a b hE)⟩

/-- **Stacks 08E9 (2).** Let `X = Spec R` be an affine scheme and let `M` be an object of `D(R)`.
Then the associated object `M̃` of `D(𝒪_X)` has finite Tor dimension if and only if `M` has finite
Tor dimension. -/
@[stacks 08E9 "part (2)"]
theorem hasFiniteTorDimension_tilde_iff (M : DerivedCategory (ModuleCat.{u} R)) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension (Spec R).toRingedSpace
        ((tilde.functor R).mapDerivedCategory.obj M) ↔
      StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical R M :=
  (exists_congr fun a => exists_congr fun b => hasTorAmplitude_tilde_iff M a b).trans
    (StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      (R : Type u) M).symm

end AlgebraicGeometry

end
