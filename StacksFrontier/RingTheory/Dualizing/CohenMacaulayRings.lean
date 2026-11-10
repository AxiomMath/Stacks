module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.Homology.HomComplex.Evaluation.KFlat
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayCriterion
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayDuality
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
import StacksFrontier.RingTheory.Dualizing.DepthFromExt

/-!
# Cohen--Macaulay rings and the Cohen--Macaulay locus of a module

Let `(A, m, κ)` be a Noetherian local ring with a normalized dualizing complex `ω_A`, and let
`ω_A = H^{-dim(A)}(ω_A)` be the associated dualizing module. The depth of `A` is the least
`δ ≥ 0` with `H^{-δ}(ω_A) ≠ 0`. Moreover `A` is Cohen--Macaulay exactly
when `ω_A` is concentrated in a single cohomological degree, and exactly when it is the dualizing
module placed in degree `-dim(A)`. In that case the dualizing module is a maximal Cohen--Macaulay
module.

Globally, for a Noetherian ring `A` admitting a dualizing complex and a finite `A`-module `M`,
the locus of primes at which `M` localizes to a Cohen--Macaulay module is open in `Spec A`, and
its intersection with the support of `M` is dense there.

## Main definitions

* `Dualizing.localRingDimension` is the natural-number dimension of a Noetherian local ring.
* `Dualizing.dualizingModule` is the degree `-dim(A)` cohomology of a normalized dualizing
  complex.
* `Dualizing.IsCohomologicallyConcentratedInOneDegree` says that all cohomology groups except
  possibly one vanish.

## Main results

* `Dualizing.depth_eq_least_nonzero_homology` identifies the depth of `A` with the least
  nonnegative `δ` whose cohomology `H^{-δ}(ω_A)` is nonzero.
* `Dualizing.isCohenMacaulay_tfae_dualizingComplex` gives the three equivalent conditions.
* `Dualizing.dualizingModule_isMaximalCohenMacaulay` proves that the dualizing module is maximal
  Cohen--Macaulay in the Cohen--Macaulay case.
* `Dualizing.cohenMacaulayLocus_subset_support` says that a Cohen--Macaulay localization belongs
  to the support.
* `Dualizing.isOpen_cohenMacaulayLocus` states relative openness in the support.
* `Dualizing.dense_cohenMacaulayLocus` states density in the support.

## Implementation notes

Normalization is `Dualizing.IsNormalizedDualizingComplex.{u, 0}`, the module universe being the
ring universe here. For a local ring, its dimension is the height of its maximal ideal;
Noetherianity makes this extended natural number finite, so `ENat.toNat` records the usual
natural-number dimension. The source's `ω_A[dim(A)]` is represented by the single complex having
`ω_A` in cohomological degree `-dim(A)`, in accordance with the cochain shift convention.

Both implications run through `Dualizing.isCohenMacaulay_iff_ext_concentrated`, the source's
Lemma 47.16.7, after `Ext^i_A(A, ω_A)` is identified with `H^i(ω_A)`: morphisms out of the unit
of the monoidal structure on cochain complexes evaluate to the complex itself, so the Hom complex
from `A[0]` into a representative of `ω_A` is that representative. The same identification turns
`Dualizing.depth_eq_least_nonzero_negative_ext` at the module `A` into the statement about depth,
whose minimality clause is recorded by `IsLeast` as in that lemma. The maximal Cohen--Macaulay
assertion is read off the same lemma's duality statement at `A` itself, whose depth is `dim(A)`
precisely because `A` is Cohen--Macaulay.

The equivalence of the three numbered assertions and the final maximal Cohen--Macaulay assertion
are the two covering declarations below.

For the Cohen--Macaulay locus the support carries the subspace topology from the prime spectrum,
so the openness and density claims are stated on the subtype of primes in the support; a third
declaration records that the source's locus, defined without intersecting the support, is indeed
a subset of it.

That containment is what fixes the shape of the openness clause.
`Module.IsCohenMacaulayAtMaximalIdeal` compares `depth` with `Module.supportDim` in `WithBot ℕ∞`,
where the zero module has depth `⊤` and support dimension `⊥`; so the zero module is not
Cohen--Macaulay, and `U` misses every prime
outside `Supp(M)` — this is `Dualizing.cohenMacaulayLocus_subset_support`. A set contained in the
closed set `Supp(M)` and dense in it cannot be open in `Spec A` unless `Supp(M)` has interior, so
the source's `U` is this `U` together with the complement of the support. The two readings agree:
for `C = Supp(M)` closed with open complement `W`, and `U ⊆ C`, one has `U = V ∩ C` for some open
`V` exactly when `U ∪ W = V ∪ W` is open in `Spec A`. Openness of `U` in the subspace `Supp(M)` is
therefore equivalent to the source's openness in `Spec A`, and it is the form stated here because
it needs no auxiliary union.

The source's `RHom_A(M, ω_A)_p = RHom_{A_p}(M_p, (ω_A)_p)` is the base-change
isomorphism `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange` along the flat map
`A → A_p`, which turns the local criterion into a condition on the supports of the finitely many
nonzero cohomology modules of `RHom_A(M, ω_A)`; those supports are closed, so the condition cuts
out an open set. Normalization at `p` is the dimension function `Dualizing.dualizingDimension`,
whose defining property `Dualizing.dualizingDimension_spec` supplies the normalizing shift that
Lemma 47.16.7 requires.

## References

* [Stacks Project, Tag 0AWR](https://stacks.math.columbia.edu/tag/0AWR)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0EHS](https://stacks.math.columbia.edu/tag/0EHS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Module
open CochainComplex.HomComplex HomologicalComplex
open CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

private noncomputable def unitHomEquiv {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) : (𝟙_ (ModuleCat.{u} A) ⟶ M) ≃ M where
  toFun f := f.hom 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton A M x)
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r • f.hom 1 = f.hom r
    rw [← map_smul]
    simp
  right_inv x := by
    change (1 : A) • x = x
    exact one_smul A x

private noncomputable def unitHomLinearEquiv {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) : (ModuleCat.of A A ⟶ M) ≃ₗ[A] M := by
  let e := unitHomEquiv M
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    change (f + g).hom 1 = f.hom 1 + g.hom 1
    simp
  · intro r f
    change (r • f).hom 1 = r • f.hom 1
    simp

private noncomputable def singleHomLinearEquiv {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) :
    (ModuleCat.of A A ⟶ M) ≃ₗ[A]
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let f : (ModuleCat.of A A ⟶ M) →ₗ[A] (F.obj (ModuleCat.of A A) ⟶ F.obj M) := {
    toFun := F.map
    map_add' := fun x y => by simp
    map_smul' := fun r x => by simp }
  exact LinearEquiv.ofBijective f
    ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective (ModuleCat.of A A) M)

private lemma isZero_unit_X {A : Type u} [CommRing A] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).X i) :=
  HomologicalComplex.isZero_single_obj_X _ 0 _ i hi

private noncomputable def unitEvalLin {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    Cochain (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) I n →ₗ[A] I.X n where
  toFun z := unitHomEquiv (I.X n)
    (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat.{u} A)) (zero_add n) z)
  map_add' z z' := by
    simp only [Cochain.fromSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, unitHomEquiv,
      Cochain.add_v, Preadditive.comp_add, ModuleCat.hom_add, LinearMap.add_apply]
  map_smul' r z := by
    simp only [Cochain.fromSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, unitHomEquiv,
      Cochain.smul_v, Linear.comp_smul, ModuleCat.hom_smul, LinearMap.smul_apply,
      RingHom.id_apply]

private lemma unitEvalLin_bijective {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    Function.Bijective (unitEvalLin I n) :=
  (unitHomEquiv (I.X n)).bijective.comp
    (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat.{u} A)) (zero_add n)).bijective

private noncomputable def unitEval {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex.HomComplexR A (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) I ⟶ I :=
  HomologicalComplex.Hom.mk (fun n => ModuleCat.ofHom (unitEvalLin I n)) (by
    rintro i j rfl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hd : (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).d 0 1 = 0 :=
      (isZero_unit_X (A := A) 1 (by omega)).eq_of_tgt _ _
    change (I.d i (i + 1)).hom (unitEvalLin I i z) = unitEvalLin I (i + 1) (δ i (i + 1) z)
    simp only [unitEvalLin, LinearMap.coe_mk, AddHom.coe_mk, Cochain.fromSingleEquiv,
      AddEquiv.coe_mk, Equiv.coe_fn_mk, unitHomEquiv]
    rw [δ_v i (i + 1) rfl z 0 (i + 1) (by omega) i 1 (by omega) (by omega), hd]
    simp)

private noncomputable def unitHomIso {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex.HomComplexR A (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) I ≅ I := by
  have (n : ℤ) : IsIso ((unitEval I).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (unitEvalLin_bijective I n)
  have : IsIso (unitEval I) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (unitEval I)

private noncomputable def unitHomComplexHomologyAddEquiv {A : Type u} [CommRing A]
    (L : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        (𝟙_ (ModuleCat.{u} A))).HomComplex L).homology i ≃+
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat).obj (L.homology i) := by
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (𝟙_ (ModuleCat.{u} A))
  let F := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  have hP : P = 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) := rfl
  have hC : P.HomComplex L =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR A P L) := rfl
  let e1 : F.obj ((CochainComplex.HomComplexR A P L).homology i) ≅
      F.obj (L.homology i) := by
    simpa [hP, HomologicalComplex.homologyFunctor_obj] using
      F.mapIso ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A)
        (ComplexShape.up ℤ) i).mapIso (unitHomIso L))
  let e : (P.HomComplex L).homology i ≅ F.obj (L.homology i) := by
    rw [hC]
    exact ((CochainComplex.HomComplexR A P L).sc i).mapHomologyIso F ≪≫ e1
  exact e.addCommGroupIsoToAddEquiv

/-- `Ext^i_A(A[0], K)` is the degree `i` cohomology of `K`: the ring itself is the unit of the
monoidal structure, and evaluation at `1` identifies the Hom complex out of the unit with its
target. -/
private noncomputable def extEquivHomology {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) K i ≃
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (𝟙_ (ModuleCat.{u} A))
  haveI : P.IsStrictlyLE 0 := by
    dsimp [P]
    infer_instance
  haveI : ∀ j : ℤ, Projective (P.X j) := by
    intro j
    by_cases hj : j = 0
    · subst j
      exact ModuleCat.projective_of_free (M := ModuleCat.of A A) (Basis.singleton Unit A)
    · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj).projective
  let L := DerivedCategory.Q.objPreimage K
  let q := HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let eP := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P
  let eShift := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L⟦i⟧) ≪≫
    (DerivedCategory.Q.commShiftIso i).app L
  let eK := DerivedCategory.Q.objObjPreimageIso K
  let eMorph :
      (DerivedCategory.Qh.obj (q.obj P) ⟶ DerivedCategory.Qh.obj (q.obj (L⟦i⟧))) ≃
        DerivedCategory.Ext (DerivedCategory.Q.obj P) K i :=
    (Iso.homCongr eP eShift).trans
      (Iso.homCongr (Iso.refl (DerivedCategory.Q.obj P))
        ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) i).mapIso eK))
  let eRHom := homComplexHomologyRHomAddEquiv P L 0 i
  let eUnit := unitHomComplexHomologyAddEquiv L i
  let F := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K ≅ L.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eK).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app L
  exact ((eRHom.toEquiv.trans eMorph).symm.trans eUnit.toEquiv).trans
    (F.mapIso eH).addCommGroupIsoToAddEquiv.toEquiv.symm

private lemma ext_subsingleton_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) K i) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  rw [(extEquivHomology K i).subsingleton_congr]
  change Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) ↔ _
  exact ModuleCat.isZero_iff_subsingleton.symm

private lemma ext_nontrivial_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) K i) ↔
      Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  simpa using (extEquivHomology K i).nontrivial_congr

/-- **Stacks Project, Tag 0AWR.** The depth of a Noetherian local ring `A` with normalized
dualizing complex `ω_A` is the least `δ ≥ 0` with `H^{-δ}(ω_A) ≠ 0`. -/
@[stacks 0AWR]
public theorem depth_eq_least_nonzero_homology {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, 0} K) :
    ∃ δ : ℕ,
      IsLeast
          {i : ℕ |
            ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj K)}
          δ ∧
        Module.depth A (IsLocalRing.maximalIdeal A) A = (δ : ℕ∞) := by
  obtain ⟨δ, hleast, hdepth⟩ :=
    depth_eq_least_nonzero_negative_ext.{u, 0} (A := A) (M := A) K hK inferInstance
  refine ⟨δ, ?_, hdepth⟩
  have hset :
      {i : ℕ |
        Nontrivial
          (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
            K (-(i : ℤ)))} =
      {i : ℕ |
        ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj K)} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    rw [ext_nontrivial_iff K (-(i : ℤ)), ModuleCat.isZero_iff_subsingleton,
      not_subsingleton_iff_nontrivial]
  rwa [hset] at hleast

private lemma isCohenMacaulayLocalRing_iff_moduleAtMaximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsCohenMacaulayLocalRing A ↔ Module.IsCohenMacaulayAtMaximalIdeal A A := by
  have hproper : IsLocalRing.maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self,
    IsCohenMacaulayModule]
  change (Module.depthSup A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) =
      Module.supportDim A A ↔
    (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) = Module.supportDim A A
  have hd : Module.depthSup A (IsLocalRing.maximalIdeal A) A =
      Module.depth A (IsLocalRing.maximalIdeal A) A := by
    rw [Module.depthSup_eq_iSup, Module.depth, ite_eq_right hproper]
  rw [← congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hd]

/-- The (finite) Krull dimension of a Noetherian local ring, as a natural number. -/
public abbrev localRingDimension (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : ℕ :=
  (IsLocalRing.maximalIdeal A).height.toNat

private lemma localRingDimension_cast_eq {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    ((localRingDimension A : ℕ∞) : WithBot ℕ∞) = ringKrullDim A := by
  let : (IsLocalRing.maximalIdeal A : Ideal A).FiniteHeight :=
    Ideal.finiteHeight_of_isNoetherianRing _
  have hh : (IsLocalRing.maximalIdeal A : Ideal A).height ≠ ⊤ :=
    Ideal.height_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [localRingDimension, ENat.natCast_toNat_eq_self.mpr hh]
  exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim

private lemma supportDim_self_eq_localRingDimension {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    Module.supportDim A A = ((localRingDimension A : ℕ∞) : WithBot ℕ∞) := by
  rw [Module.supportDim_self_eq_ringKrullDim]
  exact localRingDimension_cast_eq.symm

private lemma depth_eq_localRingDimension {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : IsCohenMacaulayLocalRing A) :
    Module.depth A (IsLocalRing.maximalIdeal A) A = (localRingDimension A : ℕ∞) := by
  have hcm := isCohenMacaulayLocalRing_iff_moduleAtMaximalIdeal A |>.mp hA
  rw [Module.IsCohenMacaulayAtMaximalIdeal, Module.supportDim_self_eq_ringKrullDim] at hcm
  exact_mod_cast hcm.trans localRingDimension_cast_eq.symm

/-- The dualizing module associated to `K` is its cohomology in degree `-dim(A)`. -/
public abbrev dualizingModule {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A)) : ModuleCat.{u} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(localRingDimension A : ℤ))).obj K

/-- A derived object is cohomologically concentrated in a single degree if all its homology
objects except possibly one are zero. -/
public abbrev IsCohomologicallyConcentratedInOneDegree {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i ≠ n →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)

private lemma homology_isZero_of_not_ext_nontrivial {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (i : ℤ)
    (h : ¬ Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) K i)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (not_nontrivial_iff_subsingleton.mp fun h' => h ((ext_nontrivial_iff K i).mpr h'))

private lemma homology_isZero_off_dimension_of_cm {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, 0} K)
    (hA : IsCohenMacaulayLocalRing A) (i : ℤ) (hi : i ≠ -(localRingDimension A : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  have hcrit := isCohenMacaulay_iff_ext_concentrated.{u, 0} (M := A) K hK
  have hCM : Module.IsCohenMacaulayAtMaximalIdeal A A :=
    (isCohenMacaulayLocalRing_iff_moduleAtMaximalIdeal A).mp hA
  have hcriterion3 : Module.IsCohenMacaulayAtMaximalIdeal A A ↔
      (∀ i : ℤ,
        ¬ (0 ≤ i ∧ Module.supportDim A A = ((i.toNat : ℕ∞) : WithBot ℕ∞)) →
          Subsingleton (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) K (-i))) :=
    hcrit.out 1 3
  have hdim : Module.supportDim A A = ((localRingDimension A : ℕ∞) : WithBot ℕ∞) :=
    supportDim_self_eq_localRingDimension
  by_cases hpos : 0 < i
  · apply homology_isZero_of_not_ext_nontrivial K i
    intro hExt
    have hmem := ext_degree_mem_Icc_of_nontrivial.{u, 0} (M := A) K hK
      (localRingDimension A) hdim i hExt
    have hright := (Set.mem_Icc.mp hmem).2
    omega
  · let j : ℤ := -i
    have hj : 0 ≤ j := by dsimp [j]; omega
    have hjd : j ≠ localRingDimension A := by
      intro heq
      apply hi
      dsimp [j] at heq
      omega
    have hnotDim : ¬ (0 ≤ j ∧ Module.supportDim A A =
        ((j.toNat : ℕ∞) : WithBot ℕ∞)) := by
      rintro ⟨_, hEq⟩
      have hcast : ((localRingDimension A : ℕ∞) : WithBot ℕ∞) =
          ((j.toNat : ℕ∞) : WithBot ℕ∞) := hdim.symm.trans hEq
      have hnat : localRingDimension A = j.toNat :=
        WithTop.coe_injective (WithBot.coe_injective hcast)
      apply hjd
      have hjcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
      omega
    have hzero := hcriterion3.mp hCM j hnotDim
    have hzero' := (ext_subsingleton_iff K (-j)).mp hzero
    simpa [j] using hzero'

private lemma concentrated_of_iso_single {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (M : ModuleCat.{u} A)
    (h : Nonempty (K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M)) :
    IsCohomologicallyConcentratedInOneDegree K := by
  rcases h with ⟨e⟩
  refine ⟨n, fun i hi => ?_⟩
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M)) := by
    have hsingle := HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) n M i hi
    exact hsingle.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) n).obj M))
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e)

private lemma homology_degree_eq_of_nontrivial {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n i : ℤ)
    (hzero : ∀ i : ℤ, i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (h : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    i = n := by
  by_contra hne
  exact not_subsingleton _ (ModuleCat.isZero_iff_subsingleton.mp (hzero i hne))

private lemma isCohenMacaulayLocalRing_of_concentrated {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, 0} K)
    (hconc : IsCohomologicallyConcentratedInOneDegree K) : IsCohenMacaulayLocalRing A := by
  have hcrit := isCohenMacaulay_iff_ext_concentrated.{u, 0} (M := A) K hK
  have hext : ∀ i j : ℤ,
      Nontrivial (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) K i) →
      Nontrivial (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) K j) →
      i = j := by
    rcases hconc with ⟨n, hn⟩
    intro i j hi hj
    exact (homology_degree_eq_of_nontrivial K n i hn
      ((ext_nontrivial_iff K i).mp hi)).trans
      (homology_degree_eq_of_nontrivial K n j hn
        ((ext_nontrivial_iff K j).mp hj)).symm
  have hCM := (hcrit.out 1 2).mpr hext
  exact (isCohenMacaulayLocalRing_iff_moduleAtMaximalIdeal A).mpr hCM

/-- **Stacks Project, Tag 0AWS, equivalent conditions (1)--(3).** A Noetherian local ring is
Cohen--Macaulay exactly when its normalized dualizing complex is concentrated in one degree,
and exactly when it is its dualizing module placed in degree minus the dimension. -/
@[stacks 0AWS "equivalent conditions (1)--(3)"]
public theorem isCohenMacaulay_tfae_dualizingComplex {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, 0} K) :
    List.TFAE
      [ IsCohenMacaulayLocalRing A,
        IsCohomologicallyConcentratedInOneDegree K,
        Nonempty
          (K ≅
            (DerivedCategory.singleFunctor (ModuleCat.{u} A)
              (-(localRingDimension A : ℤ))).obj (dualizingModule K)) ] := by
  have h12 : IsCohenMacaulayLocalRing A ↔ IsCohomologicallyConcentratedInOneDegree K :=
    ⟨fun hA => ⟨_, homology_isZero_off_dimension_of_cm K hK hA⟩,
      isCohenMacaulayLocalRing_of_concentrated K hK⟩
  have h13 : IsCohenMacaulayLocalRing A ↔
      Nonempty (K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A)
        (-(localRingDimension A : ℤ))).obj (dualizingModule K)) :=
    ⟨fun hA => DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero K
      (-(localRingDimension A : ℤ)) (homology_isZero_off_dimension_of_cm K hK hA),
      fun h => h12.mpr (concentrated_of_iso_single K _ (dualizingModule K) h)⟩
  tfae_have 1 ↔ 2 := h12
  tfae_have 1 ↔ 3 := h13
  tfae_finish

private noncomputable def extModuleLinearEquivDualizingModule {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, 0} K)
    (hA : IsCohenMacaulayLocalRing A) :
    (extIntoDualizingComplex.{u, 0} K (localRingDimension A)).obj
      (Opposite.op (ModuleCat.of A A)) ≃ₗ[A]
        ULift.{max 1 (u + 1)} (dualizingModule K) := by
  let d := localRingDimension A
  let P := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let omega := dualizingModule K
  let eK : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj omega :=
    Classical.choice (((isCohenMacaulay_tfae_dualizingComplex K hK).out 1 3).mp hA)
  let eShift : (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-(d : ℤ))).obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj omega :=
    (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-(d : ℤ))).mapIso eK ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-(d : ℤ)) 0 (-(d : ℤ))
        (by dsimp [d]; omega)).app omega
  have eHom : (P ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-(d : ℤ))).obj K) ≃ₗ[A]
      (P ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj omega) :=
    Linear.homCongr A (Iso.refl P) eShift
  dsimp [extIntoDualizingComplex]
  change (P ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-(d : ℤ))).obj K) ≃ₗ[A]
    ULift.{u + 1} omega
  exact eHom.trans ((singleHomLinearEquiv omega).symm.trans
    ((unitHomLinearEquiv omega).trans ULift.moduleEquiv.symm))

/-- The depth of a subsingleton module is `⊤`. -/
private lemma depth_eq_top_of_subsingleton {R : Type*} [CommRing R] (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] [Subsingleton M] : Module.depth R I M = ⊤ := by
  simp [Module.depth, Subsingleton.elim (I • (⊤ : Submodule R M)) ⊤]

private lemma depth_eq_of_linearEquiv_of_smulTop_neTop {R : Type*} [CommRing R]
    {I : Ideal R} {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (hM : I • (⊤ : Submodule R M) ≠ ⊤)
    (hN : I • (⊤ : Submodule R N) ≠ ⊤) :
    Module.depth R I M = Module.depth R I N := by
  rw [Module.depth, ite_eq_right hM, ← Module.depthSup_eq_iSup,
    Module.depth, ite_eq_right hN, ← Module.depthSup_eq_iSup]
  exact depth_eq_of_linearEquiv I e

/-- **Stacks Project, Tag 0AWS, final assertion.** Over a Cohen--Macaulay local ring, the
dualizing module of a normalized dualizing complex is maximal Cohen--Macaulay. -/
@[stacks 0AWS "the dualizing module is maximal Cohen--Macaulay"]
public theorem dualizingModule_isMaximalCohenMacaulay {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, 0} K)
    (hA : IsCohenMacaulayLocalRing A) :
    Module.IsMaximalCohenMacaulay A (dualizingModule K) := by
  let d := localRingDimension A
  let CM := CohenMacaulayModulesOfDepth.{u, u} A d
  let x₀ : CM := ⟨ModuleCat.of A A, ⟨inferInstance,
    (isCohenMacaulayLocalRing_iff_moduleAtMaximalIdeal A).mp hA, depth_eq_localRingDimension hA⟩⟩
  let x := Opposite.op x₀
  let F := cohenMacaulayExtDuality.{u, 0} K hK d
  have hforget := Classical.choice
    (cohenMacaulayExtDuality_forget.{u, 0} K hK d)
  let eForget : ((F.functor.obj x).1) ≃ₗ[A]
      ((extIntoDualizingComplex.{u, 0} K d).obj
        (Opposite.op (ModuleCat.of A A))) := (hforget.app x).toLinearEquiv
  let eOmega := (eForget.trans (extModuleLinearEquivDualizingModule K hK hA)).trans
    ULift.moduleEquiv
  have hdepthSrc : Module.depth A (IsLocalRing.maximalIdeal A) ((F.functor.obj x).1) =
      (d : ℕ∞) := (F.functor.obj x).2.2.2
  have : Nontrivial ((F.functor.obj x).1) := by
    by_contra hn
    have : Subsingleton ((F.functor.obj x).1) := not_nontrivial_iff_subsingleton.mp hn
    exact ENat.natCast_ne_top d
      (hdepthSrc.symm.trans (depth_eq_top_of_subsingleton _))
  have : Module.Finite A ((F.functor.obj x).1) := (F.functor.obj x).2.1
  have : Module.Finite A (dualizingModule K) := Module.Finite.equiv eOmega
  have : Nontrivial (dualizingModule K) := eOmega.toEquiv.nontrivial_congr.mp inferInstance
  have hdepthOmega := depth_eq_of_linearEquiv_of_smulTop_neTop eOmega
    (Module.maximalIdeal_smul_top_ne_top _) (Module.maximalIdeal_smul_top_ne_top _)
  have hdim : ((d : ℕ∞) : WithBot ℕ∞) = ringKrullDim A := localRingDimension_cast_eq
  rw [Module.IsMaximalCohenMacaulay, ← hdim]
  exact_mod_cast hdepthOmega.symm.trans hdepthSrc

private theorem finite_single_homology {A : Type u} [CommRing A]
    (M : ModuleCat.{v} A) [Module.Finite A M] (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)) := by
  by_cases hi : i = 0
  · subst i
    have : Module.Finite A ((𝟭 (ModuleCat.{v} A)).obj M) := by
      change Module.Finite A M
      infer_instance
    exact Module.Finite.equiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{v} A) 0).app M).symm.toLinearEquiv
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)) := by
      by_cases h : i < 0
      · exact DerivedCategory.isZero_of_isGE _ 0 i h
      · exact DerivedCategory.isZero_of_isLE _ 0 i (by omega)
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Module.Finite.of_finite

private noncomputable def uliftDerivedIso {A : Type u} [CommRing A] :
    (ModuleCat.uliftFunctor.{u, max u v} A).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{max u v} A)) := by
  let U := ModuleCat.uliftFunctor.{u, max u v} A
  let e : U ≅ 𝟭 (ModuleCat.{max u v} A) := NatIso.ofComponents
    (fun M => (ULift.moduleEquiv : ULift.{u} M ≃ₗ[A] M).toModuleIso)
    (by intros; ext; rfl)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ))
    (U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
    U.mapDerivedCategory (𝟭 _)
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)) DerivedCategory.Q)

private noncomputable def flatExtensionSingleIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (M : ModuleCat.{max u v} A) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u,u,v} f).functor.obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
    (DerivedCategory.singleFunctor _ 0).obj ((ModuleCat.extendScalars f).obj M) := by
  let E := CochainComplex.DerivedTensor.extensionScalars.{u,u,v} f
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u,u,v} f
  have : E.PreservesHomology :=
    CochainComplex.DerivedTensor.extensionScalars_preservesHomology f hf
  have : PreservesFiniteLimits E := E.preservesFiniteLimits_of_preservesHomology
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{max u v} A) (.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((E.mapHomologicalComplex _).map g))
      infer_instance)
  exact D.functor.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M) ≪≫
    (asIso D.comparison).app ((CochainComplex.singleFunctor _ 0).obj M) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (E.obj M)).symm

private noncomputable def extTargetShiftEquiv
    {A : Type u} [CommRing A] (X K : DerivedCategory (ModuleCat.{v} A))
    (a i : ℤ) :
    DerivedCategory.Ext X (K⟦a⟧) i ≃ DerivedCategory.Ext X K (a + i) := by
  let e := (shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} A)) a i (a + i) rfl).app K
  exact Iso.homCongr (Iso.refl X) e.symm

/-- The Cohen--Macaulay criterion of [stacks 0B5A] with the normalizing shift kept explicit: the
dualizing complex `K` is normalized only after shifting by `-n`, and the uniqueness of the degree
in which `Ext` is nonzero is invariant under that shift. -/
private theorem cohenMacaulay_iff_ext_unique
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u w)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] (K : DerivedCategory (ModuleCat.{max u w} A))
    (n : ℤ) (hn : IsNormalizedDualizingComplex (K⟦-n⟧)) :
    Module.IsCohenMacaulayAtMaximalIdeal A M ↔
      ∀ i j : ℤ,
        Nontrivial (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max u w} A) 0).obj (ModuleCat.of A M)) K i) →
        Nontrivial (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max u w} A) 0).obj (ModuleCat.of A M)) K j) →
        i = j := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u w} A) 0).obj (ModuleCat.of A M)
  have hforward := (isCohenMacaulay_iff_ext_concentrated (M := M) (K⟦-n⟧) hn).out 1 2
  have up : ∀ k, Nontrivial (DerivedCategory.Ext X K k) →
      Nontrivial (DerivedCategory.Ext X (K⟦-n⟧) (k + n)) := fun k hk => by
    apply (extTargetShiftEquiv (A := A) X K (-n) (k + n)).symm.nontrivial_congr.mp
    convert hk using 1
    abel_nf
  have down : ∀ k, Nontrivial (DerivedCategory.Ext X (K⟦-n⟧) k) →
      Nontrivial (DerivedCategory.Ext X K (-n + k)) := fun k hk => by
    simpa only [neg_one_smul] using
      (extTargetShiftEquiv (A := A) X K (-n) k).nontrivial_congr.mp hk
  refine ⟨fun hcm i j hi hj => ?_, fun hu => hforward.mpr fun i j hi hj => ?_⟩
  · have := hforward.mp hcm (i + n) (j + n) (up i hi) (up j hj)
    omega
  · have := hu (-n + i) (-n + j) (down i hi) (down j hj)
    omega

private noncomputable def extensionLocalizationIso {A : Type u} [CommRing A]
    (S : Submonoid A) (M : ModuleCat.{max u v} A) :
    (ModuleCat.extendScalars (algebraMap A (Localization S))).obj M ≅
      ModuleCat.of (Localization S) (LocalizedModule S M) := by
  let E := (ModuleCat.extendScalars (algebraMap A (Localization S))).obj M
  let R := (ModuleCat.restrictScalars (algebraMap A (Localization S))).obj E
  letI : Module (Localization S) R := inferInstanceAs (Module (Localization S) E)
  letI : IsScalarTower A (Localization S) R := ⟨fun r s x => by
    change (r • s) • x = (algebraMap A (Localization S)) r • (s • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let e : R ≃ₗ[A] LocalizedModule S M :=
    (CochainComplex.DerivedTensor.extensionScalarsLocalizedModuleIso
    (A := Localization S) S M).toLinearEquiv
  exact (e.extendScalarsOfIsLocalization S (Localization S)).toModuleIso

private theorem single_pseudoCoherent {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : ModuleCat.{max u v} A) [Module.Finite A M] :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) :=
  (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    _ 0 M).2.1.mpr ⟨⟨0, fun i hi => DerivedCategory.isZero_of_isLE _ 0 i hi⟩,
    finite_single_homology M⟩

private noncomputable def derivedHomIsoInternal {A : Type u} [CommRing A]
    (X Y : DerivedCategory (ModuleCat.{max u v} A)) :
    (Dualizing.dualizingDerivedHomFunctor A Y).obj (.op X) ≅
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u,v} A).obj (.op X, Y) :=
  Iso.refl _

/-- The source's `RHom_A(M, ω_A)_p = RHom_{A_p}(M_p, (ω_A)_p)`: the degree `i` cohomology of
derived Hom, localized at `p`, is `Ext^i` over `A_p` from `M_p` into the localized complex. -/
private noncomputable def localizedHomologyExtEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : ModuleCat.{max u v} A) [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : Dualizing.IsDualizingComplex K) (p : PrimeSpectrum A) (i : ℤ) :
    LocalizedModule p.asIdeal.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u,max u v} A K).obj (.op
          ((DerivedCategory.singleFunctor _ 0).obj M)))) ≃
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} (Localization.AtPrime p.asIdeal)) 0).obj
        (ModuleCat.of (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M)))
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime p.asIdeal))).obj K) i := by
  let B := Localization.AtPrime p.asIdeal
  let f := algebraMap A B
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u,u,max u v} f
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  let H := (Dualizing.dualizingDerivedHomFunctor.{u,max u v} A K).obj (.op X)
  let Kp := (StacksDraft.PseudoCoherence.derivedExtensionScalars f).obj K
  let Mp := ModuleCat.of B (LocalizedModule.AtPrime p.asIdeal M)
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B p.asIdeal.primeCompl)
  have hGE : ∃ a : ℤ, K.IsGE a := by
    obtain ⟨a, b, I, hIa, hIb, hIinj, ⟨e⟩⟩ := hK.finiteInjectiveDimension
    exact ⟨a, DerivedCategory.TStructure.t.isGE_of_iso e.symm a⟩
  let eBC := @Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u,u,v} A B _ _ f
    D.functor D.comparison D.isLeftDerived X K
  letI : IsIso eBC := @Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u,u,v} A B _ _ f
    D.functor D.comparison D.isLeftDerived X K
      (.inr (.inr (.inl ⟨hf, single_pseudoCoherent M, hGE⟩)))
  let eX : D.functor.obj X ≅ (DerivedCategory.singleFunctor _ 0).obj Mp :=
    flatExtensionSingleIso.{u,max u v} f hf M ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (extensionLocalizationIso p.asIdeal.primeCompl M)
  let eK : D.functor.obj K ≅ Kp :=
    D.functor.mapIso (uliftDerivedIso.app K).symm
  let eH : D.functor.obj H ≅ (Dualizing.dualizingDerivedHomFunctor.{u,max u v} B Kp).obj
      (.op ((DerivedCategory.singleFunctor _ 0).obj Mp)) :=
    D.functor.mapIso (derivedHomIsoInternal.{u,max u v} X K) ≪≫
      asIso eBC ≪≫
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u,max u v} B).mapIso
        (eX.symm.op.prod eK) ≪≫
      (derivedHomIsoInternal.{u,max u v} ((DerivedCategory.singleFunctor _ 0).obj Mp) Kp).symm
  let eLoc :=
    (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u,u,max u v}
      (R := A) (A := B) p.asIdeal.primeCompl i).app H
  let eHhom := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).mapIso eH
  exact eLoc.toLinearEquiv.toEquiv.symm.trans (eHhom.toLinearEquiv.toEquiv.trans
    (Dualizing.extIntoOmegaAtLinearEquiv.{u,max u v} B Kp i Mp).toEquiv.symm)

/-- The locus where at most one cohomology module of a bounded complex with finite cohomology is
supported is open: only finitely many degrees contribute, and each support is closed. -/
private theorem isOpen_unique_support {A : Type u} [CommRing A]
    (H : DerivedCategory (ModuleCat.{v} A))
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj H))
    (hb : (DerivedCategory.TStructure.t).bounded H) :
    IsOpen {p : PrimeSpectrum A | ∀ i j : ℤ,
      p ∈ Module.support A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj H) →
      p ∈ Module.support A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).obj H) →
        i = j} := by
  classical
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
  have : H.IsGE a := ha
  have : H.IsLE b := hb
  let S := Finset.Icc a b
  let Z := fun i => Module.support A
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj H)
  have hmem (p : PrimeSpectrum A) (i : ℤ) (hp : p ∈ Z i) : i ∈ S := by
    by_contra hi
    have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj H) := by
      by_cases h : i < a
      · exact DerivedCategory.isZero_of_isGE H a i h
      · exact DerivedCategory.isZero_of_isLE H b i (by
          simp only [S, Finset.mem_Icc, not_and_or, not_le] at hi
          omega)
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    have : Subsingleton (LocalizedModule.AtPrime p.asIdeal
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj H)) := inferInstance
    exact (not_nontrivial_iff_subsingleton.mpr this) (Module.mem_support_iff.mp hp)
  have heq : {p : PrimeSpectrum A | ∀ i j : ℤ, p ∈ Z i → p ∈ Z j → i = j} =
      ⋂ i ∈ S, ⋂ j ∈ S, {p | p ∈ Z i → p ∈ Z j → i = j} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h i _ j _ => h i j, fun h i j hi hj => h i (hmem p i hi) j (hmem p j hj) hi hj⟩
  rw [heq]
  apply isOpen_biInter_finset
  intro i hi
  apply isOpen_biInter_finset
  intro j hj
  by_cases hij : i = j
  · simp [hij]
  · have := hfin i
    have := hfin j
    convert ((Module.isClosed_support (R := A) (M :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj H))).inter
        (Module.isClosed_support (R := A) (M :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).obj H)))).isOpen_compl using 1
    ext p
    simp [Z, hij, not_and]

private theorem cohenMacaulay_congr {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    Module.IsCohenMacaulayAtMaximalIdeal A M ↔ Module.IsCohenMacaulayAtMaximalIdeal A N := by
  have hd (I : Ideal A) : Module.depth A I M = Module.depth A I N := by
    have hs : {rs : List A | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs} =
        {rs : List A | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular N rs} := by
      ext rs
      simp only [Set.mem_ofPred_eq, e.isRegular_congr rs]
    have ht : I • (⊤ : Submodule A M) = ⊤ ↔ I • (⊤ : Submodule A N) = ⊤ := by
      rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_smul'', Submodule.map_top,
        LinearEquiv.range]
    simp only [Module.depth, hs, ht]
  unfold Module.IsCohenMacaulayAtMaximalIdeal
  rw [hd, Module.supportDim_eq_of_equiv e]

private noncomputable def localizationEquiv {A : Type u} [CommRing A]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (p : PrimeSpectrum A) :
    LocalizedModule.AtPrime p.asIdeal M ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal N :=
  ((IsLocalizedModule.isBaseChange p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).equiv.symm.trans
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) e)).trans
  (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)).equiv

private theorem supportDim_eq_zero_of_support_points_eq_maximal
    {R : Type u} [CommRing R] [IsLocalRing R] {N : Type v}
    [AddCommGroup N] [Module R N] [Nontrivial N]
    (h : ∀ q : PrimeSpectrum R, q ∈ Module.support R N →
      q.asIdeal = IsLocalRing.maximalIdeal R) :
    Module.supportDim R N = 0 := by
  have : Subsingleton (Module.support R N) := ⟨fun a b =>
    Subtype.ext (PrimeSpectrum.ext ((h a.1 a.2).trans (h b.1 b.2).symm))⟩
  have hne : Module.supportDim R N ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial R N
  rw [Module.supportDim] at hne ⊢
  have : Nonempty (Module.support R N) := Order.krullDim_ne_bot_iff.mp hne
  exact Order.krullDim_eq_zero

private theorem localized_support_point_eq_maximal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (hmin : (Module.annihilator A M).IsMinimalPrime p.asIdeal)
    (q : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    (hq : q ∈ Module.support (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)) :
    q.asIdeal = IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
  have hqann := Module.annihilator_le_of_mem_support hq
  have hcomap : Module.annihilator A M ≤
      Ideal.comap (algebraMap A (Localization.AtPrime p.asIdeal)) q.asIdeal := by
    intro a ha
    apply Ideal.mem_comap.mpr
    apply hqann
    rw [Module.mem_annihilator]
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk,
        Module.mem_annihilator.mp ha m]
      exact LocalizedModule.zero_mk s
  have hle : Ideal.comap (algebraMap A (Localization.AtPrime p.asIdeal)) q.asIdeal ≤
      p.asIdeal := by
    calc
      _ ≤ Ideal.comap (algebraMap A (Localization.AtPrime p.asIdeal))
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) :=
            Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime q.asIdeal)
      _ = p.asIdeal := Localization.AtPrime.under_maximalIdeal
  have heq := hmin.eq_of_le
    ⟨Ideal.comap_isPrime _ _, hcomap⟩ hle
  exact (Localization.AtPrime.eq_maximalIdeal_iff_under_eq).mp (by
    simpa [Ideal.under] using heq)

private theorem localized_module_supportDim_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (hmin : (Module.annihilator A M).IsMinimalPrime p.asIdeal)
    [Nontrivial (LocalizedModule.AtPrime p.asIdeal M)] :
    Module.supportDim (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) = 0 :=
  supportDim_eq_zero_of_support_points_eq_maximal fun q hq =>
    localized_support_point_eq_maximal p hmin q hq

/-- At a generic point of its support a finite module has `depth = dim = 0`, so it is
Cohen--Macaulay there. This is the source's density argument. -/
private theorem cohenMacaulay_at_minimal_support
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (hmin : (Module.annihilator A M).IsMinimalPrime p.asIdeal) :
    Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := by
  have : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) :=
    (Module.mem_support_iff.mpr (Module.mem_support_iff_of_finite.mpr hmin.le))
  have hdim : Module.supportDim (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) = 0 :=
    localized_module_supportDim_eq_zero p hmin
  have hdepthle :
      (Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal M) : WithBot ℕ∞) ≤ 0 := by
    rw [← hdim]
    exact Module.depth_le_supportDim _ _ _ (Module.maximalIdeal_smul_top_ne_top _)
  have hdepth :
      (Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal M) : WithBot ℕ∞) = 0 :=
    le_antisymm hdepthle (WithBot.coe_le_coe.mpr bot_le)
  change (Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule.AtPrime p.asIdeal M) : WithBot ℕ∞) =
    Module.supportDim (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)
  rw [hdepth, hdim]

/-- A Cohen--Macaulay localization of a module is nonzero, so its prime lies in the support. -/
@[stacks 0EHS "the locus is contained in the support"]
public theorem cohenMacaulayLocus_subset_support
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] :
    {p : PrimeSpectrum A |
      Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)} ⊆ Module.support A M := by
  intro p hp
  by_contra hpM
  have : Subsingleton (LocalizedModule.AtPrime p.asIdeal M) :=
    not_nontrivial_iff_subsingleton.mp hpM
  have hdepth : Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule.AtPrime p.asIdeal M) = ⊤ := depth_eq_top_of_subsingleton _
  have hdim : Module.supportDim (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) = ⊥ :=
    Module.supportDim_eq_bot_of_subsingleton _ _
  change (Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule.AtPrime p.asIdeal M) : WithBot ℕ∞) =
    Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) at hp
  rw [hdepth, hdim] at hp
  exact top_ne_bot hp

/-- **Stacks Project, Tag 0EHS, openness.** The Cohen--Macaulay locus of a finite module over a
Noetherian ring with a dualizing complex is open in the support of the module. -/
@[stacks 0EHS "relative openness"]
public theorem isOpen_cohenMacaulayLocus
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (ω : DerivedCategory (ModuleCat.{w} A)) (hω : Dualizing.IsDualizingComplex ω) :
    IsOpen {p : ↥(Module.support A M) |
      Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal M)} := by
  classical
  let : Small.{max u w} M := Module.Finite.small A M
  let N := ModuleCat.of A (Shrink.{max u w} M)
  let e : M ≃ₗ[A] N := (Shrink.linearEquiv A M).symm
  let K := (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A A)).obj ω
  have hK : Dualizing.IsDualizingComplex K :=
    isDualizingComplex_derivedExtensionScalars_self ω hω
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u w} A) 0).obj N
  let H := (Dualizing.dualizingDerivedHomFunctor.{u,max u w} A K).obj (.op X)
  have hXfin := finite_single_homology N
  have hXbounded : (DerivedCategory.TStructure.t).bounded X :=
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  have ho := isOpen_unique_support H
    (Dualizing.dualizingDerivedHom_finiteCohomology.{u,max u w} A K hK X hXfin)
    (Dualizing.dualizingDerivedHom_bounded.{u,max u w} A K hK X hXfin hXbounded)
  have hpull := ho.preimage (continuous_subtype_val :
    Continuous (Subtype.val : Module.support A M → PrimeSpectrum A))
  convert hpull using 1
  ext p
  change Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p.1.asIdeal)
    (LocalizedModule.AtPrime p.1.asIdeal M) ↔ ∀ i j : ℤ,
      p.1 ∈ Module.support A ((DerivedCategory.homologyFunctor (ModuleCat.{max u w} A) i).obj H) →
      p.1 ∈ Module.support A ((DerivedCategory.homologyFunctor (ModuleCat.{max u w} A) j).obj H) →
        i = j
  rw [cohenMacaulay_congr (localizationEquiv e p.1)]
  have : Nontrivial (LocalizedModule.AtPrime p.1.asIdeal M) := Module.mem_support_iff.mp p.2
  have : Nontrivial (LocalizedModule.AtPrime p.1.asIdeal N) :=
    (localizationEquiv e p.1).toEquiv.nontrivial_congr.mp inferInstance
  let Kp := (StacksDraft.PseudoCoherence.derivedExtensionScalars
    (algebraMap A (Localization.AtPrime p.1.asIdeal))).obj K
  let n := Dualizing.dualizingDimension K p.1
  have hn : IsNormalizedDualizingComplex (Kp⟦-n⟧) :=
    Dualizing.dualizingDimension_spec K hK p.1
  refine (cohenMacaulay_iff_ext_unique Kp n hn).trans ?_
  have hs (i : ℤ) : p.1 ∈ Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u w} A) i).obj H) ↔
      Nontrivial (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max u w} (Localization.AtPrime p.1.asIdeal)) 0).obj
          (ModuleCat.of (Localization.AtPrime p.1.asIdeal)
            (LocalizedModule.AtPrime p.1.asIdeal N))) Kp i) :=
    Module.mem_support_iff.trans (localizedHomologyExtEquiv N K hK p.1 i).nontrivial_congr
  exact ⟨fun h i j hi hj => h i j ((hs i).mp hi) ((hs j).mp hj),
    fun h i j hi hj => h i j ((hs i).mpr hi) ((hs j).mpr hj)⟩

/-- **Stacks Project, Tag 0EHS, density.** The Cohen--Macaulay locus of a finite module over a
Noetherian ring is dense in the support of the module. -/
@[stacks 0EHS "density"]
public theorem dense_cohenMacaulayLocus
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Dense {p : ↥(Module.support A M) |
      Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal M)} := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨V, hV, hUV⟩ := isOpen_induced_iff.mp hU
  have hxpre : x ∈ Subtype.val ⁻¹' V := hUV.symm ▸ hxU
  have hxV : x.1 ∈ V := hxpre
  obtain ⟨J, hJ, hJx⟩ :=
    Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp x.2)
  let r : PrimeSpectrum A := ⟨J, hJ.isPrime⟩
  have hrle : r ≤ x.1 := PrimeSpectrum.asIdeal_le_asIdeal r x.1 |>.mpr hJx
  have hrsupp : r ∈ Module.support A M :=
    Module.mem_support_iff_of_finite.mpr hJ.le
  obtain ⟨T, hTb, hxt, hTV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp
      (IsOpen.mem_nhds hV hxV)
  obtain ⟨f, rfl⟩ := hTb
  have hfx : f ∉ x.1.asIdeal := (PrimeSpectrum.mem_basicOpen f x.1).mp hxt
  have hfr : r ∈ PrimeSpectrum.basicOpen f :=
    (PrimeSpectrum.mem_basicOpen f r).mpr fun h => hfx (hrle h)
  exact ⟨⟨r, hrsupp⟩, hUV ▸ hTV hfr, cohenMacaulay_at_minimal_support r hJ⟩

end Dualizing

end
