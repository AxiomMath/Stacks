module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MilnorPatching.ModuleCategory
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties.MonoidalStructure
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties.MonoidalStructure

/-!
# Properties and tensor products under formal glueing

## Main results

* `FormalGlueing.formalGlueing_preserves_moduleProperties_tensor_and_algebras`: property
  detection and the pointwise symmetric monoidal enhancement of the canonical glueing
  equivalence.

## Implementation notes

Requiring the generic and every local projection to be strong braided fixes the symmetric
monoidal structure on glueing data pointwise and retains all coherence and naturality data. The
principal-localization and adic-completion formulations are stated for the actual canonical
functors occurring in Tags 05ES and 05ET: their pullback tensors are fixed pointwise by the two
braided projection functors, the overlap comparisons are monoidal natural isomorphisms, and the
induced commutative algebra equivalences are the canonical `Equivalence.mapCommMon`. Here
algebras are commutative, as in the Stacks Project convention (Tag 0006).

## References

* [Stacks Project, Tag 05EU](https://stacks.math.columbia.edu/tag/05EU)
-/

@[expose] public section

namespace FormalGlueing

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open FormalGlueing

open scoped TensorProduct
open TensorProduct

private theorem baseChange_hom_ext
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    {φ ψ : S ⊗[R] M →ₗ[S] N}
    (h : ∀ m, φ ((1 : S) ⊗ₜ[R] m) = ψ ((1 : S) ⊗ₜ[R] m)) : φ = ψ := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
    have eq : s ⊗ₜ[R] m = s • ((1 : S) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [eq, map_smul, map_smul, h]

/-- A functor out of the transported symmetric monoidal structure is braided as soon as its
precomposition with the equivalence is isomorphic to a braided functor. -/
private noncomputable abbrev braidedProjection_of_iso
    {C D E : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C] [Category D]
    [Category E] [MonoidalCategory E] [SymmetricCategory E]
    (e : C ≌ D) (P : D ⥤ E) {Q : C ⥤ E} [Q.Braided] (i : Q ≅ e.functor ⋙ P) :
    letI := Monoidal.transport e
    letI : SymmetricCategory D := Monoidal.Transported.instSymmetricCategory e
    P.Braided :=
  letI := braidedOfNatIso i
  braidedProjection e P

/-- The transported monoidal structure makes an equivalence monoidal. -/
private theorem isMonoidal_transport
    {C D : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C] [Category D]
    (e : C ≌ D) :
    letI := Monoidal.transport e
    letI : SymmetricCategory D := Monoidal.Transported.instSymmetricCategory e
    letI : e.functor.Braided := Monoidal.instBraidedTransportedFunctorEquivalenceTransported e
    letI : e.inverse.Braided := Monoidal.instBraidedTransportedInverseEquivalenceTransported e
    e.IsMonoidal := by
  let := Monoidal.transport e
  let : SymmetricCategory D := Monoidal.Transported.instSymmetricCategory e
  let : e.functor.Braided := Monoidal.instBraidedTransportedFunctorEquivalenceTransported e
  let : e.inverse.Braided := Monoidal.instBraidedTransportedInverseEquivalenceTransported e
  let : (Monoidal.equivalenceTransported e).symm.IsMonoidal := inferInstance
  exact Equivalence.isMonoidal_symm (e := (Monoidal.equivalenceTransported e).symm)

-- Tensor coherence involves several nested scalar extensions and their module structures.
set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private noncomputable def finiteScalarExtensionMonoidal
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (FormalGlueing.finiteExtensionOfScalars.{u, u, u} R S).Monoidal := by
  let unit := AlgebraTensorModule.rid R S S
  exact Functor.CoreMonoidal.toMonoidal
    (Functor.CoreMonoidal.mk'
      (εIso := unit.symm.toFGModuleCatIso)
      (μIso := fun M N ↦ (AlgebraTensorModule.distribBaseChange R S M N).symm.toFGModuleCatIso)
      (μIso_inv_natural_left := fun {M M'} g N ↦ by
        apply FGModuleCat.hom_ext
        apply baseChange_hom_ext
        intro t
        change TensorProduct.map (g.hom.hom.baseChange S) LinearMap.id
            (AlgebraTensorModule.distribBaseChange R S M N ((1 : S) ⊗ₜ[R] t)) =
          AlgebraTensorModule.distribBaseChange R S M' N
            ((1 : S) ⊗ₜ[R] TensorProduct.map g.hom.hom LinearMap.id t)
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | tmul m n => rfl)
      (μIso_inv_natural_right := fun {N N'} M g ↦ by
        apply FGModuleCat.hom_ext
        apply baseChange_hom_ext
        intro t
        change TensorProduct.map LinearMap.id (g.hom.hom.baseChange S)
            (AlgebraTensorModule.distribBaseChange R S M N ((1 : S) ⊗ₜ[R] t)) =
          AlgebraTensorModule.distribBaseChange R S M N'
            ((1 : S) ⊗ₜ[R] TensorProduct.map LinearMap.id g.hom.hom t)
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | tmul m n => rfl)
      (oplax_associativity := fun M N K ↦ by
        apply FGModuleCat.hom_ext
        apply baseChange_hom_ext
        intro t
        change TensorProduct.assoc S (S ⊗[R] M) (S ⊗[R] N) (S ⊗[R] K)
            (TensorProduct.map (AlgebraTensorModule.distribBaseChange R S M N).toLinearMap
              LinearMap.id (AlgebraTensorModule.distribBaseChange R S (M ⊗[R] N) K
                ((1 : S) ⊗ₜ[R] t))) =
          TensorProduct.map LinearMap.id (AlgebraTensorModule.distribBaseChange R S N K).toLinearMap
            (AlgebraTensorModule.distribBaseChange R S M (N ⊗[R] K)
              ((1 : S) ⊗ₜ[R] TensorProduct.assoc R M N K t))
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | tmul x k =>
          induction x using TensorProduct.induction_on with
          | zero => simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]
          | add x y hx hy => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx,
            hy]
          | tmul m n => rfl)
      (oplax_left_unitality := fun M ↦ by
        apply FGModuleCat.hom_ext
        apply baseChange_hom_ext
        intro m
        change ((1 : S)) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) =
          (unit ((1 : S) ⊗ₜ[R] ((1 : R)))) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)
        congr 1
        change (1 : S) = ((1 : R) • (1 : S))
        rw [one_smul])
      (oplax_right_unitality := fun M ↦ by
        apply FGModuleCat.hom_ext
        apply baseChange_hom_ext
        intro m
        change ((1 : S) ⊗ₜ[R] m) ⊗ₜ[S] ((1 : S)) =
          ((1 : S) ⊗ₜ[R] m) ⊗ₜ[S] (unit ((1 : S) ⊗ₜ[R] ((1 : R))))
        congr 1
        change (1 : S) = ((1 : R) • (1 : S))
        rw [one_smul]))

-- Normalize the two tensor flips through extension of scalars.
set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private noncomputable def finiteScalarExtensionBraided
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (FormalGlueing.finiteExtensionOfScalars.{u, u, u} R S).Braided := by
  refine { __ := finiteScalarExtensionMonoidal R S, braided := ?_ }
  intro M N
  apply FGModuleCat.hom_ext
  change ((TensorProduct.comm R M N).toLinearMap.baseChange S).comp
      (AlgebraTensorModule.distribBaseChange R S M N).symm.toLinearMap =
    (AlgebraTensorModule.distribBaseChange R S N M).symm.toLinearMap.comp
      (TensorProduct.comm S (S ⊗[R] M) (S ⊗[R] N)).toLinearMap
  apply TensorProduct.ext'
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | tmul b n =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        AlgebraTensorModule.distribBaseChange_symm_tmul, LinearMap.baseChange_tmul,
        TensorProduct.comm_tmul, mul_comm]

-- Compare the iterated tensorators on pure tensors.
set_option backward.isDefEq.respectTransparency false in
private theorem finiteScalarComparison_isMonoidal
    (R S T U : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S U] [Algebra T U]
    (τ : FormalGlueing.finiteExtensionOfScalars R S ⋙ FormalGlueing.finiteExtensionOfScalars S U ⟶
      FormalGlueing.finiteExtensionOfScalars R T ⋙ FormalGlueing.finiteExtensionOfScalars T U)
    (hτ : ∀ (M : FGModuleCat.{u} R) (m : M),
      τ.app M ((1 : U) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) =
        (1 : U) ⊗ₜ[T] ((1 : T) ⊗ₜ[R] m)) :
    letI := finiteScalarExtensionMonoidal R S
    letI := finiteScalarExtensionMonoidal R T
    letI := finiteScalarExtensionMonoidal S U
    letI := finiteScalarExtensionMonoidal T U
    τ.IsMonoidal := by
  let := finiteScalarExtensionMonoidal R S
  let := finiteScalarExtensionMonoidal R T
  let := finiteScalarExtensionMonoidal S U
  let := finiteScalarExtensionMonoidal T U
  let F := FormalGlueing.finiteExtensionOfScalars.{u, u, u} R S ⋙
    FormalGlueing.finiteExtensionOfScalars S U
  let G := FormalGlueing.finiteExtensionOfScalars.{u, u, u} R T ⋙
    FormalGlueing.finiteExtensionOfScalars T U
  constructor
  · apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    show τ.app (FGModuleCat.of R R) (s ⊗ₜ[S] ((1 : S) ⊗ₜ[R] (1 : R))) =
      s ⊗ₜ[T] ((1 : T) ⊗ₜ[R] (1 : R))
    have h := congrArg (fun x ↦ (show U from s) • x) (hτ (FGModuleCat.of R R) (1 : R))
    rw [← map_smul] at h
    change τ.app (FGModuleCat.of R R) ((s * 1) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] (1 : R))) =
      (s * 1) ⊗ₜ[T] ((1 : T) ⊗ₜ[R] (1 : R)) at h
    simpa only [mul_one] using h
  · intro M N
    apply (cancel_epi (Functor.OplaxMonoidal.δ F M N)).mp
    apply (cancel_mono (Functor.OplaxMonoidal.δ G M N)).mp
    simp only [F, G, Category.assoc, Functor.Monoidal.δ_μ_assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]
    apply FGModuleCat.hom_ext
    apply doubleTensor_hom_ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul m n =>
      show (Functor.OplaxMonoidal.δ G M N)
          (τ.app (M ⊗ N) ((1 : U) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] (m ⊗ₜ[R] n)))) =
        (τ.app M ((1 : U) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))) ⊗ₜ[U]
          (τ.app N ((1 : U) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] n)))
      rw [hτ, hτ, hτ]
      rfl

-- Assemble the three equivalences with their dependent monoidal structures.
set_option backward.isDefEq.respectTransparency false in
/-- The three standard formal-glueing equivalences, with their compatible symmetric monoidal
structures and detection of finite generation, finite presentation, flatness, and projectivity. -/
private theorem formalGlueing_equivalences :
    (∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
      (r : ℕ) (f : Fin r → R) (hflat : Module.Flat R S)
      (hq : Function.Bijective
        (Ideal.quotientMap
          ((Ideal.span (Set.range f)).map (algebraMap R S))
          (algebraMap R S) Ideal.le_comap_map)),
      let c := moduleGlueingConstruction.{u, v, w} S f
      letI := c.category
      let G := ModuleGlueingDatum.{u, v, w} S f c.comparison
      ∃ (sourceTensor : LargeModuleMonoidalStructure.{u, max u v w} R)
          (genericTensor : LargeModuleMonoidalStructure.{v, max u v w} S)
          (localTensor : ∀ i, LargeModuleMonoidalStructure.{u, max u v w}
            (Localization.Away (f i)))
          (glueingTensor : MonoidalCategory G)
          (e : ModuleCat.{max u v w} R ≌ G),
        letI := sourceTensor.monoidal
        letI := genericTensor.monoidal
        letI (i : Fin r) := (localTensor i).monoidal
        letI := sourceTensor.symmetric
        letI := genericTensor.symmetric
        letI (i : Fin r) := (localTensor i).symmetric
        letI := glueingTensor
        ∃ (_ : SymmetricCategory G)
            (_ : (genericProjection S f c).Braided)
            (_ : ∀ i, (localProjection S f c i).Braided)
            (_ : c.canonical.Braided) (_ : c.sections.Braided)
            (_ : e.functor.Braided) (_ : e.inverse.Braided) (_ : e.IsMonoidal),
          e.functor = c.canonical ∧ e.inverse = c.sections ∧
          (∀ M : ModuleCat.{max u v w} R,
            (Module.Finite R M ↔
              Module.Finite S (e.functor.obj M).generic ∧
                ∀ i, Module.Finite (Localization.Away (f i))
                  ((e.functor.obj M).localPiece i)) ∧
            (Module.FinitePresentation R M ↔
              Module.FinitePresentation S (e.functor.obj M).generic ∧
                ∀ i, Module.FinitePresentation (Localization.Away (f i))
                  ((e.functor.obj M).localPiece i)) ∧
            (Module.Flat R M ↔
              Module.Flat S (e.functor.obj M).generic ∧
                ∀ i, Module.Flat (Localization.Away (f i))
                  ((e.functor.obj M).localPiece i)) ∧
            (Module.Projective R M ↔
              Module.Projective S (e.functor.obj M).generic ∧
                ∀ i, Module.Projective (Localization.Away (f i))
                  ((e.functor.obj M).localPiece i))) ∧
          ∃ algebraEquivalence : CommMon (ModuleCat.{max u v w} R) ≌ CommMon G,
            algebraEquivalence = e.mapCommMon) ∧
    (∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
      (f : R) (hflat : Module.Flat R S)
      (hq : Function.Bijective
        (Ideal.quotientMap ((Ideal.span {f}).map (algebraMap R S))
          (algebraMap R S) Ideal.le_comap_map)),
      let Rf := Localization.Away f
      let Sf := Localization.Away (algebraMap R S f)
      let ρ := FormalGlueing.principalLocalizationMap R S f
      letI : Algebra Rf Sf := ρ.toAlgebra
      let generic := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)
      let localPiece := ModuleCat.extendScalars.{u, u, max u v w} (algebraMap R Rf)
      let genericOverlap := ModuleCat.extendScalars.{v, v, max u v w} (algebraMap S Sf)
      let localOverlap := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap Rf Sf)
      ∃ comparison : generic ⋙ genericOverlap ≅ localPiece ⋙ localOverlap,
        (∀ (M : ModuleCat.{max u v w} R) (m : M),
          comparison.hom.app M
              ((ModuleCat.extendRestrictScalarsAdj.{max u v w, v, v}
                (algebraMap S Sf)).unit.app
                (generic.obj M)
                ((ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v}
                  (algebraMap R S)).unit.app M m)) =
            (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v}
              (algebraMap Rf Sf)).unit.app
              (localPiece.obj M)
              ((ModuleCat.extendRestrictScalarsAdj.{max u v w, u, u}
                (algebraMap R Rf)).unit.app M m)) ∧
        let F := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
          genericOverlap localOverlap (ModuleCat.{max u v w} R)).obj
          { fst := generic, snd := localPiece, iso := comparison }
        ∃ (sourceTensor : LargeModuleMonoidalStructure.{u, max u v w} R)
            (genericTensor : LargeModuleMonoidalStructure.{v, max u v w} S)
            (localTensor : LargeModuleMonoidalStructure.{u, max u v w} Rf)
            (overlapTensor : LargeModuleMonoidalStructure.{v, max u v w} Sf)
            (glueingTensor : MonoidalCategory
              (CategoricalPullback genericOverlap localOverlap))
            (e : ModuleCat.{max u v w} R ≌
              CategoricalPullback genericOverlap localOverlap),
          letI := sourceTensor.monoidal
          letI := genericTensor.monoidal
          letI := localTensor.monoidal
          letI := overlapTensor.monoidal
          letI := sourceTensor.symmetric
          letI := genericTensor.symmetric
          letI := localTensor.symmetric
          letI := overlapTensor.symmetric
          letI := glueingTensor
          ∃ (_ : SymmetricCategory (CategoricalPullback genericOverlap localOverlap))
              (_ : generic.Braided) (_ : localPiece.Braided)
              (_ : genericOverlap.Braided) (_ : localOverlap.Braided)
              (_ : comparison.hom.IsMonoidal)
              (_ : (CategoricalPullback.π₁ genericOverlap localOverlap).Braided)
              (_ : (CategoricalPullback.π₂ genericOverlap localOverlap).Braided)
              (_ : F.Braided) (_ : e.functor.Braided) (_ : e.inverse.Braided)
              (_ : e.IsMonoidal),
            e.functor = F ∧
            (∀ M : ModuleCat.{max u v w} R,
              (Module.Finite R M ↔ Module.Finite S (F.obj M).fst ∧
                Module.Finite Rf (F.obj M).snd) ∧
              (Module.FinitePresentation R M ↔
                Module.FinitePresentation S (F.obj M).fst ∧
                  Module.FinitePresentation Rf (F.obj M).snd) ∧
              (Module.Flat R M ↔ Module.Flat S (F.obj M).fst ∧
                Module.Flat Rf (F.obj M).snd) ∧
              (Module.Projective R M ↔ Module.Projective S (F.obj M).fst ∧
                Module.Projective Rf (F.obj M).snd)) ∧
            ∃ algebraEquivalence : CommMon (ModuleCat.{max u v w} R) ≌
                CommMon (CategoricalPullback genericOverlap localOverlap),
              algebraEquivalence = e.mapCommMon) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (f : R),
      let I := Ideal.span {f}
      let Rhat := AdicCompletion I R
      let Rf := Localization.Away f
      let Sf := Localization.Away (algebraMap R Rhat f)
      let ρ := FormalGlueing.principalLocalizationMap R Rhat f
      letI : Algebra Rf Sf := ρ.toAlgebra
      let completion := FormalGlueing.finiteAdicCompletion R I
      let localPiece := FormalGlueing.finiteExtensionOfScalars R Rf
      let completionOverlap := FormalGlueing.finiteExtensionOfScalars Rhat Sf
      let localOverlap := FormalGlueing.finiteExtensionOfScalars Rf Sf
      ∃ comparison : completion ⋙ completionOverlap ≅ localPiece ⋙ localOverlap,
        (∀ (M : FGModuleCat.{u} R) (m : M) (s : Sf),
          comparison.hom.app M (s ⊗ₜ[Rhat] AdicCompletion.of I M m) =
            s ⊗ₜ[Rf] ((1 : Rf) ⊗ₜ[R] m)) ∧
        let F := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
          completionOverlap localOverlap (FGModuleCat.{u} R)).obj
          { fst := completion, snd := localPiece, iso := comparison }
        ∃ (glueingTensor : MonoidalCategory
              (CategoricalPullback completionOverlap localOverlap))
            (e : FGModuleCat.{u} R ≌
              CategoricalPullback completionOverlap localOverlap),
          letI := glueingTensor
          ∃ (_ : SymmetricCategory (CategoricalPullback completionOverlap localOverlap))
              (_ : completion.Braided) (_ : localPiece.Braided)
              (_ : completionOverlap.Braided) (_ : localOverlap.Braided)
              (_ : comparison.hom.IsMonoidal)
              (_ : (CategoricalPullback.π₁ completionOverlap localOverlap).Braided)
              (_ : (CategoricalPullback.π₂ completionOverlap localOverlap).Braided)
              (_ : F.Braided) (_ : e.functor.Braided) (_ : e.inverse.Braided)
              (_ : e.IsMonoidal),
            e.functor = F ∧
            (∀ M : FGModuleCat.{u} R,
              (Module.Finite R M ↔ Module.Finite Rhat (F.obj M).fst ∧
                Module.Finite Rf (F.obj M).snd) ∧
              (Module.FinitePresentation R M ↔
                Module.FinitePresentation Rhat (F.obj M).fst ∧
                  Module.FinitePresentation Rf (F.obj M).snd) ∧
              (Module.Flat R M ↔ Module.Flat Rhat (F.obj M).fst ∧
                Module.Flat Rf (F.obj M).snd) ∧
              (Module.Projective R M ↔ Module.Projective Rhat (F.obj M).fst ∧
                Module.Projective Rf (F.obj M).snd)) ∧
            ∃ algebraEquivalence : CommMon (FGModuleCat.{u} R) ≌
                CommMon (CategoricalPullback completionOverlap localOverlap),
              algebraEquivalence = e.mapCommMon) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R S _ _ _ r f hflat hq
    obtain ⟨e, he, hi⟩ := FormalGlueing.canonicalFunctor_sections_areQuasiInverse
      R S f hflat hq
    let sourceTensor := largeModuleTensor.{u, max u v w} R
    let genericTensor := largeModuleTensor.{v, max u v w} S
    let localTensor := fun i ↦ largeModuleTensor.{u, max u v w} (Localization.Away (f i))
    let := sourceTensor.monoidal
    let c := moduleGlueingConstruction.{u, v, w} S f
    let := c.category
    refine ⟨sourceTensor, genericTensor, localTensor, Monoidal.transport e, e, ?_⟩
    let := genericTensor.monoidal
    let (i : Fin r) := (localTensor i).monoidal
    let := sourceTensor.symmetric
    let := genericTensor.symmetric
    let (i : Fin r) := (localTensor i).symmetric
    let := Monoidal.transport e
    let : SymmetricCategory (ModuleGlueingDatum S f c.comparison) :=
      Monoidal.Transported.instSymmetricCategory e
    let : e.functor.Braided := Monoidal.instBraidedTransportedFunctorEquivalenceTransported e
    let : e.inverse.Braided := Monoidal.instBraidedTransportedInverseEquivalenceTransported e
    let : e.IsMonoidal := isMonoidal_transport e
    have hcan : c.canonical.Braided := he ▸ (inferInstance : e.functor.Braided)
    have hsec : c.sections.Braided := hi ▸ (inferInstance : e.inverse.Braided)
    refine ⟨inferInstance, ?_, ?_, hcan, hsec, inferInstance, inferInstance,
      inferInstance, he, hi, ?_, e.mapCommMon, rfl⟩
    · let : (ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).Braided :=
        scalarExtensionBraided.{u, v, max u v w} (algebraMap R S)
      let iso : e.functor ⋙ genericProjection S f c ≅
          ModuleCat.extendScalars (algebraMap R S) := he ▸ canonicalGenericIso S f
      exact braidedProjection_of_iso e _ iso.symm
    · intro i
      let : (ModuleCat.extendScalars.{u, u, max u v w}
          (algebraMap R (Localization.Away (f i)))).Braided :=
        scalarExtensionBraided.{u, u, max u v w}
          (algebraMap R (Localization.Away (f i)))
      let iso : e.functor ⋙ localProjection S f c i ≅
          ModuleCat.extendScalars (algebraMap R (Localization.Away (f i))) :=
        he ▸ canonicalLocalIso S f i
      exact braidedProjection_of_iso e _ iso.symm
    · intro M
      rw [he]
      have h (k : Fin 4) : moduleProperty k R M ↔
          moduleProperty k S (c.canonical.obj M).generic ∧
            ∀ i, moduleProperty k (Localization.Away (f i))
              ((c.canonical.obj M).localPiece i) := by
        refine (moduleProperty_iff_glueing_baseChange k S f hflat hq M).trans
          (and_congr (moduleProperty_equiv_iff k (c.canonicalGeneric M)).symm
            (forall_congr' fun i ↦ ?_))
        exact (moduleProperty_equiv_iff k ((c.canonicalLocal M i).trans
          (LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) M))).symm
      exact ⟨h 0, h 1, h 2, h 3⟩
  · intro R S _ _ _ f hflat hq
    obtain ⟨comparison, hc, hF⟩ := FormalGlueing.exists_canonicalModuleGlueingEquivalence
      R S f hflat hq
    refine ⟨comparison, hc, ?_⟩
    let Rf := Localization.Away f
    let Sf := Localization.Away (algebraMap R S f)
    let : Algebra Rf Sf := (FormalGlueing.principalLocalizationMap R S f).toAlgebra
    let generic := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)
    let localPiece := ModuleCat.extendScalars.{u, u, max u v w} (algebraMap R Rf)
    let genericOverlap := ModuleCat.extendScalars.{v, v, max u v w} (algebraMap S Sf)
    let localOverlap := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap Rf Sf)
    let F := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      genericOverlap localOverlap (ModuleCat.{max u v w} R)).obj
      ⟨generic, localPiece, comparison⟩
    have : F.IsEquivalence := hF
    let e := F.asEquivalence
    let sR := largeModuleTensor.{u, max u v w} R
    let sS := largeModuleTensor.{v, max u v w} S
    let sRf := largeModuleTensor.{u, max u v w} Rf
    let sSf := largeModuleTensor.{v, max u v w} Sf
    let := sR.monoidal
    refine ⟨sR, sS, sRf, sSf, Monoidal.transport e, e, ?_⟩
    let := sS.monoidal
    let := sRf.monoidal
    let := sSf.monoidal
    let := sR.symmetric
    let := sS.symmetric
    let := sRf.symmetric
    let := sSf.symmetric
    let : generic.Braided := scalarExtensionBraided.{u, v, max u v w} _
    let : localPiece.Braided := scalarExtensionBraided.{u, u, max u v w} _
    let : genericOverlap.Braided := scalarExtensionBraided.{v, v, max u v w} _
    let : localOverlap.Braided := scalarExtensionBraided.{u, v, max u v w} _
    let := Monoidal.transport e
    let symm : SymmetricCategory (CategoricalPullback genericOverlap localOverlap) :=
      Monoidal.Transported.instSymmetricCategory e
    let := symm
    let hf : e.functor.Braided :=
      Monoidal.instBraidedTransportedFunctorEquivalenceTransported e
    let hi : e.inverse.Braided :=
      Monoidal.instBraidedTransportedInverseEquivalenceTransported e
    let := hf
    let := hi
    have hm : e.IsMonoidal := isMonoidal_transport e
    let := hm
    have hπ₁ : (CategoricalPullback.π₁ genericOverlap localOverlap).Braided :=
      braidedProjection_of_iso e _ (Q := generic) (Iso.refl _)
    have hπ₂ : (CategoricalPullback.π₂ genericOverlap localOverlap).Braided :=
      braidedProjection_of_iso e _ (Q := localPiece) (Iso.refl _)
    refine ⟨symm, inferInstance, inferInstance, inferInstance, inferInstance, ?_,
      hπ₁, hπ₂, hf, hf, hi, hm, rfl, ?_, e.mapCommMon, rfl⟩
    · exact scalarComparison_isMonoidal.{max u v w, u, v, u, v}
        (algebraMap R S) (algebraMap R Rf) (algebraMap S Sf) (algebraMap Rf Sf)
        comparison.hom hc
    · intro M
      exact ⟨moduleProperty_iff_principal_baseChange 0 S f hflat hq M,
        moduleProperty_iff_principal_baseChange 1 S f hflat hq M,
        moduleProperty_iff_principal_baseChange 2 S f hflat hq M,
        moduleProperty_iff_principal_baseChange 3 S f hflat hq M⟩
  · intro R _ _ f
    obtain ⟨comparison, hc, hF⟩ := FormalGlueing.exists_adicCompletionGlueingEquivalence R f
    refine ⟨comparison, hc, ?_⟩
    let I := Ideal.span {f}
    let Rhat := AdicCompletion I R
    let Rf := Localization.Away f
    let Sf := Localization.Away (algebraMap R Rhat f)
    let : Algebra Rf Sf := (FormalGlueing.principalLocalizationMap R Rhat f).toAlgebra
    let completion := FormalGlueing.finiteAdicCompletion R I
    let localPiece := FormalGlueing.finiteExtensionOfScalars R Rf
    let completionOverlap := FormalGlueing.finiteExtensionOfScalars Rhat Sf
    let localOverlap := FormalGlueing.finiteExtensionOfScalars Rf Sf
    let F := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      completionOverlap localOverlap (FGModuleCat.{u} R)).obj
      ⟨completion, localPiece, comparison⟩
    have : F.IsEquivalence := hF
    let e := F.asEquivalence
    let : (FormalGlueing.finiteExtensionOfScalars.{u, u, u} R Rhat).Braided :=
      finiteScalarExtensionBraided R Rhat
    let : localPiece.Braided := finiteScalarExtensionBraided R Rf
    let : completionOverlap.Braided := finiteScalarExtensionBraided Rhat Sf
    let : localOverlap.Braided := finiteScalarExtensionBraided Rf Sf
    let cIso := FormalGlueing.finiteAdicCompletionIsoExtensionOfScalars.{u, u} R I
    let : completion.Braided := braidedOfNatIso cIso.symm
    have hcIsoInv : cIso.inv.IsMonoidal :=
      Functor.Monoidal.natTransIsMonoidal_of_transport cIso.symm
    have hcIso : cIso.hom.IsMonoidal := by
      let : cIso.symm.hom.IsMonoidal := hcIsoInv
      exact inferInstanceAs cIso.symm.inv.IsMonoidal
    have hcMon : comparison.hom.IsMonoidal := by
      let c' := Functor.isoWhiskerRight cIso.symm completionOverlap ≪≫ comparison
      have h' : c'.hom.IsMonoidal := by
        apply finiteScalarComparison_isMonoidal R Rhat Rf Sf c'.hom
        intro M m
        show comparison.hom.app M
          ((1 : Sf) ⊗ₜ[Rhat] (cIso.inv.app M ((1 : Rhat) ⊗ₜ[R] m))) = _
        rw [FormalGlueing.finiteAdicCompletionIsoExtensionOfScalars_inv_app_tmul, one_smul]
        exact hc M m 1
      have heq : comparison.hom = Functor.whiskerRight cIso.hom completionOverlap ≫ c'.hom := by
        apply NatTrans.ext
        funext M
        show comparison.hom.app M = completionOverlap.map (cIso.hom.app M) ≫
          completionOverlap.map (cIso.inv.app M) ≫ comparison.hom.app M
        rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id, Category.id_comp]
      rw [heq]
      let := hcIso
      let := h'
      infer_instance
    refine ⟨Monoidal.transport e, e, ?_⟩
    let := Monoidal.transport e
    let symm : SymmetricCategory (CategoricalPullback completionOverlap localOverlap) :=
      Monoidal.Transported.instSymmetricCategory e
    let := symm
    let hf : e.functor.Braided :=
      Monoidal.instBraidedTransportedFunctorEquivalenceTransported e
    let hi : e.inverse.Braided :=
      Monoidal.instBraidedTransportedInverseEquivalenceTransported e
    let := hf
    let := hi
    have hm : e.IsMonoidal := isMonoidal_transport e
    let := hm
    have hπ₁ : (CategoricalPullback.π₁ completionOverlap localOverlap).Braided :=
      braidedProjection_of_iso e _ (Q := completion) (Iso.refl _)
    have hπ₂ : (CategoricalPullback.π₂ completionOverlap localOverlap).Braided :=
      braidedProjection_of_iso e _ (Q := localPiece) (Iso.refl _)
    refine ⟨symm, inferInstance, inferInstance, inferInstance, inferInstance, hcMon,
      hπ₁, hπ₂, hf, hf, hi, hm, rfl, ?_, e.mapCommMon, rfl⟩
    intro M
    have h (k : Fin 4) : moduleProperty k R M ↔
        moduleProperty k Rhat (F.obj M).fst ∧ moduleProperty k Rf (F.obj M).snd :=
      (moduleProperty_iff_principal_baseChange k Rhat f
        (AdicCompletion.flat_of_isNoetherian I)
        (AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing) M.obj).trans (and_congr
        (moduleProperty_equiv_iff k ((largeExtendScalarsEquiv Rhat M.obj).trans
          (FormalGlueing.adicCompletionTensorEquiv R I M)))
        (moduleProperty_equiv_iff k (largeExtendScalarsEquiv Rf M.obj)))
    exact ⟨h 0, h 1, h 2, h 3⟩


/-- **Stacks 05EU.** Formal glueing detects the standard finiteness and flatness properties,
is pointwise symmetric monoidal, and hence induces an equivalence on commutative algebra objects.
The final two clauses state property detection, pointwise symmetry, and the canonical commutative
algebra equivalence for the principal-localization and adic-completion functors of Tags 05ES
and 05ET. -/
@[stacks 05EU]
public theorem formalGlueing_preserves_moduleProperties_tensor_and_algebras :
    (∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
      (r : ℕ) (f : Fin r → R) (hflat : Module.Flat R S)
      (hq : Function.Bijective
        (Ideal.quotientMap
          ((Ideal.span (Set.range f)).map (algebraMap R S))
          (algebraMap R S) Ideal.le_comap_map)),
      let c := moduleGlueingConstruction.{u, v, w} S f
      letI := c.category
      let G := ModuleGlueingDatum.{u, v, w} S f c.comparison
      ∃ (sourceTensor : LargeModuleMonoidalStructure.{u, max u v w} R)
          (genericTensor : LargeModuleMonoidalStructure.{v, max u v w} S)
          (localTensor : ∀ i, LargeModuleMonoidalStructure.{u, max u v w}
            (Localization.Away (f i)))
          (glueingTensor : MonoidalCategory G)
          (e : ModuleCat.{max u v w} R ≌ G),
        letI := sourceTensor.monoidal
        letI := genericTensor.monoidal
        letI (i : Fin r) := (localTensor i).monoidal
        letI := sourceTensor.symmetric
        letI := genericTensor.symmetric
        letI (i : Fin r) := (localTensor i).symmetric
        letI := glueingTensor
        ∃ (_ : SymmetricCategory G)
            (_ : (genericProjection S f c).Braided)
            (_ : ∀ i, (localProjection S f c i).Braided)
            (_ : c.canonical.Braided) (_ : c.sections.Braided)
            (_ : e.functor.Braided) (_ : e.inverse.Braided) (_ : e.IsMonoidal),
          e.functor = c.canonical ∧ e.inverse = c.sections ∧
          (∀ M : ModuleCat.{max u v w} R,
            (Module.Finite R M ↔
              Module.Finite S (e.functor.obj M).generic ∧
                ∀ i, Module.Finite (Localization.Away (f i))
                  ((e.functor.obj M).localPiece i)) ∧
            (Module.FinitePresentation R M ↔
              Module.FinitePresentation S (e.functor.obj M).generic ∧
                ∀ i, Module.FinitePresentation (Localization.Away (f i))
                  ((e.functor.obj M).localPiece i)) ∧
            (Module.Flat R M ↔
              Module.Flat S (e.functor.obj M).generic ∧
                ∀ i, Module.Flat (Localization.Away (f i))
                  ((e.functor.obj M).localPiece i)) ∧
            (Module.Projective R M ↔
              Module.Projective S (e.functor.obj M).generic ∧
                ∀ i, Module.Projective (Localization.Away (f i))
                  ((e.functor.obj M).localPiece i))) ∧
          ∃ algebraEquivalence : CommMon (ModuleCat.{max u v w} R) ≌ CommMon G,
            algebraEquivalence = e.mapCommMon) ∧
    (∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
      (f : R) (hflat : Module.Flat R S)
      (hq : Function.Bijective
        (Ideal.quotientMap ((Ideal.span {f}).map (algebraMap R S))
          (algebraMap R S) Ideal.le_comap_map)),
      let Rf := Localization.Away f
      let Sf := Localization.Away (algebraMap R S f)
      let ρ := FormalGlueing.principalLocalizationMap R S f
      letI : Algebra Rf Sf := ρ.toAlgebra
      let generic := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)
      let localPiece := ModuleCat.extendScalars.{u, u, max u v w} (algebraMap R Rf)
      let genericOverlap := ModuleCat.extendScalars.{v, v, max u v w} (algebraMap S Sf)
      let localOverlap := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap Rf Sf)
      ∃ comparison : generic ⋙ genericOverlap ≅ localPiece ⋙ localOverlap,
        (∀ (M : ModuleCat.{max u v w} R) (m : M),
          comparison.hom.app M
              ((ModuleCat.extendRestrictScalarsAdj.{max u v w, v, v}
                (algebraMap S Sf)).unit.app
                (generic.obj M)
                ((ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v}
                  (algebraMap R S)).unit.app M m)) =
            (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v}
              (algebraMap Rf Sf)).unit.app
              (localPiece.obj M)
              ((ModuleCat.extendRestrictScalarsAdj.{max u v w, u, u}
                (algebraMap R Rf)).unit.app M m)) ∧
        let F := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
          genericOverlap localOverlap (ModuleCat.{max u v w} R)).obj
          { fst := generic, snd := localPiece, iso := comparison }
        ∃ (sourceTensor : LargeModuleMonoidalStructure.{u, max u v w} R)
            (genericTensor : LargeModuleMonoidalStructure.{v, max u v w} S)
            (localTensor : LargeModuleMonoidalStructure.{u, max u v w} Rf)
            (overlapTensor : LargeModuleMonoidalStructure.{v, max u v w} Sf)
            (glueingTensor : MonoidalCategory
              (CategoricalPullback genericOverlap localOverlap))
            (e : ModuleCat.{max u v w} R ≌
              CategoricalPullback genericOverlap localOverlap),
          letI := sourceTensor.monoidal
          letI := genericTensor.monoidal
          letI := localTensor.monoidal
          letI := overlapTensor.monoidal
          letI := sourceTensor.symmetric
          letI := genericTensor.symmetric
          letI := localTensor.symmetric
          letI := overlapTensor.symmetric
          letI := glueingTensor
          ∃ (_ : SymmetricCategory (CategoricalPullback genericOverlap localOverlap))
              (_ : generic.Braided) (_ : localPiece.Braided)
              (_ : genericOverlap.Braided) (_ : localOverlap.Braided)
              (_ : comparison.hom.IsMonoidal)
              (_ : (CategoricalPullback.π₁ genericOverlap localOverlap).Braided)
              (_ : (CategoricalPullback.π₂ genericOverlap localOverlap).Braided)
              (_ : F.Braided) (_ : e.functor.Braided) (_ : e.inverse.Braided)
              (_ : e.IsMonoidal),
            e.functor = F ∧
            (∀ M : ModuleCat.{max u v w} R,
              (Module.Finite R M ↔ Module.Finite S (F.obj M).fst ∧
                Module.Finite Rf (F.obj M).snd) ∧
              (Module.FinitePresentation R M ↔
                Module.FinitePresentation S (F.obj M).fst ∧
                  Module.FinitePresentation Rf (F.obj M).snd) ∧
              (Module.Flat R M ↔ Module.Flat S (F.obj M).fst ∧
                Module.Flat Rf (F.obj M).snd) ∧
              (Module.Projective R M ↔ Module.Projective S (F.obj M).fst ∧
                Module.Projective Rf (F.obj M).snd)) ∧
            ∃ algebraEquivalence : CommMon (ModuleCat.{max u v w} R) ≌
                CommMon (CategoricalPullback genericOverlap localOverlap),
              algebraEquivalence = e.mapCommMon) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (f : R),
      let I := Ideal.span {f}
      let Rhat := AdicCompletion I R
      let Rf := Localization.Away f
      let Sf := Localization.Away (algebraMap R Rhat f)
      let ρ := FormalGlueing.principalLocalizationMap R Rhat f
      letI : Algebra Rf Sf := ρ.toAlgebra
      let completion := FormalGlueing.finiteAdicCompletion R I
      let localPiece := FormalGlueing.finiteExtensionOfScalars R Rf
      let completionOverlap := FormalGlueing.finiteExtensionOfScalars Rhat Sf
      let localOverlap := FormalGlueing.finiteExtensionOfScalars Rf Sf
      ∃ comparison : completion ⋙ completionOverlap ≅ localPiece ⋙ localOverlap,
        (∀ (M : FGModuleCat.{u} R) (m : M) (s : Sf),
          comparison.hom.app M (s ⊗ₜ[Rhat] AdicCompletion.of I M m) =
            s ⊗ₜ[Rf] ((1 : Rf) ⊗ₜ[R] m)) ∧
        let F := (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
          completionOverlap localOverlap (FGModuleCat.{u} R)).obj
          { fst := completion, snd := localPiece, iso := comparison }
        ∃ (glueingTensor : MonoidalCategory
              (CategoricalPullback completionOverlap localOverlap))
            (e : FGModuleCat.{u} R ≌
              CategoricalPullback completionOverlap localOverlap),
          letI := glueingTensor
          ∃ (_ : SymmetricCategory (CategoricalPullback completionOverlap localOverlap))
              (_ : completion.Braided) (_ : localPiece.Braided)
              (_ : completionOverlap.Braided) (_ : localOverlap.Braided)
              (_ : comparison.hom.IsMonoidal)
              (_ : (CategoricalPullback.π₁ completionOverlap localOverlap).Braided)
              (_ : (CategoricalPullback.π₂ completionOverlap localOverlap).Braided)
              (_ : F.Braided) (_ : e.functor.Braided) (_ : e.inverse.Braided)
              (_ : e.IsMonoidal),
            e.functor = F ∧
            (∀ M : FGModuleCat.{u} R,
              (Module.Finite R M ↔ Module.Finite Rhat (F.obj M).fst ∧
                Module.Finite Rf (F.obj M).snd) ∧
              (Module.FinitePresentation R M ↔
                Module.FinitePresentation Rhat (F.obj M).fst ∧
                  Module.FinitePresentation Rf (F.obj M).snd) ∧
              (Module.Flat R M ↔ Module.Flat Rhat (F.obj M).fst ∧
                Module.Flat Rf (F.obj M).snd) ∧
              (Module.Projective R M ↔ Module.Projective Rhat (F.obj M).fst ∧
                Module.Projective Rf (F.obj M).snd)) ∧
            ∃ algebraEquivalence : CommMon (FGModuleCat.{u} R) ≌
                CommMon (CategoricalPullback completionOverlap localOverlap),
              algebraEquivalence = e.mapCommMon) :=
  formalGlueing_equivalences

end FormalGlueing

end
