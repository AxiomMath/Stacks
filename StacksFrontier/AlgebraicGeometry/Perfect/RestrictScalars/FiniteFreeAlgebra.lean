module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings

/-!
# Pseudo-coherence over a finite free algebra

Let `A` be a commutative ring and let `R` be a possibly noncommutative `A`-algebra which is
finite free as an `A`-module. An object of the derived category of right `R`-modules which is
pseudo-coherent after restriction of scalars to `A` is represented by a bounded-above complex of
finite free right `R`-modules.

## Main results

* `StacksDraft.PseudoCoherence.exists_boundedAboveFiniteFree_of_isPseudoCoherent_restrictScalars`
  gives the finite free representative.

## Implementation notes

Right `R`-modules are represented as left modules over the opposite ring `Rᵐᵒᵖ`, which is where
the possible noncommutativity of `R` is felt: `Rᵐᵒᵖ` carries no `CommRing` instance, so the
restriction-of-scalars equivalence of Stacks 064Z is used at its general signature, which allows
both rings to be noncommutative.

Since the pseudo-coherence predicate of this development is indexed by a cutoff, unqualified
pseudo-coherence of the restriction of scalars is expressed by requiring it for every integer
cutoff.

## References

* [Stacks Project, Tag 0CSF](https://stacks.math.columbia.edu/tag/0CSF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe uA uR v uN

namespace StacksDraft.PseudoCoherence

/-- A finite free module is pseudo-coherent: the complex concentrated in degree `0` is already a
bounded complex of finite free modules. -/
private lemma isModulePseudoCoherent_of_finite_free {A : Type uA} [Ring A]
    (N : ModuleCat.{uN} A) (hN : Module.Finite A N ∧ Module.Free A N) :
    IsModulePseudoCoherent (R := A) N := by
  let E := (HomologicalComplex.single (ModuleCat.{uN} A) (ComplexShape.up ℤ) 0).obj N
  refine ⟨E, ⟨⟨0, inferInstance⟩, ?_⟩, ⟨Iso.refl _⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact hN
  · have hz := ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N i hi)
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton A _⟩

/-- The opposite ring of an algebra, as a module over the base ring: multiplication in `Rᵐᵒᵖ` is
reversed, but the base ring acts centrally, so `op` is `A`-linear. -/
private def opAlgebraLinearEquiv {A : Type uA} {R : Type uR}
    [CommRing A] [Ring R] [Algebra A R] : R ≃ₗ[A] Rᵐᵒᵖ where
  toFun := MulOpposite.op
  invFun := MulOpposite.unop
  left_inv := MulOpposite.unop_op
  right_inv := MulOpposite.op_unop
  map_add' := MulOpposite.op_add
  map_smul' a r := by simp [Algebra.smul_def, Algebra.commutes]

/-- The opposite ring of a finite free algebra is pseudo-coherent as a module over the base. -/
private lemma isModulePseudoCoherent_restrictScalars_op {A : Type uA} {R : Type uR}
    [CommRing A] [Ring R] [Algebra A R] (hR : Module.Finite A R ∧ Module.Free A R) :
    IsModulePseudoCoherent (R := A) ((ModuleCat.restrictScalars.{uR} (algebraMap A Rᵐᵒᵖ)).obj
      (ModuleCat.of.{uR, uR} Rᵐᵒᵖ Rᵐᵒᵖ)) := by
  let eA := opAlgebraLinearEquiv (A := A) (R := R)
  let G := ModuleCat.restrictScalars.{uR} (algebraMap A Rᵐᵒᵖ)
  let N := G.obj (ModuleCat.of.{uR, uR} Rᵐᵒᵖ Rᵐᵒᵖ)
  let e : Rᵐᵒᵖ ≃ₗ[A] N :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' a b := by
        apply MulOpposite.unop_injective
        dsimp only [N, G]
        have hsource : MulOpposite.unop (a • b) = a • MulOpposite.unop b :=
          (congrArg MulOpposite.unop (eA.map_smul a (MulOpposite.unop b))).symm
        show MulOpposite.unop (a • b) = MulOpposite.unop (algebraMap A Rᵐᵒᵖ a * b)
        rw [hsource, MulOpposite.unop_mul, Algebra.smul_def]
        show algebraMap A R a * MulOpposite.unop b =
          MulOpposite.unop b * algebraMap A R a
        exact Algebra.commutes a (MulOpposite.unop b) }
  have := hR.2
  exact isModulePseudoCoherent_of_finite_free N
    ⟨(Module.Finite.equiv_iff (eA.trans e)).mp hR.1, Module.Free.of_equiv (eA.trans e)⟩

/-- **Stacks 0CSF.** If a derived right `R`-module is pseudo-coherent over `A`, where `R` is a
possibly noncommutative `A`-algebra which is finite free over `A`, then it is represented by a
bounded-above complex of finite free right `R`-modules. -/
@[stacks 0CSF]
theorem exists_boundedAboveFiniteFree_of_isPseudoCoherent_restrictScalars
    (A : Type uA) (R : Type uR) [CommRing A] [Ring R] [Algebra A R]
    (M : DerivedCategory (ModuleCat.{max uA uR v} Rᵐᵒᵖ))
    (hR : Module.Finite A R ∧ Module.Free A R)
    (hM : ∀ m : ℤ, IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{max uA uR v} (algebraMap A Rᵐᵒᵖ)).mapDerivedCategory.obj M)
      m) :
    ∃ E : CochainComplex (ModuleCat.{max uA uR v} Rᵐᵒᵖ) ℤ,
      IsBoundedAboveFiniteFree E ∧ Nonempty (DerivedCategory.Q.obj E ≅ M) := by
  let f : A →+* Rᵐᵒᵖ := algebraMap A Rᵐᵒᵖ
  -- `Rᵐᵒᵖ` is finite free over `A`, hence pseudo-coherent as an `A`-module: the input to 064Z.
  have hB := isModulePseudoCoherent_restrictScalars_op (A := A) (R := R) hR
  let F := ModuleCat.restrictScalars.{max uA uR v} f
  let K := DerivedCategory.Q.objPreimage M
  let e : DerivedCategory.Q.obj K ≅ M := DerivedCategory.Q.objObjPreimageIso M
  -- Pseudo-coherence over `A` of `M`, then of a complex representing it.
  have hPCₐ : IsPseudoCoherent (F.mapDerivedCategory.obj M) :=
    (pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective.{uA, max uR v}
      (F.mapDerivedCategory.obj M) 0).1.2 hM
  have hPCₐK : IsPseudoCoherent (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) :=
    hPCₐ.ofIso (F.mapDerivedCategory.mapIso e).symm
  have hPCₐK' : IsPseudoCoherent
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    hPCₐK.ofIso (F.mapDerivedCategoryFactors.app K)
  -- Stacks 064Z reflects pseudo-coherence back to `B = Rᵐᵒᵖ`.
  have hPCᵦK : IsPseudoCoherent (DerivedCategory.Q.obj K) :=
    (pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars f hB K 0).2.2 hPCₐK'
  exact hPCᵦK.ofIso e

end StacksDraft.PseudoCoherence

end
