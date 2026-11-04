module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassificationRefined
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleLiftWeakIdealOfDefinitionRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleModWeakIdeal

/-!
# An étale algebra from an étale system of quotient stages

Let `R` be a commutative ring with a topology, let `(J_i)` be a fundamental system of weak
ideals of definition of `R` and let `(B_i)` be an inverse system of `R ⧸ J_i`-algebras of the
kind Stacks 0AL1 attaches to a finite type morphism of affine formal algebraic spaces over
`Spf R`
(`AlgebraicGeometry.FormalSpace.FiniteTypeAlgebraSystem`): the transition `B_j → B_i` for
`i ≤ j` is surjective with kernel `J_i B_j`. Assume moreover that every structure map
`R ⧸ J_i → B_i` is étale. Then, once one index `i₀` is fixed, there is an étale `R`-algebra `A`
together with isomorphisms

`A ⧸ J_i A ≅ B_i` over `R ⧸ J_i`, for every `i ≥ i₀`,

compatible with the transitions of the two systems.

## Main definitions

* `AlgebraicGeometry.FormalSpace.weakIdealsBasis`: all the weak ideals of definition of a
  topological ring, ordered by reverse inclusion, as a fundamental system — the index in which
  the canonical diagrams of a formal spectrum are written.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_etale_algebra_of_etaleSystem`: the statement above.

## Implementation notes

This is the ring-theoretic content of the essential-surjectivity clause of **Stacks 0AN8** —
`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf` — namely the two steps of its proof
which cite Algebra and More on Algebra. Writing `B` for the source's base ring, `X` for the
affine formal algebraic space representable étale over `Y = Spf B` and `J₀` for the chosen weak
ideal of definition, the source argues: `X₀ = Spec(B/J₀) ×_Y X` is `Spec(A₀)` with `B/J₀ → A₀`
étale, so Stacks 04D1 produces an étale `B → A` with `A/J₀A ≅ A₀`; for any smaller ideal of
definition `J` both `B/J → A/JA` and `B/J → Ā` are étale and lift `B/J₀ → A₀`, so Stacks 0ALI
gives a unique `B/J`-algebra isomorphism `φ_J : A/JA → Ā` over that identification; and
uniqueness makes the `φ_J` compatible for varying `J`.

Here `Ā` is the member `B_i` of the given system and the identification of its reduction with
`A₀` is the system's own transition to the stage at `i₀`, whose kernel is the extended ideal.
Stacks 04D1 enters as `etale_lift_along_surjection`, and the unique-lifting clause of Stacks
0ALI as `RingHom.Etale.existsUnique_ringEquiv_of_isLocallyNilpotent` together with
`RingHom.Etale.ringHom_ext_of_isLocallyNilpotent`, whose locally nilpotent ideal is the image of
`J₀` in `R ⧸ J_i` — nilpotent by
`TopologicalRing.map_quotient_le_nilradical_of_isWeakIdealOfDefinition`, which needs only that
`J_i` is open. The compatibility in `i` is proved exactly as the source proves it: the two
composites `A ⧸ J_j A → B_i` are étale-algebra maps over `R ⧸ J_j` which agree after the
transition to `B_{i₀}`, and that transition has locally nilpotent kernel, so they are equal.

The indices are restricted to `i ≥ i₀` because the comparison used at `i` is the transition
`B_i → B_{i₀}`, which the system provides only for `i₀ ≤ i`. That is no loss where the index is
directed, as it is for the consumers of Stacks 0AL1: the indices above `i₀` are then cofinal, so
the isomorphisms `A ⧸ J_i A ≅ B_i` already determine the colimit.

This file is untagged substrate. The source does not number these two steps separately — they
are steps inside the proof of Stacks 0AN8 — and the clause itself is not proved here: producing
the system `(B_i)` from a representable étale morphism `X → Spf B`, and converting the
isomorphisms `A ⧸ J_i A ≅ B_i` back into the isomorphism `X ≅ Spf A^∧` of fppf sheaves, are the
geometric halves of the argument. The first of those is
`AlgebraicGeometry.FormalSpace.StageEtale.exists_etale_algebra_of_isRepresentableEtale` and the
second is `AlgebraicGeometry.FormalSpace.StageEtale.assemblyNatIso` fed to
`AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso`, which carries the stagewise
identification as a hypothesis; the quotient system of `A^∧` and the continuous map into it
come from `AlgebraicGeometry.FormalSpace.exists_completionOver_quotientSystem` (Stacks 0ANM).
The clause itself is `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 0AL1](https://stacks.math.columbia.edu/tag/0AL1)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.FormalSpace

open CategoryTheory Opposite

universe u v

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Type v} [Preorder I]

/-- All the weak ideals of definition of a topological ring, ordered by reverse inclusion, as a
fundamental system: the index `AlgebraicGeometry.FormalSpace.WeakIdeals` is the whole collection,
so each weak ideal of definition is cofinal below itself. This is the index in which the
canonical diagrams of a formal spectrum are written. -/
def weakIdealsBasis (R : Type u) [CommRing R] [TopologicalSpace R] :
    IdealBasis R (WeakIdeals R) where
  ideal J := (OrderDual.ofDual J).1
  weak J := (OrderDual.ofDual J).2
  antitone := fun {_i _j} h => h
  cofinal K hK := ⟨OrderDual.toDual ⟨K, hK⟩, le_rfl⟩

/-- The ideal of `weakIdealsBasis R` at an index `J` is the weak ideal of definition `J` itself. -/
@[simp]
theorem weakIdealsBasis_ideal (R : Type u) [CommRing R] [TopologicalSpace R]
    (J : WeakIdeals R) : (weakIdealsBasis R).ideal J = (OrderDual.ofDual J).1 := rfl

/-- **An étale algebra from an étale system of quotient stages**: the two steps of the proof of
the essential-surjectivity clause of Stacks 0AN8 which cite Stacks 04D1 and Stacks 0ALI.

Let `(B_i)` be an inverse system of algebras over the quotients of `R` by a fundamental system
of weak ideals of definition, as in Stacks 0AL1, whose structure maps `R ⧸ J_i → B_i` are all
étale, and fix an index `i₀`. Then there is an étale `R`-algebra `A` and, for every `i ≥ i₀`, an
isomorphism `A ⧸ J_i A ≅ B_i` over `R ⧸ J_i`, compatible with the transitions of both systems.

`A` is the lift of `B_{i₀}` along `R ↠ R ⧸ J_{i₀}` given by Stacks 04D1; each isomorphism is the
unique one lifting the identification of `B_i` modulo the image of `J_{i₀}` with `B_{i₀}`, and
that uniqueness is what makes the family compatible. -/
theorem exists_etale_algebra_of_etaleSystem (JB : IdealBasis R I)
    (P : FiniteTypeAlgebraSystem R I JB) (hP : ∀ i, (P.algebraMap i).Etale) (i₀ : I) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
      (θ : ∀ i : I, i₀ ≤ i →
        (A ⧸ (JB.ideal i).map (algebraMap R A)) ≃+* P.B.obj (op i)),
      (∀ (i : I) (hi : i₀ ≤ i),
        (θ i hi : (A ⧸ (JB.ideal i).map (algebraMap R A)) →+* P.B.obj (op i)).comp
          (Ideal.quotientMap ((JB.ideal i).map (algebraMap R A))
            (algebraMap R A) Ideal.le_comap_map) = P.algebraMap i) ∧
      ∀ (i j : I) (hi : i₀ ≤ i) (hij : i ≤ j),
        (P.B.map (homOfLE hij).op).hom.comp
            (θ j (hi.trans hij) :
              (A ⧸ (JB.ideal j).map (algebraMap R A)) →+* P.B.obj (op j)) =
          (θ i hi : (A ⧸ (JB.ideal i).map (algebraMap R A)) →+* P.B.obj (op i)).comp
            (Ideal.Quotient.factor (Ideal.map_mono (JB.antitone hij))) := by
  classical
  let : Algebra (R ⧸ JB.ideal i₀) (P.B.obj (op i₀)) := (P.algebraMap i₀).toAlgebra
  have : Algebra.Etale (R ⧸ JB.ideal i₀) (P.B.obj (op i₀)) := hP i₀
  let : Algebra R (P.B.obj (op i₀)) :=
    ((P.algebraMap i₀).comp (Ideal.Quotient.mk (JB.ideal i₀))).toAlgebra
  have : IsScalarTower R (R ⧸ JB.ideal i₀) (P.B.obj (op i₀)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show (P.algebraMap i₀) (Ideal.Quotient.mk (JB.ideal i₀) x) = _
      rw [Ideal.Quotient.algebraMap_eq]
      rfl
  obtain ⟨A, _, _, hAet, ψ, hψs, hψk⟩ :=
    etale_lift_along_surjection R (R ⧸ JB.ideal i₀) (P.B.obj (op i₀))
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
  have hAetm : (algebraMap R A).Etale := RingHom.etale_algebraMap.mpr hAet
  have hker : RingHom.ker (ψ : A →+* P.B.obj (op i₀)) =
      (JB.ideal i₀).map (algebraMap R A) := by
    rw [hψk, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  -- the identification of the stage of `A` at `i₀` with `B i₀`
  obtain ⟨ψbar, hψbar⟩ :
      ∃ e : (A ⧸ (JB.ideal i₀).map (algebraMap R A)) ≃+* P.B.obj (op i₀),
        ∀ a : A, e (Ideal.Quotient.mk ((JB.ideal i₀).map (algebraMap R A)) a) = ψ a := by
    refine ⟨(Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hψs), fun a => ?_⟩
    simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hψs a
  have hqAet : ∀ i : I, (Ideal.quotientMap ((JB.ideal i).map (algebraMap R A))
      (algebraMap R A) Ideal.le_comap_map).Etale := fun i =>
    RingHom.Etale.quotientMap (algebraMap R A) hAetm (JB.ideal i)
  have hN : ∀ i : I, ((JB.ideal i₀).map (Ideal.Quotient.mk (JB.ideal i))).IsLocallyNilpotent :=
    fun i x hx => mem_nilradical.mp
      (TopologicalRing.map_quotient_le_nilradical_of_isWeakIdealOfDefinition
        (JB.weak i₀) (JB.weak i).1 hx)
  -- the comparison surjection of the `i`-th stage of `A` onto `B i₀` and its kernel
  have hfactor_surj : ∀ {J K : Ideal A} (h : J ≤ K),
      Function.Surjective (Ideal.Quotient.factor h) := by
    intro J K h x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.factor_mk _ _⟩
  have hkerN : ∀ (i : I) (hi : i₀ ≤ i),
      ((JB.ideal i₀).map (Ideal.Quotient.mk (JB.ideal i))).map
          (Ideal.quotientMap ((JB.ideal i).map (algebraMap R A))
            (algebraMap R A) Ideal.le_comap_map) =
        Ideal.map (Ideal.Quotient.mk ((JB.ideal i).map (algebraMap R A)))
          ((JB.ideal i₀).map (algebraMap R A)) := by
    intro i _
    rw [Ideal.map_map, Ideal.quotientMap_comp_mk, ← Ideal.map_map]
  have hE : ∀ (i : I), i₀ ≤ i →
      (JB.ideal i).map (algebraMap R A) ≤ (JB.ideal i₀).map (algebraMap R A) := fun _ hi =>
    Ideal.map_mono (JB.antitone hi)
  have hker_trans : ∀ (i : I) (hi : i₀ ≤ i), RingHom.ker (P.B.map (homOfLE hi).op).hom =
        ((JB.ideal i₀).map (Ideal.Quotient.mk (JB.ideal i))).map (P.algebraMap i) := by
    intro i hi
    rw [P.transition_ker hi, Ideal.map_map]
  -- the stagewise isomorphisms
  have key : ∀ (i : I) (hi : i₀ ≤ i),
      ∃ g : (A ⧸ (JB.ideal i).map (algebraMap R A)) ≃+* P.B.obj (op i),
        (g : _ →+* _).comp (Ideal.quotientMap ((JB.ideal i).map (algebraMap R A))
            (algebraMap R A) Ideal.le_comap_map) = P.algebraMap i ∧
          (P.B.map (homOfLE hi).op).hom.comp (g : _ →+* _) =
            (ψbar : (A ⧸ (JB.ideal i₀).map (algebraMap R A)) →+* P.B.obj (op i₀)).comp
              (Ideal.Quotient.factor (Ideal.map_mono (JB.antitone hi))) := by
    intro i hi
    have hEle := hE i hi
    have hps : Function.Surjective
        ((ψbar : (A ⧸ (JB.ideal i₀).map (algebraMap R A)) →+* P.B.obj (op i₀)).comp
          (Ideal.Quotient.factor hEle)) :=
      ψbar.surjective.comp (hfactor_surj hEle)
    have hpk : RingHom.ker
        ((ψbar : (A ⧸ (JB.ideal i₀).map (algebraMap R A)) →+* P.B.obj (op i₀)).comp
          (Ideal.Quotient.factor hEle)) =
        ((JB.ideal i₀).map (Ideal.Quotient.mk (JB.ideal i))).map
          (Ideal.quotientMap ((JB.ideal i).map (algebraMap R A))
            (algebraMap R A) Ideal.le_comap_map) := by
      rw [hkerN i hi, ← Ideal.Quotient.factor_ker hEle]
      refine Ideal.ext fun x => ?_
      simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.coe_toRingHom]
      exact ⟨fun h => ψbar.injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
    have hpq : ((ψbar : (A ⧸ (JB.ideal i₀).map (algebraMap R A)) →+* P.B.obj (op i₀)).comp
          (Ideal.Quotient.factor hEle)).comp
          (Ideal.quotientMap ((JB.ideal i).map (algebraMap R A))
            (algebraMap R A) Ideal.le_comap_map) =
        (P.B.map (homOfLE hi).op).hom.comp (P.algebraMap i) := by
      refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
      have hl : ψbar (Ideal.Quotient.factor hEle
          (Ideal.quotientMap ((JB.ideal i).map (algebraMap R A))
            (algebraMap R A) Ideal.le_comap_map (Ideal.Quotient.mk (JB.ideal i) r))) =
          ψ (algebraMap R A r) := by
        rw [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, hψbar]
      have hr := DFunLike.congr_fun (P.compatible hi) (Ideal.Quotient.mk (JB.ideal i) r)
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom] at *
      rw [hl, hr, Ideal.Quotient.factor_mk]
      exact (ψ.commutes r).trans rfl
    obtain ⟨g, hg, -⟩ := RingHom.Etale.existsUnique_ringEquiv_of_isLocallyNilpotent
      (hqAet i) (hP i) (hN i) hps (P.transition_surjective hi) hpk (hker_trans i hi) hpq
    exact ⟨g, hg.1, hg.2⟩
  choose θ hθ1 hθ2 using key
  refine ⟨A, inferInstance, inferInstance, hAet, θ, hθ1, ?_⟩
  -- naturality, from the uniqueness of the lifts
  intro i j hi hij
  have hij₀ : i₀ ≤ j := hi.trans hij
  have hJij : JB.ideal j ≤ JB.ideal i := JB.antitone hij
  have hEij : (JB.ideal j).map (algebraMap R A) ≤ (JB.ideal i).map (algebraMap R A) :=
    Ideal.map_mono hJij
  have hEi := hE i hi
  have hEj := hE j hij₀
  -- the comparison of the stage maps of `A` with the quotient maps of `R`
  have hstage : (Ideal.Quotient.factor hEij).comp
        (Ideal.quotientMap ((JB.ideal j).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) =
      (Ideal.quotientMap ((JB.ideal i).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map).comp
        (Ideal.Quotient.factor hJij) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.quotientMap_mk]
  -- the transition of the system, split through the stage at `i`
  have htrans : (P.B.map (homOfLE hij₀).op).hom =
      (P.B.map (homOfLE hi).op).hom.comp (P.B.map (homOfLE hij).op).hom := by
    have : P.B.map (homOfLE hij₀).op =
        P.B.map (homOfLE hij).op ≫ P.B.map (homOfLE hi).op := by
      rw [← P.B.map_comp]
      exact congrArg P.B.map (Subsingleton.elim _ _)
    rw [this]
    rfl
  refine RingHom.Etale.ringHom_ext_of_isLocallyNilpotent (hqAet j)
    ((P.algebraMap i).comp (Ideal.Quotient.factor hJij))
    (Ideal.IsLocallyNilpotent0544.map (P.algebraMap i) _ (hN i)) ?_ ?_ ?_
  · rw [RingHom.comp_assoc, hθ1 j hij₀]
    exact P.compatible hij
  · rw [RingHom.comp_assoc, hstage, ← RingHom.comp_assoc, hθ1 i hi]
  · -- both sides agree after the transition to the stage at `i₀`
    have hker := hker_trans i hi
    have hl : (P.B.map (homOfLE hi).op).hom.comp
          ((P.B.map (homOfLE hij).op).hom.comp (θ j hij₀ : _ →+* _)) =
        (ψbar : (A ⧸ (JB.ideal i₀).map (algebraMap R A)) →+* P.B.obj (op i₀)).comp
          (Ideal.Quotient.factor hEj) := by
      rw [← RingHom.comp_assoc, ← htrans]
      exact hθ2 j hij₀
    have hr : (P.B.map (homOfLE hi).op).hom.comp
          ((θ i hi : _ →+* _).comp (Ideal.Quotient.factor hEij)) =
        (ψbar : (A ⧸ (JB.ideal i₀).map (algebraMap R A)) →+* P.B.obj (op i₀)).comp
          (Ideal.Quotient.factor hEj) := by
      rw [← RingHom.comp_assoc, hθ2 i hi, RingHom.comp_assoc,
        Ideal.Quotient.factor_comp hEij hEi]
    refine RingHom.ext fun x => ?_
    have hdiff := DFunLike.congr_fun (hl.trans hr.symm) x
    rw [← hker] at *
    simp only [RingHom.coe_comp, Function.comp_apply] at hdiff
    exact Ideal.Quotient.eq.mpr ((RingHom.sub_mem_ker_iff _).mpr hdiff)

end AlgebraicGeometry.FormalSpace

end
