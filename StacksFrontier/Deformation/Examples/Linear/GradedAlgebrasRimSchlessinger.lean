module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.Examples.Linear.CompatiblePairsPatching
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebrasPieces
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport

/-!
# Graded algebras satisfy the Rim–Schlessinger condition

Graded algebras finite projective in each degree satisfy condition (RS) over the category `𝒞_Λ`
of Artinian local `Λ`-algebras with residue field `k`. Given `f : X ⟶ Z` and `g : Y ⟶ Z` with
`g` surjective on base algebras, the patch is the ring of compatible pairs `X.carrier ×_{Z}
Y.carrier` over the fibre product of the base algebras, graded by the pairs homogeneous in both
coordinates. Each graded piece is finite projective over the fibre product by Milnor patching,
and the two projections exhibit the two given algebras as its extensions of scalars because they
do so in each degree.

Consequently the deformations of a fixed graded `k`-algebra form a deformation category.

## Main results

* `Deformation.Examples.ProjectiveGradedAlgebra.satisfiesRS_projection`: condition (RS) for the
  category of graded algebras finite projective in each degree.
* `Deformation.Examples.ProjectiveGradedAlgebra.isDeformationCategory_deformationCategory`: the
  deformations of a fixed graded `k`-algebra form a deformation category.

## Implementation notes

Every reference to the fibre product of the two base algebras goes through one
`RingFibreProduct.Situation` and the projections `ringFibreProductFst`, `ringFibreProductSnd`
named at its type. The fibre product also appears as the carrier of an object of `𝒞_Λ` and as
`RingHom.pullback`; the three descriptions agree, but only after unfolding, so forming the
patch's module structures from two of them at once is what makes the degreewise patching step
expensive.

The base-change field of the lifted morphism is proved as a separate lemma rather than inline in
the structure instance: supplied inline it is checked against the field type while the
semilinearity field is still a metavariable, and since the field type mentions that proof the
check unfolds both descriptions of the module structure on the patch.

The deformation-category statement is obtained from condition (RS) by
`isDeformationCategory_objectsOverFunctor_of_baseIso`, whose hypothesis is an isomorphism
between the image of the chosen object and the residue-field object of `𝒞_Λ`; here that is
`residueFieldBaseIso`, since the special fibre of a graded `k`-algebra is supported on `k`
itself rather than on a lift of `k`.

## References

* [Stacks Project, Tag 0DVY](https://stacks.math.columbia.edu/tag/0DVY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace Deformation.Examples.ProjectiveGradedAlgebra

universe u v w m

section PullbackGrading

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {X Y Z : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
  (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The object of `𝒞_Λ` underlying the fibre product of the two base algebras. -/
private noncomputable abbrev pullbackBase (hg : Function.Surjective g.base.hom) :
    ArtinianLocalAlgCat.{u, v, w} Λ k :=
  ArtinianLocalAlgCat.pullbackObj_of_surjective f.base g.base (Or.inr hg)

/-- The fibre-product situation formed by the two base algebras. -/
private theorem pullbackSituation (hg : Function.Surjective g.base.hom) :
    RingFibreProduct.Situation f.base.hom.toRingHom g.base.hom.toRingHom
      (RingHom.ker g.base.hom.toRingHom) :=
  ⟨hg, rfl⟩

/-- The scalar action of the fibre product of the base algebras on the ring of compatible
pairs of carriers. -/
private def pullbackScalarMap :
    RingHom.pullback f.base.hom.toRingHom g.base.hom.toRingHom →+*
      RingHom.pullback f.map g.map :=
  (RingHom.prodMap (algebraMap (↑X.base) X.carrier)
    (algebraMap (↑Y.base) Y.carrier)).restrict
    (RingHom.pullback f.base.hom.toRingHom g.base.hom.toRingHom)
    (RingHom.pullback f.map g.map)
    (fun a ha => by
      change f.map (algebraMap (↑X.base) X.carrier a.1) =
        g.map (algebraMap (↑Y.base) Y.carrier a.2)
      have hf := f.map_smul a.1 (1 : X.carrier)
      have hg := g.map_smul a.2 (1 : Y.carrier)
      simp only [Algebra.smul_def, mul_one, map_one] at hf hg
      rw [hf, hg]
      exact congrArg (algebraMap (↑Z.base) Z.carrier) ha)

/-- The algebra structure on the ring of compatible pairs of carriers. -/
private abbrev pullbackAlgebra := (pullbackScalarMap f g).toAlgebra

/-- The grading of the ring of compatible pairs: the pairs homogeneous of one degree in both
coordinates. -/
private def pullbackGrading :
    letI := pullbackAlgebra f g
    ℕ → Submodule (RingHom.pullback f.base.hom.toRingHom g.base.hom.toRingHom)
      (RingHom.pullback f.map g.map) := by
  letI := pullbackAlgebra f g
  exact fun d => {
    carrier := {p | p.1.1 ∈ X.grading d ∧ p.1.2 ∈ Y.grading d}
    zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    add_mem' := fun ha hb => ⟨Submodule.add_mem _ ha.1 hb.1,
      Submodule.add_mem _ ha.2 hb.2⟩
    smul_mem' := fun a p hp => by
      change (algebraMap (↑X.base) X.carrier a.1.1 * p.1.1 ∈ X.grading d) ∧
        (algebraMap (↑Y.base) Y.carrier a.1.2 * p.1.2 ∈ Y.grading d)
      exact ⟨by simpa only [Algebra.smul_def] using (X.grading d).smul_mem a.1.1 hp.1,
        by simpa only [Algebra.smul_def] using (Y.grading d).smul_mem a.1.2 hp.2⟩ }

/-- The degree-`d` component of a compatible pair. -/
private def pullbackDegree (d : ℕ) (p : RingHom.pullback f.map g.map) :
    letI := pullbackAlgebra f g
    pullbackGrading f g d := by
  letI := pullbackAlgebra f g
  refine ⟨⟨(GradedAlgebra.proj X.grading d p.1.1,
    GradedAlgebra.proj Y.grading d p.1.2), ?_⟩, ?_⟩
  · change f.map (GradedAlgebra.proj X.grading d p.1.1) =
      g.map (GradedAlgebra.proj Y.grading d p.1.2)
    rw [← gradedHom_proj_apply, ← gradedHom_proj_apply]
    exact congrArg (GradedAlgebra.proj Z.grading d) p.2
  · exact ⟨(DirectSum.decompose X.grading p.1.1 d).property,
      (DirectSum.decompose Y.grading p.1.2 d).property⟩

/-- The decomposition of a compatible pair into its homogeneous components. -/
private noncomputable def pullbackDecompose :
    letI := pullbackAlgebra f g
    RingHom.pullback f.map g.map → DirectSum ℕ (fun d => pullbackGrading f g d) := by
  letI := pullbackAlgebra f g
  classical
  intro p
  let s := (DirectSum.decompose X.grading p.1.1).support ∪
    (DirectSum.decompose Y.grading p.1.2).support
  refine ⟨fun d => pullbackDegree f g d p, Trunc.mk ⟨s.val, fun d => ?_⟩⟩
  by_cases hd : d ∈ s
  · exact Or.inl hd
  · right
    have hx : (DirectSum.decompose X.grading p.1.1) d = 0 :=
      DFinsupp.notMem_support_iff.mp (fun h => hd (Finset.mem_union_left _ h))
    have hy : (DirectSum.decompose Y.grading p.1.2) d = 0 :=
      DFinsupp.notMem_support_iff.mp (fun h => hd (Finset.mem_union_right _ h))
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hx) (congrArg Subtype.val hy)

/-- Taking the degree-`d` component of a sum of homogeneous pairs recovers its `d`-th term. -/
private theorem pullbackDegree_recompose :
    letI := pullbackAlgebra f g
    ∀ (q : DirectSum ℕ (fun d => pullbackGrading f g d)) (d : ℕ),
      pullbackDegree f g d (DirectSum.coeAddMonoidHom (pullbackGrading f g) q) = q d := by
  let := pullbackAlgebra f g
  intro q d
  induction q using DirectSum.induction_on with
  | zero =>
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (map_zero (GradedAlgebra.proj X.grading d))
        (map_zero (GradedAlgebra.proj Y.grading d))
  | add a b ha hb =>
      have hadd (p r : RingHom.pullback f.map g.map) :
          pullbackDegree f g d (p + r) =
            pullbackDegree f g d p + pullbackDegree f g d r := by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (map_add (GradedAlgebra.proj X.grading d) _ _)
          (map_add (GradedAlgebra.proj Y.grading d) _ _)
      rw [map_add, hadd, ha, hb]
      rfl
  | of i a =>
      rw [DirectSum.coeAddMonoidHom_of]
      by_cases h : i = d
      · subst d
        rw [DirectSum.of_eq_same]
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (DirectSum.decompose_of_mem_same X.grading a.2.1)
          (DirectSum.decompose_of_mem_same Y.grading a.2.2)
      · rw [DirectSum.of_eq_of_ne (β := fun j => ↥(pullbackGrading f g j)) i d a (Ne.symm h)]
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (DirectSum.decompose_of_mem_ne X.grading a.2.1 h)
          (DirectSum.decompose_of_mem_ne Y.grading a.2.2 h)

/-- The ring of compatible pairs is a graded algebra for the pairwise grading. -/
@[instance_reducible]
private noncomputable def pullbackGradedAlgebra :
    letI := pullbackAlgebra f g
    GradedAlgebra (pullbackGrading f g) := by
  letI := pullbackAlgebra f g
  refine {
    one_mem := ⟨SetLike.one_mem_graded X.grading, SetLike.one_mem_graded Y.grading⟩
    mul_mem := fun i j a b ha hb => ⟨SetLike.mul_mem_graded ha.1 hb.1,
      SetLike.mul_mem_graded ha.2 hb.2⟩
    decompose' := pullbackDecompose f g
    left_inv := ?_
    right_inv := ?_ }
  · intro p
    have h (d : ℕ) := pullbackDegree_recompose f g (pullbackDecompose f g p) d
    apply Subtype.ext
    apply Prod.ext
    · apply (DirectSum.decomposeAlgEquiv X.grading).injective
      ext d
      exact congrArg (fun a : pullbackGrading f g d => a.1.1.1) (h d)
    · apply (DirectSum.decomposeAlgEquiv Y.grading).injective
      ext d
      exact congrArg (fun a : pullbackGrading f g d => a.1.1.2) (h d)
  · exact fun q => DFinsupp.ext (pullbackDegree_recompose f g q)

/-- The compatible pair of graded pieces attached to a degree, as an object of the categorical
pullback of the two extension-of-scalars functors. -/
private noncomputable abbrev pullbackPiecePair (d : ℕ)
    [Small.{v} (X.grading d)] [Small.{v} (Y.grading d)] :
    CategoricalPullback
      (ModuleCat.extendScalars.{v, v, v} f.base.hom.toRingHom)
      (ModuleCat.extendScalars.{v, v, v} g.base.hom.toRingHom) := by
  letI : Algebra (↑X.base) (↑Z.base) := f.base.hom.toAlgebra
  letI : Algebra (↑Y.base) (↑Z.base) := g.base.hom.toAlgebra
  letI : Algebra (↑X.base) Z.carrier :=
    ((algebraMap (↑Z.base) Z.carrier).comp f.base.hom.toRingHom).toAlgebra
  letI : Algebra (↑Y.base) Z.carrier :=
    ((algebraMap (↑Z.base) Z.carrier).comp g.base.hom.toRingHom).toAlgebra
  letI : IsScalarTower (↑X.base) (↑Z.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower (↑Y.base) (↑Z.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact {
    fst := ModuleCat.of (↑X.base) (Shrink.{v} (X.grading d))
    snd := ModuleCat.of (↑Y.base) (Shrink.{v} (Y.grading d))
    iso := (((LinearEquiv.baseChange (↑X.base) (↑Z.base) (Shrink.{v} (X.grading d))
          (X.grading d) (Shrink.linearEquiv.{v} (↑X.base) (X.grading d))).trans
          ((homPiece_isBaseChange f d).equiv.trans
            (Submodule.restrictScalarsEquiv (↑X.base) (↑Z.base) Z.carrier (Z.grading d)))).trans
      (((LinearEquiv.baseChange (↑Y.base) (↑Z.base) (Shrink.{v} (Y.grading d))
          (Y.grading d) (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d))).trans
          ((homPiece_isBaseChange g d).equiv.trans
            (Submodule.restrictScalarsEquiv (↑Y.base) (↑Z.base) Z.carrier
              (Z.grading d)))).symm)).toModuleIso }

/-- Membership of the compatible submodule, read off through the two shrinking
equivalences. -/
private theorem pullbackPiecePair_iso_apply_iff (d : ℕ)
    [Small.{v} (X.grading d)] [Small.{v} (Y.grading d)]
    (x : Shrink.{v} (X.grading d)) (y : Shrink.{v} (Y.grading d)) :
    letI : Algebra (↑X.base) (↑Z.base) := f.base.hom.toAlgebra
    letI : Algebra (↑Y.base) (↑Z.base) := g.base.hom.toAlgebra
    (pullbackPiecePair f g d).iso.hom ((1 : Z.base) ⊗ₜ[↑X.base] x) =
        (1 : Z.base) ⊗ₜ[↑Y.base] y ↔
      f.map (Shrink.linearEquiv.{v} (↑X.base) (X.grading d) x).1 =
        g.map (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d) y).1 := by
  let : Algebra (↑X.base) (↑Z.base) := f.base.hom.toAlgebra
  let : Algebra (↑Y.base) (↑Z.base) := g.base.hom.toAlgebra
  let : Algebra (↑X.base) Z.carrier :=
    ((algebraMap (↑Z.base) Z.carrier).comp f.base.hom.toRingHom).toAlgebra
  let : Algebra (↑Y.base) Z.carrier :=
    ((algebraMap (↑Z.base) Z.carrier).comp g.base.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Z.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (↑Y.base) (↑Z.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eF := (LinearEquiv.baseChange (↑X.base) (↑Z.base) (Shrink.{v} (X.grading d))
      (X.grading d) (Shrink.linearEquiv.{v} (↑X.base) (X.grading d))).trans
      ((homPiece_isBaseChange f d).equiv.trans
        (Submodule.restrictScalarsEquiv (↑X.base) (↑Z.base) Z.carrier (Z.grading d)))
  let eG := (LinearEquiv.baseChange (↑Y.base) (↑Z.base) (Shrink.{v} (Y.grading d))
      (Y.grading d) (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d))).trans
      ((homPiece_isBaseChange g d).equiv.trans
        (Submodule.restrictScalarsEquiv (↑Y.base) (↑Z.base) Z.carrier (Z.grading d)))
  change eG.symm (eF (1 ⊗ₜ[↑X.base] x)) = 1 ⊗ₜ[↑Y.base] y ↔ _
  rw [LinearEquiv.symm_apply_eq]
  change eF (1 ⊗ₜ[↑X.base] x) = eG (1 ⊗ₜ[↑Y.base] y) ↔ _
  simp only [eF, eG, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    IsBaseChange.equiv_tmul, one_smul]
  exact Subtype.ext_iff

/-- The two components of the compatible pair are finite projective. -/
private theorem pullbackPiecePair_finiteProjective (d : ℕ)
    [Small.{v} (X.grading d)] [Small.{v} (Y.grading d)] :
    (Module.Finite (↑X.base) (pullbackPiecePair f g d).fst ∧
        Module.Projective (↑X.base) (pullbackPiecePair f g d).fst) ∧
      (Module.Finite (↑Y.base) (pullbackPiecePair f g d).snd ∧
        Module.Projective (↑Y.base) (pullbackPiecePair f g d).snd) :=
  ⟨⟨Module.Finite.equiv (Shrink.linearEquiv.{v} (↑X.base) (X.grading d)).symm,
      Module.Projective.of_equiv (Shrink.linearEquiv.{v} (↑X.base) (X.grading d)).symm⟩,
    ⟨Module.Finite.equiv (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)).symm,
      Module.Projective.of_equiv (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)).symm⟩⟩

/-- The pairwise grading of degree `d` is the module of compatible pairs of the two graded
pieces. -/
private noncomputable def pullbackGradingEquiv (hg : Function.Surjective g.base.hom) (d : ℕ)
    [Small.{v} (X.grading d)] [Small.{v} (Y.grading d)] :
    letI := pullbackAlgebra f g
    pullbackGrading f g d ≃ₗ[(pullbackSituation f g hg).fibreProduct]
      MilnorPatching.compatiblePairsModule (ringFibreProductFst (pullbackSituation f g hg))
        (ringFibreProductSnd (pullbackSituation f g hg)) f.base.hom.toRingHom
        g.base.hom.toRingHom (ringFibreProduct_comm (pullbackSituation f g hg))
        (pullbackPiecePair f g d) := by
  letI := pullbackAlgebra f g
  letI : Algebra (↑X.base) (↑Z.base) := f.base.hom.toAlgebra
  letI : Algebra (↑Y.base) (↑Z.base) := g.base.hom.toAlgebra
  let hc := pullbackPiecePair_iso_apply_iff f g d
  exact {
    toFun := fun p =>
      ⟨((Shrink.linearEquiv.{v} (↑X.base) (X.grading d)).symm ⟨p.1.1.1, p.2.1⟩,
        (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)).symm ⟨p.1.1.2, p.2.2⟩),
        (hc _ _).mpr (by
          simp only [LinearEquiv.apply_symm_apply]
          exact p.1.2)⟩
    invFun := fun q =>
      ⟨⟨(((Shrink.linearEquiv.{v} (↑X.base) (X.grading d)) q.1.1).1,
          ((Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)) q.1.2).1), (hc _ _).mp q.2⟩,
        ((Shrink.linearEquiv.{v} (↑X.base) (X.grading d)) q.1.1).2,
        ((Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)) q.1.2).2⟩
    left_inv := fun p => by
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val
          ((Shrink.linearEquiv.{v} (↑X.base) (X.grading d)).apply_symm_apply _)
      · exact congrArg Subtype.val
          ((Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)).apply_symm_apply _)
    right_inv := fun q => by
      apply Subtype.ext
      apply Prod.ext
      · exact (Shrink.linearEquiv.{v} (↑X.base) (X.grading d)).symm_apply_apply _
      · exact (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)).symm_apply_apply _
    map_add' := fun p q => by
      apply Subtype.ext
      apply Prod.ext
      · exact (Shrink.linearEquiv.{v} (↑X.base) (X.grading d)).symm.map_add
          ⟨p.1.1.1, p.2.1⟩ ⟨q.1.1.1, q.2.1⟩
      · exact (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)).symm.map_add
          ⟨p.1.1.2, p.2.2⟩ ⟨q.1.1.2, q.2.2⟩
    map_smul' := fun a p => by
      apply Subtype.ext
      apply Prod.ext
      · convert (Shrink.linearEquiv.{v} (↑X.base) (X.grading d)).symm.map_smul a.1.1
          (⟨p.1.1.1, p.2.1⟩ : X.grading d) using 1 <;> try rfl
        apply congrArg (Shrink.linearEquiv.{v} (↑X.base) (X.grading d)).symm
        apply Subtype.ext
        change algebraMap (↑X.base) X.carrier a.1.1 * p.1.1.1 = a.1.1 • p.1.1.1
        rw [Algebra.smul_def]
      · convert (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)).symm.map_smul a.1.2
          (⟨p.1.1.2, p.2.2⟩ : Y.grading d) using 1 <;> try rfl
        apply congrArg (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d)).symm
        apply Subtype.ext
        change algebraMap (↑Y.base) Y.carrier a.1.2 * p.1.1.2 = a.1.2 • p.1.1.2
        rw [Algebra.smul_def] }

/-- Milnor patching for the pairwise grading: each degree is finite projective over the fibre
product of the base algebras. -/
private theorem pullbackGrading_finiteProjective (hg : Function.Surjective g.base.hom) (d : ℕ) :
    letI := pullbackAlgebra f g
    let s := pullbackSituation f g hg
    Module.Finite s.fibreProduct (pullbackGrading f g d) ∧
      Module.Projective s.fibreProduct (pullbackGrading f g d) := by
  let := pullbackAlgebra f g
  let : Small.{v} (X.grading d) := Module.Finite.small (↑X.base) (X.grading d)
  let : Small.{v} (Y.grading d) := Module.Finite.small (↑Y.base) (Y.grading d)
  let s := pullbackSituation f g hg
  let E := pullbackGradingEquiv f g hg d
  obtain ⟨hfin, hproj⟩ := compatiblePairsModule_finiteProjective
    f.base.hom.toRingHom g.base.hom.toRingHom _ s (pullbackPiecePair f g d)
    (pullbackPiecePair_finiteProjective f g d)
  exact ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm⟩

/-- Milnor patching for the pairwise grading: its extension of scalars to the first base
algebra is the corresponding graded piece of the first algebra. -/
private theorem pullbackGrading_baseChangeEquivFst (hg : Function.Surjective g.base.hom)
    (d : ℕ) :
    letI := pullbackAlgebra f g
    let s := pullbackSituation f g hg
    letI : Algebra s.fibreProduct (↑X.base) := (ringFibreProductFst s).toAlgebra
    ∃ e : TensorProduct s.fibreProduct (↑X.base) (pullbackGrading f g d) ≃ₗ[↑X.base]
        X.grading d,
      ∀ p : pullbackGrading f g d, e (1 ⊗ₜ[s.fibreProduct] p) = ⟨p.1.1.1, p.2.1⟩ := by
  let := pullbackAlgebra f g
  let : Small.{v} (X.grading d) := Module.Finite.small (↑X.base) (X.grading d)
  let : Small.{v} (Y.grading d) := Module.Finite.small (↑Y.base) (Y.grading d)
  let s := pullbackSituation f g hg
  let : Algebra s.fibreProduct (↑X.base) := (ringFibreProductFst s).toAlgebra
  let E := pullbackGradingEquiv f g hg d
  obtain ⟨e₁, _, he⟩ := exists_compatiblePairsModule_baseChangeEquiv
    f.base.hom.toRingHom g.base.hom.toRingHom _ s (pullbackPiecePair f g d)
  refine ⟨(LinearEquiv.baseChange s.fibreProduct (↑X.base) (pullbackGrading f g d) _ E).trans
      (e₁.trans (Shrink.linearEquiv.{v} (↑X.base) (X.grading d))), fun p => ?_⟩
  simp only [LinearEquiv.trans_apply]
  rw [LinearEquiv.baseChange_tmul s.fibreProduct (↑X.base) (pullbackGrading f g d),
    (he (E p)).1]
  exact LinearEquiv.apply_symm_apply _ _

/-- Milnor patching for the pairwise grading: its extension of scalars to the second base
algebra is the corresponding graded piece of the second algebra. -/
private theorem pullbackGrading_baseChangeEquivSnd (hg : Function.Surjective g.base.hom)
    (d : ℕ) :
    letI := pullbackAlgebra f g
    let s := pullbackSituation f g hg
    letI : Algebra s.fibreProduct (↑Y.base) := (ringFibreProductSnd s).toAlgebra
    ∃ e : TensorProduct s.fibreProduct (↑Y.base) (pullbackGrading f g d) ≃ₗ[↑Y.base]
        Y.grading d,
      ∀ p : pullbackGrading f g d, e (1 ⊗ₜ[s.fibreProduct] p) = ⟨p.1.1.2, p.2.2⟩ := by
  let := pullbackAlgebra f g
  let : Small.{v} (X.grading d) := Module.Finite.small (↑X.base) (X.grading d)
  let : Small.{v} (Y.grading d) := Module.Finite.small (↑Y.base) (Y.grading d)
  let s := pullbackSituation f g hg
  let : Algebra s.fibreProduct (↑Y.base) := (ringFibreProductSnd s).toAlgebra
  let E := pullbackGradingEquiv f g hg d
  obtain ⟨_, e₂, he⟩ := exists_compatiblePairsModule_baseChangeEquiv
    f.base.hom.toRingHom g.base.hom.toRingHom _ s (pullbackPiecePair f g d)
  refine ⟨(LinearEquiv.baseChange s.fibreProduct (↑Y.base) (pullbackGrading f g d) _ E).trans
      (e₂.trans (Shrink.linearEquiv.{v} (↑Y.base) (Y.grading d))), fun p => ?_⟩
  simp only [LinearEquiv.trans_apply]
  rw [LinearEquiv.baseChange_tmul s.fibreProduct (↑Y.base) (pullbackGrading f g d),
    (he (E p)).2]
  exact LinearEquiv.apply_symm_apply _ _

/-- The patch: the ring of compatible pairs of the two carriers, with the pairwise grading. -/
private noncomputable def gradedPullback (hg : Function.Surjective g.base.hom) :
    ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k := {
  base := pullbackBase f g hg
  carrier := RingHom.pullback f.map g.map
  algebra := pullbackAlgebra f g
  grading := pullbackGrading f g
  graded := pullbackGradedAlgebra f g
  finite := fun d => (pullbackGrading_finiteProjective f g hg d).1
  projective := fun d => (pullbackGrading_finiteProjective f g hg d).2 }

/-- A morphism of `𝒞_Λ` with a prescribed underlying algebra map, equal to a given morphism. -/
private def homOfHomEq {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (b : A ⟶ B)
    (φ : A →ₐ[Λ] B) (hb : b.hom = φ) : A ⟶ B where
  hom := φ
  isLocal := by
    rw [← hb]
    exact b.isLocal
  residue_comm := by
    intro a
    have h := b.residue_comm a
    rw [hb] at h
    convert h using 1

/-- The first projection of the patch, on base algebras. -/
private noncomputable def gradedPullbackFstBase (hg : Function.Surjective g.base.hom) :
    (gradedPullback f g hg).base ⟶ X.base :=
  homOfHomEq (ArtinianLocalAlgCat.pullbackFst_of_surjective f.base g.base (Or.inr hg))
    (AlgHom.pullbackFst f.base.hom g.base.hom)
    (ArtinianLocalAlgCat.pullbackFst_of_surjective_hom _ _ _)

/-- The first projection of the patch. -/
private noncomputable def gradedPullbackFst (hg : Function.Surjective g.base.hom) :
    gradedPullback f g hg ⟶ X := by
  let Q := gradedPullback f g hg
  have hs (r : Q.base) (p : Q.carrier) :
      (RingHom.pullbackFst f.map g.map) (r • p) =
        (gradedPullbackFstBase f g hg).hom r • (RingHom.pullbackFst f.map g.map) p := by
    change algebraMap (↑X.base) X.carrier r.1.1 * p.1.1 = r.1.1 • p.1.1
    rw [Algebra.smul_def]
  refine {
    base := gradedPullbackFstBase f g hg
    map := RingHom.pullbackFst f.map g.map
    map_smul := hs
    map_mem := fun d p hp => hp.1
    isBaseChange := ?_ }
  let : Algebra (↑Q.base) (↑X.base) :=
    (gradedPullbackFstBase f g hg).hom.toAlgebra
  let : Module (↑Q.base) X.carrier :=
    Module.compHom X.carrier (gradedPullbackFstBase f g hg).hom.toRingHom
  let : IsScalarTower (↑Q.base) (↑X.base) X.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let l : Q.carrier →ₗ[↑Q.base] X.carrier := {
    (RingHom.pullbackFst f.map g.map).toAddMonoidHom with map_smul' := hs }
  let ε (d : ℕ) : Q.grading d →ₗ[↑Q.base] (X.grading d).restrictScalars Q.base := {
    toFun := fun p => ⟨p.1.1.1, p.2.1⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun r p => by
      apply Subtype.ext
      convert hs r p.1 using 1 <;> rfl }
  apply isBaseChange_of_graded Q.grading X.grading l ε (fun _ _ => rfl)
  intro d
  obtain ⟨e₁, he⟩ := pullbackGrading_baseChangeEquivFst f g hg d
  exact IsBaseChange.of_equiv e₁ he

/-- The second projection of the patch, on base algebras. -/
private noncomputable def gradedPullbackSndBase (hg : Function.Surjective g.base.hom) :
    (gradedPullback f g hg).base ⟶ Y.base :=
  homOfHomEq (ArtinianLocalAlgCat.pullbackSnd_of_surjective f.base g.base (Or.inr hg))
    (AlgHom.pullbackSnd f.base.hom g.base.hom)
    (ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom _ _ _)

/-- The second projection of the patch. -/
private noncomputable def gradedPullbackSnd (hg : Function.Surjective g.base.hom) :
    gradedPullback f g hg ⟶ Y := by
  let Q := gradedPullback f g hg
  have hs (r : Q.base) (p : Q.carrier) :
      (RingHom.pullbackSnd f.map g.map) (r • p) =
        (gradedPullbackSndBase f g hg).hom r • (RingHom.pullbackSnd f.map g.map) p := by
    change algebraMap (↑Y.base) Y.carrier r.1.2 * p.1.2 = r.1.2 • p.1.2
    rw [Algebra.smul_def]
  refine {
    base := gradedPullbackSndBase f g hg
    map := RingHom.pullbackSnd f.map g.map
    map_smul := hs
    map_mem := fun d p hp => hp.2
    isBaseChange := ?_ }
  let : Algebra (↑Q.base) (↑Y.base) :=
    (gradedPullbackSndBase f g hg).hom.toAlgebra
  let : Module (↑Q.base) Y.carrier :=
    Module.compHom Y.carrier (gradedPullbackSndBase f g hg).hom.toRingHom
  let : IsScalarTower (↑Q.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let l : Q.carrier →ₗ[↑Q.base] Y.carrier := {
    (RingHom.pullbackSnd f.map g.map).toAddMonoidHom with map_smul' := hs }
  let ε (d : ℕ) : Q.grading d →ₗ[↑Q.base] (Y.grading d).restrictScalars Q.base := {
    toFun := fun p => ⟨p.1.1.2, p.2.2⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun r p => by
      apply Subtype.ext
      convert hs r p.1 using 1 <;> rfl }
  apply isBaseChange_of_graded Q.grading Y.grading l ε (fun _ _ => rfl)
  intro d
  obtain ⟨e₂, he⟩ := pullbackGrading_baseChangeEquivSnd f g hg d
  exact IsBaseChange.of_equiv e₂ he

/-- The patch, as a cone over the given cospan. -/
private noncomputable def gradedPullbackCone (hg : Function.Surjective g.base.hom) :
    PullbackCone f g :=
  PullbackCone.mk (gradedPullbackFst f g hg) (gradedPullbackSnd f g hg) (by
    apply ProjectiveGradedAlgebra.Hom.ext
    · apply ArtinianLocalAlgCat.hom_ext
      ext r
      exact r.2
    · ext p
      exact p.2)

/-- The carrier of a graded algebra, finite projective in each degree, is flat over its base
algebra. -/
private theorem gradedCarrier_flat (W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k) :
    Module.Flat (↑W.base) W.carrier := by
  let : ∀ d, Module.Flat (↑W.base) (W.grading d) := fun _ => Module.Flat.of_projective
  exact Module.Flat.of_linearEquiv (DirectSum.decomposeAlgEquiv W.grading).toLinearEquiv

/-- The lift of a competing cone, on base algebras. -/
private noncomputable def gradedPullbackLiftBase (hg : Function.Surjective g.base.hom)
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    W.base ⟶ (gradedPullback f g hg).base := by
  have hbase : a.base ≫ f.base = b.base ≫ g.base :=
    congrArg ProjectiveGradedAlgebra.Hom.base h
  let p := (ArtinianLocalAlgCat.isPullback_of_surjective f.base g.base
    (Or.inr hg)).lift a.base b.base hbase
  let q : W.base →ₐ[Λ] (gradedPullback f g hg).base :=
    AlgHom.codRestrict (a.base.hom.prod b.base.hom)
      (AlgHom.pullback f.base.hom g.base.hom) (fun x =>
        congrArg (fun t : W.base ⟶ Z.base => t.hom x) hbase)
  have hp : p.hom = q := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · have hh := congrArg (fun t : W.base ⟶ X.base => t.hom x)
        ((ArtinianLocalAlgCat.isPullback_of_surjective f.base g.base
          (Or.inr hg)).lift_fst a.base b.base hbase)
      simp only [ArtinianLocalAlgCat.comp_hom,
        ArtinianLocalAlgCat.pullbackFst_of_surjective_hom] at hh
      convert hh using 1 <;> rfl
    · have hh := congrArg (fun t : W.base ⟶ Y.base => t.hom x)
        ((ArtinianLocalAlgCat.isPullback_of_surjective f.base g.base
          (Or.inr hg)).lift_snd a.base b.base hbase)
      simp only [ArtinianLocalAlgCat.comp_hom,
        ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom] at hh
      convert hh using 1 <;> rfl
  exact {
    hom := q
    isLocal := by
      rw [← hp]
      exact p.isLocal
    residue_comm := by
      intro x
      rw [← hp]
      exact p.residue_comm x }

/-- The lift of a competing cone, on carriers. -/
private def gradedPullbackLiftMap
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    W.carrier →+* RingHom.pullback f.map g.map :=
  RingHom.codRestrict (a.map.prod b.map) (RingHom.pullback f.map g.map)
    (fun x => congrArg (fun t : W ⟶ Z => t.map x) h)

/-- The lift respects the gradings. -/
private theorem gradedPullbackLiftMap_mem
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g)
    (d : ℕ) (x : W.carrier) (hx : x ∈ W.grading d) :
    gradedPullbackLiftMap f g a b h x ∈ pullbackGrading f g d :=
  ⟨a.map_mem d x hx, b.map_mem d x hx⟩

/-- The lift is semilinear over its base morphism. -/
private theorem gradedPullbackLiftMap_smul
    (hg : Function.Surjective g.base.hom)
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g)
    (r : W.base) (x : W.carrier) :
    gradedPullbackLiftMap f g a b h (r • x) =
      (pullbackScalarMap f g) ((gradedPullbackLiftBase f g hg a b h).hom r) *
        gradedPullbackLiftMap f g a b h x := by
  apply Subtype.ext
  apply Prod.ext
  · change a.map (r • x) =
        algebraMap (↑X.base) X.carrier (a.base.hom r) * a.map x
    simpa [Algebra.smul_def] using a.map_smul r x
  · change b.map (r • x) =
        algebraMap (↑Y.base) Y.carrier (b.base.hom r) * b.map x
    simpa [Algebra.smul_def] using b.map_smul r x

/-- The lift exhibits the patch as an extension of scalars of the competing cone's apex: the
patch is cut out of the product of the two carriers by a kernel–image sequence of base
algebras, and the apex is flat, so the sequence stays exact after tensoring. -/
private theorem gradedPullbackLift_isBaseChange
    (hg : Function.Surjective g.base.hom)
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    letI : Algebra (↑W.base) (↑(gradedPullback f g hg).base) :=
      (gradedPullbackLiftBase f g hg a b h).hom.toAlgebra
    letI : Module (↑W.base) (gradedPullback f g hg).carrier :=
      Module.compHom (gradedPullback f g hg).carrier
        (gradedPullbackLiftBase f g hg a b h).hom.toRingHom
    letI : IsScalarTower (↑W.base) (↑(gradedPullback f g hg).base)
        (gradedPullback f g hg).carrier :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    IsBaseChange (↑(gradedPullback f g hg).base)
      ({ (gradedPullbackLiftMap f g a b h).toAddMonoidHom with
          map_smul' := fun r x => by
            change gradedPullbackLiftMap f g a b h (r • x) =
              (pullbackScalarMap f g) ((gradedPullbackLiftBase f g hg a b h).hom r) *
                gradedPullbackLiftMap f g a b h x
            exact gradedPullbackLiftMap_smul f g hg a b h r x } :
        W.carrier →ₗ[↑W.base] (gradedPullback f g hg).carrier) := by
  let Q := gradedPullback f g hg
  let R := W.base
  let S := Q.base
  let φ := (gradedPullbackLiftBase f g hg a b h).hom
  let : Algebra R S := φ.toAlgebra
  let : Module R Q.carrier := Module.compHom Q.carrier φ.toRingHom
  let : IsScalarTower R S Q.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let l : W.carrier →ₗ[R] Q.carrier := {
    (gradedPullbackLiftMap f g a b h).toAddMonoidHom with
    map_smul' := gradedPullbackLiftMap_smul f g hg a b h }
  change IsBaseChange S l
  let B := X.base
  let C := Y.base
  let A := Z.base
  let : Module R B := Module.compHom B a.base.hom.toRingHom
  let : Module R C := Module.compHom C b.base.hom.toRingHom
  let : Module R A :=
    Module.compHom A (f.base.hom.comp a.base.hom).toRingHom
  have hbase (r : R) : f.base.hom (a.base.hom r) = g.base.hom (b.base.hom r) :=
    congrArg (fun t : W.base ⟶ Z.base => t.hom r)
      (congrArg ProjectiveGradedAlgebra.Hom.base h)
  let j : S →ₗ[R] B × C := {
    toFun := fun x => x.1
    map_add' := fun _ _ => rfl
    map_smul' := fun r x => by
      apply Prod.ext <;> rfl }
  let d : B × C →ₗ[R] A := {
    toFun := fun x => f.base.hom x.1 - g.base.hom x.2
    map_add' := fun x y => by
      change f.base.hom (x.1 + y.1) - g.base.hom (x.2 + y.2) =
        (f.base.hom x.1 - g.base.hom x.2) + (f.base.hom y.1 - g.base.hom y.2)
      simp only [map_add]
      abel
    map_smul' := fun r x => by
      change f.base.hom (a.base.hom r * x.1) - g.base.hom (b.base.hom r * x.2) =
        f.base.hom (a.base.hom r) * (f.base.hom x.1 - g.base.hom x.2)
      rw [map_mul, map_mul, ← hbase r]
      ring }
  have hj : Function.Injective j := fun _ _ hxy => Subtype.ext hxy
  have hex : Function.Exact j d := by
    intro x
    constructor
    · exact fun hx => ⟨⟨x, sub_eq_zero.mp hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact sub_eq_zero.mpr y.2
  let : Module.Flat R W.carrier := gradedCarrier_flat W
  have hθinj : Function.Injective (j.rTensor W.carrier) :=
    Module.Flat.rTensor_preserves_injective_linearMap j hj
  have hθexact : Function.Exact (j.rTensor W.carrier) (d.rTensor W.carrier) :=
    Module.Flat.rTensor_exact W.carrier hex
  let : Algebra R B := a.base.hom.toAlgebra
  let : Algebra R C := b.base.hom.toAlgebra
  let : Algebra R A := (f.base.hom.comp a.base.hom).toAlgebra
  let eB := (morphismPushoutEquiv a).toLinearEquiv
  let eC := (morphismPushoutEquiv b).toLinearEquiv
  let eA := (morphismPushoutEquiv (a ≫ f)).toLinearEquiv
  let pr := TensorProduct.prodLeft R R B C W.carrier
  let θ : S ⊗[R] W.carrier →ₗ[R] (B ⊗[R] W.carrier) × (C ⊗[R] W.carrier) :=
    pr.toLinearMap.comp (j.rTensor W.carrier)
  have hθinjective : Function.Injective θ := pr.injective.comp hθinj
  have hθrange (p : (B ⊗[R] W.carrier) × (C ⊗[R] W.carrier))
      (hp : (d.rTensor W.carrier) (pr.symm p) = 0) : ∃ t, θ t = p := by
    obtain ⟨t, ht⟩ := (hθexact (pr.symm p)).mp hp
    exact ⟨t, by simpa [θ] using congrArg pr ht⟩
  let bil : S →ₗ[S] (W.carrier →ₗ[R] Q.carrier) := {
    toFun := fun s => s • l
    map_add' := by
      intro s t
      ext x
      exact add_smul s t (l x)
    map_smul' := by
      intro s t
      ext x
      simp [smul_smul] }
  let eQ : S ⊗[R] W.carrier →ₗ[S] Q.carrier := AlgebraTensorModule.lift bil
  have heQ_tmul (s : S) (x : W.carrier) : eQ (s ⊗ₜ[R] x) = s • l x := rfl
  have hθ_tmul (s : S) (x : W.carrier) :
      θ (s ⊗ₜ[R] x) = ((s.1.1 : B) ⊗ₜ[R] x, (s.1.2 : C) ⊗ₜ[R] x) := by
    change pr ((s.1.1, s.1.2) ⊗ₜ[R] x) = _
    exact TensorProduct.prodLeft_tmul R R B C W.carrier _ _ _
  have hfst_add (p q : Q.carrier) : (p + q).1.1 = p.1.1 + q.1.1 := rfl
  have hsnd_add (p q : Q.carrier) : (p + q).1.2 = p.1.2 + q.1.2 := rfl
  have hcoordB (t : S ⊗[R] W.carrier) : (eQ t).1.1 = eB (θ t).1 := by
    induction t using TensorProduct.inductionOn with
    | add t u ht hu =>
        simpa only [map_add, hfst_add, Prod.fst_add] using congrArg₂ (· + ·) ht hu
    | tmul s x =>
        rw [heQ_tmul, hθ_tmul]
        have hs' : (s • l x).1.1 = (s.1.1 : B) • a.map x := by
          convert (gradedPullbackFst f g hg).map_smul s (l x) using 1 <;> rfl
        rw [hs']
        exact (morphismPushoutEquiv_tmul a s.1.1 x).symm
  have hcoordC (t : S ⊗[R] W.carrier) : (eQ t).1.2 = eC (θ t).2 := by
    induction t using TensorProduct.inductionOn with
    | add t u ht hu =>
        simpa only [map_add, hsnd_add, Prod.snd_add] using congrArg₂ (· + ·) ht hu
    | tmul s x =>
        rw [heQ_tmul, hθ_tmul]
        have hs' : (s • l x).1.2 = (s.1.2 : C) • b.map x := by
          convert (gradedPullbackSnd f g hg).map_smul s (l x) using 1 <;> rfl
        rw [hs']
        exact (morphismPushoutEquiv_tmul b s.1.2 x).symm
  have hδ (t : (B × C) ⊗[R] W.carrier) :
      eA ((d.rTensor W.carrier) t) = f.map (eB (pr t).1) - g.map (eC (pr t).2) := by
    induction t using TensorProduct.inductionOn with
    | add t u ht hu =>
        simp only [LinearMap.map_add, LinearEquiv.map_add, RingHom.map_add,
          Prod.fst_add, Prod.snd_add]
        rw [ht, hu]
        abel
    | tmul p x =>
        change eA ((f.base.hom p.1 - g.base.hom p.2) ⊗ₜ[R] x) =
          f.map (eB (p.1 ⊗ₜ[R] x)) - g.map (eC (p.2 ⊗ₜ[R] x))
        have hx : f.map (a.map x) = g.map (b.map x) :=
          congrArg (fun t : W ⟶ Z => t.map x) h
        change morphismPushoutEquiv (a ≫ f)
            ((f.base.hom p.1 - g.base.hom p.2) ⊗ₜ[R] x) =
          f.map (morphismPushoutEquiv a (p.1 ⊗ₜ[R] x)) -
            g.map (morphismPushoutEquiv b (p.2 ⊗ₜ[R] x))
        rw [morphismPushoutEquiv_tmul, morphismPushoutEquiv_tmul,
          morphismPushoutEquiv_tmul, f.map_smul, g.map_smul, ← hx, sub_smul]
        rfl
  have heQ_injective : Function.Injective eQ := by
    intro t u htu
    apply hθinjective
    apply Prod.ext
    · apply eB.injective
      calc
        eB (θ t).1 = (eQ t).1.1 := (hcoordB t).symm
        _ = (eQ u).1.1 := congrArg (fun q : Q.carrier => q.1.1) htu
        _ = eB (θ u).1 := hcoordB u
    · apply eC.injective
      calc
        eC (θ t).2 = (eQ t).1.2 := (hcoordC t).symm
        _ = (eQ u).1.2 := congrArg (fun q : Q.carrier => q.1.2) htu
        _ = eC (θ u).2 := hcoordC u
  have heQ_surjective : Function.Surjective eQ := by
    intro q
    let p : (B ⊗[R] W.carrier) × (C ⊗[R] W.carrier) := (eB.symm q.1.1, eC.symm q.1.2)
    have hp : (d.rTensor W.carrier) (pr.symm p) = 0 := by
      apply eA.injective
      rw [hδ, map_zero]
      change f.map (eB (pr (pr.symm p)).1) - g.map (eC (pr (pr.symm p)).2) = 0
      simp only [LinearEquiv.apply_symm_apply, p]
      exact sub_eq_zero.mpr q.2
    obtain ⟨t, ht⟩ := hθrange p hp
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · calc
        (eQ t).1.1 = eB (θ t).1 := hcoordB t
        _ = eB p.1 := congrArg (fun z => eB z.1) ht
        _ = q.1.1 := eB.apply_symm_apply _
    · calc
        (eQ t).1.2 = eC (θ t).2 := hcoordC t
        _ = eC p.2 := congrArg (fun z => eC z.2) ht
        _ = q.1.2 := eC.apply_symm_apply _
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective eQ ⟨heQ_injective, heQ_surjective⟩)
    (fun x => by
      change eQ (1 ⊗ₜ[R] x) = l x
      rw [heQ_tmul, one_smul])

/-- The lift of a competing cone to the patch. -/
private noncomputable def gradedPullbackLift
    (hg : Function.Surjective g.base.hom)
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    W ⟶ gradedPullback f g hg := {
  base := gradedPullbackLiftBase f g hg a b h
  map := gradedPullbackLiftMap f g a b h
  map_smul := fun r x => by
    change gradedPullbackLiftMap f g a b h (r • x) =
      (pullbackScalarMap f g) ((gradedPullbackLiftBase f g hg a b h).hom r) *
        gradedPullbackLiftMap f g a b h x
    exact gradedPullbackLiftMap_smul f g hg a b h r x
  map_mem := gradedPullbackLiftMap_mem f g a b h
  isBaseChange := gradedPullbackLift_isBaseChange f g hg a b h }

/-- The lift factors the first leg of the competing cone. -/
private theorem gradedPullbackLift_fst
    (hg : Function.Surjective g.base.hom)
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    gradedPullbackLift f g hg a b h ≫ gradedPullbackFst f g hg = a := by
  apply ProjectiveGradedAlgebra.Hom.ext
  · apply ArtinianLocalAlgCat.hom_ext
    ext r
    rfl
  · ext x
    rfl

/-- The lift factors the second leg of the competing cone. -/
private theorem gradedPullbackLift_snd
    (hg : Function.Surjective g.base.hom)
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    gradedPullbackLift f g hg a b h ≫ gradedPullbackSnd f g hg = b := by
  apply ProjectiveGradedAlgebra.Hom.ext
  · apply ArtinianLocalAlgCat.hom_ext
    ext r
    rfl
  · ext x
    rfl

/-- The lift is the only morphism factoring both legs. -/
private theorem gradedPullbackLift_unique
    (hg : Function.Surjective g.base.hom)
    {W : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g)
    (l : W ⟶ gradedPullback f g hg)
    (hl₁ : l ≫ gradedPullbackFst f g hg = a)
    (hl₂ : l ≫ gradedPullbackSnd f g hg = b) :
    l = gradedPullbackLift f g hg a b h := by
  apply ProjectiveGradedAlgebra.Hom.ext
  · apply ArtinianLocalAlgCat.hom_ext
    ext r
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun t : W ⟶ X => t.base.hom r) hl₁
    · exact congrArg (fun t : W ⟶ Y => t.base.hom r) hl₂
  · ext x
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun t : W ⟶ X => t.map x) hl₁
    · exact congrArg (fun t : W ⟶ Y => t.map x) hl₂

end PullbackGrading

/-- The category of graded algebras finite projective in each degree satisfies the
Rim–Schlessinger condition. -/
@[stacks 0DVY "Rim-Schlessinger condition"]
public theorem satisfiesRS_projection
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    SatisfiesRS
      (ProjectiveGradedAlgebra.projection.{u, v, w, max v m} (Λ := Λ) (k := k)) :=
  ⟨ProjectiveGradedAlgebra.projection_isCofiberedInGroupoids (Λ := Λ) (k := k), by
    intro X Y Z f g hg
    let c := gradedPullbackCone f g hg
    refine ⟨c, ⟨PullbackCone.isLimitAux' c (fun s => ?_)⟩, ?_⟩
    · exact ⟨gradedPullbackLift f g hg s.fst s.snd s.condition,
        gradedPullbackLift_fst f g hg s.fst s.snd s.condition,
        gradedPullbackLift_snd f g hg s.fst s.snd s.condition,
        fun {_} hm₁ hm₂ => gradedPullbackLift_unique f g hg s.fst s.snd
          s.condition _ hm₁ hm₂⟩
    · refine ⟨PullbackCone.isLimitAux' (c.map
        (ProjectiveGradedAlgebra.projection.{u, v, w, max v m} (Λ := Λ) (k := k)))
        (fun s => ?_)⟩
      let t := (ArtinianLocalAlgCat.isPullback_of_surjective f.base g.base
        (Or.inr hg)).isLimit
      have hf : (c.map
          (ProjectiveGradedAlgebra.projection.{u, v, w, max v m} (Λ := Λ) (k := k))).fst =
          (ArtinianLocalAlgCat.isPullback_of_surjective f.base g.base
            (Or.inr hg)).cone.fst := by
        apply ArtinianLocalAlgCat.hom_ext
        change (gradedPullbackFstBase f g hg).hom =
          (ArtinianLocalAlgCat.pullbackFst_of_surjective f.base g.base (Or.inr hg)).hom
        rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
        rfl
      have hs : (c.map
          (ProjectiveGradedAlgebra.projection.{u, v, w, max v m} (Λ := Λ) (k := k))).snd =
          (ArtinianLocalAlgCat.isPullback_of_surjective f.base g.base
            (Or.inr hg)).cone.snd := by
        apply ArtinianLocalAlgCat.hom_ext
        change (gradedPullbackSndBase f g hg).hom =
          (ArtinianLocalAlgCat.pullbackSnd_of_surjective f.base g.base (Or.inr hg)).hom
        rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]
        rfl
      refine ⟨PullbackCone.IsLimit.lift t s.fst s.snd s.condition, ?_, ?_, ?_⟩
      · rw [hf]
        exact PullbackCone.IsLimit.lift_fst t _ _ _
      · rw [hs]
        exact PullbackCone.IsLimit.lift_snd t _ _ _
      · intro m hm₁ hm₂
        rw [hf] at hm₁
        rw [hs] at hm₂
        exact PullbackCone.IsLimit.hom_ext t
          (hm₁.trans (PullbackCone.IsLimit.lift_fst t _ _ _).symm)
          (hm₂.trans (PullbackCone.IsLimit.lift_snd t _ _ _).symm)⟩

/-- The deformations of a fixed graded `k`-algebra, finite-dimensional in each degree, form a
deformation category. -/
@[stacks 0DVY "deformation category"]
public theorem isDeformationCategory_deformationCategory
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)] :
    IsDeformationCategory
      (objectsOverFunctor
        (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
        (specialFiber (Λ := Λ) P grading)) :=
  isDeformationCategory_objectsOverFunctor_of_baseIso
    (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
    satisfiesRS_projection (specialFiber (Λ := Λ) P grading) residueFieldBaseIso

end Deformation.Examples.ProjectiveGradedAlgebra
