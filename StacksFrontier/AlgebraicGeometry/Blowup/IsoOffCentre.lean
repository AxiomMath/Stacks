module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjOfOpenInAffine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic

/-!
# A blowup is an isomorphism away from its centre

The blowup of a scheme `X` in a quasi-coherent ideal sheaf `I` restricts to an isomorphism over
the open complement of the support of `I`. This is Stacks tag 02OS part (1), and it is what makes
the blowup a modification: it changes `X` only along the closed subscheme cut out by `I`.

## Main results

* `AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`: the blowup morphism
  `AlgebraicGeometry.blowUpToBase I` restricted to `I.support.compl` is an isomorphism. It is an
  instance, so the hypothesis `[IsIso (blowUpToBase I ∣_ I.support.compl)]` carried by several
  statements about blowups is now discharged automatically.

## Implementation notes

The statement is local on the base, since being an isomorphism is Zariski-local at the target,
so it suffices to treat an affine open `V` of `X` disjoint from the support of `I`. On such a `V`
the ideal is the unit ideal (`AlgebraicGeometry.ideal_eq_top_of_le_compl_support` of
`StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/Basic.lean`, which reads
the condition off `Scheme.IdealSheafData.mem_support_iff_of_mem` and feeds it to
`AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff`), and the part of the blowup lying
over `V` is the canonical affine chart of the relative `Proj`,
`Stacks.RelativeProj.Situation.relativeProjChart_isPullback`. So everything reduces to the chart:
the projective spectrum of the graded ring `⨁ₙ (I.ideal V)ⁿ` of local sections of the Rees
algebra, mapping to `V`.

Where `I.ideal V = ⊤` that graded ring is `Γ(X, V)[T]` with `T` of degree one, which is the
graded ring tag 0G5W attaches to the *whole* spectrum of `Γ(X, V)`
(`AlgebraicGeometry.openProjGrading ⊤`). The comparison is built degreewise — each piece is a
copy of `Γ(X, V)` carried by a single monomial — and assembled by
`AlgebraicGeometry.directSumRingEquiv`, which turns a multiplicative family of additive
isomorphisms of homogeneous pieces into a ring isomorphism of the direct sums. Tag 0G5W's
`AlgebraicGeometry.projOpenIso` then identifies the resulting `Proj` with the open subscheme,
here the whole of `Spec Γ(X, V)`, and `AlgebraicGeometry.Proj.map_toSpecZero` is what makes that
identification a morphism over the base.

Two spelling choices are worth recording. The graded-ring structure of tag 0G5W is a `def`
depending on the open, so it is declared a local instance here rather than carried in every
statement. And the canonical map from the structure sheaf multiplies the unit section by a
function, an operation whose scalar must be spelled in the `Scheme.ringCatSheaf` language, so
the two lemmas about it take their argument there and ascribe it to `Γ(X, V)` on the other side.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0G5W](https://stacks.math.columbia.edu/tag/0G5W)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite DirectSum

universe u

-- The graded-ring structure attached to an open of an affine scheme by tag 0G5W is a `def`,
-- because it depends on the open. It is made an instance for this file so that the statements
-- about the projective spectrum of that grading need not each carry it.
attribute [local instance] openProjGradedRing

/-! ### A graded ring isomorphism from degreewise additive isomorphisms -/

section DirectSumBridge

variable {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
variable {D E : ι → Type*} [∀ i, AddCommGroup (D i)] [∀ i, AddCommGroup (E i)]
variable [DirectSum.GCommRing D] [DirectSum.GCommRing E]

/-- A family of additive isomorphisms of the homogeneous pieces that is multiplicative on
homogeneous elements assembles into a ring isomorphism of the direct sums. -/
private noncomputable def directSumRingEquiv (e : ∀ i, D i ≃+ E i)
    (hmul : ∀ {i j} (a : D i) (b : D j),
      e (i + j) (GradedMonoid.GMul.mul a b) = GradedMonoid.GMul.mul (e i a) (e j b)) :
    (⨁ i, D i) ≃+* (⨁ i, E i) := by
  let f : (⨁ i, D i) →+ (⨁ i, E i) := DirectSum.map fun i => (e i).toAddMonoidHom
  let g : (⨁ i, E i) →+ (⨁ i, D i) := DirectSum.map fun i => (e i).symm.toAddMonoidHom
  let eAdd : (⨁ i, D i) ≃+ (⨁ i, E i) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        apply DirectSum.ext
        intro i
        simp [f, g]
      right_inv := by
        intro x
        apply DirectSum.ext
        intro i
        simp [f, g]
      map_add' := f.map_add }
  refine RingEquiv.mk eAdd ?_ ?_
  · refine fun x z => (AddMonoidHom.map_mul_iff f).2 ?_ x z
    refine DirectSum.addHom_ext fun i a => DirectSum.addHom_ext fun j b => ?_
    simp only [AddMonoidHom.compl₂_apply, AddMonoidHom.compr₂_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.mul_apply, DirectSum.of_mul_of, f, DirectSum.map_of,
      AddEquiv.coe_toAddMonoidHom]
    exact congrArg (DirectSum.of E (i + j)) (hmul a b)
  · exact f.map_add

private theorem directSumRingEquiv_of (e : ∀ i, D i ≃+ E i)
    (hmul : ∀ {i j} (a : D i) (b : D j),
      e (i + j) (GradedMonoid.GMul.mul a b) = GradedMonoid.GMul.mul (e i a) (e j b))
    (i : ι) (a : D i) :
    directSumRingEquiv e hmul (DirectSum.of D i a) = DirectSum.of E i (e i a) := by
  show DirectSum.map (fun k => (e k).toAddMonoidHom) (DirectSum.of D i a) = _
  simp

end DirectSumBridge

/-! ### `Proj` of a graded ring only depends on its graded isomorphism class -/

section ProjIso

variable {R S σ τ : Type u} [CommRing R] [CommRing S]
variable [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ S] [AddSubgroupClass τ S]
variable {𝒟 : ℕ → σ} {ℰ : ℕ → τ} [GradedRing 𝒟] [GradedRing ℰ]

/-- A graded ring homomorphism with a one-sided inverse satisfies Mathlib's hypothesis for
`AlgebraicGeometry.Proj.map`. -/
private theorem irrelevant_le_map_of_comp_eq_id (f : 𝒟 →+*ᵍ ℰ) (g : ℰ →+*ᵍ 𝒟)
    (hfg : f.comp g = GradedRingHom.id ℰ) :
    HomogeneousIdeal.irrelevant ℰ ≤ (HomogeneousIdeal.irrelevant 𝒟).map f := by
  refine (HomogeneousIdeal.irrelevant_le _).2 fun n hn x hx => ?_
  have hxy : f (g x) = x := by
    show (f.comp g) x = x
    rw [hfg]; rfl
  rw [← hxy]
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn (g.map_mem hx))

end ProjIso

/-! ### One-variable polynomials -/

section OneVar

variable {A : Type u} [CommRing A]

/-- On the whole spectrum every function is an admissible coefficient. -/
private theorem openProjIdeal_top : openProjIdeal (⊤ : (Spec (.of A)).Opens) = ⊤ := by
  ext a
  rw [openProjIdeal, PrimeSpectrum.mem_vanishingIdeal]
  show (∀ x ∈ (Set.univ : Set (PrimeSpectrum A))ᶜ, a ∈ x.asIdeal) ↔ a ∈ (⊤ : Ideal A)
  simp

/-- A function, as a homogeneous element of degree `n` of the graded ring of tag 0G5W attached
to the whole spectrum. -/
private noncomputable def topProjMonomial (n : ℕ) (a : A) :
    openProjGrading (A := A) ⊤ n := by
  refine ⟨⟨MvPolynomial.monomial (Finsupp.single 0 n) a,
    Algebra.subset_adjoin ⟨n, a, by rw [openProjIdeal_top]; simp, rfl⟩⟩, ?_⟩
  change MvPolynomial.monomial (Finsupp.single 0 n) a ∈
    MvPolynomial.homogeneousSubmodule (Fin 1) A n
  exact (MvPolynomial.mem_homogeneousSubmodule n _).2
    (MvPolynomial.isHomogeneous_monomial a (by simp))

/-- The degree-`n` piece of the graded ring of tag 0G5W attached to the whole spectrum is a copy
of the coefficient ring. -/
private noncomputable def topProjMonomialEquiv (n : ℕ) :
    A ≃+ openProjGrading (A := A) ⊤ n where
  toFun := topProjMonomial n
  invFun q := q.1.1.coeff (Finsupp.single 0 n)
  left_inv a := by simp [topProjMonomial]
  right_inv q := by
    refine Subtype.ext (Subtype.ext ?_)
    change MvPolynomial.monomial (Finsupp.single 0 n)
      (q.1.1.coeff (Finsupp.single 0 n)) = q.1.1
    exact (openProj_homogeneous_shape q.1.1 n
      ((MvPolynomial.mem_homogeneousSubmodule n _).1 q.2)).symm
  map_add' a b := by
    refine Subtype.ext (Subtype.ext ?_)
    ext d
    simp [topProjMonomial]

/-- Monomials multiply by adding degrees. -/
private theorem topProjMonomial_mul (n m : ℕ) (a b : A) :
    @GradedMonoid.GMul.mul ℕ (fun k => ↥(openProjGrading (A := A) ⊤ k)) inferInstance _ n m
      (topProjMonomial n a) (topProjMonomial m b) = topProjMonomial (n + m) (a * b) := by
  refine Subtype.ext (Subtype.ext ?_)
  show MvPolynomial.monomial (Finsupp.single 0 n) a *
      MvPolynomial.monomial (Finsupp.single 0 m) b =
    MvPolynomial.monomial (Finsupp.single 0 (n + m)) (a * b)
  rw [MvPolynomial.monomial_mul_monomial, Finsupp.single_add]

end OneVar


/-! ### The blowup chart over an affine open where the centre is trivial -/

section ReesChart

open Stacks.RelativeProj

variable {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
  (hI : I.ideal V = ⊤)

include hI

/-- Where the ideal is the unit ideal, each of its powers is a copy of the coefficient ring. -/
private noncomputable def reesPowEquivOfTop (n : ℕ) :
    ↥(I.ideal V ^ n) ≃+ ↑Γ(X, V.1) where
  toFun x := x.1
  invFun x := ⟨x, by rw [hI, Ideal.top_pow]; trivial⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Where the centre is trivial on `V`, the degree-`n` homogeneous sections of the Rees algebra
over `V` are the degree-`n` piece of the graded ring of tag 0G5W for the whole spectrum of
`Γ(X, V)`. -/
private noncomputable def reesPieceEquivOfTop (n : ℕ) :
    (reesSituation I).sectionPieces V.1 n ≃+
      openProjGrading (A := ↑Γ(X, V.1)) ⊤ n :=
  (((reesAlgebraData I).pieceEquiv (n : ℤ) (Int.natCast_nonneg n) V).trans
    ((reesPowEquivOfTop I V hI n).trans (topProjMonomialEquiv n)))

private theorem reesPieceEquivOfTop_apply (n : ℕ)
    (a : (reesSituation I).sectionPieces V.1 n) :
    reesPieceEquivOfTop I V hI n a =
      topProjMonomial n (reesPowEquivOfTop I V hI n
        ((reesAlgebraData I).pieceEquiv (n : ℤ) (Int.natCast_nonneg n) V a)) := rfl

private theorem reesPieceEquivOfTop_mul (n m : ℕ)
    (a : (reesSituation I).sectionPieces V.1 n)
    (b : (reesSituation I).sectionPieces V.1 m) :
    reesPieceEquivOfTop I V hI (n + m) (GradedMonoid.GMul.mul a b) =
      @GradedMonoid.GMul.mul ℕ
        (fun k => ↥(openProjGrading (A := ↑Γ(X, V.1)) ⊤ k)) inferInstance _ n m
        (reesPieceEquivOfTop I V hI n a) (reesPieceEquivOfTop I V hI m b) := by
  have hmul := (reesAlgebraData I).pieceEquiv_mul (n : ℤ) (m : ℤ)
    (Int.natCast_nonneg n) (Int.natCast_nonneg m) V a b
  have hs : (GradedMonoid.GMul.mul a b : (reesSituation I).sectionPieces V.1 (n + m)) =
      ((reesSituation I).algebra.mul (n : ℤ) (m : ℤ)).app (op V.1) a b :=
    eq_of_heq ((Situation.sectionRingStructure (reesSituation I)).mul_homogeneous V.1 n m a b)
  rw [hs, reesPieceEquivOfTop_apply, reesPieceEquivOfTop_apply, reesPieceEquivOfTop_apply,
    topProjMonomial_mul]
  exact congrArg (topProjMonomial (n + m)) hmul


/-- Where the centre is trivial on `V`, the graded ring of homogeneous sections of the Rees
algebra over `V` is the graded ring of tag 0G5W for the whole spectrum of `Γ(X, V)`. -/
private noncomputable def reesDirectSumEquivOfTop :
    (reesSituation I).sectionRing V.1 ≃+*
      (⨁ n : ℕ, ↥(openProjGrading (A := ↑Γ(X, V.1)) ⊤ n)) :=
  directSumRingEquiv (ι := ℕ)
    (D := fun n => (reesSituation I).sectionPieces V.1 n)
    (E := fun n => ↥(openProjGrading (A := ↑Γ(X, V.1)) ⊤ n))
    (reesPieceEquivOfTop I V hI) (fun a b => reesPieceEquivOfTop_mul I V hI _ _ a b)

/-- The same identification, read inside the ambient graded ring rather than its direct sum. -/
private noncomputable def reesTotalEquivOfTop :
    (reesSituation I).sectionRing V.1 ≃+* ↥(openProjAlgebra (A := ↑Γ(X, V.1)) ⊤) :=
  (reesDirectSumEquivOfTop I V hI).trans
    (DirectSum.decomposeRingEquiv (openProjGrading (A := ↑Γ(X, V.1)) ⊤)).symm

private theorem reesDirectSumEquivOfTop_of (n : ℕ)
    (a : (reesSituation I).sectionPieces V.1 n) :
    reesDirectSumEquivOfTop I V hI
        (DirectSum.of ((reesSituation I).sectionPieces V.1) n a) =
      DirectSum.of (fun k => ↥(openProjGrading (A := ↑Γ(X, V.1)) ⊤ k)) n
        (reesPieceEquivOfTop I V hI n a) :=
  directSumRingEquiv_of _ _ n a

private theorem reesTotalEquivOfTop_apply (x : (reesSituation I).sectionRing V.1) :
    reesTotalEquivOfTop I V hI x =
      (DirectSum.decomposeRingEquiv (openProjGrading (A := ↑Γ(X, V.1)) ⊤)).symm
        (reesDirectSumEquivOfTop I V hI x) := rfl

private theorem reesTotalEquivOfTop_of (n : ℕ) (a : (reesSituation I).sectionPieces V.1 n) :
    reesTotalEquivOfTop I V hI (DirectSum.of ((reesSituation I).sectionPieces V.1) n a) =
      ((reesPieceEquivOfTop I V hI n a : ↥(openProjGrading (A := ↑Γ(X, V.1)) ⊤ n)) :
        ↥(openProjAlgebra (A := ↑Γ(X, V.1)) ⊤)) := by
  rw [reesTotalEquivOfTop_apply, reesDirectSumEquivOfTop_of]
  exact DirectSum.decompose_symm_of (ℳ := openProjGrading (A := ↑Γ(X, V.1)) ⊤) _

private theorem reesTotalEquivOfTop_symm_of (n : ℕ)
    (z : ↥(openProjGrading (A := ↑Γ(X, V.1)) ⊤ n)) :
    (reesTotalEquivOfTop I V hI).symm (z : ↥(openProjAlgebra (A := ↑Γ(X, V.1)) ⊤)) =
      DirectSum.of ((reesSituation I).sectionPieces V.1) n
        ((reesPieceEquivOfTop I V hI n).symm z) := by
  refine (reesTotalEquivOfTop I V hI).injective ?_
  rw [RingEquiv.apply_symm_apply, reesTotalEquivOfTop_of,
    (reesPieceEquivOfTop I V hI n).apply_symm_apply]

/-- The identification of the two graded rings, as a graded ring homomorphism. -/
private noncomputable def reesToTopProjGraded :
    (reesSituation I).sectionRingGrading V.1 →+*ᵍ openProjGrading (A := ↑Γ(X, V.1)) ⊤ where
  toRingHom := (reesTotalEquivOfTop I V hI).toRingHom
  map_mem := by
    rintro n x ⟨a, rfl⟩
    change reesTotalEquivOfTop I V hI
      (DirectSum.of ((reesSituation I).sectionPieces V.1) n a) ∈ _
    rw [reesTotalEquivOfTop_of]
    exact (reesPieceEquivOfTop I V hI n a).property

end ReesChart


/-! ### Globalising over the complement of the centre -/

/-- **Stacks Project, Tag 02OS.** A blowup is an isomorphism away from its centre: the blowup
morphism of `X` in a quasi-coherent ideal sheaf `I` restricts to an isomorphism over the open
complement of the support of `I`.

This is `AlgebraicGeometry.isIso_blowUp_restrict_compl_support` of
`StacksFrontier/AlgebraicGeometry/Blowup/IsomorphismOffCenter/Basic.lean`, which states and proves
it with the complement written out; the tag is registered there.  The instance is kept so that
`IsIso (blowUpToBase I ∣_ I.support.compl)` is found by synthesis at the `.compl` spelling. -/
@[sga "7 XVIII 2.1" "more general"]
public instance isIso_blowUpToBase_restrict_compl_support {X : Scheme.{u}}
    (I : X.IdealSheafData) : IsIso (blowUpToBase I ∣_ I.support.compl) :=
  isIso_blowUp_restrict_compl_support I

end AlgebraicGeometry

end
