module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjQuasiCompact
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverShortExact

/-!
# Higher cohomology of the blowup of a regular local surface

The blowup of a two-dimensional regular local ring at its maximal ideal has no quasi-coherent
cohomology in degrees at least two.

## Main results

* `AlgebraicGeometry.isZero_cohomology_of_two_le`: the higher-cohomology vanishing.

## Implementation notes

The centre is the ideal sheaf associated to the maximal ideal under the canonical
identification of a ring with the global functions on its spectrum, and cohomology is the
right-derived global-sections functor on sheaves of modules.

The proof exhibits the blowup as the ordinary `Proj` of the Rees algebra of the maximal ideal:
the base is affine, so the single chart over the top affine open is already the whole blowup.
Two generators of the maximal ideal give two standard opens of that `Proj` which cover it and
are affine, so the blowup is covered by two affine opens and the vanishing follows from the
cohomological dimension of a finite affine cover.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Pointwise DirectSum

namespace AlgebraicGeometry

universe u v w

/-- The product of an element of `Iⁿ` and an element of `Iᵐ` lies in `Iⁿ⁺ᵐ`. -/
private theorem mul_mem_pow_add {R : Type*} [CommRing R] {I : Ideal R} {n m : ℕ} {a b : R}
    (ha : a ∈ I ^ n) (hb : b ∈ I ^ m) : a * b ∈ I ^ (n + m) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul ha hb

private theorem pow_span_lift
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (s : Finset R) (hI : I = Ideal.span (s : Set R))
    (ι : R →+* S) (lift : ∀ n : ℕ, ∀ a : R, a ∈ I ^ n → S)
    (hz : ∀ n, lift n 0 (by simp) = 0)
    (hAdd : ∀ n a b (ha : a ∈ I ^ n) (hb : b ∈ I ^ n),
      lift n (a + b) (by exact add_mem ha hb) = lift n a ha + lift n b hb)
    (hSmul : ∀ n r a (ha : a ∈ I ^ n),
      lift n (r * a) ((I ^ n).mul_mem_left r ha) = ι r * lift n a ha)
    (hMul : ∀ n m a b (ha : a ∈ I ^ n) (hb : b ∈ I ^ m),
      lift (n + m) (a * b) (mul_mem_pow_add ha hb) =
        lift n a ha * lift m b hb)
    (g : s → S)
    (hG : ∀ b (hb : b ∈ (s : Set R)),
      lift 1 b (by rw [pow_one, hI]; exact Ideal.subset_span hb) = g ⟨b, hb⟩)
    {n : ℕ} (hn : 0 < n) {a : R} (ha : a ∈ I ^ n) :
    lift n a ha ∈ Ideal.span (Set.range g) := by
  classical
  let K : Ideal S := Ideal.span (Set.range g)
  have heq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hpow : I ^ n = Ideal.span (((I ^ (n - 1) : Ideal R) : Set R) * (s : Set R)) := by
    calc
      I ^ n = I ^ (n - 1 + 1) := by rw [heq]
      _ = I ^ (n - 1) * I := by
        simpa using (Submodule.pow_succ (M := (I : Submodule R R)) (n := n - 1))
      _ = I ^ (n - 1) * Ideal.span (s : Set R) := congrArg _ hI
      _ = Ideal.span (((I ^ (n - 1) : Ideal R) : Set R) * (s : Set R)) := by
        rw [← Ideal.span_eq (I ^ (n - 1)), Ideal.span_mul_span, Ideal.span_eq]
  have hp : ∀ x (hx : x ∈ Ideal.span (((I ^ (n - 1) : Ideal R) : Set R) * (s : Set R))),
      lift n x (hpow.symm ▸ hx) ∈ K := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro z hz
      rcases Set.mem_mul.mp hz with ⟨b, hb, c, hc, rfl⟩
      have hcPow : c ∈ I ^ 1 := by
        rw [pow_one, hI]
        exact Ideal.subset_span hc
      have hmul : lift n (b * c) (hpow.symm ▸ Ideal.subset_span hz) =
          lift (n - 1) b hb * lift 1 c hcPow := by
        simpa [heq] using hMul (n - 1) 1 b c hb hcPow
      rw [hmul, hG c hc]
      exact K.mul_mem_left _ (Ideal.subset_span (Set.mem_range.mpr ⟨⟨c, hc⟩, rfl⟩))
    · rw [hz]
      exact K.zero_mem
    · intro x y hx hy ihx ihy
      rw [hAdd]
      · exact K.add_mem ihx ihy
      · exact hpow.symm ▸ hx
      · exact hpow.symm ▸ hy
    · intro r x hx ih
      have hxI : x ∈ I ^ n := hpow.symm ▸ hx
      have he : lift n (r • x)
          (hpow.symm ▸ (Submodule.smul_mem
            (Ideal.span (((I ^ (n - 1) : Ideal R) : Set R) * (s : Set R))) r hx)) =
          ι r * lift n x hxI := by
        simpa [smul_eq_mul] using hSmul n r x hxI
      exact he ▸ K.mul_mem_left _ ih
  exact hp a (hpow.symm ▸ ha)

private theorem cast_heq_eq {α β : Sort u} {a : α} {b : β} (h : HEq a b) :
    cast (type_eq_of_heq h) a = b := by
  cases h
  rfl

private theorem cast_smul_indexed {ι : Type v} {R : Type w} (M : ι → Type u)
    [∀ i, SMul R (M i)] {i j : ι} (h : i = j) (r : R) (x : M i) :
    cast (congrArg M h) (r • x) = r • cast (congrArg M h) x := by
  cases h
  rfl

section ReesLift

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The homogeneous section of degree `n` of the Rees algebra of `I` over the affine open `U`
attached to an element of `I(U)ⁿ`. -/
private noncomputable def reesLift (n : ℕ) (a : X.presheaf.obj (op U.1))
    (ha : a ∈ I.ideal U ^ n) : (AlgebraicGeometry.reesSituation I).sectionRing U.1 :=
  DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces U.1) n
    (((AlgebraicGeometry.reesAlgebraData I).pieceEquiv (n : ℤ) (by omega) U).symm
      ⟨a, by simpa using ha⟩)

private theorem reesLift_add : ∀ (n : ℕ) (a b : X.presheaf.obj (op U.1))
    (ha : a ∈ I.ideal U ^ n) (hb : b ∈ I.ideal U ^ n),
    reesLift I U n (a + b) (by exact add_mem ha hb) =
      reesLift I U n a ha + reesLift I U n b hb := by
  let situ := AlgebraicGeometry.reesSituation I
  let data := AlgebraicGeometry.reesAlgebraData I
  intro n a b ha hb
  change (DirectSum.of (situ.sectionPieces U.1) n)
      ((data.pieceEquiv (n : ℤ) (by omega) U).symm ⟨a + b, by simpa using add_mem ha hb⟩) = _
  rw [show (data.pieceEquiv (n : ℤ) (by omega) U).symm ⟨a + b, by simpa using add_mem ha hb⟩ =
    (data.pieceEquiv (n : ℤ) (by omega) U).symm ⟨a, ha⟩ +
      (data.pieceEquiv (n : ℤ) (by omega) U).symm ⟨b, hb⟩ by
    apply (data.pieceEquiv (n : ℤ) (by omega) U).injective
    simp]
  exact (DirectSum.of (situ.sectionPieces U.1) n).map_add _ _

private theorem reesLift_zero : ∀ n : ℕ, reesLift I U n 0 (by simp) = 0 := fun n => by
  simpa using reesLift_add I U n 0 0 (zero_mem _) (zero_mem _)

private theorem reesLift_smul : ∀ (n : ℕ) (r a : X.presheaf.obj (op U.1))
    (ha : a ∈ I.ideal U ^ n),
    reesLift I U n (r * a) ((I.ideal U ^ n).mul_mem_left r ha) =
      (AlgebraicGeometry.reesSituation I).sectionRingBaseMap U.1 r * reesLift I U n a ha := by
  let situ := AlgebraicGeometry.reesSituation I
  let data := AlgebraicGeometry.reesAlgebraData I
  let R := X.presheaf.obj (op U.1)
  let J : Ideal R := I.ideal U
  intro n r a ha
  let : Module (situ.sectionPieces U.1 0) (situ.sectionPieces U.1 n) := inferInstance
  let q := data.pieceEquiv (n : ℤ) (by omega) U
  let rS : X.ringCatSheaf.obj.obj (op U.1) := r
  have hq : q.symm ⟨r * a, (J ^ n).mul_mem_left r ha⟩ = rS • q.symm ⟨a, ha⟩ := by
    apply q.injective
    rw [q.apply_symm_apply]
    apply Subtype.ext
    simpa [q, rS] using (data.pieceEquiv_smul (n : ℤ) (by omega) U rS
      (q.symm ⟨a, ha⟩)).symm
  rw [Stacks.RelativeProj.Situation.sectionRingBaseMap,
    (Stacks.RelativeProj.Situation.sectionRingStructure situ).baseMap_apply U.1 rS]
  change DirectSum.of (situ.sectionPieces U.1) n
        (q.symm ⟨r * a, (J ^ n).mul_mem_left r ha⟩) =
    DirectSum.of (situ.sectionPieces U.1) 0
        (rS • situ.algebra.one.eval (op U.1)) *
      DirectSum.of (situ.sectionPieces U.1) n (q.symm ⟨a, ha⟩)
  rw [hq, DirectSum.of_mul_of]
  let M : ℤ → Type u := fun i => ((situ.algebra.piece i).val.obj (op U.1)).1
  have hidx : (0 : ℤ) + (n : ℤ) = (n : ℤ) := Int.zero_add _
  let e := situ.algebra.one.eval (op U.1)
  have honeHEq := situ.algebra.one_mul (n : ℤ) (op U.1) (q.symm ⟨a, ha⟩)
  let hTy := type_eq_of_heq honeHEq
  have honeCast : cast hTy ((situ.algebra.mul 0 (n : ℤ)).app (op U.1) e
      (q.symm ⟨a, ha⟩)) = q.symm ⟨a, ha⟩ := cast_heq_eq honeHEq
  have hpTy : hTy = congrArg M hidx := Subsingleton.elim _ _
  have hGMul := (Stacks.RelativeProj.Situation.sectionRingStructure situ).mul_homogeneous
    U.1 0 n (rS • e) (q.symm ⟨a, ha⟩)
  let hGMulTy := type_eq_of_heq hGMul.symm
  let hNatTy := congrArg (situ.sectionPieces U.1) (Nat.zero_add n)
  have hcoeff : rS • q.symm ⟨a, ha⟩ = cast hNatTy
      (GradedMonoid.GMul.mul (A := situ.sectionPieces U.1) (i := 0) (j := n)
        (rS • e) (q.symm ⟨a, ha⟩)) := by
    calc
      rS • q.symm ⟨a, ha⟩ = rS • cast hTy
          ((situ.algebra.mul 0 (n : ℤ)).app (op U.1) e (q.symm ⟨a, ha⟩)) := by
        rw [honeCast]
      _ = cast hTy (rS •
          (situ.algebra.mul 0 (n : ℤ)).app (op U.1) e (q.symm ⟨a, ha⟩)) := by
        simpa [hpTy] using (cast_smul_indexed M hidx rS
          ((situ.algebra.mul 0 (n : ℤ)).app (op U.1) e (q.symm ⟨a, ha⟩))).symm
      _ = cast hTy ((situ.algebra.mul 0 (n : ℤ)).app (op U.1) (rS • e)
          (q.symm ⟨a, ha⟩)) :=
        congrArg (cast hTy) ((situ.algebra.mul 0 (n : ℤ)).map_smul_left
          (op U.1) rS e (q.symm ⟨a, ha⟩)).symm
      _ = cast hNatTy (cast hGMulTy ((situ.algebra.mul 0 (n : ℤ)).app (op U.1) (rS • e)
          (q.symm ⟨a, ha⟩))) := by
        rw [show hTy = hGMulTy.trans hNatTy from Subsingleton.elim _ _]
        simp
      _ = cast hNatTy (GradedMonoid.GMul.mul (A := situ.sectionPieces U.1)
          (i := 0) (j := n) (rS • e) (q.symm ⟨a, ha⟩)) :=
        congrArg (cast hNatTy) (cast_heq_eq hGMul.symm)
  have hSigma : GradedMonoid.mk n (rS • q.symm ⟨a, ha⟩) =
      GradedMonoid.mk (0 + n) (GradedMonoid.GMul.mul
        (A := situ.sectionPieces U.1) (i := 0) (j := n)
        (rS • e) (q.symm ⟨a, ha⟩)) :=
    Sigma.ext (Nat.zero_add n).symm ((heq_of_eq hcoeff).trans (cast_heq _ _))
  exact DirectSum.of_eq_of_gradedMonoid_eq hSigma

private theorem reesLift_mul : ∀ (n m : ℕ) (a b : X.presheaf.obj (op U.1))
    (ha : a ∈ I.ideal U ^ n) (hb : b ∈ I.ideal U ^ m),
    reesLift I U (n + m) (a * b) (mul_mem_pow_add ha hb) =
      reesLift I U n a ha * reesLift I U m b hb := by
  let situ := AlgebraicGeometry.reesSituation I
  let data := AlgebraicGeometry.reesAlgebraData I
  let R := X.presheaf.obj (op U.1)
  intro n m a b ha hb
  let qn := data.pieceEquiv (n : ℤ) (by omega) U
  let qm := data.pieceEquiv (m : ℤ) (by omega) U
  let qnm := data.pieceEquiv ((n + m : ℕ) : ℤ) (by omega) U
  change DirectSum.of (situ.sectionPieces U.1) (n + m)
      (qnm.symm ⟨a * b, _⟩) =
    DirectSum.of (situ.sectionPieces U.1) n (qn.symm ⟨a, ha⟩) *
      DirectSum.of (situ.sectionPieces U.1) m (qm.symm ⟨b, hb⟩)
  rw [DirectSum.of_mul_of]
  apply congrArg (DirectSum.of (situ.sectionPieces U.1) (n + m))
  apply qnm.injective
  have hmul := data.pieceEquiv_mul (n : ℤ) (m : ℤ) (by omega) (by omega) U
    (qn.symm ⟨a, ha⟩) (qm.symm ⟨b, hb⟩)
  have hGMul := (Stacks.RelativeProj.Situation.sectionRingStructure situ).mul_homogeneous
    U.1 n m (qn.symm ⟨a, ha⟩) (qm.symm ⟨b, hb⟩)
  let M : ℤ → Type u := fun i => ((situ.algebra.piece i).val.obj (op U.1)).1
  have hidx : ((n + m : ℕ) : ℤ) = (n : ℤ) + (m : ℤ) := Int.natCast_add _ _
  let hTy : M ((n + m : ℕ) : ℤ) = M ((n : ℤ) + (m : ℤ)) := congrArg M hidx
  have hGMulCast : cast hTy (GradedMonoid.GMul.mul
      (A := situ.sectionPieces U.1) (i := n) (j := m)
      (qn.symm ⟨a, ha⟩) (qm.symm ⟨b, hb⟩)) =
      (situ.algebra.mul (n : ℤ) (m : ℤ)).app (op U.1)
        (qn.symm ⟨a, ha⟩) (qm.symm ⟨b, hb⟩) := by
    have hp : type_eq_of_heq hGMul = hTy := Subsingleton.elim _ _
    simpa [hp] using cast_heq_eq hGMul
  let qnmInt := data.pieceEquiv ((n : ℤ) + (m : ℤ)) (by omega) U
  apply Subtype.ext
  have hqnmCast : (qnmInt (cast hTy (GradedMonoid.GMul.mul
      (A := situ.sectionPieces U.1) (i := n) (j := m)
      (qn.symm ⟨a, ha⟩) (qm.symm ⟨b, hb⟩))) : R) =
      (qnm (GradedMonoid.GMul.mul (A := situ.sectionPieces U.1) (i := n) (j := m)
        (qn.symm ⟨a, ha⟩) (qm.symm ⟨b, hb⟩)) : R) := by
    simp [qnm, qnmInt, Int.natCast_add]
  have hcoeff : (qnmInt ((situ.algebra.mul (n : ℤ) (m : ℤ)).app (op U.1)
      (qn.symm ⟨a, ha⟩) (qm.symm ⟨b, hb⟩)) : R) = a * b := by
    simpa [qn, qm, qnmInt] using hmul
  simpa using (hqnmCast.symm.trans
    ((congrArg (fun z => (qnmInt z : R)) hGMulCast).trans hcoeff)).symm

/-- The degree-one homogeneous section of the Rees algebra attached to a chosen generator of
`I(U)`. -/
private noncomputable def reesGen (s : Finset (X.presheaf.obj (op U.1)))
    (hJ : I.ideal U = Ideal.span (s : Set (X.presheaf.obj (op U.1)))) (z : ↥s) :
    (AlgebraicGeometry.reesSituation I).sectionRing U.1 :=
  reesLift I U 1 z.1 (by rw [pow_one, hJ]; exact Ideal.subset_span z.2)

private theorem reesGen_mem_degree_one (s : Finset (X.presheaf.obj (op U.1)))
    (hJ : I.ideal U = Ideal.span (s : Set (X.presheaf.obj (op U.1)))) (z : ↥s) :
    reesGen I U s hJ z ∈ (AlgebraicGeometry.reesSituation I).sectionRingGrading U.1 1 :=
  ⟨((AlgebraicGeometry.reesAlgebraData I).pieceEquiv 1 (by omega) U).symm ⟨z.1, by
    have hmem : (z : X.presheaf.obj (op U.1)) ∈ I.ideal U := by
      rw [hJ]
      exact Ideal.subset_span z.2
    simpa using hmem⟩, rfl⟩

/-- The irrelevant ideal of the section ring of the Rees algebra over `U` is contained in the
ideal generated by the degree-one sections attached to a generating set of `I(U)`. -/
private theorem irrelevant_le_span_reesGen (s : Finset (X.presheaf.obj (op U.1)))
    (hJ : I.ideal U = Ideal.span (s : Set (X.presheaf.obj (op U.1)))) :
    (HomogeneousIdeal.irrelevant
        ((AlgebraicGeometry.reesSituation I).sectionRingGrading U.1)).toIdeal ≤
      Ideal.span (Set.range (reesGen I U s hJ)) := by
  classical
  let situ := AlgebraicGeometry.reesSituation I
  let data := AlgebraicGeometry.reesAlgebraData I
  let R := X.presheaf.obj (op U.1)
  let J : Ideal R := I.ideal U
  let P := situ.sectionRingGrading U.1
  let lift := reesLift I U
  let g := reesGen I U s hJ
  have hG : ∀ b (hb : b ∈ (s : Set R)),
      lift 1 b (by rw [pow_one, hJ]; exact Ideal.subset_span hb) = g ⟨b, hb⟩ :=
    fun _ _ => rfl
  have hpositive : ∀ n (hn : 0 < n) (z : situ.sectionRing U.1),
      z ∈ P n → z ∈ Ideal.span (Set.range g) := by
    intro n hn z hz
    rcases hz with ⟨v, rfl⟩
    let hcoeff := data.pieceEquiv (n : ℤ) (by omega) U v
    have h := pow_span_lift J s hJ (situ.sectionRingBaseMap U.1) lift
      (reesLift_zero I U) (reesLift_add I U) (reesLift_smul I U) (reesLift_mul I U)
      g hG hn hcoeff.property
    have hEq : lift n hcoeff hcoeff.property = DirectSum.of (situ.sectionPieces U.1) n v := by
      have hv : (data.pieceEquiv (n : ℤ) (by omega) U).symm
          ⟨(hcoeff : X.presheaf.obj (op U.1)), by simp⟩ = v := by
        rw [Subtype.coe_eta]
        exact (data.pieceEquiv (n : ℤ) (by omega) U).symm_apply_apply v
      exact congrArg (DirectSum.of (situ.sectionPieces U.1) n) hv
    exact hEq ▸ h
  rw [HomogeneousIdeal.irrelevant_eq_span]
  refine Ideal.span_le.mpr fun z hz ↦ ?_
  obtain ⟨n, hn, hzn⟩ := Set.mem_iUnion₂.mp hz
  exact hpositive n hn z hzn

end ReesLift

/-! ### Vanishing above degree one for a cover by two affine opens

This section proves the case of [Stacks, Tag 01XI] used below: a scheme with affine diagonal
covered by two affine opens has no quasi-coherent cohomology in degrees at least two.

The argument is Mayer--Vietoris. Writing `restrictPush O W` for restriction to `W` followed by
pushforward back, the short complex of endofunctors of `Mod(O)`

`0 ⟶ id ⟶ restrictPush U ⊞ restrictPush V ⟶ restrictPush (U ⊓ V) ⟶ 0`

is short exact at every injective sheaf of modules. Composing with global sections keeps that
property, because a short exact sequence with injective first term splits and a split short
exact sequence survives every additive functor; so the long exact sequence of right derived
functors applies and gives

`⋯ ⟶ Hⁿ⁻¹(U ⊓ V, F) ⟶ Hⁿ(X, F) ⟶ Hⁿ(U, F) ⊕ Hⁿ(V, F) ⟶ ⋯`.

For `n ≥ 2` the two neighbours vanish by Serre vanishing on the affines `U ⊓ V`, `U` and `V`,
which is [Stacks, Tag 01XB], hence so does the middle.
-/

section MayerVietorisTwoAffineCover

open Stacks.Cohomology Stacks.Cohomology.RestrictionCover

section Cover

variable {Y : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

/-- Global sections of the restriction of a module to the open `W`, as a functor.  It is
definitionally `Γ(W, -)` up to rewriting the open `(openIntersection W).obj ⊤` to `W`. -/
private noncomputable abbrev secOpen (W : Opens Y) := restrictPush O W ⋙ secF O ⊤

/-- Global sections of the middle term of the Mayer--Vietoris short complex of functors. -/
private noncomputable abbrev secMiddle (U V : Opens Y) := restrictionCoverMiddle O U V ⋙ secF O ⊤

variable (U V : Opens Y)

/-- Right derived functors of `secOpen O W` compute `Hⁿ(W, -)`: a vanishing statement for the
cohomology of `W` is literally a vanishing statement for `secOpen O W`. -/
private theorem isZero_rightDerived_secOpen (W : Opens Y) (n : ℕ) (M : SheafOfModules.{u} O)
    (h : IsZero (Hgroup O W n M)) : IsZero (((secOpen O W).rightDerived n).obj M) := by
  have h' : IsZero (Hgroup O ((openIntersection W).obj ⊤) n M) := by
    rwa [show (openIntersection W).obj ⊤ = W by simp [openIntersection]]
  exact h'

/-! ### The four structure maps of the middle term -/

/-- The first projection of the middle term of the Mayer--Vietoris short complex. -/
private noncomputable def middleFst : restrictionCoverMiddle O U V ⟶ restrictPush O U where
  app _ := biprod.fst
  naturality _ _ _ := by simp [restrictionCoverMiddle]

/-- The second projection of the middle term of the Mayer--Vietoris short complex. -/
private noncomputable def middleSnd : restrictionCoverMiddle O U V ⟶ restrictPush O V where
  app _ := biprod.snd
  naturality _ _ _ := by simp [restrictionCoverMiddle]

/-- The first inclusion into the middle term of the Mayer--Vietoris short complex. -/
private noncomputable def middleInl : restrictPush O U ⟶ restrictionCoverMiddle O U V where
  app _ := biprod.inl
  naturality _ _ _ := by simp [restrictionCoverMiddle]

/-- The second inclusion into the middle term of the Mayer--Vietoris short complex. -/
private noncomputable def middleInr : restrictPush O V ⟶ restrictionCoverMiddle O U V where
  app _ := biprod.inr
  naturality _ _ _ := by simp [restrictionCoverMiddle]

/-- The first projection of the middle term, after taking global sections. -/
private noncomputable def secMiddleFst : secMiddle O U V ⟶ secOpen O U :=
  Functor.whiskerRight (middleFst O U V) (secF O ⊤)

/-- The second projection of the middle term, after taking global sections. -/
private noncomputable def secMiddleSnd : secMiddle O U V ⟶ secOpen O V :=
  Functor.whiskerRight (middleSnd O U V) (secF O ⊤)

/-- The first inclusion into the middle term, after taking global sections. -/
private noncomputable def secMiddleInl : secOpen O U ⟶ secMiddle O U V :=
  Functor.whiskerRight (middleInl O U V) (secF O ⊤)

/-- The second inclusion into the middle term, after taking global sections. -/
private noncomputable def secMiddleInr : secOpen O V ⟶ secMiddle O U V :=
  Functor.whiskerRight (middleInr O U V) (secF O ⊤)

omit [EnoughInjectives (SheafOfModules.{u} O)] in
/-- The biproduct identity `fst ≫ inl + snd ≫ inr = 𝟙` for the middle term after taking
global sections: `Γ(⊤, -)` is additive, so it is the image of `Limits.biprod.total`. -/
private theorem secMiddle_total :
    secMiddleFst O U V ≫ secMiddleInl O U V + secMiddleSnd O U V ≫ secMiddleInr O U V =
      𝟙 (secMiddle O U V) := by
  refine NatTrans.ext (funext fun M => ?_)
  have h : ∀ A B : SheafOfModules.{u} O,
      (secF O ⊤).map (biprod.fst ≫ biprod.inl : A ⊞ B ⟶ A ⊞ B) +
          (secF O ⊤).map (biprod.snd ≫ biprod.inr : A ⊞ B ⟶ A ⊞ B) =
        𝟙 ((secF O ⊤).obj (A ⊞ B)) := by
    intro A B
    rw [← Functor.map_add, biprod.total]
    exact (secF O ⊤).map_id _
  exact h ((restrictPush O U).obj M) ((restrictPush O V).obj M)

/-- The biproduct identity of `secMiddle_total`, transported through right derivation. -/
private theorem rightDerived_secMiddle_total (n : ℕ) :
    NatTrans.rightDerived (secMiddleFst O U V) n ≫
          NatTrans.rightDerived (secMiddleInl O U V) n +
        NatTrans.rightDerived (secMiddleSnd O U V) n ≫
          NatTrans.rightDerived (secMiddleInr O U V) n =
      𝟙 ((secMiddle O U V).rightDerived n) := by
  rw [← NatTrans.rightDerived_comp, ← NatTrans.rightDerived_comp, ← NatTrans.rightDerived_add,
    secMiddle_total, NatTrans.rightDerived_id]

/-- **The middle term of the Mayer--Vietoris sequence vanishes when both cohomology groups
do.**  Both summands of the derived biproduct identity factor through a zero object, so the
identity of the middle term is zero. -/
private theorem isZero_rightDerived_secMiddle (n : ℕ) (M : SheafOfModules.{u} O)
    (hU : IsZero (Hgroup O U n M)) (hV : IsZero (Hgroup O V n M)) :
    IsZero (((secMiddle O U V).rightDerived n).obj M) := by
  have ht := congrArg (fun t : (secMiddle O U V).rightDerived n ⟶ _ => t.app M)
    (rightDerived_secMiddle_total O U V n)
  simp only [NatTrans.app_add, NatTrans.comp_app, NatTrans.id_app] at ht
  rw [(isZero_rightDerived_secOpen O U n M hU).eq_zero_of_src
      ((NatTrans.rightDerived (secMiddleInl O U V) n).app M),
    (isZero_rightDerived_secOpen O V n M hV).eq_zero_of_src
      ((NatTrans.rightDerived (secMiddleInr O U V) n).app M),
    comp_zero, comp_zero, add_zero] at ht
  exact (IsZero.iff_id_eq_zero _).mpr ht.symm

/-! ### The short complex of functors after taking global sections -/

/-- The first map of the Mayer--Vietoris short complex of functors, after taking global
sections: restriction of a section over `X` to `U` and to `V`. -/
private noncomputable def secFirst : secF O ⊤ ⟶ secMiddle O U V :=
  Functor.whiskerRight (restrictionCoverFirst O U V) (secF O ⊤)

/-- The second map of the Mayer--Vietoris short complex of functors, after taking global
sections: the difference of the two restrictions to `U ⊓ V`. -/
private noncomputable def secSecond : secMiddle O U V ⟶ secOpen O (U ⊓ V) :=
  Functor.whiskerRight (restrictionCoverSecond O U V) (secF O ⊤)

omit [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)] in
/-- The two maps of the short complex compose to zero, being the image of a composite which
already vanishes before taking sections. -/
private theorem secFirst_comp_second : secFirst O U V ≫ secSecond O U V = 0 := by
  refine NatTrans.ext (funext fun M => ?_)
  have h0 : (restrictionCoverFirst O U V).app M ≫ (restrictionCoverSecond O U V).app M = 0 := by
    simpa using NatTrans.congr_app (restrictionCoverFirst_comp_second O U V) M
  have h : (secF O ⊤).map ((restrictionCoverFirst O U V).app M) ≫
      (secF O ⊤).map ((restrictionCoverSecond O U V).app M) = 0 := by
    rw [← Functor.map_comp, h0, Functor.map_zero]
  exact h

omit [EnoughInjectives (SheafOfModules.{u} O)] in
/-- **The short complex of functors is short exact at every injective sheaf of modules.**  The
sequence of sheaves of modules has an injective first term, hence splits, and a split short
exact sequence stays short exact after applying the additive functor `Γ(⊤, -)`. -/
private theorem sec_shortExact_on_injectives (hUV : U ⊔ V = ⊤) (M : SheafOfModules.{u} O)
    (hM : Injective M) :
    (NatTrans.appShortComplex (secFirst O U V) (secSecond O U V)
      (secFirst_comp_second O U V) M).ShortExact := by
  let S : ShortComplex (SheafOfModules.{u} O) :=
    ShortComplex.mk ((restrictionCoverFirst O U V).app M)
      ((restrictionCoverSecond O U V).app M)
      (NatTrans.congr_app (restrictionCoverFirst_comp_second O U V) M)
  have hS : S.ShortExact := restrictionCoverShortExact_object O U V hUV M
  have : Mono S.f := hS.mono_f
  have : Injective S.X₁ := hM
  let sp : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hS.exact
    (Injective.factorThru (𝟙 S.X₁) S.f) (Injective.comp_factorThru _ _) hS.epi_g
  exact (sp.map (secF O ⊤)).shortExact

/-- **The Mayer--Vietoris vanishing step.**  If `U` and `V` cover the space, the cohomology of
`U` and of `V` vanishes in degree `n + 1` and the cohomology of `U ⊓ V` vanishes in degree `n`,
then the cohomology of the whole space vanishes in degree `n + 1`. -/
private theorem isZero_hgroup_top_of_cover (hUV : U ⊔ V = ⊤) (M : SheafOfModules.{u} O) (n : ℕ)
    (hU : IsZero (Hgroup O U (n + 1) M)) (hV : IsZero (Hgroup O V (n + 1) M))
    (hUV' : IsZero (Hgroup O (U ⊓ V) n M)) :
    IsZero (Hgroup O ⊤ (n + 1) M) := by
  obtain ⟨delta, -, hexact⟩ :=
    longExact_rightDerived_of_shortExact_on_injectives (secFirst O U V) (secSecond O U V)
      (secFirst_comp_second O U V) (sec_shortExact_on_injectives O U V hUV)
  have h5 := hexact n M
  have hz : (delta n).app M ≫ (NatTrans.rightDerived (secFirst O U V) (n + 1)).app M = 0 :=
    h5.toIsComplex.zero' 2 3 4
  have hex : (ShortComplex.mk ((delta n).app M)
      ((NatTrans.rightDerived (secFirst O U V) (n + 1)).app M) hz).Exact := h5.exact 2
  exact hex.isZero_of_both_isZero (isZero_rightDerived_secOpen O (U ⊓ V) n M hUV')
    (isZero_rightDerived_secMiddle O U V (n + 1) M hU hV)

end Cover

/-- **Stacks 01XI for `t = 2`.**  Let `X` be a scheme with affine diagonal which is covered by
two affine opens, and let `F` be a quasi-coherent `𝒪_X`-module.  Then `Hⁿ(X, F) = 0` for every
`n ≥ 2`. -/
private theorem isZero_rightDerived_sections_of_two_affine_cover (X : Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : Fin 2 → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hUcover : ⨆ i, U i = ⊤)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (op (⊤ : X.Opens))).rightDerived n).obj F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsup : U 0 ⊔ U 1 = ⊤ := by
    rw [← hUcover]
    refine le_antisymm (sup_le (le_iSup U 0) (le_iSup U 1)) (iSup_le ?_)
    rw [Fin.forall_fin_two]
    exact ⟨le_sup_left, le_sup_right⟩
  exact isZero_hgroup_top_of_cover X.ringCatSheaf (U 0) (U 1) hsup F m
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F (U 0) (hU 0) (m + 1)
      (Nat.succ_pos m))
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F (U 1) (hU 1) (m + 1)
      (Nat.succ_pos m))
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F (U 0 ⊓ U 1)
      ((hU 0).inf (hU 1)) m (by omega))

end MayerVietorisTwoAffineCover

/-- If the ideal `I` of an affine scheme `X` is generated over the top open by two elements,
then the blowup of `X` in `I` is covered by two affine opens, so it has no quasi-coherent
cohomology in degrees at least two.

The blowup is the ordinary `Proj` of the Rees algebra of `I(X)`, because `X` is affine and the
chart over the top affine open is therefore the whole blowup. The two degree-one sections
attached to the generators span the irrelevant ideal, so their standard opens cover that `Proj`
and are affine. -/
private theorem isZero_rightDerived_blowUp_of_two_generators {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (s : Finset (X.presheaf.obj (op (⊤ : X.Opens))))
    (hJ : I.ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.span (s : Set (X.presheaf.obj (op (⊤ : X.Opens)))))
    (e : Fin 2 ≃ ↥s) (F : (AlgebraicGeometry.blowUp I).Modules) [F.IsQuasicoherent]
    (p : ℕ) (hp : 2 ≤ p) :
    IsZero (((SheafOfModules.toSheaf (AlgebraicGeometry.blowUp I).ringCatSheaf ⋙
      (sheafSections (Opens.grothendieckTopology (AlgebraicGeometry.blowUp I))
          AddCommGrpCat).obj
        (op (⊤ : (AlgebraicGeometry.blowUp I).Opens))).rightDerived p).obj F) := by
  classical
  let situ : Stacks.RelativeProj.Situation := AlgebraicGeometry.reesSituation I
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let P := situ.sectionRingGrading U.1
  let g : ↥s → situ.sectionRing U.1 := reesGen I U s hJ
  let f : Fin 2 → situ.sectionRing U.1 := fun i => g (e i)
  let sProj : Finset (situ.sectionRing U.1) := Finset.univ.image f
  have hfRange : Set.range f = (sProj : Set (situ.sectionRing U.1)) := by
    ext z
    simp [sProj]
  have hrangeGen : Set.range f = Set.range g := e.surjective.range_comp g
  have hspanProj : (HomogeneousIdeal.irrelevant P).toIdeal ≤
      Ideal.span (sProj : Set (situ.sectionRing U.1)) := by
    rw [← hfRange, hrangeGen]
    exact irrelevant_le_span_reesGen I U s hJ
  have hcoverP : (⨆ i : Fin 2, Proj.basicOpen P (f i)) = ⊤ := by
    apply top_unique
    intro x hx
    have hx' : x ∈ ⨆ z, ⨆ (_ : z ∈ sProj), Proj.basicOpen P z := by
      rw [AlgebraicGeometry.Proj.iSup_basicOpen_eq_top_of_irrelevant_le_radical P sProj
        (hspanProj.trans Ideal.le_radical)]
      simp
    rcases Opens.mem_iSup.mp hx' with ⟨z, hz⟩
    rcases Opens.mem_iSup.mp hz with ⟨hzS, hxz⟩
    rcases Finset.mem_image.mp hzS with ⟨i, -, rfl⟩
    exact Opens.mem_iSup.mpr ⟨i, hxz⟩
  have : IsIso U.1.ι := by
    change IsIso ((⊤ : X.Opens).ι)
    rw [← Scheme.topIso_hom]
    infer_instance
  have : IsIso (situ.relativeProjChart U) :=
    (situ.relativeProjChart_isPullback U).isIso_fst_of_isIso
  let chartIso : (AlgebraicGeometry.Proj P) ≅ AlgebraicGeometry.blowUp I :=
    asIso (situ.relativeProjChart U)
  have : (AlgebraicGeometry.Proj P).IsSeparated := inferInstance
  have : (AlgebraicGeometry.blowUp I).IsSeparated := by
    have hsep' := MorphismProperty.RespectsIso.precomp (P := @IsSeparated)
      chartIso.inv (terminal.from (AlgebraicGeometry.Proj P)) inferInstance
    exact ⟨by simpa using hsep'⟩
  have : IsAffineHom (pullback.diagonal (terminal.from (AlgebraicGeometry.blowUp I))) :=
    inferInstance
  let cover : Fin 2 → (AlgebraicGeometry.blowUp I).Opens := fun i =>
    chartIso.inv ⁻¹ᵁ (Proj.basicOpen P (f i))
  have hcover : ⨆ i : Fin 2, cover i = ⊤ := by
    rw [← chartIso.inv.preimage_iSup, hcoverP]
    simp
  refine isZero_rightDerived_sections_of_two_affine_cover
      (AlgebraicGeometry.blowUp I) cover (fun i => ?_) hcover F p hp
  exact (Proj.isAffineOpen_basicOpen P (f i) (reesGen_mem_degree_one I U s hJ (e i))
    (by omega)).preimage_of_isIso chartIso.inv

/-- The maximal ideal of a two-dimensional regular local ring, transported to the global
functions on its spectrum, is generated by two elements. -/
private theorem exists_two_generators_of_regular_dim_two (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    ∃ (s : Finset ((Spec (CommRingCat.of A)).presheaf.obj
        (op (⊤ : (Spec (CommRingCat.of A)).Opens))))
      (_ : (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
            (IsLocalRing.maximalIdeal A))).ideal
          ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ = Ideal.span (s : Set _)),
      Nonempty (Fin 2 ≃ ↥s) := by
  classical
  let X : Scheme := Spec (CommRingCat.of A)
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let R := X.presheaf.obj (op U.1)
  let I : X.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (IsLocalRing.maximalIdeal A))
  obtain ⟨sA, hsAcard, hsAspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  have hdimGen : (IsLocalRing.maximalIdeal A).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  let φEquiv : A ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let φ : A →+* R := φEquiv
  let s : Finset R := sA.image φ
  have hJ : I.ideal U = Ideal.span (s : Set R) := by
    have hφ : φ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
      ext a
      rfl
    have hIdeal : I.ideal U = Ideal.map φ (IsLocalRing.maximalIdeal A) := by
      rw [hφ]
      simp [I, U, Scheme.IdealSheafData.ofIdealTop_ideal]
    rw [hIdeal, ← hsAspan, Ideal.map_span]
    change Ideal.span (φ '' (sA : Set A)) = Ideal.span (s : Set R)
    congr 1
    ext a
    simp [s]
  have hcard : s.card = 2 :=
    (Finset.card_image_of_injective sA φEquiv.injective).trans (hsAcard.trans hdimGen)
  exact ⟨s, hJ, ⟨(Fintype.equivFinOfCardEq (by simpa using hcard)).symm⟩⟩

/-- **Stacks Project, Tag 0AGS.** Quasi-coherent cohomology of the blowup of a two-dimensional
regular local ring at its closed point vanishes in degrees at least two. -/
@[stacks 0AGS "higher_cohomology_vanishes"]
public theorem isZero_cohomology_of_two_le
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2)
    (F : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
          (IsLocalRing.maximalIdeal A)))).Modules)
    [F.IsQuasicoherent] (p : ℕ) (hp : 2 ≤ p) :
    IsZero (((SheafOfModules.toSheaf
      (AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
            (IsLocalRing.maximalIdeal A)))).ringCatSheaf ⋙
        (sheafSections
          (Opens.grothendieckTopology
            (AlgebraicGeometry.blowUp
              (Scheme.IdealSheafData.ofIdealTop
                (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
                  (IsLocalRing.maximalIdeal A)))))
          AddCommGrpCat).obj (op (⊤ :
          (AlgebraicGeometry.blowUp
              (Scheme.IdealSheafData.ofIdealTop
                (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
                  (IsLocalRing.maximalIdeal A)))).Opens))).rightDerived p).obj F) := by
  have H := exists_two_generators_of_regular_dim_two A hdim
  obtain ⟨s, hJ, ⟨e⟩⟩ := H
  exact isZero_rightDerived_blowUp_of_two_generators _ s hJ e F p hp

end AlgebraicGeometry

end
