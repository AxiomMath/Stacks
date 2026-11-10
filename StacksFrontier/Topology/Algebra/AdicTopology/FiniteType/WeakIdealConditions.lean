module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Defs.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Nilpotent.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.QuotientDiagram
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType.RestrictedPowerSeries

/-!
# Algebras topologically of finite type: implications between the conditions

This file proves the implications between the characterisations of algebras topologically of
finite type that do not construct a restricted-power-series presentation: a presentation gives
tautness and finite type modulo every weak ideal of definition, finite type modulo every weak
ideal of definition is equivalent to topological finite type, and it is equivalent to finite
type modulo a cofinal family.

## Implementation notes

`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal` proves that
finite type modulo every weak ideal of definition implies topological finite type by the
argument of Stacks 0ANT, which needs nothing of the source beyond a single weak ideal of
definition: generators of `S ⧸ J(I)` over `R ⧸ I` are lifted to `b₁, …, b_r ∈ S`, and for a
smaller weak ideal of definition `I' ⊆ I` the identity `S ⧸ (J(I') + I S) = S ⧸ J(I)` — which
holds because `J(I)` is the closure of `I S` and `J(I')` is open — lets Stacks 07RD upgrade
surjectivity of `(R ⧸ I')[x] → S ⧸ J(I)` to surjectivity of `(R ⧸ I')[x] → S ⧸ J(I')`. Since
the ideals `J(I')` form a neighbourhood basis of zero, the map `R[x₁, …, x_r] → S` has dense
image.

## References

* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 07RD](https://stacks.math.columbia.edu/tag/07RD)
-/

@[expose] public section

namespace TopologicalRing

section

open Filter

universe u v w

variable {B : Type u} {A : Type v}
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- The image of an ideal of topologically nilpotent elements in the quotient by an open ideal
is locally nilpotent. -/
private theorem isLocallyNilpotent_map_mk_of_isTopologicallyNilpotent
    {R : Type*} [CommRing R] [TopologicalSpace R] (I I' : Ideal R) (hI' : IsOpen (I' : Set R))
    (h : ∀ a ∈ I, IsTopologicallyNilpotent a) :
    (I.map (Ideal.Quotient.mk I')).IsLocallyNilpotent := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective _
    Ideal.Quotient.mk_surjective hx
  obtain ⟨k, hk⟩ := eventually_atTop.mp ((h a ha).eventually (hI'.mem_nhds I'.zero_mem))
  exact ⟨k, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hk k le_rfl)⟩

/-- If the sets of a neighbourhood basis of zero each contain an element `x - f y` for every `x`,
then `f` has dense range. -/
private theorem denseRange_of_forall_sub_mem {S X : Type*} [CommRing S] [TopologicalSpace S]
    [IsTopologicalRing S] {ι : Sort*} {p : ι → Prop} {s : ι → Set S}
    (hs : (nhds (0 : S)).HasBasis p s) (f : X → S) (h : ∀ x i, p i → ∃ y, x - f y ∈ s i) :
    DenseRange f := fun x ↦ mem_closure_iff.mpr fun U hUopen hxU ↦ by
  have hpre : (fun y : S ↦ x - y) ⁻¹' U ∈ nhds (0 : S) :=
    ((continuous_const.sub continuous_id).continuousAt (x := (0 : S))).preimage_mem_nhds
      (by simpa using hUopen.mem_nhds hxU)
  obtain ⟨i, hi, hsub⟩ := hs.mem_iff.mp hpre
  obtain ⟨y, hy⟩ := h x i hi
  exact ⟨f y, by simpa using hsub hy, y, rfl⟩

omit [IsTopologicalRing B] [IsLinearTopology B B] [IsLinearTopology A A] in
private theorem taut_of_presentation (φ : B →+* A) :
    HasRestrictedPowerSeriesPresentation φ → RingHom.IsTaut φ := by
  rintro ⟨n, K, hKclosed, e, he, he_symm, hcompat⟩
  let P := MvPolynomial (Fin n) B
  let R := RestrictedPowerSeries B (Fin n)
  let Q := R ⧸ K
  let : UniformSpace P := restrictedPolynomialUniformSpace B (Fin n)
  let : TopologicalSpace P := restrictedPolynomialTopology B (Fin n)
  let p : P →+* R := polynomialToRestrictedPowerSeries B (Fin n)
  let q : R →+* Q := Ideal.Quotient.mk K
  let c : B →+* R := coeffToRestrictedPowerSeries B (Fin n)
  let ψ : B →+* Q := q.comp c
  let eH : Q ≃ₜ A :=
    { toEquiv := e
      continuous_toFun := he
      continuous_invFun := he_symm }
  have hcompat' : e.toRingHom.comp ψ = φ := by
    simpa [ψ, q, c] using hcompat
  let idx := { J : Ideal B // IsOpen (J : Set B) }
  let L : idx → Ideal R := fun J =>
    Ideal.closure (Ideal.map p (J.1.map (MvPolynomial.C : B →+* P)))
  let M : idx → Ideal Q := fun J => Ideal.map q (L J)
  have hLset (J : idx) : (L J : Set R) =
      closure ((p : P → R) '' (J.1.map (MvPolynomial.C : B →+* P) : Set P)) :=
    idealClosure_map_eq_closure_image_of_denseRange p
      UniformSpace.Completion.denseRange_coe (J.1.map (MvPolynomial.C : B →+* P))
  have hLmem (J : idx) : (L J : Set R) ∈ nhds (0 : R) := by
    rw [hLset J]
    exact (restrictedPowerSeries_nhds_hasBasis B (Fin n)).mem_of_mem (show True from trivial)
  have hLopen (J : idx) : IsOpen (L J : Set R) :=
    (L J).toAddSubgroup.isOpen_of_mem_nhds (g := (0 : R)) (by simpa using hLmem J)
  have hMset (J : idx) : (M J : Set Q) = q '' (L J : Set R) := by
    change (Ideal.map q (L J) : Set Q) = q '' (L J : Set R)
    exact Ideal.map_eq_image_of_surjective q (fun x => Ideal.Quotient.mk_surjective x)
  have hMopen (J : idx) : IsOpen (M J : Set Q) := by
    rw [hMset J]
    exact (QuotientRing.isOpenMap_coe K) _ (hLopen J)
  have hMclosed (J : idx) : IsClosed (M J : Set Q) :=
    (M J).toAddSubgroup.isClosed_of_isOpen (hMopen J)
  have hM_eq (J : idx) : closure (Ideal.map ψ J.1 : Set Q) = (M J : Set Q) := by
    have hNle : Ideal.map ψ J.1 ≤ M J := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro b hb
      have hCb : MvPolynomial.C b ∈ J.1.map (MvPolynomial.C : B →+* P) :=
        Ideal.mem_map_of_mem _ hb
      have hc : c b ∈ L J := subset_closure (Ideal.mem_map_of_mem p hCb)
      change q (c b) ∈ M J
      exact Ideal.mem_map_of_mem q hc
    have hmapIdeals : (J.1.map (MvPolynomial.C : B →+* P)).map (q.comp p) =
        J.1.map ψ := by
      rw [Ideal.map_map]
      congr 1
    have hmaps : Set.MapsTo (q : R → Q)
        (p '' (J.1.map (MvPolynomial.C : B →+* P) : Set P))
        (Ideal.map ψ J.1 : Set Q) := by
      rintro y ⟨x, hx, rfl⟩
      have hy : q (p x) ∈
          (J.1.map (MvPolynomial.C : B →+* P)).map (q.comp p) :=
        Ideal.mem_map_of_mem (q.comp p) hx
      rw [hmapIdeals] at hy
      exact hy
    have hsub : (M J : Set Q) ⊆ closure (Ideal.map ψ J.1 : Set Q) := by
      rw [hMset J]
      rintro y ⟨x, hx, rfl⟩
      rw [hLset J] at hx
      exact map_mem_closure continuous_quot_mk hx hmaps
    exact (closure_minimal hNle (hMclosed J)).antisymm hsub
  have hφmap (J : idx) : J.1.map φ = (J.1.map ψ).map e.toRingHom := by
    rw [← hcompat', Ideal.map_map]
  have hIset (J : idx) :
      (Ideal.closure (J.1.map φ) : Set A) = eH '' (M J : Set Q) := by
    rw [Ideal.coe_closure, hφmap]
    rw [show (Ideal.map e.toRingHom (J.1.map ψ) : Set A) =
        eH '' (Ideal.map ψ J.1 : Set Q) by
          rw [Ideal.map_eq_image_of_surjective e.toRingHom e.surjective]
          rfl]
    rw [← eH.image_closure, hM_eq J]
  have hQbasis : (nhds (0 : Q)).HasBasis (fun J : idx => True)
      (fun J => (M J : Set Q)) := by
    have hq := QuotientRing.isOpenQuotientMap_mk K
    rw [← map_zero q, ← hq.map_nhds_eq (0 : R)]
    refine ((restrictedPowerSeries_nhds_hasBasis B (Fin n)).map q).congr (fun _ => Iff.rfl)
      fun J _ => ?_
    rw [hMset J, hLset J]
  have hABasis' : (nhds (0 : A)).HasBasis (fun J : idx => True)
      (fun J => eH '' (M J : Set Q)) := by
    have hz : eH (0 : Q) = (0 : A) := by
      change e 0 = 0
      simp
    rw [← hz, ← eH.map_nhds_eq (0 : Q)]
    exact hQbasis.map eH
  have hABasis : (nhds (0 : A)).HasBasis
      (fun J : Ideal B => IsOpen (J : Set B))
      (fun J : Ideal B => ((Ideal.closure (J.map φ) : Ideal A) : Set A)) := by
    refine ⟨?_⟩
    intro U
    constructor
    · intro hU
      obtain ⟨J, hJ, hJU⟩ := hABasis'.mem_iff.mp hU
      exact ⟨J.1, J.2, hIset J ▸ hJU⟩
    · rintro ⟨J, hJ, hJU⟩
      exact hABasis'.mem_iff.mpr ⟨⟨J, hJ⟩, trivial, (hIset ⟨J, hJ⟩).symm ▸ hJU⟩
  refine ⟨fun J hJ => ?_, hABasis⟩
  rw [hIset ⟨J, hJ⟩]
  exact eH.isOpenMap _ (hMopen ⟨J, hJ⟩)

/-- A taut homomorphism of linearly topologized rings whose source is weakly pre-admissible
and which is of finite type modulo every weak ideal of definition is topologically of finite
type: condition (a) of **Stacks 0ANU** implies condition (2) of **Stacks 0ANT**.

It needs no countability assumption, and no completeness or separatedness either: weak
pre-admissibility of the source alone suffices.  This is the converse of
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType` below, so the
two conditions are equivalent outright and `TopologicalRing.finiteType_tfae` is not the only
route between them. -/
theorem isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal'
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {S : Type v} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →+* S) (hR : IsWeaklyPreAdmissible R)
    (h : FiniteTypeModuloEveryWeakIdeal φ) :
    IsTopologicallyOfFiniteType φ := by
  classical
  obtain ⟨htaut, hft⟩ := h
  obtain ⟨I, hI⟩ := hR
  -- Generators of `S ⧸ J(I)` over `R ⧸ I`, lifted to elements `b i` of `S`.
  let _ : Algebra (R ⧸ I) (S ⧸ Ideal.closure (I.map φ)) :=
    (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
      (Ideal.map_le_iff_le_comap.mp subset_closure)).toAlgebra
  obtain ⟨r, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (RingHom.finiteType_algebraMap.mp (hft I hI))
  choose b hb using fun i : Fin r ↦
    Ideal.Quotient.mk_surjective (I := Ideal.closure (I.map φ)) (g (MvPolynomial.X i))
  let Φ : MvPolynomial (Fin r) R →+* S := MvPolynomial.eval₂Hom φ b
  -- `R[x₁, …, x_r] → S ⧸ J(I)` is surjective.
  have hsurjI : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.closure (I.map φ))).comp Φ) := by
    have hring : (Ideal.Quotient.mk (Ideal.closure (I.map φ))).comp Φ =
        g.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk I)) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
      · have hcom := g.commutes (Ideal.Quotient.mk I a)
        rw [MvPolynomial.algebraMap_eq] at hcom
        simp only [RingHom.comp_apply, MvPolynomial.map_C, Φ, MvPolynomial.eval₂Hom_C]
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hcom]
        exact Ideal.quotientMap_mk.symm
      · simp only [RingHom.comp_apply, MvPolynomial.map_X, Φ, MvPolynomial.eval₂Hom_X',
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        exact hb i
    rw [hring]
    exact hg.comp (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  -- `R[x₁, …, x_r] → S ⧸ J(I')` is surjective for every weak ideal of definition `I' ⊆ I`.
  have key : ∀ I' : Ideal R, IsWeakIdealOfDefinition I' → I' ≤ I →
      Function.Surjective ((Ideal.Quotient.mk (Ideal.closure (I'.map φ))).comp Φ) := by
    intro I' hI' hle
    let _ : Algebra (R ⧸ I') (S ⧸ Ideal.closure (I'.map φ)) :=
      (Ideal.quotientMap (Ideal.closure (I'.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp subset_closure)).toAlgebra
    have hftR : Algebra.FiniteType (R ⧸ I') (S ⧸ Ideal.closure (I'.map φ)) :=
      RingHom.finiteType_algebraMap.mp (hft I' hI')
    let N : Ideal (R ⧸ I') := I.map (Ideal.Quotient.mk I')
    have hN : N.IsLocallyNilpotent :=
      isLocallyNilpotent_map_mk_of_isTopologicallyNilpotent I I' hI'.1 hI.2
    let fAlg : MvPolynomial (Fin r) (R ⧸ I') →ₐ[R ⧸ I'] S ⧸ Ideal.closure (I'.map φ) :=
      MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk (Ideal.closure (I'.map φ)) (b i))
    have hcomp : (Ideal.Quotient.mk (Ideal.closure (I'.map φ))).comp Φ =
        fAlg.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk I')) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C, Φ, MvPolynomial.eval₂Hom_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fAlg, MvPolynomial.aeval_C]
        exact Ideal.quotientMap_mk.symm
      · simp only [RingHom.comp_apply, MvPolynomial.map_X, Φ, MvPolynomial.eval₂Hom_X',
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fAlg, MvPolynomial.aeval_X]
    -- `J(I)` is contained in `J(I') + I S`, since the latter is open hence closed.
    have hsup : Ideal.closure (I.map φ) ≤ Ideal.closure (I'.map φ) ⊔ I.map φ := by
      have hopen : IsOpen ((Ideal.closure (I'.map φ) ⊔ I.map φ : Ideal S) : Set S) :=
        AddSubgroup.isOpen_mono
          (H₁ := (Ideal.closure (I'.map φ)).toAddSubgroup)
          (H₂ := (Ideal.closure (I'.map φ) ⊔ I.map φ : Ideal S).toAddSubgroup)
          (fun x hx ↦ (le_sup_left : Ideal.closure (I'.map φ) ≤ _) hx) (htaut.1 I' hI'.1)
      refine SetLike.coe_subset_coe.mp ?_
      rw [Ideal.coe_closure]
      exact closure_minimal (SetLike.coe_subset_coe.mpr le_sup_right)
        ((Ideal.closure (I'.map φ) ⊔ I.map φ : Ideal S).toAddSubgroup.isClosed_of_isOpen hopen)
    -- surjectivity of `(R ⧸ I')[x] → S ⧸ J(I')` modulo the extended ideal
    have hext : _root_.extendedIdeal N (S ⧸ Ideal.closure (I'.map φ)) =
        (I.map φ).map (Ideal.Quotient.mk (Ideal.closure (I'.map φ))) := by
      change Ideal.map (algebraMap (R ⧸ I') (S ⧸ Ideal.closure (I'.map φ)))
        (I.map (Ideal.Quotient.mk I')) = _
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
    have hmod : Function.Surjective
        ((Ideal.Quotient.mk (_root_.extendedIdeal N (S ⧸ Ideal.closure (I'.map φ)))).comp
          fAlg.toRingHom) := by
      intro z
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨p, hp⟩ := hsurjI (Ideal.Quotient.mk (Ideal.closure (I.map φ)) y)
      have hmem : y - Φ p ∈ Ideal.closure (I.map φ) :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hp.symm
      obtain ⟨j, hj, w', hw', hsum⟩ := Submodule.mem_sup.mp (hsup hmem)
      refine ⟨MvPolynomial.map (Ideal.Quotient.mk I') p, ?_⟩
      have hfp : fAlg.toRingHom (MvPolynomial.map (Ideal.Quotient.mk I') p) =
          Ideal.Quotient.mk (Ideal.closure (I'.map φ)) (Φ p) :=
        (congrArg (fun ρ : MvPolynomial (Fin r) R →+*
          S ⧸ Ideal.closure (I'.map φ) ↦ ρ p) hcomp).symm
      simp only [RingHom.comp_apply, hfp]
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
      rw [hext]
      have hdiff : Ideal.Quotient.mk (Ideal.closure (I'.map φ)) (Φ p) -
          Ideal.Quotient.mk (Ideal.closure (I'.map φ)) y =
          -Ideal.Quotient.mk (Ideal.closure (I'.map φ)) w' := by
        rw [← map_sub]
        have : Φ p - y = -(j + w') := by rw [hsum]; ring
        rw [this, map_neg, map_add,
          (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.closure (I'.map φ))).mpr hj]
        ring
      rw [hdiff]
      exact neg_mem (Ideal.mem_map_of_mem _ hw')
    have hsurj := surjective_of_surjective_mod_locallyNilpotent N hN fAlg hmod hftR
    intro y
    obtain ⟨q, hq⟩ := hsurj y
    obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk I')
      Ideal.Quotient.mk_surjective q
    refine ⟨p, ?_⟩
    have := congrArg (fun ρ : MvPolynomial (Fin r) R →+*
      S ⧸ Ideal.closure (I'.map φ) ↦ ρ p) hcomp
    simp only [RingHom.comp_apply] at this ⊢
    rw [this, hp]
    exact hq
  -- Density of `R[x₁, …, x_r] → S`.
  refine ⟨r, Φ, by ext a; simp [Φ], denseRange_of_forall_sub_mem htaut.2 Φ fun x I' hI'open ↦ ?_⟩
  obtain ⟨p, hp⟩ := key (I ⊓ I') (isWeakIdealOfDefinition_inf_of_isOpen_right hI hI'open)
    inf_le_left (Ideal.Quotient.mk _ x)
  refine ⟨p, ?_⟩
  have h1 : x - Φ p ∈ Ideal.closure ((I ⊓ I').map φ) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hp.symm
  exact closure_mono (SetLike.coe_subset_coe.mpr (Ideal.map_mono inf_le_right)) h1

omit [IsTopologicalRing B] [IsLinearTopology B B] [IsLinearTopology A A] in
theorem finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType
    (φ : B →+* A) (hTaut : RingHom.IsTaut φ) :
    TopologicalRing.IsTopologicallyOfFiniteType φ → FiniteTypeModuloEveryWeakIdeal φ := by
  rintro ⟨n, f, hfcomp, hfdense⟩
  refine ⟨hTaut, fun J hJ => ?_⟩
  let I : Ideal A := Ideal.closure (J.map φ)
  have hIopen : IsOpen (I : Set A) := hTaut.1 J hJ.1
  have hJI : J.map φ ≤ I := subset_closure
  let qA : A →+* A ⧸ I := Ideal.Quotient.mk I
  let qB : B →+* B ⧸ J := Ideal.Quotient.mk J
  let qbar : B ⧸ J →+* A ⧸ I := Ideal.quotientMap I φ
    (Ideal.map_le_iff_le_comap.mp hJI)
  change qbar.FiniteType
  let : DiscreteTopology (A ⧸ I) := QuotientAddGroup.discreteTopology_iff.mpr hIopen
  let qP : Ideal (MvPolynomial (Fin n) B) :=
    J.map (MvPolynomial.C : B →+* MvPolynomial (Fin n) B)
  let F : MvPolynomial (Fin n) B →+* A ⧸ I := qA.comp f
  have hFsurj : Function.Surjective F := by
    have hqsurj : Function.Surjective qA := fun y => Ideal.Quotient.mk_surjective y
    have hqcont : Continuous qA := continuous_quot_mk
    have hdense : DenseRange (qA ∘ f) := by
      exact hqsurj.denseRange.comp hfdense hqcont
    change DenseRange F at hdense
    exact (denseRange_discrete.mp hdense)
  have hqPker : qP ≤ RingHom.ker F := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change F (MvPolynomial.C b) = 0
    have hmem : φ b ∈ I := by
      change φ b ∈ closure (J.map φ : Set A)
      exact subset_closure (Ideal.mem_map_of_mem φ hb)
    change Ideal.Quotient.mk I (f (MvPolynomial.C b)) = 0
    rw [show f (MvPolynomial.C b) = φ b by
      exact DFunLike.congr_fun hfcomp b]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hqPker' : ∀ a ∈ qP, F a = 0 := fun a ha =>
    RingHom.mem_ker.mp (hqPker ha)
  let lift : (MvPolynomial (Fin n) B) ⧸ qP →+* A ⧸ I :=
    Ideal.Quotient.lift qP F hqPker'
  let eqv : MvPolynomial (Fin n) (B ⧸ J) ≃ₐ[B]
      (MvPolynomial (Fin n) B ⧸ qP) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin n) J
  let fbar : MvPolynomial (Fin n) (B ⧸ J) →+* A ⧸ I :=
    lift.comp eqv.toRingEquiv.toRingHom
  have hlift : Function.Surjective lift := by
    intro y
    obtain ⟨x, rfl⟩ := hFsurj y
    refine ⟨Ideal.Quotient.mk qP x, ?_⟩
    change Ideal.Quotient.lift qP F hqPker' (Ideal.Quotient.mk qP x) = F x
    rw [Ideal.Quotient.lift_mk]
  have hfbar : Function.Surjective fbar := hlift.comp eqv.surjective
  have hfbarC : fbar.comp (MvPolynomial.C : B ⧸ J →+*
      MvPolynomial (Fin n) (B ⧸ J)) = qbar := by
    ext b
    change lift (eqv (MvPolynomial.C (qB b))) = qA (φ b)
    have heqv : eqv (MvPolynomial.C (qB b)) =
        Ideal.Quotient.mk qP (MvPolynomial.C b) := by
      calc
        _ = eqv (algebraMap B (MvPolynomial (Fin n) (B ⧸ J)) b) := by
          simp [MvPolynomial.algebraMap_apply, qB]
        _ = algebraMap B (MvPolynomial (Fin n) B ⧸ qP) b := eqv.commutes b
        _ = Ideal.Quotient.mk qP (MvPolynomial.C b) := by
          rw [← Ideal.Quotient.mk_algebraMap (R₁ := B) qP b]
          simp [MvPolynomial.algebraMap_eq]
    rw [heqv]
    change Ideal.Quotient.lift qP F hqPker'
      (Ideal.Quotient.mk qP (MvPolynomial.C b)) = qA (φ b)
    rw [Ideal.Quotient.lift_mk]
    change qA (f (MvPolynomial.C b)) = qA (φ b)
    have hconst : f (MvPolynomial.C b) = φ b := DFunLike.congr_fun hfcomp b
    rw [hconst]
  let : Algebra (B ⧸ J) (A ⧸ I) := qbar.toAlgebra
  let fbarAlg : MvPolynomial (Fin n) (B ⧸ J) →ₐ[B ⧸ J] A ⧸ I :=
    { toRingHom := fbar
      commutes' := fun b => DFunLike.congr_fun hfbarC b }
  change Algebra.FiniteType (B ⧸ J) (A ⧸ I)
  exact Algebra.FiniteType.of_surjective fbarAlg hfbar

omit [IsTopologicalRing B] [IsLinearTopology B B] [IsLinearTopology A A] in
/-- A continuous taut homomorphism of linearly topologized rings which is topologically of
finite type is of finite type modulo every weak ideal of definition: condition (2) of
**Stacks 0ANT** implies condition (a) of **Stacks 0ANU**.

No countability assumption is involved. The converse,
`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal`, needs only
that the source be weakly pre-admissible, so the two conditions are equivalent outright and
`TopologicalRing.finiteType_tfae` is not the only route between them. -/
alias finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType' :=
  finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType

omit [IsTopologicalRing B] [IsLinearTopology B B] [IsTopologicalRing A]
  [IsLinearTopology A A] in
private theorem topologicallyOfFiniteType_of_presentation (φ : B →+* A) :
    HasRestrictedPowerSeriesPresentation φ →
      TopologicalRing.IsTopologicallyOfFiniteType φ := by
  rintro ⟨n, K, hKclosed, e, he, he_symm, hcompat⟩
  let P := MvPolynomial (Fin n) B
  let R := RestrictedPowerSeries B (Fin n)
  let : UniformSpace P := restrictedPolynomialUniformSpace B (Fin n)
  let : TopologicalSpace P := restrictedPolynomialTopology B (Fin n)
  let p : P →+* R := polynomialToRestrictedPowerSeries B (Fin n)
  let q : R →+* R ⧸ K := Ideal.Quotient.mk K
  let g : R →+* A := e.toRingHom.comp q
  let f : P →+* A := g.comp p
  refine ⟨n, f, ?_, ?_⟩
  · change (e.toRingHom.comp q).comp (p.comp MvPolynomial.C) = φ
    rw [RingHom.comp_assoc]
    simpa [q, p, coeffToRestrictedPowerSeries] using hcompat
  · have hqcont : Continuous q := continuous_quot_mk
    have hgcont : Continuous g := he.comp hqcont
    have hgsurj : Function.Surjective g := by
      intro a
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm a)
      refine ⟨x, ?_⟩
      change e (Ideal.Quotient.mk K x) = a
      rw [hx, e.apply_symm_apply]
    have hp : DenseRange p := by
      change DenseRange ((↑) : P → UniformSpace.Completion P)
      exact UniformSpace.Completion.denseRange_coe
    change DenseRange (fun x : P => g (p x))
    exact hgsurj.denseRange.comp hp hgcont

omit [IsLinearTopology A A] in
theorem finiteTypeModuloEveryWeakIdeal_to_cofinal
    (φ : B →+* A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hBcount : (nhds (0 : B)).IsCountablyGenerated) :
    FiniteTypeModuloEveryWeakIdeal φ → FiniteTypeModuloCofinalWeakIdeals φ := by
  rintro ⟨htaut, hfinite⟩
  obtain ⟨J₀, hJ₀⟩ := (show ∃ J : Ideal B, TopologicalRing.IsWeakIdealOfDefinition J from hB.1)
  obtain ⟨U, hU⟩ := (isCountablyGenerated_iff_exists_antitone_basis.mp hBcount)
  let hb := (isLinearTopology_iff_hasBasis_open_ideal (R := B)).mp inferInstance
  have hUm (m : ℕ) : U m ∈ nhds (0 : B) := hU.1.mem_of_mem trivial
  choose I hIopen hIle using fun m => (hb.mem_iff.mp (hUm m))
  let J : ℕ → Ideal B := fun m => J₀ ⊓ I m
  have hweak : ∀ m, TopologicalRing.IsWeakIdealOfDefinition (J m) := by
    intro m
    refine ⟨?_, ?_⟩
    · exact hJ₀.1.inter (hIopen m)
    · intro x hx
      exact hJ₀.2 x hx.1
  have hcofinal : ∀ K : Ideal B, TopologicalRing.IsWeakIdealOfDefinition K →
      ∃ m, J m ≤ K := by
    intro K hK
    obtain ⟨m, _, hUK⟩ := hU.1.mem_iff.mp (hK.1.mem_nhds (zero_mem K))
    refine ⟨m, ?_⟩
    intro x hx
    exact hUK (hIle m hx.2)
  exact ⟨htaut, J, hweak, hcofinal, fun m => hfinite (J m) (hweak m)⟩

theorem exists_fundamental_weak_ideal_sequence
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hBcount : (nhds (0 : B)).IsCountablyGenerated) :
    ∃ J : ℕ → Ideal B,
      RingHom.QuotientDiagram.IsFundamentalSequence J := by
  obtain ⟨J₀, hJ₀⟩ := hB.1
  obtain ⟨U, hU⟩ := (isCountablyGenerated_iff_exists_antitone_basis.mp hBcount)
  let hb := (isLinearTopology_iff_hasBasis_open_ideal (R := B)).mp inferInstance
  have hUm (m : ℕ) : U m ∈ nhds (0 : B) := hU.1.mem_of_mem trivial
  choose I hIopen hIle using fun m => (hb.mem_iff.mp (hUm m))
  let J : ℕ → Ideal B := Nat.rec (J₀ ⊓ I 0) (fun m K => K ⊓ I (m + 1))
  have hJopen (m : ℕ) : IsOpen {x : B | x ∈ J m} := by
    induction m with
    | zero => exact hJ₀.1.inter (hIopen 0)
    | succ m ih => exact ih.inter (hIopen (m + 1))
  have hJanti : Antitone J := antitone_nat_of_succ_le fun _ => inf_le_left
  have hJweak (m : ℕ) : TopologicalRing.IsWeakIdealOfDefinition (J m) :=
    ⟨hJopen m, fun x hx => hJ₀.2 x ((hJanti (Nat.zero_le m)).trans inf_le_left hx)⟩
  have hJleI (m : ℕ) : J m ≤ I m := by
    cases m <;> exact inf_le_right
  have hJbasis : (nhds (0 : B)).HasBasis (fun _ : ℕ => True)
      (fun m => {x : B | x ∈ J m}) := by
    refine ⟨?_⟩
    intro V
    constructor
    · intro hV
      obtain ⟨m, _, hm⟩ := hU.1.mem_iff.mp hV
      exact ⟨m, trivial, fun x hx => hm (hIle m (hJleI m hx))⟩
    · rintro ⟨m, _, hm⟩
      exact Filter.mem_of_superset ((hJopen m).mem_nhds (J m).zero_mem) hm
  exact ⟨J, hJweak, hJanti, hJbasis⟩

theorem finiteTypeModuloEveryWeakIdeal_to_topologicallyOfFiniteType
    (φ : B →+* A)
    (hB : TopologicalRing.IsWeaklyAdmissible B) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hBcount : (nhds (0 : B)).IsCountablyGenerated)
    (hFT : FiniteTypeModuloEveryWeakIdeal φ) :
    TopologicalRing.IsTopologicallyOfFiniteType φ := by
  classical
  obtain ⟨J, hJ⟩ := exists_fundamental_weak_ideal_sequence B hB hBcount
  have hdiag : RingHom.QuotientDiagram.HasQuotientDiagram φ J hJ.2.1 :=
    (RingHom.QuotientDiagram.isTaut_iff_hasQuotientDiagram
      φ hA J hJ).mp hFT.1
  let I : ℕ → Ideal A := fun m =>
    RingHom.QuotientDiagram.targetIdeal φ J m
  let qA : (m : ℕ) → A →+* A ⧸ I m := fun m => Ideal.Quotient.mk (I m)
  let ψ : (m : ℕ) → B ⧸ J m →+* A ⧸ I m := fun m =>
    Ideal.quotientMap (I m) φ (Ideal.map_le_iff_le_comap.mp subset_closure)
  let : (m : ℕ) → Algebra (B ⧸ J m) (A ⧸ I m) := fun m => (ψ m).toAlgebra
  have hftStage (m : ℕ) : Algebra.FiniteType (B ⧸ J m) (A ⧸ I m) :=
    RingHom.finiteType_algebraMap.mp (hFT.2 (J m) (hJ.1 m))
  let : Algebra (B ⧸ J 0) (A ⧸ I 0) := (ψ 0).toAlgebra
  obtain ⟨n, f₀, hf₀⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (hftStage 0)
  choose a ha using fun i => Ideal.Quotient.mk_surjective (f₀ (MvPolynomial.X i))
  let f : MvPolynomial (Fin n) B →+* A := MvPolynomial.eval₂Hom φ a
  have hfconst : f.comp MvPolynomial.C = φ := by
    ext b
    simp [f]
  let stage : (m : ℕ) → MvPolynomial (Fin n) (B ⧸ J m) →+* A ⧸ I m := fun m =>
    MvPolynomial.eval₂Hom (ψ m) (fun i => qA m (a i))
  let stageAlg : (m : ℕ) → MvPolynomial (Fin n) (B ⧸ J m) →ₐ[B ⧸ J m] A ⧸ I m :=
    fun m =>
      { toRingHom := stage m
        commutes' := by
          intro r
          change MvPolynomial.eval₂Hom (ψ m) (fun i => qA m (a i)) (MvPolynomial.C r) = ψ m r
          simp [MvPolynomial.eval₂Hom_C] }
  have hstage0 : stage 0 = f₀.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro b
      change MvPolynomial.eval₂Hom (ψ 0) (fun i => qA 0 (a i)) (MvPolynomial.C b) = _
      rw [MvPolynomial.eval₂Hom_C]
      change algebraMap (B ⧸ J 0) (A ⧸ I 0) b =
        f₀ (algebraMap (B ⧸ J 0) (MvPolynomial (Fin n) (B ⧸ J 0)) b)
      exact (f₀.commutes b).symm
    · intro i
      change MvPolynomial.eval₂Hom (ψ 0) (fun i => qA 0 (a i)) (MvPolynomial.X i) = _
      rw [MvPolynomial.eval₂Hom_X']
      exact ha i
  have hstageSurj : ∀ m, Function.Surjective (stage m) := by
    intro m
    induction m with
    | zero => simpa [hstage0] using hf₀
    | succ m ih =>
      let R := B ⧸ J (m + 1)
      let S := A ⧸ I (m + 1)
      let N : Ideal R := (J m).map (Ideal.Quotient.mk (J (m + 1)))
      let M : Ideal S := Ideal.map (ψ (m + 1)) N
      let qB : B ⧸ J (m + 1) →+* B ⧸ J m :=
        Ideal.Quotient.factor (hJ.2.1 (Nat.le_succ m))
      let qS := RingHom.QuotientDiagram.quotientTransition
        φ J hJ.2.1 m
      have hqSker : RingHom.ker qS = M := by
        rw [show M = (J m).map ((Ideal.Quotient.mk (I (m + 1))).comp φ) by
          dsimp [M, N]
          rw [Ideal.map_map]
          congr 1]
        exact hdiag.2.2.1 m
      have hNnil : N.IsLocallyNilpotent :=
        isLocallyNilpotent_map_mk_of_isTopologicallyNilpotent (J m) (J (m + 1))
          (hJ.1 (m + 1)).1 (hJ.1 m).2
      have hqSsurj : Function.Surjective qS := by
        intro y
        obtain ⟨x, rfl⟩ := Ideal.Quotient.factor_surjective
          (show I (m + 1) ≤ I m from
            closure_mono (Ideal.map_mono (hJ.2.1 (Nat.le_succ m)))) y
        exact ⟨x, rfl⟩
      let eS : S ⧸ M ≃+* A ⧸ I m :=
        (Ideal.quotEquivOfEq hqSker.symm).trans (qS.quotientKerEquivOfSurjective hqSsurj)
      have heS_mk (z : S) : eS.toRingHom (Ideal.Quotient.mk M z) = qS z := by
        simp [eS, RingHom.quotientKerEquivOfSurjective_apply_mk,
          Ideal.quotEquivOfEq_mk]
      have hcomm : qS.comp (ψ (m + 1)) = (ψ m).comp qB := by
        ext r
        simp only [RingHom.QuotientDiagram.quotientTransition, RingHom.coe_comp,
          Function.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, qS, ψ, qB]
        rw [Ideal.Quotient.factor_mk]
      have hcompat : eS.toRingHom.comp ((Ideal.Quotient.mk M).comp (stage (m + 1))) =
          (stage m).comp (MvPolynomial.map qB) := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp only [RingHom.comp_apply]
          simp only [MvPolynomial.map_C]
          change eS.toRingHom (Ideal.Quotient.mk M (stage (m + 1) (MvPolynomial.C r))) =
            stage m (MvPolynomial.C (qB r))
          rw [MvPolynomial.eval₂Hom_C, heS_mk, MvPolynomial.eval₂Hom_C]
          exact DFunLike.congr_fun hcomm r
        · intro i
          simp only [RingHom.comp_apply]
          simp only [MvPolynomial.map_X]
          change eS.toRingHom (Ideal.Quotient.mk M (stage (m + 1) (MvPolynomial.X i))) =
            stage m (MvPolynomial.X i)
          rw [MvPolynomial.eval₂Hom_X', heS_mk, MvPolynomial.eval₂Hom_X']
          change Ideal.Quotient.factor
              (show I (m + 1) ≤ I m from
                closure_mono (Ideal.map_mono (hJ.2.1 (Nat.le_succ m))))
              (Ideal.Quotient.mk (I (m + 1)) (a i)) =
            Ideal.Quotient.mk (I m) (a i)
          rw [Ideal.Quotient.factor_mk]
      have hmodsurj : Function.Surjective
          ((Ideal.Quotient.mk M).comp (stage (m + 1))) := by
        intro y
        obtain ⟨x, hx⟩ :=
          (ih.comp (MvPolynomial.map_surjective qB (Ideal.Quotient.factor_surjective _)))
            (eS y)
        refine ⟨x, ?_⟩
        apply eS.injective
        exact (congrArg (fun g => g x) hcompat).trans hx
      have hftnext : Algebra.FiniteType R S := hftStage (m + 1)
      have hmodsurj' : Function.Surjective
          ((Ideal.Quotient.mk (extendedIdeal N S)).comp (stageAlg (m + 1)).toRingHom) := by
        change Function.Surjective ((Ideal.Quotient.mk M).comp (stage (m + 1)))
        exact hmodsurj
      exact surjective_of_surjective_mod_locallyNilpotent
        N hNnil (stageAlg (m + 1)) hmodsurj'
        hftnext
  have hstageLift (m : ℕ) :
      (stage m).comp (MvPolynomial.map (Ideal.Quotient.mk (J m))) =
        (qA m).comp f := by
    apply MvPolynomial.ringHom_ext'
    · ext b
      simp [stage, f, ψ, Ideal.quotientMap_mk]
      rfl
    · intro i
      simp [stage, f]
  have hdense : DenseRange f := by
    refine denseRange_of_forall_sub_mem hdiag.2.1 f fun x m _ ↦ ?_
    obtain ⟨z, hz⟩ := hstageSurj m (qA m x)
    obtain ⟨p, hp⟩ := MvPolynomial.map_surjective
      (Ideal.Quotient.mk (J m)) Ideal.Quotient.mk_surjective z
    refine ⟨p, ?_⟩
    have hfun := congrArg (fun g => g p) (hstageLift m)
    simp only [RingHom.comp_apply, hp] at hfun
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hfun.symm.trans hz).symm
  exact ⟨n, f, hfconst, hdense⟩

omit [IsTopologicalRing B] [IsLinearTopology B B] [IsLinearTopology A A] in
theorem finiteTypeModuloCofinal_to_every (φ : B →+* A) :
    FiniteTypeModuloCofinalWeakIdeals φ → FiniteTypeModuloEveryWeakIdeal φ := by
  rintro ⟨htaut, J, hJ, hcofinal, hfinite⟩
  refine ⟨htaut, fun K hK => ?_⟩
  obtain ⟨m, hle⟩ := hcofinal K hK
  let Im : Ideal A := Ideal.closure ((J m).map φ)
  let IK : Ideal A := Ideal.closure (K.map φ)
  have hImle : Im ≤ IK := by
    change closure ((J m).map φ : Set A) ⊆ closure (K.map φ : Set A)
    exact closure_mono (Ideal.map_mono hle)
  let qB : B ⧸ J m →+* B ⧸ K := Ideal.Quotient.factor hle
  let qA : A ⧸ Im →+* A ⧸ IK := Ideal.Quotient.factor hImle
  let fm : B ⧸ J m →+* A ⧸ Im := Ideal.quotientMap Im φ
    (Ideal.map_le_iff_le_comap.mp subset_closure)
  let fK : B ⧸ K →+* A ⧸ IK := Ideal.quotientMap IK φ
    (Ideal.map_le_iff_le_comap.mp subset_closure)
  have hcomm : fK.comp qB = qA.comp fm := by
    ext b
    simp [fK, qB, qA, fm, Ideal.quotientMap_mk]
  have hqAsurj : Function.Surjective qA :=
    Ideal.Quotient.factor_surjective hImle
  have hft : (qA.comp fm).FiniteType := (hfinite m).comp_surjective hqAsurj
  have hft' : (fK.comp qB).FiniteType := hcomm ▸ hft
  exact RingHom.FiniteType.of_comp_finiteType hft'

omit [IsTopologicalRing B] [IsLinearTopology B B] [IsLinearTopology A A] in
@[ega "0 7.5.5" "(c), (c) ⇒ (a)"]
theorem finiteTypeModuloEveryWeakIdeal_of_presentation (φ : B →+* A) :
    HasRestrictedPowerSeriesPresentation φ → FiniteTypeModuloEveryWeakIdeal φ := by
  intro hp
  exact finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType φ
    (taut_of_presentation φ hp) (topologicallyOfFiniteType_of_presentation φ hp)

end

end TopologicalRing

end
