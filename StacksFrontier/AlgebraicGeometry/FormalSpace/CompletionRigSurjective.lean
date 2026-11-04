module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMapsIntoCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveCriterion
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence

/-!
# Substrate for rig-surjectivity of a morphism of completions

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a closed set of points of `X`, with `T' = |f|⁻¹ T`
and with `U ⊂ X`, `U' = f⁻¹U ⊂ X'` the open complements; this is the situation of **Stacks
0GDB**. **Stacks 0AQW** says that if `X` is locally Noetherian, `f` is proper and `U' → U` is
surjective, then `f_{/T} : X'_{/T'} ⟶ X_{/T}` is rig-surjective.

That statement is `AlgebraicGeometry.FormalSpace.isRigSurjective_completionSheafMap` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ProperValuativeLifting`. The source's proof produces,
from an adic morphism `Spf R ⟶ X_{/T}` out of a complete discrete valuation ring, its
algebraization `Spec R ⟶ X` (**Stacks 0GBU**), a point of `U'` over the generic point of `Spec R`
and hence a finitely generated field extension `K'/K`, a discrete valuation ring inside `K'`
dominating `R` (**Stacks 00PH**), a lift of it to `X'` by the valuative criterion of properness
(**Stacks 0A40**), and finally the completion of that ring, which is again a complete discrete
valuation ring (**Stacks 0AP1**). This file carries the steps of that chain which the library does
not already have and which do not depend on those cited lemmas:

* the passage from a point in the image of a morphism to a field-valued representative of it
  lifted to the source, which is how surjectivity of `U' → U` produces the extension `K'/K`;
* the finite generation of the residue field of a point of a scheme locally of finite type
  over a field, which is the hypothesis `Algebra.EssFiniteType K K'` of Stacks 00PH;
* the membership of the ordinary spectrum of `R` in the site, which every statement about
  maps out of `Spf R` into an algebraic space needs;
* a structure morphism `Spec R ⟶ S` compatible with a given quotient system for `R`, which is
  the hypothesis `q` of the statements about maps out of `Spf R`. A quotient system records
  only the structure morphisms of the quotient stages, so this is what turns an adic point of
  a completion, which comes with a quotient system and nothing else, into an input for
  **Stacks 0AQH** and **Stacks 0GBU**.

## Main results

* `AlgebraicGeometry.Space.exists_fieldValuedPoint_of_class_mem_range`
* `AlgebraicGeometry.essFiniteType_preimage_residueField`
* `AlgebraicGeometry.FormalSpace.contains_spec_of_quotientSystem`
* `AlgebraicGeometry.FormalSpace.exists_specHom_compatible_overS` and
  `AlgebraicGeometry.FormalSpace.exists_specHom_compatible_overS_maximalIdeal`

## Implementation notes

*The compatible structure morphism.* The source of **Stacks 0AQG** reduces maps out of a
formal spectrum to maps into an affine open of the target by using that the quotient stages
are spectra of local rings with a common closed point. The same reduction is run here for the
base `S` itself, and it is shorter: when the topology is the adic topology of a *prime* ideal
`I`, every weak ideal of definition is contained in `I`, so `I` is the largest one and every
stage compares with the stage of `I` directly, with no need to pass to meets of weak ideals.
`StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToScheme` proves the corresponding facts for a
general weakly admissible ring, but privately; what is needed here is re-proved rather than
exposed, that module being imported widely.

The passage from the compatible family of ring maps `Γ(S, W) ⟶ R ⧸ I ^ (n + 1)` to a single
`Γ(S, W) ⟶ R` is the universal property `IsAdicComplete.StrictMono.liftRingHom` of adic
completeness, indexed by the positive powers of `I`; the stages of the remaining weak ideals
of definition are then reached because each contains a power of `I`.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0A40](https://stacks.math.columbia.edu/tag/0A40)
* [Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
* [Stacks Project, Tag 0AQW](https://stacks.math.columbia.edu/tag/0AQW)
* [Stacks Project, Tag 0GBU](https://stacks.math.columbia.edu/tag/0GBU)
* [Stacks Project, Tag 0GDB](https://stacks.math.columbia.edu/tag/0GDB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A point of a presheaf in the image of a morphism is the image of a point of the source,
realised on field-valued representatives: a field-valued representative of the point is
dominated by the image of a field-valued representative of a preimage. -/
theorem exists_fieldValuedPoint_of_class_mem_range
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (p : FieldValuedPoint B S hS G)
    (hp : p.class B S hS G ∈ Set.range (pointsMap B S hS F f)) :
    ∃ (q : FieldValuedPoint B S hS F) (i : q.siteObject B S hS F ⟶ p.siteObject B S hS G),
      f.app _ q.value = G.map i.op p.value := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨q₀, rfl⟩ := Quot.exists_rep z
  obtain ⟨r, ⟨j, hj⟩, ⟨i, hi⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS G
      (FieldValuedPoint.map B S hS F f q₀) p).mp hz
  exact ⟨⟨r.carrier, r.contained, r.toBase, F.map j.op q₀.value⟩, i,
    (NatTrans.naturality_apply f j.op q₀.value).trans (hj.trans hi.symm)⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-- The residue field of a point of a scheme locally of finite type over a field is
essentially of finite type over that field: the composite `Spec κ(v) ⟶ V ⟶ Spec K` factors
through `Spec κ(b v)`, whose ring map is of finite type because a point of the spectrum of a
field is a closed immersion, and whose second factor is essentially of finite type because the
stalk map of a morphism locally of finite type is. -/
theorem essFiniteType_preimage_residueField
    (K : Type u) [Field K] {V : Scheme.{u}}
    (b : V ⟶ Spec (.of K)) [LocallyOfFiniteType b] (v : V) :
    (Spec.preimage (V.fromSpecResidueField v ≫ b)).hom.EssFiniteType := by
  rw [← b.SpecMap_residueFieldMap_fromSpecResidueField v,
    Spec.preimage_comp, Spec.preimage_map]
  apply RingHom.EssFiniteType.comp
  · have : IsClosedImmersion ((Spec (.of K)).fromSpecResidueField (b v)) :=
      isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
    have hft : LocallyOfFiniteType
        (Spec.map (Spec.preimage ((Spec (.of K)).fromSpecResidueField (b v)))) := by
      rw [Spec.map_preimage]
      infer_instance
    exact (HasRingHomProperty.Spec_iff.mp hft).essFiniteType
  · exact RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap b v)

end AlgebraicGeometry

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The ordinary spectrum of a topological ring carrying a quotient system over `S` and an
adic complete topology belongs to the site: the quotient system bounds the cardinality of the
ring by `AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem`. -/
theorem contains_spec_of_quotientSystem {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {I : Ideal A} (h : IsAdic I) (hc : IsAdicComplete I A)
    (D : QuotientSystem B S hS A) : B.Contains (Spec (.of A)) := by
  show (Spec (.of A)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (mk_lt_cutoff_of_quotientSystem h hc D)

/-! ### A structure morphism on the ordinary spectrum compatible with a quotient system -/

section CompatibleSpecHom

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- Every weak ideal of definition of a ring whose topology is the adic topology of a prime
ideal `I` is contained in `I`: its elements are topologically nilpotent and `I` is a
neighbourhood of zero, so a power of each of them lies in `I`, which is prime. -/
theorem weakIdealOfDefinition_le_of_isPrime {I : Ideal R} (hadic : IsAdic I) (hI : I.IsPrime)
    {J : Ideal R} (hJ : TopologicalRing.IsWeakIdealOfDefinition J) : J ≤ I := by
  intro x hx
  have hopen : IsOpen ((I : Ideal R) : Set R) := by
    simpa using isOpen_pow_of_isAdic hadic 1
  have ht : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds (0 : R)) := hJ.2 x hx
  obtain ⟨n, hn⟩ := (ht.eventually_mem (hopen.mem_nhds I.zero_mem)).exists
  exact hI.mem_of_pow_mem n hn

/-- The quotient of a local ring by a weak ideal of definition of the adic topology of a prime
ideal is again a local ring: the weak ideal is contained in that prime, hence proper. -/
theorem isLocalRing_quotient_of_isWeakIdealOfDefinition [IsLocalRing R] {I : Ideal R}
    (hadic : IsAdic I) (hI : I.IsPrime) {J : Ideal R}
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) : IsLocalRing (R ⧸ J) := by
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top hI.ne_top (weakIdealOfDefinition_le_of_isPrime hadic hI hJ))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

/-- A morphism out of the spectrum of a local ring whose closed point lands in an open
subscheme has its whole image there: the preimage of the open subscheme is an open containing
the closed point, hence the whole spectrum. -/
theorem range_subset_of_closedPoint_mem {A : Type u} [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : Spec (.of A) ⟶ X) (U : X.Opens)
    (hx : f (IsLocalRing.closedPoint A) ∈ U) :
    Set.range f ⊆ Set.range (Scheme.Opens.ι U) := by
  rintro x ⟨y, rfl⟩
  exact ⟨⟨f y, (Scheme.preimage_eq_top_of_closedPoint_mem f hx ▸ trivial : y ∈ f ⁻¹ᵁ U)⟩, rfl⟩

/-- A family of ring maps into the quotients of an adically complete ring by the positive
powers of the defining ideal, compatible with the transition maps, comes from a single ring
map into the ring itself: this is the universal property
`IsAdicComplete.StrictMono.liftRingHom` of adic completeness, read for the cofinal family of
positive powers. -/
theorem exists_ringHom_of_compatible_quotientPow {A R' : Type*} [CommRing A] [CommRing R']
    {I : Ideal R'} (hcomplete : IsAdicComplete I R')
    (f : (n : ℕ) → A →+* R' ⧸ I ^ (n + 1))
    (hf : ∀ k : ℕ, (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)))).comp (f (k + 1)) = f k) :
    ∃ ψ : A →+* R', ∀ n : ℕ, (Ideal.Quotient.mk (I ^ (n + 1))).comp ψ = f n := by
  have := hcomplete
  have hsucc : StrictMono (fun n : ℕ => n + 1) := fun _ _ => Nat.succ_lt_succ
  exact ⟨IsAdicComplete.StrictMono.liftRingHom I hsucc f fun {k} => hf k,
    fun n => IsAdicComplete.StrictMono.mk_comp_liftRingHom I hsucc f (fun {k} => hf k)⟩

/-- The closed points of the quotient stages of a quotient system all have the same image in
the base: for `J ≤ M` the transition map `R ⧸ J ⟶ R ⧸ M` is a surjection of local rings, so
its spectrum carries the closed point to the closed point, and the structure morphisms are
compatible with it. -/
theorem overS_closedPoint_eq (D : QuotientSystem B S hS R)
    {J M : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }} (h : J.1 ≤ M.1)
    [IsLocalRing (R ⧸ J.1)] [IsLocalRing (R ⧸ M.1)] :
    (D.overS M) (IsLocalRing.closedPoint (R ⧸ M.1)) =
      (D.overS J) (IsLocalRing.closedPoint (R ⧸ J.1)) := by
  have : IsLocalHom (Ideal.Quotient.factor h) :=
    IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective h)
  have hpt : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))
      (IsLocalRing.closedPoint (R ⧸ M.1)) = IsLocalRing.closedPoint (R ⧸ J.1) :=
    AlgebraicGeometry.Spec_closedPoint
  calc (D.overS M) (IsLocalRing.closedPoint (R ⧸ M.1))
      = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ D.overS J)
          (IsLocalRing.closedPoint (R ⧸ M.1)) := by rw [D.compatible J M h]
    _ = (D.overS J) (IsLocalRing.closedPoint (R ⧸ J.1)) := by
        show (D.overS J) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))
          (IsLocalRing.closedPoint (R ⧸ M.1))) = _
        rw [hpt]

/-- **A structure morphism on the ordinary spectrum compatible with a quotient system.** Let
`R` be a local ring whose topology is the adic topology of a prime ideal `I` for which `R` is
adically complete, and let `D` be a quotient system for `R` over `S`. Then the structure
morphisms of `D` are induced by a single morphism `Spec R ⟶ S`.

Every weak ideal of definition is contained in `I`, so `I` itself is the largest one and every
quotient stage receives the stage of `I`; the stages are spectra of local rings and their
closed points therefore share an image in `S`, so a single affine open `W ⊆ S` receives all of
them. The resulting compatible family of ring maps `Γ(S, W) ⟶ R ⧸ I ^ (n + 1)` lifts through
the adic completeness of `R` to a ring map `Γ(S, W) ⟶ R`, and every weak ideal of definition
contains a power of `I`, so the lift is compatible with every stage and not only with the
powers of `I`. -/
@[sga "3 XI 3.3" "partial", sga "3 XV 1.4" "Surjectivity of (∗)"]
theorem exists_specHom_compatible_overS [IsLocalRing R] {I : Ideal R} (hadic : IsAdic I)
    (hI : I.IsPrime) (hcomplete : IsAdicComplete I R) (D : QuotientSystem B S hS R) :
    ∃ q : Spec (.of R) ⟶ S,
      ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J := by
  have := hcomplete
  have hloc : ∀ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K },
      IsLocalRing (R ⧸ J.1) :=
    fun J => isLocalRing_quotient_of_isWeakIdealOfDefinition hadic hI J.2
  -- `I` is the largest weak ideal of definition
  have hIw : TopologicalRing.IsWeakIdealOfDefinition I := by
    simpa using isWeakIdealOfDefinition_pow_of_isAdic hadic (n := 1) one_ne_zero
  have hJI : ∀ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K },
      J.1 ≤ (⟨I, hIw⟩ : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K }).1 :=
    fun J => weakIdealOfDefinition_le_of_isPrime hadic hI J.2
  have : IsLocalRing (R ⧸ I) := isLocalRing_quotient_of_isWeakIdealOfDefinition hadic hI hIw
  -- one affine open of the base receives every quotient stage
  obtain ⟨W, hWaff, hsW, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := S) (U := ⊤)
    (x := (D.overS ⟨I, hIw⟩) (IsLocalRing.closedPoint (R ⧸ I))) trivial
  have hmemW : ∀ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K },
      (D.overS J) (IsLocalRing.closedPoint (R ⧸ J.1)) ∈ W := by
    intro J
    rw [← overS_closedPoint_eq D (hJI J)]
    exact hsW
  obtain ⟨g, hg⟩ : ∃ g : ∀ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K },
      Spec (.of (R ⧸ J.1)) ⟶ W.toScheme, ∀ J, g J ≫ Scheme.Opens.ι W = D.overS J :=
    ⟨fun J => IsOpenImmersion.lift (Scheme.Opens.ι W) (D.overS J)
        (range_subset_of_closedPoint_mem (D.overS J) W (hmemW J)),
      fun J => IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨φ, hφ0⟩ : ∃ φ : ∀ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K },
      Γ(S, W) ⟶ CommRingCat.of (R ⧸ J.1),
      ∀ J, Spec.map (φ J) = g J ≫ hWaff.isoSpec.hom :=
    ⟨fun J => Spec.preimage (g J ≫ hWaff.isoSpec.hom), fun J => Spec.map_preimage _⟩
  have hφ : ∀ (J L : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K })
      (h : J.1 ≤ L.1), φ L = φ J ≫ CommRingCat.ofHom (Ideal.Quotient.factor h) := by
    intro J L h
    have hgcomp : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ g J = g L :=
      (cancel_mono (Scheme.Opens.ι W)).1 (by rw [Category.assoc, hg J, hg L, D.compatible J L h])
    apply Spec.map_injective
    rw [Spec.map_comp, hφ0 L, hφ0 J, ← Category.assoc, hgcomp]
  -- the powers of `I` and the lift supplied by adic completeness
  have hIpow : ∀ n : ℕ, TopologicalRing.IsWeakIdealOfDefinition (I ^ (n + 1)) :=
    fun n => isWeakIdealOfDefinition_pow_of_isAdic hadic (Nat.succ_ne_zero n)
  obtain ⟨L, hL⟩ := exists_ringHom_of_compatible_quotientPow (A := Γ(S, W)) hcomplete
    (fun n => (φ ⟨I ^ (n + 1), hIpow n⟩).hom) fun k => by
      have h1 := hφ ⟨I ^ (k + 2), hIpow (k + 1)⟩ ⟨I ^ (k + 1), hIpow k⟩
        (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)))
      simp only [h1, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(S, W) ⟶ CommRingCat.of R,
      ∀ J : { K : Ideal R // TopologicalRing.IsWeakIdealOfDefinition K },
        φ J = ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J.1) := by
    refine ⟨CommRingCat.ofHom L, fun J => ?_⟩
    obtain ⟨n, hn⟩ := exists_pow_le_of_isWeakIdealOfDefinition hadic J
    have hn' : I ^ (n + 1) ≤ J.1 := le_trans (Ideal.pow_le_pow_right (Nat.le_succ n)) hn
    have h2 : (φ J).hom =
        (Ideal.Quotient.factor hn').comp (φ ⟨I ^ (n + 1), hIpow n⟩).hom := by
      simp only [hφ ⟨I ^ (n + 1), hIpow n⟩ J hn', CommRingCat.hom_comp,
        CommRingCat.hom_ofHom]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom L, h2, ← hL n, ← RingHom.comp_assoc,
      Ideal.Quotient.factor_comp_mk, CommRingCat.hom_ofHom]
  refine ⟨Spec.map ψ ≫ hWaff.isoSpec.inv ≫ Scheme.Opens.ι W, fun J => ?_⟩
  calc Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
        (Spec.map ψ ≫ hWaff.isoSpec.inv ≫ Scheme.Opens.ι W)
      = Spec.map (ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
          (hWaff.isoSpec.inv ≫ Scheme.Opens.ι W) := by
        rw [Spec.map_comp, Category.assoc]
    _ = (g J ≫ hWaff.isoSpec.hom) ≫ (hWaff.isoSpec.inv ≫ Scheme.Opens.ι W) := by
        rw [← hψ J, hφ0 J]
    _ = D.overS J := by
        rw [Category.assoc, ← Category.assoc hWaff.isoSpec.hom, Iso.hom_inv_id,
          Category.id_comp, hg J]

/-- `AlgebraicGeometry.FormalSpace.exists_specHom_compatible_overS` for a Noetherian complete
local ring carrying its `𝔪`-adic topology: this is the shape in which the statements about
maps out of a formal spectrum — `AlgebraicGeometry.FormalSpace.injective_map_into_algebraicSpace`
and `AlgebraicGeometry.FormalSpace.existsUnique_algebraization_of_adic_into_completion` — ask
for their structure morphism `q` and its compatibility `hq`. -/
@[sga "3 XV 1.4" "partial"]
theorem exists_specHom_compatible_overS_maximalIdeal (hR : IsNoetherianCompleteLocalRing R)
    (hadic : IsAdic (@IsLocalRing.maximalIdeal R _ hR.isLocal))
    (D : QuotientSystem B S hS R) :
    ∃ q : Spec (.of R) ⟶ S,
      ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J := by
  have := hR.isLocal
  exact exists_specHom_compatible_overS hadic
    (IsLocalRing.maximalIdeal.isMaximal R).isPrime hR.isComplete D

end CompatibleSpecHom

end AlgebraicGeometry.FormalSpace

end
