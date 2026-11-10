module

public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A complete separated ring is the limit of its quotients along a fundamental system of ideals

Call a family `P` of ideals of a topological ring `A` a *fundamental system of ideals* when its
members are open, it is closed under intersection, and it is a neighbourhood basis of zero. For
such a family the induced map from `A` into the inverse limit of the discrete rings `A ⧸ I`,
taken over the members `I` of `P` ordered by inclusion, is injective when `A` is separated and
surjective when `A` is complete, hence an isomorphism of topological rings for a complete
separated `A`.

Two families of this kind occur. In an admissible topological ring the ideals of definition form
one; in a weakly admissible topological ring — McQuillan's weakening, where only `fⁿ → 0` for
`f ∈ I` is asked of a weak ideal of definition `I` — the *weak* ideals of definition form one.
The second is not a consequence of the first: the powers `Iⁿ` of a weak ideal of definition need
not be cofinal among the neighbourhoods of zero, and the argument below never uses them, running
instead over the whole directed family.

## Main definitions

* `TopologicalRing.IsFundamentalIdealSystem`: the three conditions on the family.
* `TopologicalRing.idealLimit` and `TopologicalRing.toIdealLimit`: the inverse limit of the
  quotients along the family, and the comparison map into it.

## Main results

* `TopologicalRing.IsIdealOfDefinition.inf`: the ideals of definition are closed under
  intersection, and meeting one with an arbitrary open ideal again gives one.
* `TopologicalRing.exists_isIdealOfDefinition_le`: a finite family of open ideals has a common
  lower bound which is an ideal of definition, and
  `TopologicalRing.IsFundamentalIdealSystem.exists_forall_ringHom_comp_mk`: a finite family of
  continuous homomorphisms into discrete rings therefore factors through the quotient by one and
  the same member of a fundamental system of ideals.
* `TopologicalRing.hasBasis_isIdealOfDefinition`: in a linearly topologized pre-admissible ring
  the ideals of definition form a neighbourhood basis of zero.
* `TopologicalRing.isFundamentalIdealSystem_isIdealOfDefinition` and
  `TopologicalRing.isFundamentalIdealSystem_isWeakIdealOfDefinition`: the ideals of definition of
  an admissible ring and the weak ideals of definition of a weakly admissible one are fundamental
  systems of ideals.
* `TopologicalRing.toIdealLimit_injective`: separatedness makes the comparison map injective.
* `TopologicalRing.toIdealLimit_surjective`: completeness makes it surjective.
* `TopologicalRing.homeomorphIdealLimit` and `TopologicalRing.ringEquivIdealLimit`: the
  comparison map is an isomorphism of topological rings.

## References

* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
-/

@[expose] public section

namespace TopologicalRing

open Filter
open scoped Topology

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- Meeting an ideal of definition with an open ideal again gives an ideal of definition. -/
public theorem IsIdealOfDefinition.inf_of_isOpen {I J : Ideal A}
    (hI : IsIdealOfDefinition I) (hJ : IsOpen (J : Set A)) :
    IsIdealOfDefinition (I ⊓ J) := by
  refine ⟨?_, fun U hU ↦ ?_⟩
  · rw [Submodule.coe_inf]
    exact hI.1.inter hJ
  · obtain ⟨n, hn⟩ := hI.2 U hU
    exact ⟨n, fun _ hx ↦ hn (Ideal.pow_right_mono inf_le_left n hx)⟩

/-- The ideals of definition of a topological ring are closed under intersection. -/
public theorem IsIdealOfDefinition.inf {I J : Ideal A}
    (hI : IsIdealOfDefinition I) (hJ : IsIdealOfDefinition J) :
    IsIdealOfDefinition (I ⊓ J) :=
  hI.inf_of_isOpen hJ.1

/-- A finite intersection of open ideals is open. -/
private theorem isOpen_iInf_ideal {ι : Sort*} [Finite ι] {K : ι → Ideal A}
    (hK : ∀ i, IsOpen (K i : Set A)) : IsOpen ((⨅ i, K i : Ideal A) : Set A) := by
  rw [Submodule.coe_iInf]
  exact isOpen_iInter_of_finite hK

/-- Meeting an ideal of definition with a *finite* family of open ideals again gives an ideal of
definition: a finite intersection of open sets is open, so `AlgebraicGeometry` arguments that
produce one open ideal per member of a finite family can always be made to use a single ideal of
definition. -/
public theorem IsIdealOfDefinition.iInf_of_isOpen {ι : Sort*} [Finite ι] {I : Ideal A}
    (hI : IsIdealOfDefinition I) {K : ι → Ideal A} (hK : ∀ i, IsOpen (K i : Set A)) :
    IsIdealOfDefinition (I ⊓ ⨅ i, K i) := by
  exact hI.inf_of_isOpen (isOpen_iInf_ideal hK)

/-- **One ideal of definition below a whole finite family of open ideals.** In a pre-admissible
topological ring any finite family of open ideals admits a common lower bound which is itself an
ideal of definition, namely the intersection of the family with one ideal of definition.

This is the uniformity statement behind every argument that chooses an open ideal separately for
each member of a finite family — one quasi-compact open of a formal spectrum at a time, say — and
then needs a single choice serving them all. -/
public theorem exists_isIdealOfDefinition_le {ι : Sort*} [Finite ι] (hA : IsPreAdmissible A)
    (K : ι → Ideal A) (hK : ∀ i, IsOpen (K i : Set A)) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∀ i, I ≤ K i := by
  obtain ⟨I₀, hI₀⟩ := hA
  exact ⟨I₀ ⊓ ⨅ i, K i, hI₀.iInf_of_isOpen hK, fun i => inf_le_right.trans (iInf_le _ i)⟩

/-- In a linearly topologized pre-admissible ring the ideals of definition form a neighbourhood
basis of zero. -/
public theorem hasBasis_isIdealOfDefinition [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsPreAdmissible A) :
    (𝓝 (0 : A)).HasBasis (fun I : Ideal A ↦ IsIdealOfDefinition I) (fun I ↦ (I : Set A)) := by
  obtain ⟨I, hI⟩ := hA
  refine (IsLinearTopology.hasBasis_open_ideal (R := A)).to_hasBasis ?_ ?_
  · intro J hJ
    refine ⟨I ⊓ J, hI.inf_of_isOpen hJ, ?_⟩
    rw [Submodule.coe_inf]
    exact Set.inter_subset_right
  · exact fun J hJ ↦ ⟨J, hJ.1, subset_rfl⟩

/-- The quotient of a topological ring by an open ideal is discrete. -/
public theorem discreteTopology_quotient_of_isOpen [IsTopologicalRing A] {I : Ideal A}
    (hI : IsOpen (I : Set A)) : DiscreteTopology (A ⧸ I) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have heq : (Ideal.Quotient.mk I) '' (I : Set A) = {(0 : A ⧸ I)} := by
    ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨a, ha, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    · obtain rfl : x = 0 := by simpa using hx
      exact ⟨0, I.zero_mem, map_zero _⟩
  rw [← heq]
  exact (QuotientRing.isOpenMap_coe I) _ hI

/-! ### Fundamental systems of ideals -/

/-- A family `P` of ideals of a topological ring `A` is a *fundamental system of ideals* when
every member of it is open, the family is closed under intersection, and the members form a
neighbourhood basis of zero.

These are the only three properties of the family that the identification of `A` with the limit
of the discrete rings `A ⧸ I`, `I` running through `P`, consumes: openness makes each quotient
discrete, closure under intersection makes the index directed, and the basis condition is what
separatedness and completeness of `A` are expressed against. In particular no cofinality of the
*powers* of a member is used, which is why both the ideals of definition of an admissible ring
and the weak ideals of definition of a weakly admissible one are covered. -/
public structure IsFundamentalIdealSystem (A : Type u) [CommRing A] [TopologicalSpace A]
    (P : Ideal A → Prop) : Prop where
  /-- Every member of the family is open. -/
  isOpen : ∀ I : Ideal A, P I → IsOpen (I : Set A)
  /-- The family is closed under intersection. -/
  inf_mem : ∀ {I J : Ideal A}, P I → P J → P (I ⊓ J)
  /-- The members of the family form a neighbourhood basis of zero. -/
  hasBasis : (𝓝 (0 : A)).HasBasis P (fun I : Ideal A ↦ (I : Set A))

variable {P : Ideal A → Prop}

/-- A fundamental system of ideals is nonempty: the whole ring is a neighbourhood of zero, so
some member of the family is contained in it. -/
public theorem IsFundamentalIdealSystem.exists_mem (h : IsFundamentalIdealSystem A P) :
    ∃ I : Ideal A, P I := by
  obtain ⟨I, hI, -⟩ := h.hasBasis.mem_iff.mp Filter.univ_mem
  exact ⟨I, hI⟩

/-- Every member of a fundamental system of ideals is a neighbourhood of zero. -/
public theorem IsFundamentalIdealSystem.mem_nhds (h : IsFundamentalIdealSystem A P)
    {I : Ideal A} (hI : P I) : (I : Set A) ∈ 𝓝 (0 : A) :=
  h.hasBasis.mem_of_mem hI

/-- An open ideal contains a member of any fundamental system of ideals. -/
public theorem IsFundamentalIdealSystem.exists_mem_le_of_isOpen
    (h : IsFundamentalIdealSystem A P) {J : Ideal A} (hJ : IsOpen (J : Set A)) :
    ∃ I : Ideal A, P I ∧ I ≤ J := by
  obtain ⟨I, hI, hsub⟩ := h.hasBasis.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  exact ⟨I, hI, hsub⟩

/-- **One member of the family below a whole finite family of open ideals.** A finite family of
open ideals admits a common lower bound belonging to any fundamental system of ideals: a finite
intersection of open ideals is again an open ideal, and an open ideal contains a member of the
system.

This is the uniformity statement behind every argument that chooses an open ideal separately for
each member of a finite family and then needs a single choice serving them all. -/
public theorem IsFundamentalIdealSystem.exists_mem_le (h : IsFundamentalIdealSystem A P)
    {ι : Sort*} [Finite ι] (K : ι → Ideal A) (hK : ∀ i, IsOpen (K i : Set A)) :
    ∃ I : Ideal A, P I ∧ ∀ i, I ≤ K i := by
  obtain ⟨I, hI, hle⟩ := h.exists_mem_le_of_isOpen (isOpen_iInf_ideal hK)
  exact ⟨I, hI, fun i => hle.trans (iInf_le _ i)⟩

/-- The ideals of definition of a linearly topologized pre-admissible ring form a fundamental
system of ideals: each is open, they are closed under intersection, and they are a neighbourhood
basis of zero. -/
public theorem isFundamentalIdealSystem_isIdealOfDefinition [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsPreAdmissible A) :
    IsFundamentalIdealSystem A IsIdealOfDefinition where
  isOpen _ hI := hI.1
  inf_mem hI hJ := hI.inf hJ
  hasBasis := hasBasis_isIdealOfDefinition hA

/-- **The weak ideals of definition of a weakly admissible ring form a fundamental system of
ideals.** Each is open by definition; the intersection of two of them is again one, being the
intersection of a weak ideal of definition with an open ideal; and they are a neighbourhood basis
of zero, which is the fundamental-system clause of Stacks 0AI3.

Nothing here refers to the powers of a weak ideal of definition, which need not be cofinal among
the neighbourhoods of zero. -/
public theorem isFundamentalIdealSystem_isWeakIdealOfDefinition [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsWeaklyAdmissible A) :
    IsFundamentalIdealSystem A IsWeakIdealOfDefinition where
  isOpen _ hI := hI.1
  inf_mem hI hJ := isWeakIdealOfDefinition_inf_of_isOpen_right hI hJ.1
  hasBasis := hasBasis_nhds_zero_isWeakIdealOfDefinition hA

/-! ### The limit of the quotients along a family of ideals -/

/-- The type of ideals of definition of a topological ring, the index of the limit of discrete
quotients. -/
public abbrev IdealOfDefinition (A : Type u) [CommRing A] [TopologicalSpace A] : Type u :=
  {I : Ideal A // IsIdealOfDefinition I}

/-- The inverse limit of the quotients of `A` by the members of a family `P` of ideals, realized
as the subring of compatible families of residues inside their product. -/
public def idealLimit (A : Type u) [CommRing A] [TopologicalSpace A] (P : Ideal A → Prop) :
    Subring (∀ I : {I : Ideal A // P I}, A ⧸ I.1) where
  carrier := {x | ∀ I J : {I : Ideal A // P I}, ∀ h : I.1 ≤ J.1,
    Ideal.Quotient.factor h (x I) = x J}
  one_mem' := fun _ _ _ ↦ by simp only [Pi.one_apply, map_one]
  mul_mem' hx hy := fun I J h ↦ by simp only [Pi.mul_apply, map_mul, hx I J h, hy I J h]
  zero_mem' := fun _ _ _ ↦ by simp only [Pi.zero_apply, map_zero]
  add_mem' hx hy := fun I J h ↦ by simp only [Pi.add_apply, map_add, hx I J h, hy I J h]
  neg_mem' hx := fun I J h ↦ by simp only [Pi.neg_apply, map_neg, hx I J h]

/-- The comparison ring homomorphism sending an element to its family of residues. -/
public def toIdealLimit (A : Type u) [CommRing A] [TopologicalSpace A] (P : Ideal A → Prop) :
    A →+* idealLimit A P :=
  RingHom.codRestrict (RingHom.pi fun I : {I : Ideal A // P I} ↦ Ideal.Quotient.mk I.1)
    (idealLimit A P) fun a _ _ h ↦ Ideal.Quotient.factor_mk h a

/-- The component of `toIdealLimit A P a` at `I` is the residue of `a` modulo `I`. -/
@[simp]
public theorem toIdealLimit_apply_coe (a : A) (I : {I : Ideal A // P I}) :
    (toIdealLimit A P a).1 I = Ideal.Quotient.mk I.1 a :=
  rfl

/-- The comparison map is continuous: each residue map is continuous for the quotient
topology. -/
public theorem continuous_toIdealLimit [IsTopologicalRing A] :
    Continuous (toIdealLimit A P) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun _ ↦ continuous_quot_mk

/-- In a separated topological ring the members of a fundamental system of ideals intersect in
zero. -/
public theorem IsFundamentalIdealSystem.eq_zero_of_forall_mem [T2Space A]
    (h : IsFundamentalIdealSystem A P) {a : A} (ha : ∀ I : Ideal A, P I → a ∈ I) : a = 0 := by
  by_contra hne
  have ho : ({a}ᶜ : Set A) ∈ 𝓝 (0 : A) :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simpa using Ne.symm hne)
  obtain ⟨I, hI, hsub⟩ := h.hasBasis.mem_iff.mp ho
  exact hsub (ha I hI) rfl

/-- Separatedness makes the comparison map injective. -/
public theorem toIdealLimit_injective [T2Space A] (h : IsFundamentalIdealSystem A P) :
    Function.Injective (toIdealLimit A P) := by
  intro a b hab
  refine sub_eq_zero.mp (h.eq_zero_of_forall_mem fun I hI ↦ ?_)
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp ?_
  exact congrArg (fun x : idealLimit A P ↦ x.1 ⟨I, hI⟩) hab

/-- **Completeness makes the comparison map surjective.** A compatible family of residues along
a fundamental system of ideals generates a Cauchy filter of cosets, and any limit of that filter
realizes the family.

The filter is indexed by the whole family, directed by closure under intersection; nothing is
asked of the powers of a member. -/
public theorem toIdealLimit_surjective [IsTopologicalRing A] (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    Function.Surjective (toIdealLimit A P) := by
  intro x
  have : Nonempty {I : Ideal A // P I} := h.exists_mem.elim fun I₀ hI₀ ↦ ⟨⟨I₀, hI₀⟩⟩
  choose a ha using fun I : {I : Ideal A // P I} ↦ Ideal.Quotient.mk_surjective (x.1 I)
  have hlift : ∀ I J : {I : Ideal A // P I}, I.1 ≤ J.1 → a I - a J ∈ J.1 := by
    intro I J hle
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem (a I) (a J)).mp ?_
    have hx := x.2 I J hle
    rwa [← ha I, ← ha J, Ideal.Quotient.factor_mk] at hx
  let c : {I : Ideal A // P I} → Set A := fun I ↦ {y | y - a I ∈ I.1}
  have hmemc : ∀ (I : {I : Ideal A // P I}) (y : A), y ∈ c I ↔ y - a I ∈ I.1 :=
    fun _ _ ↦ Iff.rfl
  have hsub : ∀ I J : {I : Ideal A // P I}, I.1 ≤ J.1 → c I ⊆ c J := by
    intro I J hle y hy
    have hy' : y - a I ∈ J.1 := hle ((hmemc I y).mp hy)
    have hrw : y - a J = (y - a I) + (a I - a J) := by ring
    exact (hmemc J y).mpr (hrw ▸ J.1.add_mem hy' (hlift I J hle))
  have hdir : Directed (· ≥ ·) c := fun I J ↦
    ⟨⟨I.1 ⊓ J.1, h.inf_mem I.2 J.2⟩, hsub _ _ inf_le_left, hsub _ _ inf_le_right⟩
  have hbasisF : (⨅ I, 𝓟 (c I)).HasBasis (fun _ : {I : Ideal A // P I} ↦ True) c :=
    hasBasis_iInf_principal hdir
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let _ : CompleteSpace A := hc
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have hne : (⨅ I, 𝓟 (c I)).NeBot :=
    hbasisF.neBot_iff.mpr fun {I} _ ↦
      ⟨a I, (hmemc I (a I)).mpr (by simp)⟩
  have hCauchy : Cauchy (⨅ I, 𝓟 (c I)) := by
    refine (IsUniformAddGroup.cauchy_iff_tendsto _).mpr ⟨hne, ?_⟩
    refine h.hasBasis.tendsto_right_iff.mpr fun I hI ↦ ?_
    have hmem : c ⟨I, hI⟩ ×ˢ c ⟨I, hI⟩ ∈ (⨅ J, 𝓟 (c J)) ×ˢ (⨅ J, 𝓟 (c J)) :=
      Filter.prod_mem_prod (hbasisF.mem_of_mem trivial) (hbasisF.mem_of_mem trivial)
    refine Filter.mem_of_superset hmem ?_
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    change y - z ∈ I
    rw [show y - z = (y - a ⟨I, hI⟩) - (z - a ⟨I, hI⟩) by ring]
    exact I.sub_mem ((hmemc _ y).mp hy) ((hmemc _ z).mp hz)
  obtain ⟨b, hb⟩ := CompleteSpace.complete hCauchy
  refine ⟨b, Subtype.ext (funext fun I ↦ ?_)⟩
  have hnbhd : {y : A | y - b ∈ I.1} ∈ 𝓝 b :=
    ((h.isOpen I.1 I.2).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨y, hy₁, hy₂⟩ :=
    Filter.nonempty_of_mem (Filter.inter_mem (hb hnbhd) (hbasisF.mem_of_mem (i := I) trivial))
  have hbI : b - a I ∈ I.1 := by
    have hrw : b - a I = (y - a I) - (y - b) := by ring
    exact hrw ▸ I.1.sub_mem hy₂ hy₁
  rw [toIdealLimit_apply_coe, ← ha I]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem b (a I)).mpr hbI

/-- For a complete separated ring the comparison map along a fundamental system of ideals is
bijective. -/
public theorem toIdealLimit_bijective [IsTopologicalRing A] [T2Space A]
    (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    Function.Bijective (toIdealLimit A P) :=
  ⟨toIdealLimit_injective h, toIdealLimit_surjective h hc⟩

/-- The ring isomorphism of a complete separated ring with the limit of its quotients along a
fundamental system of ideals. -/
public noncomputable def ringEquivIdealLimit [IsTopologicalRing A] [T2Space A]
    (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    A ≃+* idealLimit A P :=
  RingEquiv.ofBijective (toIdealLimit A P) (toIdealLimit_bijective h hc)

/-- The component of `ringEquivIdealLimit h hc a` at `I` is the residue of `a` modulo `I`. -/
@[simp]
public theorem ringEquivIdealLimit_apply_coe [IsTopologicalRing A] [T2Space A]
    (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (a : A)
    (I : {I : Ideal A // P I}) :
    (ringEquivIdealLimit h hc a).1 I = Ideal.Quotient.mk I.1 a :=
  rfl

/-- The inverse of the comparison isomorphism is continuous: the kernel of each projection of
the limit is open, and the members of the family are a basis of neighbourhoods of zero. -/
public theorem continuous_ringEquivIdealLimit_symm [IsTopologicalRing A] [T2Space A]
    (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    Continuous (ringEquivIdealLimit h hc).symm := by
  let e := ringEquivIdealLimit h hc
  apply continuous_of_tendsto_nhds_zero e.symm.toAddMonoidHom
  refine h.hasBasis.tendsto_right_iff.mpr fun I hI ↦ ?_
  have : DiscreteTopology (A ⧸ I) := discreteTopology_quotient_of_isOpen (h.isOpen I hI)
  have hnbhd : {y : idealLimit A P | y.1 ⟨I, hI⟩ = 0} ∈ 𝓝 (0 : idealLimit A P) :=
    ((isOpen_discrete {0}).preimage
      ((continuous_apply _).comp continuous_subtype_val)).mem_nhds rfl
  refine Filter.mem_of_superset hnbhd fun y hy ↦ Ideal.Quotient.eq_zero_iff_mem.mp ?_
  exact (congrArg (fun z : idealLimit A P ↦ z.1 ⟨I, hI⟩) (e.apply_symm_apply y)).trans hy

/-- The homeomorphism of a complete separated ring with the limit of its quotients along a
fundamental system of ideals; together with `TopologicalRing.ringEquivIdealLimit` this is an
isomorphism of topological rings. -/
public noncomputable def homeomorphIdealLimit [IsTopologicalRing A] [T2Space A]
    (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    A ≃ₜ idealLimit A P where
  toEquiv := (ringEquivIdealLimit h hc).toEquiv
  continuous_toFun := continuous_toIdealLimit
  continuous_invFun := continuous_ringEquivIdealLimit_symm h hc

/-- The component of `homeomorphIdealLimit h hc a` at `I` is the residue of `a` modulo `I`. -/
@[simp]
public theorem homeomorphIdealLimit_apply_coe [IsTopologicalRing A] [T2Space A]
    (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (a : A)
    (I : {I : Ideal A // P I}) :
    (homeomorphIdealLimit h hc a).1 I = Ideal.Quotient.mk I.1 a :=
  rfl

/-- A complete separated topological ring is the limit of its quotients along any fundamental
system of ideals: the family of residue maps is a ring isomorphism onto the limit and a
homeomorphism for the limit topology. -/
public theorem exists_ringEquiv_idealLimit [IsTopologicalRing A] [T2Space A]
    (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    ∃ e : A ≃+* idealLimit A P, Continuous e ∧ Continuous e.symm ∧
      ∀ (a : A) (I : {I : Ideal A // P I}), (e a).1 I = Ideal.Quotient.mk I.1 a :=
  ⟨ringEquivIdealLimit h hc, continuous_toIdealLimit,
    continuous_ringEquivIdealLimit_symm h hc, fun _ _ ↦ rfl⟩

/-! ### The ideals of definition of an admissible ring

The declarations below are the case `P = IsIdealOfDefinition` of the limit along a fundamental
system of ideals above: for a linearly topologized pre-admissible ring the ideals of definition
form a fundamental system of ideals, by
`TopologicalRing.isFundamentalIdealSystem_isIdealOfDefinition`. -/

/-- The inverse limit of the quotients of `A` by its ideals of definition, realized as the
subring of compatible families of residues inside their product: the case
`P = IsIdealOfDefinition` of `TopologicalRing.idealLimit`. -/
@[reducible] public def idealOfDefinitionLimit (A : Type u) [CommRing A] [TopologicalSpace A] :
    Subring (∀ I : IdealOfDefinition A, A ⧸ I.1) :=
  idealLimit A IsIdealOfDefinition

/-- The comparison ring homomorphism sending an element to its family of residues. -/
@[reducible] public def toIdealOfDefinitionLimit (A : Type u) [CommRing A] [TopologicalSpace A] :
    A →+* idealOfDefinitionLimit A :=
  toIdealLimit A IsIdealOfDefinition

/-- The component of `toIdealOfDefinitionLimit A a` at `I` is the residue of `a` modulo `I`. -/
@[simp]
public theorem toIdealOfDefinitionLimit_apply_coe (a : A) (I : IdealOfDefinition A) :
    (toIdealOfDefinitionLimit A a).1 I = Ideal.Quotient.mk I.1 a :=
  rfl

/-- The comparison map is continuous: each residue map is continuous for the quotient
topology. -/
public theorem continuous_toIdealOfDefinitionLimit [IsTopologicalRing A] :
    Continuous (toIdealOfDefinitionLimit A) :=
  continuous_toIdealLimit

/-- In a separated linearly topologized pre-admissible ring the ideals of definition intersect
in zero. -/
public theorem eq_zero_of_mem_isIdealOfDefinition [IsTopologicalRing A] [IsLinearTopology A A]
    [T2Space A] (hA : IsPreAdmissible A) {a : A}
    (ha : ∀ I : Ideal A, IsIdealOfDefinition I → a ∈ I) : a = 0 :=
  (isFundamentalIdealSystem_isIdealOfDefinition hA).eq_zero_of_forall_mem ha

/-- Separatedness makes the comparison map injective. -/
public theorem toIdealOfDefinitionLimit_injective [IsTopologicalRing A] [IsLinearTopology A A]
    [T2Space A] (hA : IsPreAdmissible A) :
    Function.Injective (toIdealOfDefinitionLimit A) :=
  toIdealLimit_injective (isFundamentalIdealSystem_isIdealOfDefinition hA)

/-- Completeness makes the comparison map surjective: a compatible family of residues generates
a Cauchy filter of cosets, and any limit of that filter realizes the family. -/
public theorem toIdealOfDefinitionLimit_surjective [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsPreAdmissible A)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    Function.Surjective (toIdealOfDefinitionLimit A) :=
  toIdealLimit_surjective (isFundamentalIdealSystem_isIdealOfDefinition hA) hc

/-- For an admissible ring the comparison map is bijective. -/
public theorem toIdealOfDefinitionLimit_bijective [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsAdmissible A) : Function.Bijective (toIdealOfDefinitionLimit A) := by
  have := hA.2.1
  exact toIdealLimit_bijective (isFundamentalIdealSystem_isIdealOfDefinition hA.1) hA.2.2

/-- The ring isomorphism of an admissible ring with the limit of its quotients by ideals of
definition. -/
public noncomputable def ringEquivIdealOfDefinitionLimit [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsAdmissible A) : A ≃+* idealOfDefinitionLimit A :=
  RingEquiv.ofBijective (toIdealOfDefinitionLimit A) (toIdealOfDefinitionLimit_bijective hA)

/-- The component of `ringEquivIdealOfDefinitionLimit hA a` at `I` is the residue of `a`
modulo `I`. -/
@[simp]
public theorem ringEquivIdealOfDefinitionLimit_apply_coe [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsAdmissible A) (a : A) (I : IdealOfDefinition A) :
    (ringEquivIdealOfDefinitionLimit hA a).1 I = Ideal.Quotient.mk I.1 a :=
  rfl

/-- The inverse of the comparison isomorphism is continuous: the kernel of each projection of
the limit is open, and the ideals of definition form a basis of neighbourhoods of zero. -/
public theorem continuous_ringEquivIdealOfDefinitionLimit_symm [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsAdmissible A) :
    Continuous (ringEquivIdealOfDefinitionLimit hA).symm :=
  have := hA.2.1
  continuous_ringEquivIdealLimit_symm (isFundamentalIdealSystem_isIdealOfDefinition hA.1) hA.2.2

/-- The homeomorphism of an admissible ring with the limit of its quotients by ideals of
definition; together with `ringEquivIdealOfDefinitionLimit` this is an isomorphism of
topological rings. -/
public noncomputable def homeomorphIdealOfDefinitionLimit [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsAdmissible A) : A ≃ₜ idealOfDefinitionLimit A where
  toEquiv := (ringEquivIdealOfDefinitionLimit hA).toEquiv
  continuous_toFun := continuous_toIdealOfDefinitionLimit
  continuous_invFun := continuous_ringEquivIdealOfDefinitionLimit_symm hA

/-- The component of `homeomorphIdealOfDefinitionLimit hA a` at `I` is the residue of `a`
modulo `I`. -/
@[simp]
public theorem homeomorphIdealOfDefinitionLimit_apply_coe [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsAdmissible A) (a : A) (I : IdealOfDefinition A) :
    (homeomorphIdealOfDefinitionLimit hA a).1 I = Ideal.Quotient.mk I.1 a :=
  rfl

/-- An admissible topological ring is the limit of its quotients by its ideals of definition:
the family of residue maps is a ring isomorphism onto the limit and a homeomorphism for the
limit topology. -/
public theorem exists_ringEquiv_idealOfDefinitionLimit [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsAdmissible A) :
    ∃ e : A ≃+* idealOfDefinitionLimit A, Continuous e ∧ Continuous e.symm ∧
      ∀ (a : A) (I : IdealOfDefinition A), (e a).1 I = Ideal.Quotient.mk I.1 a :=
  ⟨ringEquivIdealOfDefinitionLimit hA, continuous_toIdealOfDefinitionLimit,
    continuous_ringEquivIdealOfDefinitionLimit_symm hA, fun _ _ ↦ rfl⟩

/-- A weakly admissible topological ring is the limit of its quotients by its weak ideals of
definition. This is the counterpart for McQuillan's weakening of the identification used in
Stacks 0AHY, and it is proved over the whole directed family of weak ideals of definition: the
powers of one of them need not be cofinal. -/
public theorem exists_ringEquiv_weakIdealOfDefinitionLimit [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsWeaklyAdmissible A) :
    ∃ e : A ≃+* idealLimit A IsWeakIdealOfDefinition, Continuous e ∧ Continuous e.symm ∧
      ∀ (a : A) (I : {I : Ideal A // IsWeakIdealOfDefinition I}),
        (e a).1 I = Ideal.Quotient.mk I.1 a :=
  have := hA.2.2
  exists_ringEquiv_idealLimit (isFundamentalIdealSystem_isWeakIdealOfDefinition hA) hA.2.1

/-! ### Continuous maps into a discrete ring factor through a single quotient -/

/-- The kernel of a continuous ring homomorphism into a discrete ring is open. -/
private theorem isOpen_ker_of_continuous {S : Type*} [CommRing S] [TopologicalSpace S]
    [DiscreteTopology S] (ψ : A →+* S) (hψ : Continuous ψ) :
    IsOpen ((RingHom.ker ψ : Ideal A) : Set A) :=
  (isOpen_discrete {(0 : S)}).preimage hψ

/-- A continuous additive homomorphism into a discrete topological additive group vanishes on
some member of any neighbourhood basis of zero: the preimage of zero is open and contains
zero, so it contains a basic neighbourhood. -/
public theorem exists_basis_apply_eq_zero {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [DiscreteTopology T] {ι : Sort*}
    {p : ι → Prop} {s : ι → Set G} (hbasis : (𝓝 (0 : G)).HasBasis p s) (ψ : G →+ T)
    (hψ : Continuous ψ) :
    ∃ i, p i ∧ ∀ x ∈ s i, ψ x = 0 := by
  have hmem : ψ ⁻¹' {0} ∈ 𝓝 (0 : G) :=
    ((isOpen_discrete {(0 : T)}).preimage hψ).mem_nhds (map_zero ψ)
  obtain ⟨i, hi, hsub⟩ := hbasis.mem_iff.mp hmem
  exact ⟨i, hi, fun x hx ↦ hsub hx⟩

/-- A continuous ring homomorphism from a linearly topologized ring into a discrete ring
vanishes on an open ideal. -/
public theorem exists_isOpen_ideal_apply_eq_zero {S : Type*} [CommRing S] [TopologicalSpace S]
    [DiscreteTopology S] [IsTopologicalRing A] [IsLinearTopology A A] (ψ : A →+* S)
    (hψ : Continuous ψ) :
    ∃ I : Ideal A, IsOpen (I : Set A) ∧ ∀ x ∈ I, ψ x = 0 := by
  obtain ⟨I, hI, hker⟩ :=
    exists_basis_apply_eq_zero IsLinearTopology.hasBasis_open_ideal ψ.toAddMonoidHom hψ
  exact ⟨I, hI, hker⟩

/-- A continuous ring homomorphism into a discrete ring vanishes on a member of any fundamental
system of ideals. -/
public theorem IsFundamentalIdealSystem.exists_apply_eq_zero {S : Type*} [CommRing S]
    [TopologicalSpace S] [DiscreteTopology S] (h : IsFundamentalIdealSystem A P) (ψ : A →+* S)
    (hψ : Continuous ψ) : ∃ I : Ideal A, P I ∧ ∀ x ∈ I, ψ x = 0 := by
  obtain ⟨I, hI, hker⟩ := exists_basis_apply_eq_zero h.hasBasis ψ.toAddMonoidHom hψ
  exact ⟨I, hI, hker⟩

/-- **Factoring through a single quotient.** A continuous ring homomorphism into a discrete ring
factors through the quotient by a single member of any fundamental system of ideals.

The members of the system form a neighbourhood basis of zero, so the preimage of zero — open
because the target is discrete — contains one of them, and the homomorphism descends to the
quotient by that one. This is the ring-theoretic content of the statement that a continuous map
out of an inverse limit of discrete rings depends on only one term of the system. -/
@[ega "0 19.5.6.1" "partial"]
public theorem IsFundamentalIdealSystem.exists_ringHom_comp_mk {S : Type*} [CommRing S]
    [TopologicalSpace S] [DiscreteTopology S] (h : IsFundamentalIdealSystem A P) (ψ : A →+* S)
    (hψ : Continuous ψ) :
    ∃ I : Ideal A, P I ∧ ∃ χ : A ⧸ I →+* S, χ.comp (Ideal.Quotient.mk I) = ψ := by
  obtain ⟨I, hI, hker⟩ := h.exists_apply_eq_zero ψ hψ
  exact ⟨I, hI, Ideal.Quotient.lift I ψ hker, Ideal.Quotient.lift_comp_mk I ψ hker⟩

/-- **Uniformity of the kernel over a finite family of targets.** A *finite* family of continuous
ring homomorphisms into discrete rings is killed by a single member of any fundamental system of
ideals.

Each member is killed by its own open ideal, namely its kernel, and a finite family of open
ideals has a common lower bound in the system by
`TopologicalRing.IsFundamentalIdealSystem.exists_mem_le`. -/
public theorem IsFundamentalIdealSystem.exists_forall_apply_eq_zero {ι : Sort*} [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, TopologicalSpace (S i)]
    [∀ i, DiscreteTopology (S i)] (h : IsFundamentalIdealSystem A P) (ψ : ∀ i, A →+* S i)
    (hψ : ∀ i, Continuous (ψ i)) :
    ∃ I : Ideal A, P I ∧ ∀ (i : ι), ∀ x ∈ I, ψ i x = 0 := by
  obtain ⟨I, hI, hle⟩ := h.exists_mem_le (fun i => RingHom.ker (ψ i))
    fun i => isOpen_ker_of_continuous (ψ i) (hψ i)
  exact ⟨I, hI, fun i x hx => RingHom.mem_ker.1 (hle i hx)⟩

/-- **Uniform factoring through a single quotient.** A finite family of continuous ring
homomorphisms into discrete rings factors through the quotient by one and the same member of a
fundamental system of ideals. -/
public theorem IsFundamentalIdealSystem.exists_forall_ringHom_comp_mk {ι : Sort*} [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, TopologicalSpace (S i)]
    [∀ i, DiscreteTopology (S i)] (h : IsFundamentalIdealSystem A P) (ψ : ∀ i, A →+* S i)
    (hψ : ∀ i, Continuous (ψ i)) :
    ∃ I : Ideal A, P I ∧ ∃ χ : ∀ i, A ⧸ I →+* S i,
      ∀ i, (χ i).comp (Ideal.Quotient.mk I) = ψ i := by
  obtain ⟨I, hI, hker⟩ := h.exists_forall_apply_eq_zero ψ hψ
  exact ⟨I, hI, fun i => Ideal.Quotient.lift I (ψ i) (hker i),
    fun i => Ideal.Quotient.lift_comp_mk I (ψ i) (hker i)⟩

/-- A continuous ring homomorphism from a linearly topologized pre-admissible ring into a
discrete ring vanishes on an ideal of definition. -/
public theorem exists_isIdealOfDefinition_apply_eq_zero {S : Type*} [CommRing S]
    [TopologicalSpace S] [DiscreteTopology S] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsPreAdmissible A) (ψ : A →+* S) (hψ : Continuous ψ) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∀ x ∈ I, ψ x = 0 :=
  (isFundamentalIdealSystem_isIdealOfDefinition hA).exists_apply_eq_zero ψ hψ

/-- **Factoring through a single quotient.** A continuous ring homomorphism from a linearly
topologized pre-admissible ring into a discrete ring factors through the quotient by a single
ideal of definition: the case `P = IsIdealOfDefinition` of
`TopologicalRing.IsFundamentalIdealSystem.exists_ringHom_comp_mk`. -/
public theorem exists_isIdealOfDefinition_ringHom_comp_mk {S : Type*} [CommRing S]
    [TopologicalSpace S] [DiscreteTopology S] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsPreAdmissible A) (ψ : A →+* S) (hψ : Continuous ψ) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧
      ∃ χ : A ⧸ I →+* S, χ.comp (Ideal.Quotient.mk I) = ψ :=
  (isFundamentalIdealSystem_isIdealOfDefinition hA).exists_ringHom_comp_mk ψ hψ

/-- **Uniformity of the kernel over a finite family of targets.** A *finite* family of
continuous ring homomorphisms from a pre-admissible topological ring into discrete rings is
killed by a single ideal of definition.

Each member is killed by its own open ideal, namely its kernel, and a finite family of open
ideals has a common lower bound which is an ideal of definition by
`TopologicalRing.exists_isIdealOfDefinition_le`. No linearity of the topology is needed: the
kernels are already open, so no neighbourhood basis has to be produced. -/
public theorem exists_isIdealOfDefinition_forall_apply_eq_zero {ι : Sort*} [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, TopologicalSpace (S i)]
    [∀ i, DiscreteTopology (S i)] (hA : IsPreAdmissible A) (ψ : ∀ i, A →+* S i)
    (hψ : ∀ i, Continuous (ψ i)) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∀ (i : ι), ∀ x ∈ I, ψ i x = 0 := by
  obtain ⟨I, hI, hle⟩ := exists_isIdealOfDefinition_le hA (fun i => RingHom.ker (ψ i))
    fun i => isOpen_ker_of_continuous (ψ i) (hψ i)
  exact ⟨I, hI, fun i x hx => RingHom.mem_ker.1 (hle i hx)⟩

/-- **Uniform factoring through a single quotient.** A finite family of continuous ring
homomorphisms from a pre-admissible topological ring into discrete rings factors through the
quotient by one and the same ideal of definition. -/
public theorem exists_isIdealOfDefinition_forall_ringHom_comp_mk {ι : Sort*} [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, TopologicalSpace (S i)]
    [∀ i, DiscreteTopology (S i)] (hA : IsPreAdmissible A) (ψ : ∀ i, A →+* S i)
    (hψ : ∀ i, Continuous (ψ i)) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ χ : ∀ i, A ⧸ I →+* S i,
      ∀ i, (χ i).comp (Ideal.Quotient.mk I) = ψ i := by
  obtain ⟨I, hI, hker⟩ := exists_isIdealOfDefinition_forall_apply_eq_zero hA ψ hψ
  exact ⟨I, hI, fun i => Ideal.Quotient.lift I (ψ i) (hker i),
    fun i => Ideal.Quotient.lift_comp_mk I (ψ i) (hker i)⟩

/-- **Factoring through a single term of the limit.** A continuous ring homomorphism into a
discrete ring, defined on the limit of the discrete quotients along a fundamental system of
ideals of a complete separated ring, vanishes on the kernel of one of the projections of that
limit.

Equivalently it factors through that single term: the limit is the ring itself, where the members
of the system form a neighbourhood basis of zero, and the kernel of the projection at a member `I`
is the image of `I`. -/
public theorem IsFundamentalIdealSystem.exists_proj_apply_eq_zero {S : Type*} [CommRing S]
    [TopologicalSpace S] [DiscreteTopology S] [IsTopologicalRing A] [T2Space A]
    (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (ψ : idealLimit A P →+* S) (hψ : Continuous ψ) :
    ∃ I : {I : Ideal A // P I}, ∀ x : idealLimit A P, x.1 I = 0 → ψ x = 0 := by
  obtain ⟨I, hI, hker⟩ := h.exists_apply_eq_zero (ψ.comp (toIdealLimit A P))
    (hψ.comp continuous_toIdealLimit)
  refine ⟨⟨I, hI⟩, fun x hx ↦ ?_⟩
  obtain ⟨a, rfl⟩ := toIdealLimit_surjective h hc x
  rw [toIdealLimit_apply_coe] at hx
  exact hker a (Ideal.Quotient.eq_zero_iff_mem.mp hx)

/-- **Factoring through a single term of the limit.** A continuous ring homomorphism into a
discrete ring, defined on the limit of the discrete quotients of an admissible ring, vanishes on
the kernel of one of the projections of that limit: the case `P = IsIdealOfDefinition` of
`TopologicalRing.IsFundamentalIdealSystem.exists_proj_apply_eq_zero`. -/
public theorem exists_idealOfDefinition_apply_eq_zero {S : Type*} [CommRing S]
    [TopologicalSpace S] [DiscreteTopology S] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsAdmissible A) (ψ : idealOfDefinitionLimit A →+* S) (hψ : Continuous ψ) :
    ∃ I : IdealOfDefinition A, ∀ x : idealOfDefinitionLimit A, x.1 I = 0 → ψ x = 0 :=
  have := hA.2.1
  (isFundamentalIdealSystem_isIdealOfDefinition hA.1).exists_proj_apply_eq_zero hA.2.2 ψ hψ

end TopologicalRing

end
