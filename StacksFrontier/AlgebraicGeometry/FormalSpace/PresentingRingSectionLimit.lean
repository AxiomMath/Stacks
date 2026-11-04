module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsIndependentOfPresentation

/-!
# The presenting ring is the limit of the section rings (Stacks 0AIC)

Let `A` be a weakly admissible topological ring and let the fppf sheaf `X` over `S` be the
colimit of the spectra of the quotients of `A` by its weak ideals of definition — condition (1)
of **Stacks 0AIC**. The concluding clause of that lemma says that the ring is recovered from any
presentation at all:

`A = lim Γ(X_λ, 𝒪)`, endowed with its limit topology, for *every* presentation
`X = colim X_λ` by affine thickenings.

This file proves that clause. By
`AlgebraicGeometry.FormalSpace.exists_stageQuotientIso_of_weakIdealColimitPresentation` the
stage rings of an arbitrary presentation are the quotients `A ⧸ Jᵢ` by a *cofinal* system of
weak ideals of definition, compatibly with the transition morphisms. Reduction modulo the `Jᵢ`
is therefore a ring homomorphism from `A` to the inverse limit of the stage rings; it is
injective because `A` is separated and the `Jᵢ` are cofinal, and surjective because `A` is
complete: a compatible family of stage sections extends to a compatible family of classes
modulo *all* weak ideals of definition, and such a family comes from an element of `A`. It is a
homeomorphism because each `Jᵢ` is open and the `Jᵢ` are cofinal, which is the two halves of
"endowed with its limit topology".

## Main definitions

* `AlgebraicGeometry.FormalSpace.topologicalSpaceSections`: the limit topology on the inverse
  limit of the section rings of a presentation, the stage rings being discrete.
* `AlgebraicGeometry.FormalSpace.sectionLimitHom` and
  `AlgebraicGeometry.FormalSpace.sectionLimitRingEquiv`: the comparison homomorphism and, for a
  weakly admissible ring, the comparison isomorphism.

## Main results

* `AlgebraicGeometry.FormalSpace.continuous_sectionLimitRingEquiv` and
  `AlgebraicGeometry.FormalSpace.continuous_sectionLimitRingEquiv_symm`: the comparison
  isomorphism is a homeomorphism.
* `exists_continuous_ringEquiv_sections_of_weakIdealColimitPresentation`:
  **Stacks 0AIC**, the clause `A = lim Γ(X_λ, 𝒪)` with its limit topology, for an arbitrary
  presentation.

## Implementation notes

The inverse limit is the one used throughout for presentations whose index lives one universe
above the schemes: `CategoryTheory.Functor.sections` of the set-valued section diagram, with the
ring structure `AlgebraicGeometry.FormalSpace.commRingSections`. Its topology is defined here
rather than taken from `StacksFrontier.Topology.Algebra.AdicTopology.DirectedLimit`, whose
`TopologicalRing.DirectedLimit` requires the index and the rings of the system to lie in the
*same* universe: here the index lies one universe above the stage rings, so that construction
does not apply and the subspace-of-a-product topology is written out, exactly as
`TopologicalRing.CompletionOver.limitTopology` does for the weak-ideal index.

The comparison isomorphism is named rather than merely asserted to exist, because its continuity
cannot be stated otherwise: an arbitrary ring isomorphism onto the limit is not continuous, and
a statement asserting only `Nonempty (A ≃+* lim Γ(X_λ, 𝒪))` would drop the topological half of
the source's conclusion.

Extending a compatible family from the cofinal system `Jᵢ` to all weak ideals of definition uses
only that a stage below a given weak ideal exists and that two stages are dominated by a third,
so the extension is computed from any stage below the ideal and is independent of that choice;
that independence is `hb_eq` in the proof, and it is what makes the extended family compatible.

The completeness and separatedness of `A` enter only through
`AlgebraicGeometry.FormalSpace.exists_lift_compatible_weak_quotients` and
`AlgebraicGeometry.FormalSpace.eq_of_weak_ideal_submem`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### The limit topology on the inverse limit of the section rings -/

section LimitTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type (u + 1)} [Category I] (D : I ⥤ BigAffineFppf B S hS)

/-- The **limit topology** on the inverse limit of the section rings of a presentation by affine
schemes: the stage rings are discrete — a stage is a scheme, and its ring of global sections
carries no topology of its own — and the limit is topologized as a subspace of their product.
This is what Stacks 0AIC means by endowing `lim Γ(X_λ, 𝒪)` with "its limit topology". -/
@[instance_reducible]
instance topologicalSpaceSections :
    TopologicalSpace (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections :=
  TopologicalSpace.induced Subtype.val <|
    @Pi.topologicalSpace Iᵒᵖ
      (fun j ↦ (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj j) fun _ ↦ ⊥

/-- The limit topology makes the inverse limit of the section rings a topological ring: it is a
subring of a product of discrete rings. -/
instance isTopologicalRingSections :
    IsTopologicalRing (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections := by
  let (j : Iᵒᵖ) :
      TopologicalSpace ((sectionDiagram B S hS D ⋙ forget₂ CommRingCat RingCat.{u}).obj j) := ⊥
  let (j : Iᵒᵖ) :
      DiscreteTopology ((sectionDiagram B S hS D ⋙ forget₂ CommRingCat RingCat.{u}).obj j) :=
    discreteTopology_bot _
  exact (RingCat.sectionsSubring
    (sectionDiagram B S hS D ⋙ forget₂ CommRingCat RingCat.{u})).instIsTopologicalRing

/-- The elements of the inverse limit of the section rings vanishing at a given stage form an
open set: the stage rings are discrete and the limit topology is induced from their product. -/
theorem isOpen_setOf_sections_apply_eq_zero (j : Iᵒᵖ) :
    IsOpen {s : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections | s.val j = 0} := by
  let (k : Iᵒᵖ) :
      TopologicalSpace ((sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj k) := ⊥
  let (k : Iᵒᵖ) :
      DiscreteTopology ((sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj k) :=
    discreteTopology_bot _
  exact (isOpen_discrete
      ({0} : Set ((sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj j))).preimage
    ((continuous_apply j).comp continuous_induced_dom)

end LimitTopology

/-! ### The presenting ring is the inverse limit of the section rings -/

section SectionLimit

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : I ⥤ BigAffineFppf B S hS)
  (J : I → WeakIdeals A)
  (χ : ∀ k : I, CommRingCat.of (A ⧸ (J k).1) ≅
    Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj (D.obj k))))
  (hcompat : ∀ (k l : I) (f : k ⟶ l) (a : A),
    Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map (D.map f)).op
        ((χ l).hom (Ideal.Quotient.mk (J l).1 a)) =
      (χ k).hom (Ideal.Quotient.mk (J k).1 a))

include hcompat

/-- **The comparison homomorphism to the inverse limit of the section rings.** Given a
presentation `X = colim Xᵢ` whose stages have been identified with the spectra of the quotients
`A ⧸ Jᵢ` of a ring `A`, compatibly with the transition morphisms, reduction modulo the `Jᵢ` is a
ring homomorphism from `A` to the inverse limit of the stage rings. -/
def sectionLimitHom : A →+* (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections :=
  { toFun := fun a ↦
      ⟨fun k ↦ ((χ k.unop).hom).hom (Ideal.Quotient.mk (J k.unop).1 a),
        fun {k l} g ↦ hcompat l.unop k.unop g.unop a⟩
    map_one' := Subtype.ext (funext fun k ↦
      map_one (((χ k.unop).hom).hom.comp (Ideal.Quotient.mk (J k.unop).1)))
    map_mul' := fun a b ↦ Subtype.ext (funext fun k ↦
      map_mul (((χ k.unop).hom).hom.comp (Ideal.Quotient.mk (J k.unop).1)) a b)
    map_zero' := Subtype.ext (funext fun k ↦
      map_zero (((χ k.unop).hom).hom.comp (Ideal.Quotient.mk (J k.unop).1)))
    map_add' := fun a b ↦ Subtype.ext (funext fun k ↦
      map_add (((χ k.unop).hom).hom.comp (Ideal.Quotient.mk (J k.unop).1)) a b) }

omit [IsTopologicalRing A] [IsLinearTopology A A] [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The value of the comparison homomorphism at a stage is the class modulo the weak ideal
cutting out that stage, read through the identification of the stage ring with the quotient. -/
theorem sectionLimitHom_apply_val (a : A) (k : I) :
    (sectionLimitHom B S hS A I D J χ hcompat a).val (op k) =
      (χ k).hom (Ideal.Quotient.mk (J k).1 a) :=
  rfl

omit [IsTopologicalRing A] [IsLinearTopology A A] [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- A representative of a section of the inverse limit at one stage represents it at every
smaller stage: the two classes agree because the stage identifications are compatible with the
transition morphism. -/
private theorem sectionLimit_rep_le (i m : I) (φ : i ⟶ m) (a : A)
    (s : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections)
    (ha : (χ m).inv (s.val (op m)) = Ideal.Quotient.mk (J m).1 a) :
    (χ i).inv (s.val (op i)) = Ideal.Quotient.mk (J i).1 a := by
  have hsm : s.val (op m) = (χ m).hom (Ideal.Quotient.mk (J m).1 a) := by
    rw [← ha]
    exact ((χ m).inv_hom_id_apply (s.val (op m))).symm
  have hsi : s.val (op i) = (χ i).hom (Ideal.Quotient.mk (J i).1 a) := by
    rw [← s.property φ.op, hsm]
    exact hcompat i m φ a
  rw [hsi]
  exact (χ i).hom_inv_id_apply _

section Cofinal

variable (hcof : ∀ K : WeakIdeals A, ∃ i : I, K ≤ J i)

include hcof

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The comparison homomorphism is injective: the stage ideals are cofinal among the weak ideals
of definition, and `A` is separated, so an element killed by every stage is zero. -/
theorem sectionLimitHom_injective (hA : TopologicalRing.IsWeaklyAdmissible A) :
    Function.Injective (sectionLimitHom B S hS A I D J χ hcompat) := by
  intro a a' haa'
  have hquot : ∀ k : I,
      Ideal.Quotient.mk (J k).1 a = Ideal.Quotient.mk (J k).1 a' := fun k ↦
    (ConcreteCategory.bijective_of_isIso (χ k).hom).1 (congrFun (congrArg Subtype.val haa') (op k))
  refine eq_of_weak_ideal_submem' hA fun K ↦ ?_
  obtain ⟨i, hi⟩ := hcof (OrderDual.toDual K)
  exact (show (J i).1 ≤ K.1 from hi) (Ideal.Quotient.eq.mp (hquot i))

omit [Nonempty I] in
/-- The comparison homomorphism is surjective: a compatible family of stage sections extends to
a compatible family of classes modulo *all* weak ideals of definition, and `A` is complete, so
that family comes from an element of `A`. -/
theorem sectionLimitHom_surjective (hA : TopologicalRing.IsWeaklyAdmissible A) :
    Function.Surjective (sectionLimitHom B S hS A I D J χ hcompat) := by
  classical
  intro s
  choose idxOf hidxOf using fun K : TopologicalRing.WeakIdealOfDefinitionIndex A ↦
    hcof (OrderDual.toDual K)
  have hle : ∀ K : TopologicalRing.WeakIdealOfDefinitionIndex A, (J (idxOf K)).1 ≤ K.1 :=
    hidxOf
  let b : ∀ K : TopologicalRing.WeakIdealOfDefinitionIndex A, A ⧸ K.1 :=
    fun K ↦ Ideal.Quotient.factor (hle K) ((χ (idxOf K)).inv (s.val (op (idxOf K))))
  have hb_eq : ∀ (K : TopologicalRing.WeakIdealOfDefinitionIndex A) (i : I)
      (h : (J i).1 ≤ K.1),
      b K = Ideal.Quotient.factor h ((χ i).inv (s.val (op i))) := by
    intro K i h
    obtain ⟨m, him, hi₀m⟩ := directed_of (· ≤ ·) i (idxOf K)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((χ m).inv (s.val (op m)))
    show Ideal.Quotient.factor (hle K) ((χ (idxOf K)).inv (s.val (op (idxOf K)))) = _
    rw [sectionLimit_rep_le B S hS A I D J χ hcompat i m (homOfLE him) a s ha.symm,
      sectionLimit_rep_le B S hS A I D J χ hcompat (idxOf K) m (homOfLE hi₀m) a s ha.symm,
      Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]
  have hb : ∀ (K L : TopologicalRing.WeakIdealOfDefinitionIndex A) (h : K.1 ≤ L.1),
      Ideal.Quotient.factor h (b K) = b L := by
    intro K L h
    rw [hb_eq K (idxOf K) (hle K), hb_eq L (idxOf K) ((hle K).trans h)]
    exact Ideal.Quotient.factor_comp_apply (hle K) h _
  obtain ⟨a, ha⟩ := exists_lift_compatible_weak_quotients' hA b hb
  refine ⟨a, Subtype.ext (funext fun k ↦ ?_)⟩
  show (χ k.unop).hom (Ideal.Quotient.mk (J k.unop).1 a) = s.val k
  have h1 : Ideal.Quotient.mk (J k.unop).1 a = b (OrderDual.ofDual (J k.unop)) :=
    ha (OrderDual.ofDual (J k.unop))
  have h2 : b (OrderDual.ofDual (J k.unop)) =
      Ideal.Quotient.factor (le_refl (J k.unop).1) ((χ k.unop).inv (s.val (op k.unop))) :=
    hb_eq (OrderDual.ofDual (J k.unop)) k.unop (le_refl (J k.unop).1)
  rw [h1, h2, Ideal.Quotient.factor_eq, RingHom.id_apply]
  exact (χ k.unop).inv_hom_id_apply (s.val (op k.unop))

/-- **The presenting ring is the inverse limit of the section rings, as a ring isomorphism.**
Reduction modulo the weak ideals of definition cut out by the stages of a presentation is an
isomorphism from a weakly admissible ring presenting the space onto the inverse limit of the
stage rings. Its continuity in both directions is
`AlgebraicGeometry.FormalSpace.continuous_sectionLimitRingEquiv` and
`AlgebraicGeometry.FormalSpace.continuous_sectionLimitRingEquiv_symm`. -/
def sectionLimitRingEquiv (hA : TopologicalRing.IsWeaklyAdmissible A) :
    A ≃+* (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections :=
  RingEquiv.ofBijective (sectionLimitHom B S hS A I D J χ hcompat)
    ⟨sectionLimitHom_injective B S hS A I D J χ hcompat hcof hA,
      sectionLimitHom_surjective B S hS A I D J χ hcompat hcof hA⟩

omit [Nonempty I] in
/-- The comparison isomorphism `sectionLimitRingEquiv` sends `a` to its image under
`sectionLimitHom`. -/
@[simp]
theorem sectionLimitRingEquiv_apply (hA : TopologicalRing.IsWeaklyAdmissible A) (a : A) :
    sectionLimitRingEquiv B S hS A I D J χ hcompat hcof hA a =
      sectionLimitHom B S hS A I D J χ hcompat a :=
  rfl

omit [Nonempty I] in
/-- **The comparison isomorphism is continuous.** Each of its components is reduction modulo a
weak ideal of definition, which is an open ideal, so the component is continuous into a discrete
stage ring; continuity into the limit follows because the limit topology is induced from the
product of the stage rings. -/
theorem continuous_sectionLimitRingEquiv (hA : TopologicalRing.IsWeaklyAdmissible A) :
    Continuous (sectionLimitRingEquiv B S hS A I D J χ hcompat hcof hA) := by
  let (k : Iᵒᵖ) :
      TopologicalSpace ((sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj k) := ⊥
  let (k : Iᵒᵖ) :
      DiscreteTopology ((sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj k) :=
    discreteTopology_bot _
  refine continuous_induced_rng.mpr (continuous_pi fun k ↦ ?_)
  let q : A →+* (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj k :=
    ((χ k.unop).hom).hom.comp (Ideal.Quotient.mk (J k.unop).1)
  show Continuous fun a : A ↦ q a
  apply continuous_of_continuousAt_zero q.toAddMonoidHom
  rw [ContinuousAt, nhds_discrete ((sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).obj k),
    Filter.tendsto_pure]
  have hsub : (J k.unop).1 ≤ RingHom.ker q := by
    intro x hx
    show ((χ k.unop).hom).hom (Ideal.Quotient.mk (J k.unop).1 x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  filter_upwards [(Ideal.isOpen_of_isOpen_subideal hsub (J k.unop).2.1).mem_nhds
    (Ideal.zero_mem _)] with x hx
  exact (RingHom.mem_ker.mp hx).trans q.map_zero.symm

omit [Nonempty I] in
/-- **The inverse of the comparison isomorphism is continuous.** The stage ideals are cofinal
among the weak ideals of definition, so for every weak ideal of definition `K` there is a stage
at which the vanishing of a section — an open condition on the limit — forces its preimage into
`K`. -/
theorem continuous_sectionLimitRingEquiv_symm (hA : TopologicalRing.IsWeaklyAdmissible A) :
    Continuous (sectionLimitRingEquiv B S hS A I D J χ hcompat hcof hA).symm := by
  have hat : ContinuousAt
      ((sectionLimitRingEquiv B S hS A I D J χ hcompat hcof hA).symm :
        (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections → A) 0 := by
    rw [ContinuousAt, map_zero,
      (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA).tendsto_right_iff]
    intro K hK
    obtain ⟨i, hi⟩ := hcof (OrderDual.toDual
      (⟨K, hK⟩ : TopologicalRing.WeakIdealOfDefinitionIndex A))
    filter_upwards [(isOpen_setOf_sections_apply_eq_zero B S hS D (op i)).mem_nhds
      (show (0 : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections).val (op i) = 0
        from rfl)] with s hs
    -- The section vanishes at the stage `i`, so its preimage lies in `Jᵢ`, hence in `K`.
    have h := congrFun (congrArg Subtype.val
      ((sectionLimitRingEquiv B S hS A I D J χ hcompat hcof hA).apply_symm_apply s)) (op i)
    rw [sectionLimitRingEquiv_apply, sectionLimitHom_apply_val] at h
    refine (show (J i).1 ≤ K from hi) (Ideal.Quotient.eq_zero_iff_mem.mp
      ((ConcreteCategory.bijective_of_isIso (χ i).hom).1 ?_))
    rwa [map_zero, h]
  exact continuous_of_continuousAt_zero
    ((sectionLimitRingEquiv B S hS A I D J χ hcompat hcof hA).symm.toRingHom).toAddMonoidHom hat

end Cofinal

end SectionLimit

/-- **Stacks 0AIC, the concluding clause.** If `X` is the colimit of the spectra of the
quotients of a weakly admissible topological ring `A` by its weak ideals of definition, then for
*any* presentation `X = colim Xᵢ` of `X` by affine thickenings the ring `A` is the inverse limit
`lim Γ(Xᵢ, 𝒪)` of the section rings of that presentation, *as a topological ring*: the comparison
map is an isomorphism of rings which is a homeomorphism for the limit topology of
`AlgebraicGeometry.FormalSpace.topologicalSpaceSections`.

Reduction modulo the weak ideals of definition `Jᵢ` cut out by the stages is the comparison
homomorphism; it is injective because those ideals are cofinal and `A` is separated, surjective
because `A` is complete, continuous because each `Jᵢ` is open, and open because the `Jᵢ` are
cofinal. -/
@[stacks 0AIC "the associated ring is A = lim Γ(X_λ, 𝒪), with its limit topology, for an \
arbitrary presentation"]
theorem exists_continuous_ringEquiv_sections_of_weakIdealColimitPresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (eD : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    ∃ e : A ≃+* (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections,
      Continuous e ∧ Continuous e.symm := by
  obtain ⟨J, χ, hcompat, hcof⟩ :=
    exists_stageQuotientIso_of_weakIdealColimitPresentation B S hS A hA P I D hD eD
  exact ⟨sectionLimitRingEquiv B S hS A I D J χ hcompat hcof hA,
    continuous_sectionLimitRingEquiv B S hS A I D J χ hcompat hcof hA,
    continuous_sectionLimitRingEquiv_symm B S hS A I D J χ hcompat hcof hA⟩

end AlgebraicGeometry.FormalSpace

end
