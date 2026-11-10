module

public import Mathlib.CategoryTheory.Pi.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Equivalence
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ

/-!
# Peeling one point off a finite family of closed points

[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q), for a finite family of *pairwise
distinct* closed points, is proved there by induction on the number of points: given the family
`s_1, …, s_n`, write `U' = S \ {s_1, …, s_{n-1}}` and apply the one-point equivalence of
[Stacks, Tag 0BPA] to `s_n` relative to the ambient scheme `U'`.

This file records the elementary facts about `AlgebraicGeometry.complementOfClosedPoints` that
this induction needs when the family is indexed by `Option I'`, peeling off the point at `none`:
the open complement of the whole family is the open complement of the family at `some` intersected
with the complement of the single point at `none`; granting that the points are pairwise distinct,
the point at `none` lies in that intermediate complement (it has not already been removed by the
first `n - 1` points), is closed there, and its punctured open there is exactly the pullback of the
whole family's open complement along the inclusion of the intermediate complement. This last fact
identifies the open at which the next step of the induction should apply the one-point equivalence
of Tag 0BPA relative to the smaller ambient scheme. It also records that the quasi-compactness
hypothesis on the whole family's open complement descends to this intermediate open, and that the
stalk at the peeled point agrees with the stalk at `none` in the ambient scheme `S`: together these
are exactly the hypotheses Tag 0BPA's one-point equivalence needs when applied at the intermediate
scheme. Assembling that equivalence with the inductive equivalence for the family at `some` into
the general statement of Tag 0E8Q is **not** done here; it is a substantially larger undertaking,
carried out in `EquivalenceGeneral.lean`.

## Main results

* `AlgebraicGeometry.complementOfClosedPoints_option`: the open complement of an
  `Option I'`-indexed family of closed points is the open complement of the family restricted to
  `some`, intersected with the complement of the point at `none`.
* `AlgebraicGeometry.mem_complementOfClosedPoints_some_of_injective`: if the points of an
  `Option I'`-indexed family are pairwise distinct, the point at `none` lies in the open
  complement of the family restricted to `some`.
* `AlgebraicGeometry.preimage_complementOfClosedPoints_eq_puncturedOpen`: pulling back the open
  complement of the whole family along the inclusion of the open complement of the family at
  `some` gives exactly the punctured open at the peeled point there.
* `AlgebraicGeometry.quasiCompact_preimage_ι_of_quasiCompact`: quasi-compactness of the whole
  family's open complement descends to this pullback.
* `AlgebraicGeometry.stalkIsoPeeledPoint`: the stalk of `S` at the point `none` agrees with the
  stalk of the open complement of the family at `some` at the peeled point.
* `AlgebraicGeometry.complementOfClosedPointsIsoPuncturedOpen`: the open complement of the whole
  family, viewed directly inside `S`, is isomorphic to the punctured open at the peeled point,
  viewed inside the open complement of the family at `some`.
* `AlgebraicGeometry.restrictToComplementOfClosedPointsCompIso`: restricting to the open
  complement of the whole family and transporting along that comparison isomorphism agrees,
  naturally, with restricting first to the open complement of the family at `some` and then to
  its own punctured open.
* `AlgebraicGeometry.restrictionFunctorAtPoint_isEquivalence_at_peeledPoint`: granting the global
  quasi-compactness hypothesis on the whole family's open complement, Tag 0BPA's one-point
  equivalence applies at the peeled point, relative to the open complement of the family at
  `some`.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory Topology AlgebraicGeometry.GlueingNearPoint

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {I' : Type u} [Finite I'] (s : Option I' → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- The open complement of an `Option I'`-indexed family of closed points is the open complement
of the family restricted to `some`, intersected with the complement of the point at `none`. -/
theorem complementOfClosedPoints_option :
    complementOfClosedPoints s hs =
      complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i')) ⊓
        ⟨{s none}ᶜ, (mem_closedPoints_iff.mp (hs none)).isOpen_compl⟩ := by
  ext x
  simp only [complementOfClosedPoints, TopologicalSpace.Opens.coe_mk, Set.iInter_option,
    TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]
  tauto

/-- If the points of an `Option I'`-indexed family of closed points are pairwise distinct, the
point at `none` has not already been removed by the points at `some`: it lies in the open
complement of the family restricted to `some`. -/
theorem mem_complementOfClosedPoints_some_of_injective (hinj : Function.Injective s) :
    s none ∈ complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i')) := by
  simp only [complementOfClosedPoints, TopologicalSpace.Opens.mem_mk, Set.mem_iInter,
    Set.mem_compl_iff, Set.mem_singleton_iff]
  intro i' heq
  exact Option.some_ne_none i' (hinj heq).symm

variable (hinj : Function.Injective s)

/-- The point of the open complement of the family at `some` corresponding, under injectivity
of the family, to the point at `none`: the point removed at this step of the induction, viewed
inside the ambient scheme for the next step. -/
noncomputable def peeledPoint :
    (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).toScheme :=
  ⟨s none, mem_complementOfClosedPoints_some_of_injective s hs hinj⟩

/-- The peeled point maps to the point at `none` under the inclusion of the open complement of
the family at `some`. -/
@[simp]
theorem ι_peeledPoint :
    (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι (peeledPoint s hs hinj) =
      s none :=
  rfl

/-- The peeled point is closed in the open complement of the family at `some`: it is cut out by
the closed point `s none` of `S` along that complement's inclusion. -/
theorem isClosed_singleton_peeledPoint :
    IsClosed ({peeledPoint s hs hinj} :
      Set (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).toScheme) := by
  have hpre : (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι.base ⁻¹'
      ({s none} : Set S) = {peeledPoint s hs hinj} := by
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ by rw [h]; exact ι_peeledPoint s hs hinj⟩
  rw [show ({peeledPoint s hs hinj} :
      Set (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).toScheme) =
      (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι.base ⁻¹'
        ({s none} : Set S) from hpre.symm]
  exact (mem_closedPoints_iff.mp (hs none)).preimage
    (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i')) :
      _).isOpenEmbedding.continuous

/-- The open complement of the whole family is contained in the open complement of the family
restricted to `some`: removing the extra point at `none` can only shrink the complement. -/
theorem complementOfClosedPoints_le_some :
    complementOfClosedPoints s hs ≤
      complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i')) :=
  (complementOfClosedPoints_option s hs).trans_le inf_le_left

/-- The open complement of the whole family, pulled back along the inclusion of the open
complement of the family at `some`, is exactly the complement of the peeled point there: this is
the open that the next step of the induction punctures, relative to the smaller ambient scheme. -/
theorem preimage_complementOfClosedPoints_eq_puncturedOpen :
    (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι ⁻¹ᵁ
        complementOfClosedPoints s hs =
      puncturedOpen (isClosed_singleton_peeledPoint s hs hinj) := by
  apply TopologicalSpace.Opens.ext
  change (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι.base ⁻¹'
      (complementOfClosedPoints s hs : Set S) =
    ({peeledPoint s hs hinj} :
      Set (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).toScheme)ᶜ
  rw [complementOfClosedPoints_option s hs, TopologicalSpace.Opens.coe_inf, Set.preimage_inter]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hne⟩ heq
    exact hne (congrArg Subtype.val heq)
  · intro hne
    exact ⟨x.2, fun heq ↦ hne (Subtype.ext heq)⟩

/-- If the open complement of the whole family is quasi-compact over `S`, then so is its pullback
along the inclusion of the open complement of the family at `some`: this is the quasi-compactness
hypothesis the next step of the induction needs, relative to the smaller ambient scheme. -/
theorem quasiCompact_preimage_ι_of_quasiCompact
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    QuasiCompact
      ((complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι ⁻¹ᵁ
          complementOfClosedPoints s hs).ι :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict
      (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι
      (complementOfClosedPoints s hs))
    hqc

/-- The stalk of `S` at the peeled point agrees with the stalk of the open complement of the
family at `some` at the corresponding point there: open immersions induce stalk isomorphisms. -/
noncomputable def stalkIsoPeeledPoint :
    S.presheaf.stalk (s none) ≅
      (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).toScheme.presheaf.stalk
        (peeledPoint s hs hinj) := by
  have h := asIso
    ((complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι.stalkMap
      (peeledPoint s hs hinj))
  rwa [ι_peeledPoint] at h

/-- The open complement of the whole family, viewed directly inside `S`, is isomorphic, as a
scheme, to the punctured open at the peeled point, viewed inside the open complement of the
family at `some`: both describe the open subscheme obtained by removing every point of the
family from `S`, merely in two different presentations, and this identifies the comparison
between the two restriction functors that the next step of the induction needs. -/
noncomputable def complementOfClosedPointsIsoPuncturedOpen :
    (complementOfClosedPoints s hs).toScheme ≅
      puncturedOpen (isClosed_singleton_peeledPoint s hs hinj) :=
  (S.homOfLE (complementOfClosedPoints_le_some s hs)).isoOpensRange ≪≫
    (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).toScheme.isoOfEq (by
      rw [Scheme.opensRange_homOfLE]
      exact preimage_complementOfClosedPoints_eq_puncturedOpen s hs hinj)

/-- The comparison isomorphism of `AlgebraicGeometry.complementOfClosedPointsIsoPuncturedOpen` is
compatible with the inclusion into the open complement of the family at `some`: composing it with
the punctured open's inclusion there recovers the canonical inclusion of the open complement of
the whole family. -/
@[simp]
theorem complementOfClosedPointsIsoPuncturedOpen_hom_ι :
    (complementOfClosedPointsIsoPuncturedOpen s hs hinj).hom ≫
        (puncturedOpen (isClosed_singleton_peeledPoint s hs hinj)).ι =
      S.homOfLE (complementOfClosedPoints_le_some s hs) := by
  simp [complementOfClosedPointsIsoPuncturedOpen]

/-- The inverse of the comparison isomorphism, precomposed with the inclusion of the open
complement of the whole family, agrees with the punctured open's inclusion precomposed with the
inclusion of the open complement of the family at `some`: the two routes from the punctured open
down to `S` through either description of the removed-points complement coincide. -/
theorem complementOfClosedPointsIsoPuncturedOpen_inv_ι :
    (complementOfClosedPointsIsoPuncturedOpen s hs hinj).inv ≫ (complementOfClosedPoints s hs).ι =
      (puncturedOpen (isClosed_singleton_peeledPoint s hs hinj)).ι ≫
        (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).ι := by
  rw [Iso.inv_comp_eq, ← Category.assoc, complementOfClosedPointsIsoPuncturedOpen_hom_ι,
    Scheme.homOfLE_ι]

/-- Restricting a scheme of finite presentation over `S` to the open complement of the whole
family, then transporting along the comparison isomorphism into the punctured open at the
peeled point, agrees with restricting first to the open complement of the family at `some` and
then to its own punctured open there: the two ways of arriving at the fully punctured open
agree, naturally in the scheme being restricted. -/
noncomputable def restrictToComplementOfClosedPointsCompIso :
    restrictToComplementOfClosedPoints s hs ⋙
        finitePresentationBaseChange
          (complementOfClosedPointsIsoPuncturedOpen s hs hinj).inv ≅
      restrictToComplementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i')) ⋙
        finitePresentationBaseChange (puncturedOpen (isClosed_singleton_peeledPoint s hs hinj)).ι :=
  finitePresentationPullbackSquareIso (complementOfClosedPointsIsoPuncturedOpen_inv_ι s hs hinj)

/-- **Stacks Project, Tag 0BPA**, applied at the peeled point relative to the intermediate
ambient scheme: granting the global quasi-compactness hypothesis on the whole family's open
complement, restricting a scheme of finite presentation over the open complement of the family
at `some` to its own open complement of the peeled point, and to the stalk at that point, is an
equivalence onto the corresponding category of glueing data. This supplies the one-point piece
that the next step of the induction combines with the inductive equivalence for the family at
`some` to assemble the general statement of Tag 0E8Q. -/
theorem restrictionFunctorAtPoint_isEquivalence_at_peeledPoint
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    (restrictionFunctorAtPoint
      (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).toScheme
      (puncturedOpen (isClosed_singleton_peeledPoint s hs hinj))
      (peeledPoint s hs hinj)).IsEquivalence := by
  have hqc' : QuasiCompact (puncturedOpen (isClosed_singleton_peeledPoint s hs hinj)).ι := by
    rw [← preimage_complementOfClosedPoints_eq_puncturedOpen s hs hinj]
    exact quasiCompact_preimage_ι_of_quasiCompact s hs hqc
  exact restrictionFunctorAtPoint_isEquivalence
    (complementOfClosedPoints (s ∘ Option.some) (fun i' ↦ hs (some i'))).toScheme
    (peeledPoint s hs hinj) (isClosed_singleton_peeledPoint s hs hinj) hqc'

end AlgebraicGeometry

end
