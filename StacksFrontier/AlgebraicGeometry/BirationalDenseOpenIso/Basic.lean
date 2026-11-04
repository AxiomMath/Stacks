module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# A closed birational morphism is an isomorphism over a dense open

A birational morphism between schemes with finitely many irreducible components which is closed
on underlying spaces is an isomorphism over a dense open of its target, under either of the
finiteness hypotheses of Tag 0BAC.

## Main results

* `AlgebraicGeometry.preimage_genericPoints_eq_genericPoints_of_isBirational`: a birational
  morphism has the generic points of its source as the preimage of the generic points of its
  target.
* `AlgebraicGeometry.exists_dense_open_isIso_morphismRestrict_of_isClosedMap`: the conclusion of
  Tag 0BAC upgraded from an isomorphism between dense opens to an isomorphism over a dense open,
  for a closed morphism.
* `AlgebraicGeometry.exists_dense_open_isIso_morphismRestrict_of_isIntegralHom`: the same for an
  integral morphism, in particular for a finite one.

## Implementation notes

This is the content of [Stacks Project, Tag 0BAC] turned from an isomorphism of dense opens into
an isomorphism over a dense open of the target. The source does that in Tag 0BAJ, whose proof
first shrinks the target to a dense open over which the morphism becomes finite, using Tag 0BAI.
Only the resulting *closedness* of the restricted morphism is used, so when the morphism is
already closed — as it is for the integral morphisms this is applied to — the whole appeal to
Tag 0BAI is unnecessary and the dense open can be taken to be the whole target. The statements
below are therefore deliberately *not* tagged 0BAJ: they replace the hypothesis
"quasi-compact or separated" of that tag by "closed", which is neither weaker nor stronger.

Given a dense open isomorphism `f.resLE V U : U ≅ V` from Tag 0BAC, the dense open of the target
is cut out of `V` by removing the image of the complement of `U` — which is closed exactly
because `f` is closed. That the result is still dense is checked on generic points: a dense open
contains every generic point when there are finitely many irreducible components.

## References

* [Stacks Project, Tag 0BAC](https://stacks.math.columbia.edu/tag/0BAC)
* [Stacks Project, Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A birational morphism between schemes with finitely many irreducible components has the
generic points of its source as the exact preimage of the generic points of its target. -/
theorem preimage_genericPoints_eq_genericPoints_of_isBirational {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (hf : IsBirational f) : f ⁻¹' genericPoints Y = genericPoints X := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ hf.bijOn.1 hx⟩
  obtain ⟨η, hη, hηf⟩ := hf.bijOn.2.2 hx
  let y₀ := IsLocalRing.closedPoint (Y.presheaf.stalk (f x))
  obtain ⟨z, hzx, hzy⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := Y.fromSpecStalk (f x)) x y₀ (by simp [y₀])
  obtain ⟨z', hz'η, hz'y⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := Y.fromSpecStalk (f x)) η y₀ (by simpa [y₀] using hηf)
  have := isIso_pullback_snd_fromSpecStalk_of_isBirational f hf (f x) hx
  obtain rfl : z = z' := (ConcreteCategory.bijective_of_isIso
    (Limits.pullback.snd f (Y.fromSpecStalk (f x))).base).1 (hzy.trans hz'y.symm)
  exact (hz'η.symm.trans hzx) ▸ hη

/-- A dense open of a space with finitely many irreducible components contains every generic
point. -/
private theorem genericPoints_subset_of_dense_open {T : Type*} [TopologicalSpace T]
    (hfin : (irreducibleComponents T).Finite) (U : Opens T) (hU : Dense (U : Set T)) :
    genericPoints T ⊆ U := by
  intro x hx
  let Z : Set T := closure {x}
  have hZ : Z ∈ irreducibleComponents T := hx
  let O : Set T := (⋃₀ (irreducibleComponents T \ {Z}))ᶜ
  have hOne : O.Nonempty := by
    rw [← closure_nonempty_iff, closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z hZ]
    exact hZ.1.nonempty
  obtain ⟨z, hzU, hzO⟩ := hU.exists_mem_open
    (hfin.sdiff.isClosed_sUnion fun W hW ↦
      isClosed_of_mem_irreducibleComponents W hW.1).isOpen_compl hOne
  have hzZ : z ∈ Z := by
    rw [← closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z hZ]
    exact subset_closure hzO
  exact (specializes_iff_forall_open.mp (specializes_iff_mem_closure.mpr hzZ)) U U.2 hzU

/-- An isomorphism between dense opens restricts to an isomorphism over any open of the target
contained in the target open whose preimage is contained in the source open. -/
private theorem isIso_morphismRestrict_of_isIso_resLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) [IsIso (f.resLE V U hUV)] (W : Y.Opens)
    (hWV : W ≤ V) (hWU : f ⁻¹ᵁ W ≤ U) : IsIso (f ∣_ W) := by
  have hcomp : (f ∣_ W) ≫ Y.homOfLE hWV = X.homOfLE hWU ≫ f.resLE V U hUV := by
    rw [f.map_resLE, ← f.resLE_eq_morphismRestrict, f.resLE_map]
  have : IsOpenImmersion ((f ∣_ W) ≫ Y.homOfLE hWV) := by
    rw [hcomp]
    infer_instance
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨IsOpenImmersion.of_comp (f ∣_ W) (Y.homOfLE hWV), ⟨fun y ↦ ?_⟩⟩
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (f.resLE V U hUV).base).2
    ⟨y.1, hWV y.2⟩
  have hxy : f x.1 = y.1 := by
    rw [← f.coe_resLE_apply hUV x]
    exact congrArg Subtype.val hx
  refine ⟨⟨x.1, ?_⟩, ?_⟩
  · show f x.1 ∈ W
    rw [hxy]
    exact y.2
  · exact Subtype.ext ((morphismRestrict_base_coe f W _).trans hxy)

/-- **Stacks Project, Tag 0BAC**, as an isomorphism over a dense open of the target. A
birational morphism between schemes with finitely many irreducible components which is closed on
underlying spaces is an isomorphism over a dense open of its target. -/
theorem exists_dense_open_isIso_morphismRestrict_of_isClosedMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (hf : IsBirational f) (hclosed : IsClosedMap f.base)
    (hfin : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ W : Y.Opens, Dense (W : Set Y) ∧ IsIso (f ∣_ W) := by
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational f hf hfin
  let W : Y.Opens := ⟨(V : Set Y) ∩ (f '' (U : Set X)ᶜ)ᶜ,
    V.2.inter (hclosed _ U.2.isClosed_compl).isOpen_compl⟩
  have hgenW : genericPoints Y ⊆ W := by
    intro y hy
    refine ⟨genericPoints_subset_of_dense_open (Set.toFinite _) V hV hy, ?_⟩
    rintro ⟨x, hxU, rfl⟩
    refine hxU (genericPoints_subset_of_dense_open (Set.toFinite _) U hU ?_)
    rw [← preimage_genericPoints_eq_genericPoints_of_isBirational f hf]
    exact hy
  have hW : Dense (W : Set Y) := by
    rw [dense_iff_closure_eq]
    refine Set.Subset.antisymm (Set.subset_univ _) ?_
    rw [← genericPoints.closure]
    exact closure_mono hgenW
  exact ⟨W, hW, isIso_morphismRestrict_of_isIso_resLE f U V hUV W (fun y hy ↦ hy.1)
    fun x hx ↦ Classical.byContradiction fun hxU ↦ hx.2 ⟨x, hxU, rfl⟩⟩

/-- An integral birational morphism between schemes with finitely many irreducible components is
an isomorphism over a dense open of its target. An integral morphism is universally closed, so
this is the preceding statement with its closedness hypothesis discharged. -/
theorem exists_dense_open_isIso_morphismRestrict_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)] [IsIntegralHom f]
    (hf : IsBirational f)
    (hfin : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ W : Y.Opens, Dense (W : Set Y) ∧ IsIso (f ∣_ W) :=
  exists_dense_open_isIso_morphismRestrict_of_isClosedMap f hf
    (MorphismProperty.universally_le (topologically @IsClosedMap) f
      UniversallyClosed.universally_isClosedMap) hfin

end AlgebraicGeometry

end
