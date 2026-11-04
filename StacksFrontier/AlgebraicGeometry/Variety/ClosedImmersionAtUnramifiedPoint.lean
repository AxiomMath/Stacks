module

public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.FiniteUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.ClosedImmersionOpens
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointResidueField

/-!
# A finite morphism unramified at a point of a singleton fibre

Let `g : X ⟶ Y` be a finite morphism of schemes over an algebraically closed field and let `x` be
a closed point of `X` whose fibre is `{x}` and at which `g` is unramified. Then `g` is a closed
immersion over an open neighbourhood of `g x`.

Tag 04DG asks for `g` to be unramified everywhere, which is more than being unramified at `x`.
The gap is closed by shrinking the target: the unramified locus of `g` is open, and `g` is finite
hence closed, so the image of its complement is a closed subset of `Y`. That image misses `g x`,
precisely because the fibre over `g x` is the single point `x`, at which `g` is unramified. Over
the complement of that image the morphism is finite and unramified everywhere, so Tag 04DG
applies there.

## Main results

* `AlgebraicGeometry.exists_isOpen_restrict_isClosedImmersion_of_unramifiedAt`: the open
  neighbourhood of `g x` over which `g` is a closed immersion.

## Implementation notes

The unramifiedness of the restriction is obtained from
`AlgebraicGeometry.unramified_ι_comp_of_forall_unramifiedAt`, which gives unramifiedness of the
composite of the open inclusion with `g`; that composite is the restriction followed by the
inclusion of the open subset of the target, so cancelling the open immersion leaves the
restriction unramified. Finiteness of the restriction is locality at the target.

The purely inseparable hypothesis of Tag 04DG is discharged by
`AlgebraicGeometry.isPurelyInseparable_residueField_of_isClosed`: over an algebraically closed
field the residue field at a closed point is the ground field. The point `x` remains closed in
the open subscheme, and the structure morphism of that subscheme is still locally of finite type.

Tag 04DG produces an open subset of the shrunken target; it is transported to an open subset of
`Y` along `AlgebraicGeometry.morphismRestrictRestrict`, which identifies a twice-restricted
morphism with the restriction over the image of the smaller open set.

## References

* [Stacks Project, Tag 04DG](https://stacks.math.columbia.edu/tag/04DG)
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A finite morphism unramified at a point with singleton fibre is a closed immersion near the
image of that point.** This is Tag 04DG with unramifiedness assumed only at the point: the
unramified locus is open and the morphism is closed, so over the complement of the image of the
ramified locus — an open set containing the image of the point, since the fibre there is the
point itself — the morphism is unramified everywhere. -/
public theorem exists_isOpen_restrict_isClosedImmersion_of_unramifiedAt {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} (g : X ⟶ Y) (q : Y ⟶ Spec (.of k)) [IsFinite g]
    [LocallyOfFiniteType (g ≫ q)] (x : X) (hxc : IsClosed ({x} : Set X))
    (hun : UnramifiedAt g x) (hfib : g.base ⁻¹' {g.base x} = {x}) :
    ∃ R : Y.Opens, g.base x ∈ R ∧ IsClosedImmersion (g ∣_ R) := by
  classical
  -- The ramified locus is closed, and its image is closed because `g` is finite.
  set R₀ : Y.Opens := ⟨(g.base '' {y : X | UnramifiedAt g y}ᶜ)ᶜ,
    (g.isClosedMap _ (isOpen_setOf_unramifiedAt g).isClosed_compl).isOpen_compl⟩
  -- The image of `x` avoids that image, because the fibre over it is `{x}`.
  have hx0 : g.base x ∈ R₀ := by
    rintro ⟨y, hyC, hyx⟩
    obtain rfl : y = x := hfib.subset hyx
    exact hyC hun
  -- Every point over `R₀` is a point of unramifiedness.
  have hW : ∀ y ∈ g ⁻¹ᵁ R₀, UnramifiedAt g y :=
    fun y hy => Classical.byContradiction fun hcon => hy ⟨y, hcon, rfl⟩
  -- Hence the restriction over `R₀` is finite and unramified.
  have hcomp : Unramified ((g ∣_ R₀) ≫ R₀.ι) := by
    rw [morphismRestrict_ι]
    exact unramified_ι_comp_of_forall_unramifiedAt g _ hW
  have hunr : Unramified (g ∣_ R₀) := by
    rw [unramified_iff_locallyOfFiniteType_and_formallyUnramified]
    refine ⟨inferInstance, ?_⟩
    have : FormallyUnramified ((g ∣_ R₀) ≫ R₀.ι) :=
      (unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mp hcomp |>.2
    exact FormallyUnramified.of_comp (g ∣_ R₀) R₀.ι
  -- The fibre of the restriction over the image of `x` is the single point `x`.
  have hxW : x ∈ g ⁻¹ᵁ R₀ := hx0
  have hfib' : (g ∣_ R₀).base ⁻¹' {(⟨g.base x, hx0⟩ : R₀)} = {(⟨x, hxW⟩ : g ⁻¹ᵁ R₀)} := by
    ext y
    simp only [Set.mem_preimage]
    refine ⟨fun hy => Subtype.ext (hfib.subset (?_ : g.base y.1 = g.base x)), fun hy => ?_⟩
    · simpa only [morphismRestrict_base_coe] using congrArg (fun z : R₀ => (z : Y)) hy
    · subst hy
      exact Subtype.ext (morphismRestrict_base_coe g R₀ _)
  -- The structure morphism of the open subscheme is still locally of finite type.
  have hlft : LocallyOfFiniteType ((g ∣_ R₀) ≫ (R₀.ι ≫ q)) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have hxc' : IsClosed ({(⟨x, hxW⟩ : g ⁻¹ᵁ R₀)} : Set (g ⁻¹ᵁ R₀)) := by
    have he : ({(⟨x, hxW⟩ : g ⁻¹ᵁ R₀)} : Set (g ⁻¹ᵁ R₀)) = Subtype.val ⁻¹' ({x} : Set X) := by
      ext y
      exact ⟨fun hy => congrArg Subtype.val hy, fun hy => Subtype.ext hy⟩
    rw [he]
    exact hxc.preimage continuous_subtype_val
  -- Tag 04DG applies to the restriction.
  obtain ⟨U, hsU, hci⟩ :=
    exists_open_restrict_isClosedImmersion_of_finite_unramified_fiber_eq_singleton
      (g ∣_ R₀) (⟨g.base x, hx0⟩ : R₀) (⟨x, hxW⟩ : g ⁻¹ᵁ R₀) hfib'
      (isPurelyInseparable_residueField_of_isClosed (g ∣_ R₀) (R₀.ι ≫ q) _ _
        (Subtype.ext (morphismRestrict_base_coe g R₀ _)) hxc')
  -- Transport the neighbourhood back to an open subset of `Y`.
  exact ⟨R₀.ι ''ᵁ U, ⟨⟨g.base x, hx0⟩, hsU, rfl⟩,
    (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (morphismRestrictRestrict g R₀ U)).mp hci⟩

end AlgebraicGeometry

end
