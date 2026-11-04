module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.RingTheory.Length.Comparison

/-!
# Proper pushforward of the cycle of a closed subscheme that stays a closed subscheme

Let `S` be the base scheme of chapter 42 of the Stacks Project, let `X` and `Y` be locally of
finite type over `S`, let `f : X ⟶ Y` be proper over `S` and let `i : Z ⟶ X` be a closed
immersion. If the composite `i ≫ f` is again a closed immersion — so that `Z` is cut out of `Y`
as well as of `X` — then proper pushforward along `f` carries the cycle of `Z` in `X` to the
cycle of `Z` in `Y`:

  `f_* [Z ⊆ X]_k = [Z ⊆ Y]_k`.

Two facts make this work, and both are consequences of `i ≫ f` being a closed immersion rather
than of `f` being proper. First, the fibre of `f` over a point of `Y` contributes at most one
point to the cycle of `Z`, because `i ≫ f` is injective on points; and at that point `f` itself
induces an isomorphism of residue fields, so the weight of proper pushforward is one and the
delta-dimension is unchanged. Second, the multiplicity of a component of `Z` is the same computed
in `X` and in `Y`, because a closed immersion has a surjective stalk map, so the stalk of `Z`
has the same submodule lattice over either ambient local ring as over its own.

## Main results

* `Stacks.Chow.componentMultiplicity_eq_length_stalk`: the multiplicity of a component of a
  closed subscheme is the length of the stalk of the subscheme over *itself*, so it does not
  depend on the ambient scheme.
* `Stacks.Chow.componentMultiplicity_comp_of_isClosedImmersion`: consequently the multiplicity
  is unchanged on passing from `i` to `i ≫ f`.
* `Stacks.Chow.bijective_residueFieldMap_of_isClosedImmersion_comp` and
  `Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion_comp`: at a point of `Z` the second
  factor of a closed immersion induces an isomorphism of residue fields, hence has residue
  degree one.
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp`:
  the pushforward formula.

## Implementation notes

### This is a special case of Stacks 02R6 and carries no attribute

Stacks 02R6 is the pushforward formula `f_* [Z]_k = [f_* O_Z]_k` for an arbitrary proper `f`,
whose right-hand side is the cycle of a *coherent sheaf* on `Y`. That cycle is Stacks 02QX, and
it is not formalized in this repository: there is no `reducedSupport`, no `sheafMultiplicity`
and no cycle of a coherent sheaf anywhere in the tree. What is proved here is the case in which
`i ≫ f` is a closed immersion, restated so that the right-hand side is the cycle of the closed
subscheme `Z ⊆ Y` instead. For a closed immersion the direct image `(i ≫ f)_* O_Z` *is* the
structure sheaf of that closed subscheme, so the two right-hand sides agree; but identifying
them is exactly the content of Stacks 02QX that is missing, and it is not proved here. So this
is neither the whole of Stacks 02R6 nor its literal part (1), and no attribute for Stacks 02R6
is placed on anything in this file.

### No coherence hypothesis, and no delta-dimension bound

Stacks 02R6's own statement needs the direct image to be coherent in order to form its
right-hand side, which is the proper mapping theorem Stacks 02O5; and it needs a bound
`δ(Z) ≤ k` so that the support of that sheaf has delta-dimension at most `k`. Neither is needed
here. The right-hand side is a closed-subscheme cycle, which is defined for every closed
immersion and every `k`, so the statement below is free of both hypotheses. Coherence of
`(i ≫ f)_* O_Z` would in any case be available without Stacks 02O5, since `i ≫ f` is finite:
that is `pushforward_isCoherent_of_isFinite` of
`StacksFrontier.AlgebraicGeometry.PushforwardCoherent`, which carries the attribute for Stacks
01Y6, coherence of the direct image.

### Where the multiplicity comparison comes from

`Stacks.Chow.componentMultiplicity` is the length of the stalk of `Z` as a module over the stalk
of the ambient scheme, restricted along the stalk map. For a closed immersion that stalk map is
surjective, so `Stacks.RingTheory.length_restrictScalars_eq_of_surjective` — the same lemma that
makes the multiplicity finite in
`StacksFrontier.AlgebraicGeometry.Chow.CycleAssociatedClosed.Basic`, Stacks 02QT — identifies the
length with the length of the stalk over itself. Both `i` and `i ≫ f` are closed immersions, so
both multiplicities reduce to that one quantity and nothing has to be transported.

### The delta-dimensions are compared through `Z`, not through `f`

The relative dimension of `i z` over `S` and of `(i ≫ f) z` over `S` are compared by applying
`Stacks.Chow.relativeDimension_comp_closedImmersion` twice, to `i` and to `i ≫ f`, and then
using `f ≫ sY = sX`. No statement about the residue field of `f` at a general point is needed.

## References

* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The multiplicity of a component does not depend on the ambient scheme -/

/-- The multiplicity of an irreducible component of a closed subscheme `i : Z ⟶ X` is the length
of the stalk of `Z` at the component's generic point as a module over *itself*. The stalk map of
a closed immersion is surjective, so the submodule lattice of the stalk over the ambient local
ring is its lattice of ideals. -/
theorem componentMultiplicity_eq_length_stalk {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (ξ : genericPoints Z) :
    componentMultiplicity i ξ =
      ((Module.length (Z.presheaf.stalk ξ.1) (Z.presheaf.stalk ξ.1)).toNat : ℤ) := by
  let _ : Module (X.presheaf.stalk (i ξ.1)) (Z.presheaf.stalk ξ.1) :=
    Module.compHom (Z.presheaf.stalk ξ.1) (i.stalkMap ξ.1).hom
  show ((Module.length (X.presheaf.stalk (i ξ.1)) (Z.presheaf.stalk ξ.1)).toNat : ℤ) = _
  rw [length_restrictScalars_eq_of_surjective (X.presheaf.stalk (i ξ.1))
    (Z.presheaf.stalk ξ.1) (i.stalkMap ξ.1).hom
    (SurjectiveOnStalks.stalkMap_surjective i ξ.1) (Z.presheaf.stalk ξ.1)]

/-- The multiplicity of a component of `Z` is the same whether `Z` is read as a closed subscheme
of `X` or, through a morphism `f : X ⟶ Y` along which the immersion stays an immersion, as a
closed subscheme of `Y`. -/
theorem componentMultiplicity_comp_of_isClosedImmersion {X Y Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ Y) [IsClosedImmersion (i ≫ f)] (ξ : genericPoints Z) :
    componentMultiplicity (i ≫ f) ξ = componentMultiplicity i ξ := by
  rw [componentMultiplicity_eq_length_stalk (i ≫ f) ξ, componentMultiplicity_eq_length_stalk i ξ]

/-! ### Residue fields of the second factor of a closed immersion -/

/-- If `i` and `i ≫ f` are closed immersions then `f` induces an isomorphism of residue fields at
every point of the image of `i`: the residue field map of `i ≫ f` factors through that of `f`,
and both the composite and the factor belonging to `i` are isomorphisms. -/
theorem bijective_residueFieldMap_of_isClosedImmersion_comp {X Y Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ Y) [IsClosedImmersion (i ≫ f)] (z : Z) :
    Function.Bijective (f.residueFieldMap (i.base z)).hom := by
  have hfac : ∀ a, ((i ≫ f).residueFieldMap z).hom a =
      (i.residueFieldMap z).hom ((f.residueFieldMap (i.base z)).hom a) := by
    intro a
    rw [Scheme.residueFieldMap_comp]
    rfl
  refine ⟨(f.residueFieldMap (i.base z)).hom.injective, fun y ↦ ?_⟩
  obtain ⟨a, ha⟩ := (bijective_residueFieldMap_of_isClosedImmersion (i ≫ f) z).surjective
    ((i.residueFieldMap z).hom y)
  exact ⟨a, (bijective_residueFieldMap_of_isClosedImmersion i z).injective
    ((hfac a).symm.trans ha)⟩

/-- If `i` and `i ≫ f` are closed immersions then `f` has residue degree one at every point of
the image of `i`. -/
theorem residueDegree_eq_one_of_isClosedImmersion_comp {X Y Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ Y) [IsClosedImmersion (i ≫ f)] (z : Z) :
    f.residueDegree (i.base z) = 1 := by
  let _ := (f.residueFieldMap (i.base z)).hom.toAlgebra
  show Module.finrank (Y.residueField (f.base (i.base z))) (X.residueField (i.base z)) = 1
  exact Module.finrank_of_bijective_algebraMap
    (bijective_residueFieldMap_of_isClosedImmersion_comp i f z)

/-! ### The pushforward formula -/

/-- The relative dimension over the base of a point of `Z` read in `X` and read in `Y` agree,
both being its relative dimension computed on `Z` itself. -/
theorem relativeDimension_eq_of_isClosedImmersion_comp (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S) (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsClosedImmersion (i ≫ f)] (z : Z) :
    relativeDimension C.dimensionFunction sX (i.base z) =
      relativeDimension C.dimensionFunction sY ((i ≫ f).base z) := by
  rw [← relativeDimension_comp_closedImmersion C.dimensionFunction i sX z,
    ← relativeDimension_comp_closedImmersion C.dimensionFunction (i ≫ f) sY z,
    Category.assoc, hf]

/-- **A special case of Stacks 02R6, not Stacks 02R6.** Let `f : X ⟶ Y` be proper over the base
and let `i : Z ⟶ X` be a closed immersion whose composite with `f` is again a closed immersion.
Then proper pushforward along `f` carries the cycle of `Z` in `X` to the cycle of `Z` in `Y`.

The fibre of `f` over a point of `Y` meets the support of `[Z ⊆ X]_k` in at most one point, since
`i ≫ f` is injective; there the weight of proper pushforward is one and the delta-dimension is
unchanged, and the multiplicity is the same in `X` and in `Y`.

This is *not* the statement of Stacks 02R6, whose right-hand side is the cycle of the coherent
direct image `(i ≫ f)_* O_Z`; see the implementation notes. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsClosedImmersion (i ≫ f)] (k : ℤ) :
    properPushforward C sX sY f hf k (cycleAssociatedToClosedSubscheme C sX i k) =
      cycleAssociatedToClosedSubscheme C sY (i ≫ f) k := by
  classical
  have hbase : ∀ z : Z, (i ≫ f).base z = f.base (i.base z) := fun _ ↦ rfl
  have hdim := relativeDimension_eq_of_isClosedImmersion_comp C sX sY f hf i
  -- a point of `X` carrying a nonzero coefficient of `[Z ⊆ X]_k` comes from a generic point
  have hsupp : ∀ x : X, (cycleAssociatedToClosedSubscheme C sX i k).1 x ≠ 0 →
      ∃ η : genericPoints Z, i.base η.1 = x ∧
        relativeDimension C.dimensionFunction sX x = k := by
    intro x hx
    by_contra h
    exact hx (cycleAssociatedToClosedSubscheme_apply_eq_zero C sX i k x h)
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [properPushforward_apply]
  by_cases h : ∃ ξ : genericPoints Z, (i ≫ f).base ξ.1 = y ∧
      relativeDimension C.dimensionFunction sY y = k
  · obtain ⟨ξ, hξy, hξk⟩ := h
    have hxk : relativeDimension C.dimensionFunction sX (i.base ξ.1) = k := by
      rwa [hdim ξ.1, hξy]
    -- the fibre meets the support only at `i ξ`
    have hfib : ∀ x ∈ Function.support (fun x : X ↦
        (cycleAssociatedToClosedSubscheme C sX i k).1 x *
          (if relativeDimension C.dimensionFunction sX x =
              relativeDimension C.dimensionFunction sY (f.base x)
            then (f.residueDegree x : ℤ) else 0)),
        x ∈ f.base ⁻¹' {y} ↔ x ∈ ({i.base ξ.1} : Set X) := by
      intro x hx
      obtain ⟨η, hηx, _⟩ := hsupp x fun hz ↦ by simp [hz] at hx
      constructor
      · rintro (hxy : f.base x = y)
        have heq : (i ≫ f).base η.1 = (i ≫ f).base ξ.1 := by
          rw [hbase η.1, hηx, hxy, ← hξy]
        show x = i.base ξ.1
        rw [← hηx, (i ≫ f).isClosedEmbedding.injective heq]
      · rintro (rfl : x = i.base ξ.1)
        exact hξy
    rw [finsum_mem_inter_support_eq' _ _ _ hfib, finsum_mem_singleton,
      cycleAssociatedToClosedSubscheme_apply C sX i k ξ hxk, ← hξy,
      cycleAssociatedToClosedSubscheme_apply C sY (i ≫ f) k ξ (by rwa [hξy]),
      componentMultiplicity_comp_of_isClosedImmersion i f ξ, hdim ξ.1, hbase ξ.1,
      residueDegree_eq_one_of_isClosedImmersion_comp i f ξ.1]
    simp
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C sY (i ≫ f) k y h]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    by_cases hx0 : (cycleAssociatedToClosedSubscheme C sX i k).1 x = 0
    · simp [hx0]
    obtain ⟨η, hηx, hηk⟩ := hsupp x hx0
    have hy : (i ≫ f).base η.1 = y := by rw [hbase η.1, hηx]; exact hx
    exact absurd ⟨η, hy, by rwa [← hy, ← hdim η.1, hηx]⟩ h

end Stacks.Chow

end
