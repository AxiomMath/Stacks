module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.MilnorBoundaryUnits

/-!
# The tame-symbol boundary at a point of an integral scheme, and its local finiteness

Let `W` be an integral locally Noetherian scheme and let `K` be a field identified with the
function field of `W` by a ring equivalence `e`. For a point `z` of `W` whose local ring is
one-dimensional, the tame symbol of Stacks 02Q1 of that local ring, descended to Milnor
K-theory by `AlgebraicGeometry.milnorKTwoTameSymbol`, is a homomorphism

`∂_z : K₂ᴹ(K) ⟶ K₁ᴹ(κ(z))`.

This is the local component of the first differential of the complex of Stacks 0GU9, read at the
scheme `W` rather than at a bare local ring: the identification `e` puts `K` in the position of
the fraction field of every local ring of `W` at once, so a single class of `K₂ᴹ(K)` has a
boundary at every one-dimensional point simultaneously.

The point of the file is the **local finiteness** of the resulting family. Stacks 0GU9 sends a
locally finite family `ξ` of degree-two Milnor K-classes to the family whose coefficient at a
point `x'` of `δ`-dimension `k + 1` is the sum of the boundaries `∂_{x'}(ξ_x)` over the points
`x` of `δ`-dimension `k + 2` specializing to `x'`; for that family to lie in the primed direct
sum of Stacks 0GU2 one needs, on every quasi-compact open, the vanishing of all but finitely
many of those boundaries. That is what is proved here, in the form a single `x` contributes:
for a quasi-compact open `V` of `W` and a class `α` of `K₂ᴹ(K)`, only finitely many
one-dimensional points of `V` have `∂_z(α) ≠ 0`.

## The argument

A class of `K₂ᴹ(K)` is a sum of pure symbols, and the bad set of a sum is contained in the union
of the bad sets, so it suffices to treat a pure symbol `{f, g}`. By Stacks 02Q2 the tame symbol
of two units of the local ring is trivial
(`AlgebraicGeometry.milnorKTwoTameSymbol_pureSymbol_eq_zero_of_eq_algebraMap_units`), and a
nonzero element of the function field is a unit in every local ring of some affine open
containing the generic point (`AlgebraicGeometry.exists_isUnit_germ_eq`). So the bad set is
contained in the complement, inside `V`, of an open set `O` containing the generic point.

The coheight-one points of such a complement are finite. Indeed `V` is a Noetherian scheme, so
the closed subset `V \ O` of `V` is a finite union of irreducible closed subsets, each with a
generic point; a coheight-one point `z` of `W` lying in one of them must *be* its generic point,
because the only proper generization of `z` is the generic point of `W`, which lies in `O`. So
the bad set injects into a finite set of generic points.

## What is carried

* Every result below carries `[IsIntegral W]` and, from
  `Stacks.Chow.finite_coheight_eq_one_of_notMem_isOpen` onwards, `[IsLocallyNoetherian W]`.
  Integrality is what makes the function field a field and every local ring a domain, and local
  Noetherianness is what makes the local rings Noetherian and a quasi-compact open a Noetherian
  space. On the schemes of Stacks 0GUA both hold: the integral closed subscheme spanned by a
  point is integral, and a scheme locally of finite type over a locally Noetherian base is
  locally Noetherian.
* Nothing here asserts Stacks 0GU9 or Stacks 0GUA: no chain group, no differential and no
  complex is formed. The statements are about one point, or about one quasi-compact open, of one
  integral scheme.

## Main definitions

* `Stacks.Chow.stalkAlgebraOfFunctionFieldEquiv` — the algebra structure which makes `K` a
  fraction field of the local ring at a point of `W`.
* `Stacks.Chow.stalkMilnorBoundary` — the boundary `∂_z` at a one-dimensional point.

## Main results

* `Stacks.Chow.isFractionRing_stalkAlgebraOfFunctionFieldEquiv` — `K` is a fraction field of
  every local ring of `W`.
* `Stacks.Chow.stalkMilnorBoundary_pureSymbol_eq_zero_of_isUnit` — the boundary kills the pure
  symbol of two elements which come from units of the local ring.
* `Stacks.Chow.exists_isOpen_forall_isUnit_stalk` — a nonzero element of `K` comes from a unit
  of the local ring at every point of some open set containing the generic point.
* `Stacks.Chow.finite_coheight_eq_one_of_notMem_isOpen` — a quasi-compact open has only finitely
  many coheight-one points outside an open set containing the generic point.
* `Stacks.Chow.finite_stalkMilnorBoundary_ne_zero` — **local finiteness of the boundary**: on a
  quasi-compact open only finitely many one-dimensional points have nonzero boundary.

## References

* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 02Q2](https://stacks.math.columbia.edu/tag/02Q2)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {W : Scheme.{u}} [IsIntegral W] {K : Type u} [Field K]
  (e : ↥W.functionField ≃+* K)

/-! ### The function field read as a fraction field of every local ring -/

/-- The algebra structure on the local ring of `W` at `z` with values in `K`, obtained by
composing the canonical map to the function field with the identification `e`. -/
@[instance_reducible]
def stalkAlgebraOfFunctionFieldEquiv (z : W) : Algebra ↥(W.presheaf.stalk z) K :=
  (e.toRingHom.comp (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField)).toAlgebra

/-- Under that algebra structure, the image in `K` of a section of the local ring is the image
of its canonical image in the function field. -/
theorem algebraMap_stalkAlgebraOfFunctionFieldEquiv (z : W) (a : ↥(W.presheaf.stalk z)) :
    letI := stalkAlgebraOfFunctionFieldEquiv e z
    algebraMap ↥(W.presheaf.stalk z) K a =
      e (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField a) := rfl

/-- **`K` is a fraction field of the local ring of `W` at every point.** The function field is a
fraction field of every local ring of an integral scheme, and `e` transports that along a ring
equivalence of the target. -/
theorem isFractionRing_stalkAlgebraOfFunctionFieldEquiv (z : W) :
    letI := stalkAlgebraOfFunctionFieldEquiv e z
    IsFractionRing ↥(W.presheaf.stalk z) K :=
  (IsLocalization.isLocalization_iff_of_ringEquiv
    (nonZeroDivisors ↥(W.presheaf.stalk z)) e).mp inferInstance

/-! ### The boundary at a one-dimensional point -/

variable [IsLocallyNoetherian W]

/-- **The tame-symbol boundary of Stacks 0GU9 at a one-dimensional point of `W`.** The local
ring at `z` is a one-dimensional Noetherian local domain whose fraction field is `K`, so the
tame symbol of Stacks 02Q1 descends to a homomorphism from the degree-two Milnor K-group of `K`
to the degree-one Milnor K-group of the residue field at `z`. -/
def stalkMilnorBoundary (z : W) (hdim : ringKrullDim (W.presheaf.stalk z) = 1) :
    MilnorKTheory K 2 →+ MilnorKTheory ↥(W.residueField z) 1 :=
  letI := stalkAlgebraOfFunctionFieldEquiv e z
  haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  milnorKTwoTameSymbol (A := ↥(W.presheaf.stalk z)) (K := K) hdim

/-- **The boundary kills a pure symbol of two units of the local ring.** This is Stacks 02Q2 read
through the descent of the tame symbol to Milnor K-theory: the symbol of a unit against a unit is
the residue of the first raised to the order of vanishing of the second, and that order is
zero. -/
theorem stalkMilnorBoundary_pureSymbol_eq_zero_of_isUnit (z : W)
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1) (f g : Kˣ)
    (hf : ∃ u : ↥(W.presheaf.stalk z), IsUnit u ∧
      e (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField u) = (f : K))
    (hg : ∃ v : ↥(W.presheaf.stalk z), IsUnit v ∧
      e (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField v) = (g : K)) :
    stalkMilnorBoundary e z hdim (milnorKTwoPureSymbol K f g) = 0 := by
  let _ := stalkAlgebraOfFunctionFieldEquiv e z
  have _ := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  obtain ⟨_, ⟨u, rfl⟩, hue⟩ := hf
  obtain ⟨_, ⟨v, rfl⟩, hve⟩ := hg
  exact milnorKTwoTameSymbol_pureSymbol_eq_zero_of_eq_algebraMap_units
    (A := ↥(W.presheaf.stalk z)) (K := K) hdim (u := u) (v := v) hue.symm hve.symm

/-! ### Units of the local rings of an open set -/

omit [IsLocallyNoetherian W] in
/-- **A nonzero element of `K` comes from a unit of the local ring at every point of some open
set containing the generic point.** A nonzero element of the function field is the image of a
unit of the sections over some affine open containing the generic point, and the germ of a unit
is a unit. -/
theorem exists_isOpen_forall_isUnit_stalk (f : K) (hf : f ≠ 0) :
    ∃ O : W.Opens, genericPoint W ∈ (O : Set W) ∧ ∀ z ∈ (O : Set W),
      ∃ u : ↥(W.presheaf.stalk z), IsUnit u ∧
        e (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField u) = f := by
  have hF : e.symm f ≠ 0 := fun h ↦ hf (by rw [← e.apply_symm_apply f, h, map_zero])
  obtain ⟨U, -, f', hU, hgerm, hunit⟩ := exists_isUnit_germ_eq W (e.symm f) hF
  have _ := hU
  refine ⟨U, ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr (by simpa using hU), ?_⟩
  intro z hz
  refine ⟨W.presheaf.germ U z hz f', IsUnit.map (W.presheaf.germ U z hz).hom hunit, ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := W) hz f', hgerm,
    e.apply_symm_apply]

/-! ### Finiteness of the coheight-one points outside a dense open -/

/-- **A quasi-compact open has only finitely many coheight-one points outside an open set
containing the generic point.** The complement is a closed subset of the Noetherian scheme `V`,
hence a finite union of irreducible closed subsets, each with a generic point; and a
coheight-one point of `W` lying in one of them is its generic point, since its only proper
generization is the generic point of `W`, which lies in `O`. -/
theorem finite_coheight_eq_one_of_notMem_isOpen (V O : W.Opens) (hV : IsCompact (V : Set W))
    (hO : genericPoint W ∈ (O : Set W)) :
    {z : W | z ∈ (V : Set W) ∧ z ∉ (O : Set W) ∧ Order.coheight z = 1}.Finite := by
  have _ : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have _ : IsNoetherian V.toScheme := ⟨⟩
  have hnoeth : NoetherianSpace V.toScheme := inferInstance
  have hSclosed : IsClosed {z : V.toScheme | (z.1 : W) ∉ (O : Set W)} :=
    (O.isOpen.isClosed_compl).preimage continuous_subtype_val
  obtain ⟨𝒮, h𝒮fin, h𝒮closed, h𝒮irred, h𝒮union⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (α := V.toScheme) hSclosed
  have _ : Finite ↥𝒮 := h𝒮fin.to_subtype
  refine (Set.finite_range fun t : ↥𝒮 ↦ (((h𝒮irred t.1 t.2).genericPoint).1 : W)).subset ?_
  rintro z ⟨hzV, hzO, hzc⟩
  obtain ⟨t, ht𝒮, hzt⟩ : (⟨z, hzV⟩ : V.toScheme) ∈ ⋃₀ 𝒮 := by rwa [← h𝒮union]
  have hgen : closure ({(h𝒮irred t ht𝒮).genericPoint} : Set V.toScheme) = t :=
    ((h𝒮irred t ht𝒮).genericPoint_closure_eq).trans (h𝒮closed t ht𝒮).closure_eq
  have hspec : (h𝒮irred t ht𝒮).genericPoint ⤳ (⟨z, hzV⟩ : V.toScheme) :=
    specializes_iff_mem_closure.mpr (by rwa [hgen])
  have hsub : t ⊆ {z : V.toScheme | (z.1 : W) ∉ (O : Set W)} := by
    rw [h𝒮union]
    exact Set.subset_sUnion_of_mem ht𝒮
  have hmemt : (h𝒮irred t ht𝒮).genericPoint ∈ t :=
    hgen.subset (subset_closure (Set.mem_singleton _))
  have himm := (coheight_eq_one_iff_isImmediateSpecialization_genericPoint z).mp hzc
  rcases himm.2.2 (((h𝒮irred t ht𝒮).genericPoint).1 : W) (genericPoint_specializes _)
      (hspec.map continuous_subtype_val) with h | h
  · exact absurd (h ▸ hO) (hsub hmemt)
  · exact ⟨⟨t, ht𝒮⟩, h⟩

/-! ### Local finiteness of the boundary -/

/-- **Local finiteness of the tame-symbol boundary.** Let `V` be a quasi-compact open of the
integral locally Noetherian scheme `W` and let `α` be a class of the degree-two Milnor K-group of
`K`. Then only finitely many points of `V` whose local ring is one-dimensional have nonzero
boundary `∂_z(α)`.

This is the step which makes the first differential of the complex of Stacks 0GU9 land in the
locally finite direct sum of Stacks 0GU2. The class `α` is a sum of pure symbols and the bad set
of a sum is contained in the union of the bad sets, so the claim reduces to a pure symbol
`{f, g}`; there the boundary vanishes wherever `f` and `g` are both units of the local ring,
which happens on an open set containing the generic point, and the coheight-one points of the
complement of such an open set in `V` are finite in number. -/
theorem finite_stalkMilnorBoundary_ne_zero (V : W.Opens) (hV : IsCompact (V : Set W))
    (α : MilnorKTheory K 2) :
    {z : {z : W // ringKrullDim (W.presheaf.stalk z) = 1} |
      (z : W) ∈ (V : Set W) ∧ stalkMilnorBoundary e z.1 z.2 α ≠ 0}.Finite := by
  induction α using milnorKTwo_induction with
  | hsymb f g =>
    obtain ⟨Of, hOf, hOfu⟩ := exists_isOpen_forall_isUnit_stalk e (f : K) f.ne_zero
    obtain ⟨Og, hOg, hOgu⟩ := exists_isOpen_forall_isUnit_stalk e (g : K) g.ne_zero
    have hfin := finite_coheight_eq_one_of_notMem_isOpen V (Of ⊓ Og) hV ⟨hOf, hOg⟩
    refine Set.Finite.of_finite_image (f := fun z ↦ (z : W)) (hfin.subset ?_)
      (Set.injOn_of_injective Subtype.val_injective)
    rintro _ ⟨z, ⟨hzV, hzne⟩, rfl⟩
    refine ⟨hzV, fun hz ↦ hzne (stalkMilnorBoundary_pureSymbol_eq_zero_of_isUnit e z.1 z.2 f g
      (hOfu _ hz.1) (hOgu _ hz.2)), ?_⟩
    have h : ((Order.coheight (z : W) : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
      rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (z : W), z.2]
      norm_num
    exact WithBot.coe_inj.mp h
  | hadd a b ha hb =>
    refine (ha.union hb).subset ?_
    rintro z ⟨hzV, hzne⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hcon
    exact hzne (by rw [map_add, hcon.1 hzV, hcon.2 hzV, add_zero])

end Stacks.Chow

end
