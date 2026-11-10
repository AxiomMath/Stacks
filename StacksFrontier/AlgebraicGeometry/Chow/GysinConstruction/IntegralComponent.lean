module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# The fundamental cycle of an integral closed subscheme

A cycle on `X` is presented in chapter 42 of the Stacks Project as a locally finite formal sum
`∑ n_j [W_j]` of *integral* closed subschemes `W_j ⊆ X`, whereas Mathlib's `AlgebraicCycle`
indexes a prime cycle by the generic point of its support. Translating between the two
presentations is the first step of every construction of chapter 42 that is specified by its
values on integral components — the Gysin map of a zero scheme (Stacks 02T8), intersection with
a first Chern class (Stacks 02SO), the sum of a locally finite family of principal divisors
(Stacks 02RW).

The translation is the content of this file. For an integral closed subscheme `W ⊆ X` with
generic point `σ`:

* the support of `W` is the closure of `σ` (`Stacks.Chow.support_eq_closure_genericPointOf`), so
  local finiteness of a family of integral closed subschemes is local finiteness of the family
  of closures of their generic points;
* the fundamental cycle `[W]_k` of Stacks 02QU is the prime cycle `σ` with coefficient one when
  `W` has delta-dimension `k`, and zero elsewhere
  (`Stacks.Chow.cycleAssociatedToClosedSubscheme_integral_apply` and
  `Stacks.Chow.cycleAssociatedToClosedSubscheme_integral_apply_of_ne`).

The multiplicity of the single component is one because the stalk of `W` at `σ` is a field on
which the stalk of `X` at `σ` acts through a surjection, hence a simple module. The
delta-dimension of `W` is computed at `σ` because the residue field of a closed subscheme at a
point agrees with the residue field of the ambient scheme, so the two transcendence degrees
entering `Stacks.Chow.relativeDimension` agree.

## Main results

* `Stacks.Chow.relativeDimension_comp_closedImmersion` — the relative dimension of a point of a
  closed subscheme, computed on the subscheme or on the ambient scheme, is the same.
* `Stacks.Chow.componentMultiplicity_eq_one` — an integral closed subscheme has multiplicity one
  at its generic point.
* `Stacks.Chow.componentMultiplicity_eq_one_of_reduced` — a component of a reduced closed
  subscheme has multiplicity one.
* `Stacks.Chow.relativeDimension_genericPointOf` — the delta-dimension of an integral closed
  subscheme is the relative dimension of its generic point.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_integral_apply`,
  `Stacks.Chow.cycleAssociatedToClosedSubscheme_integral_apply_of_ne` — the fundamental cycle of
  an integral closed subscheme is a prime cycle with coefficient one.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### A field is a simple module over any ring surjecting onto it -/

/-- A field is a simple module over any commutative ring mapping onto it: a nonzero submodule
contains some `a ≠ 0`, and every element of the field is a multiple of `a` by a scalar. -/
theorem isSimpleModule_of_surjective_toField {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Surjective f) :
    letI : Module R K := Module.compHom K f
    IsSimpleModule R K := by
  let _ : Module R K := Module.compHom K f
  refine { eq_bot_or_eq_top := fun N => ?_ }
  rcases eq_or_ne N ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (eq_top_iff.2 fun b _ => ?_)
  obtain ⟨a, haN, ha0⟩ : ∃ a ∈ N, a ≠ 0 := Submodule.ne_bot_iff N |>.1 h
  obtain ⟨r, hr⟩ := hf (b * a⁻¹)
  have hmem : r • a ∈ N := N.smul_mem r haN
  rwa [show r • a = f r * a from rfl, hr, inv_mul_cancel_right₀ ha0] at hmem

/-! ### Residue fields and relative dimension along a closed immersion -/

/-- A closed immersion induces an isomorphism on residue fields: the induced map is a
homomorphism of fields, hence injective, and it is surjective because the stalk map is. -/
theorem bijective_residueFieldMap_of_isClosedImmersion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (z : Z) : Function.Bijective (i.residueFieldMap z).hom := by
  refine ⟨(i.residueFieldMap z).hom.injective, ?_⟩
  have hres : Function.Surjective (Z.residue z).hom := IsLocalRing.residue_surjective
  have h1 : Function.Surjective ((i.residueFieldMap z).hom ∘ (X.residue (i z)).hom) := by
    have h2 : Function.Surjective (i.stalkMap z ≫ Z.residue z).hom :=
      hres.comp (SurjectiveOnStalks.stalkMap_surjective i z)
    rwa [← Scheme.residue_residueFieldMap i z] at h2
  exact Function.Surjective.of_comp h1

/-- A closed immersion has residue degree one at every point: it induces an isomorphism on
residue fields, so the field extension entering `AlgebraicGeometry.Scheme.Hom.residueDegree` is
trivial. -/
theorem residueDegree_eq_one_of_isClosedImmersion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (z : Z) : i.residueDegree z = 1 := by
  let _ := (i.residueFieldMap z).hom.toAlgebra
  change Module.finrank (X.residueField (i.base z)) (Z.residueField z) = 1
  exact Module.finrank_of_bijective_algebraMap
    (bijective_residueFieldMap_of_isClosedImmersion i z)

/-- The relative dimension of a point of a closed subscheme `Z ⊆ X` is the relative dimension of
its image in `X`. The two differ only in the transcendence degree of a residue field over the
residue field of the base, and a closed immersion identifies the residue field of `Z` at `z`
with the residue field of `X` at `i z`. -/
theorem relativeDimension_comp_closedImmersion {X Z S : Scheme.{u}} (δ : DimensionFunction S)
    (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ S) (z : Z) :
    relativeDimension δ (i ≫ p) z = relativeDimension δ p (i z) := by
  let _ : Algebra (S.residueField (p.base (i.base z))) (X.residueField (i.base z)) :=
    (p.residueFieldMap (i.base z)).hom.toAlgebra
  let _ : Algebra (S.residueField (p.base (i.base z))) (Z.residueField z) :=
    ((i ≫ p).residueFieldMap z).hom.toAlgebra
  have hcm : ∀ r, (i.residueFieldMap z).hom
      (algebraMap (S.residueField (p.base (i.base z))) (X.residueField (i.base z)) r) =
      algebraMap (S.residueField (p.base (i.base z))) (Z.residueField z) r := by
    intro r
    change (i.residueFieldMap z).hom ((p.residueFieldMap (i.base z)).hom r) =
      ((i ≫ p).residueFieldMap z).hom r
    rw [Scheme.residueFieldMap_comp]
    rfl
  let e : X.residueField (i.base z) ≃ₐ[S.residueField (p.base (i.base z))] Z.residueField z :=
    { __ := RingEquiv.ofBijective (i.residueFieldMap z).hom
        (bijective_residueFieldMap_of_isClosedImmersion i z)
      commutes' := hcm }
  change δ (p.base (i.base z)) +
      (Cardinal.toNat (Algebra.trdeg (S.residueField (p.base (i.base z)))
        (Z.residueField z)) : ℤ) =
    δ (p.base (i.base z)) +
      (Cardinal.toNat (Algebra.trdeg (S.residueField (p.base (i.base z)))
        (X.residueField (i.base z))) : ℤ)
  rw [e.trdeg_eq]

/-! ### The multiplicity of the single component of an integral closed subscheme -/

/-- The generic point of an irreducible scheme is one of its generic points. -/
theorem genericPoint_mem_genericPoints (Z : Scheme.{u}) [IrreducibleSpace Z] :
    genericPoint Z ∈ genericPoints Z := by
  rw [genericPoints_eq_singleton]
  exact Set.mem_singleton _

/-- **Stacks 02QU.** An integral closed subscheme has multiplicity one at its generic point: the
stalk there is a field, and the stalk of the ambient scheme acts on it through a surjection, so
it is a simple module and has length one. -/
theorem componentMultiplicity_eq_one {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (hξ : genericPoint Z ∈ genericPoints Z) :
    componentMultiplicity i ⟨genericPoint Z, hξ⟩ = 1 := by
  let _ : Module (X.presheaf.stalk (i (genericPoint Z))) (Z.presheaf.stalk (genericPoint Z)) :=
    Module.compHom (Z.presheaf.stalk (genericPoint Z)) (i.stalkMap (genericPoint Z)).hom
  have hsimple : IsSimpleModule (X.presheaf.stalk (i (genericPoint Z)))
      (Z.presheaf.stalk (genericPoint Z)) :=
    isSimpleModule_of_surjective_toField (i.stalkMap (genericPoint Z)).hom
      (SurjectiveOnStalks.stalkMap_surjective i _)
  change ((Module.length (X.presheaf.stalk (i (genericPoint Z)))
    (Z.presheaf.stalk (genericPoint Z))).toNat : ℤ) = 1
  rw [Module.length_eq_one_iff.2 hsimple]
  rfl

/-! ### The multiplicity of a component of a reduced closed subscheme -/

/-- A component of a reduced closed subscheme has multiplicity one: the stalk at its generic
point is a field, and a field is a simple module over any ring mapping onto it. -/
theorem componentMultiplicity_eq_one_of_reduced {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z] (ξ : genericPoints Z) :
    componentMultiplicity i ξ = 1 := by
  let R := X.presheaf.stalk (i ξ.1)
  let M := Z.presheaf.stalk ξ.1
  let : Algebra R M := (i.stalkMap ξ.1).hom.toAlgebra
  let : IsScalarTower R M M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfield : IsField M := isField_stalk_of_closure_mem_irreducibleComponents Z ξ.1 ξ.2
  have hsurj : Function.Surjective (algebraMap R M) := i.stalkMap_surjective ξ.1
  have hsimp : IsSimpleModule R M := by
    let := hfield.toField
    exact isSimpleModule_of_surjective_toField (algebraMap R M) hsurj
  unfold componentMultiplicity
  rw [show Module.length R M = 1 from Module.length_eq_one_iff.mpr hsimp]
  rfl

/-! ### Integral closed subschemes as prime cycles -/

variable {X : Scheme.{u}}

/-- The generic point of an integral closed subscheme of `X`, as a point of `X`. The integral
closed subscheme is recovered as the closure of this point, with its reduced structure. -/
def genericPointOf (W : X.IdealSheafData) (hW : IsIntegral W.subscheme) : X :=
  letI := hW
  W.subschemeι.base (genericPoint W.subscheme)

/-- The support of an integral closed subscheme is the closure of its generic point. -/
theorem support_eq_closure_genericPointOf (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) :
    (W.support : Set X) = closure {genericPointOf W hW} := by
  let _ := hW
  have hrange : Set.range W.subschemeι.base = (W.support : Set X) := W.range_subschemeι
  refine subset_antisymm ?_ (closure_minimal ?_ W.support.isClosed)
  · rw [← hrange, ← Set.image_univ, ← genericPoint_spec W.subscheme]
    refine (image_closure_subset_closure_image W.subschemeι.continuous).trans ?_
    rw [Set.image_singleton]
    exact subset_rfl
  · rw [Set.singleton_subset_iff, ← hrange]
    exact ⟨_, rfl⟩

/-- **Stacks 02QP.** The delta-dimension of an integral closed subscheme is the relative
dimension of its generic point, read on the ambient scheme. -/
theorem relativeDimension_genericPointOf (C : ChowSituation.{u}) (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (W : X.IdealSheafData) (hW : IsIntegral W.subscheme) {k : ℤ}
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (k : EInt)) :
    relativeDimension C.dimensionFunction p (genericPointOf W hW) = k := by
  let _ := hW
  have h := schemeDeltaDimension_eq_genericPoint C (W.subschemeι ≫ p)
  rw [hDim] at h
  rw [genericPointOf, ← relativeDimension_comp_closedImmersion, ← WithBotTop.coe_injective h]

/-- The fundamental cycle of an integral closed subscheme vanishes away from its generic
point: an integral scheme has exactly one generic point. -/
theorem cycleAssociatedToClosedSubscheme_integral_apply_of_ne (C : ChowSituation.{u})
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) (k : ℤ) {x : X} (hx : x ≠ genericPointOf W hW) :
    (cycleAssociatedToClosedSubscheme C p W.subschemeι k).1 x = 0 := by
  let _ := hW
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero C p W.subschemeι k x ?_
  rintro ⟨ξ, hξ, -⟩
  refine hx ?_
  have hmem : (ξ : W.subscheme) ∈ ({genericPoint W.subscheme} : Set W.subscheme) := by
    rw [← genericPoints_eq_singleton]
    exact ξ.2
  rw [← hξ, genericPointOf, Set.mem_singleton_iff.1 hmem]

/-- **Stacks 02QU.** The fundamental cycle `[W]_k` of an integral closed subscheme of
delta-dimension `k` is the prime cycle of its generic point with coefficient one. -/
theorem cycleAssociatedToClosedSubscheme_integral_apply (C : ChowSituation.{u}) (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (W : X.IdealSheafData) (hW : IsIntegral W.subscheme) {k : ℤ}
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (k : EInt)) :
    (cycleAssociatedToClosedSubscheme C p W.subschemeι k).1 (genericPointOf W hW) = 1 := by
  let _ := hW
  have hmem : genericPoint W.subscheme ∈ genericPoints W.subscheme :=
    genericPoint_mem_genericPoints W.subscheme
  rw [genericPointOf, cycleAssociatedToClosedSubscheme_apply C p W.subschemeι k ⟨_, hmem⟩
    (relativeDimension_genericPointOf C p W hW hDim),
    componentMultiplicity_eq_one W.subschemeι hmem]

/-! ### The integral closed subscheme attached to a point -/

/-- A closed subscheme with irreducible support has irreducible underlying space: its closed
immersion is an embedding onto the support.

`AlgebraicGeometry.Scheme.IdealSheafData.irreducibleSpace_subscheme` in
`StacksFrontier.RingTheory.Nagata.Japanese` says the same thing with the hypothesis phrased on
`Set.range I.subschemeι`; it is restated here so that this file does not have to import the
whole Nagata development. A dedup pass should move one of the two next to the other. -/
theorem irreducibleSpace_subscheme_of_isIrreducible (I : X.IdealSheafData)
    (h : IsIrreducible (I.support : Set X)) : IrreducibleSpace I.subscheme := by
  have hirr : IsIrreducible (Set.range I.subschemeι.base) := I.range_subschemeι ▸ h
  have hne : Nonempty I.subscheme := by
    obtain ⟨-, z, -⟩ := hirr.1
    exact ⟨z⟩
  let _ : PreirreducibleSpace (Set.range I.subschemeι.base) :=
    Subtype.preirreducibleSpace hirr.2
  let _ : Nonempty (Set.range I.subschemeι.base) := hirr.1.to_subtype
  let _ : IrreducibleSpace (Set.range I.subschemeι.base) := ⟨‹_›⟩
  exact I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.isOpenEmbedding.irreducibleSpace

/-- The integral closed subscheme of `X` attached to a point: the reduced induced structure on
the closure of that point. Every integral closed subscheme arises this way, from its generic
point (`Stacks.Chow.integralComponentAt_genericPointOf`), so a rule on integral closed
subschemes is the same thing as a rule on points. -/
def integralComponentAt (x : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))

/-- The integral closed subscheme attached to a point is supported on the closure of it. -/
@[simp]
theorem coe_support_integralComponentAt (x : X) :
    ((integralComponentAt x).support : Set X) = closure {x} :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The reduced induced structure on the closure of a point is integral. -/
theorem isIntegral_integralComponentAt (x : X) : IsIntegral (integralComponentAt x).subscheme := by
  let _ : IsReduced (integralComponentAt x).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  let _ : IrreducibleSpace (integralComponentAt x).subscheme :=
    irreducibleSpace_subscheme_of_isIrreducible _ (by
      simpa using isIrreducible_singleton.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The generic point of the integral closed subscheme attached to `x` is `x`. -/
@[simp]
theorem genericPointOf_integralComponentAt (x : X) :
    genericPointOf (integralComponentAt x) (isIntegral_integralComponentAt x) = x := by
  have h : IsGenericPoint
      (genericPointOf (integralComponentAt x) (isIntegral_integralComponentAt x))
      (closure ({x} : Set X)) := by
    rw [IsGenericPoint, ← support_eq_closure_genericPointOf, coe_support_integralComponentAt]
  exact h.eq isGenericPoint_closure

/-- Every integral closed subscheme is the reduced induced structure on the closure of its
generic point: this is the uniqueness half of Stacks 01J3. -/
theorem integralComponentAt_genericPointOf (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) : integralComponentAt (genericPointOf W hW) = W := by
  let _ := hW
  exact (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme W _
    (Closeds.ext (support_eq_closure_genericPointOf W hW))).symm

end Stacks.Chow

end
