module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisGlobalSectionsIso

/-!
# The covering step for the square of topoi of [Stacks, Tag 07Q9]

Let `f : X' ⟶ X` be a morphism of the global crystalline situations of [Stacks, Tag 07I5] and let
`V` be an open of `X`. For every object `A` of `CRIS(X'/S)` whose structure map lands in
`f^{-1}V`, the objects of `CRIS(X'/S)` over `A` which admit a morphism, after change of divided
power base, to an object of `Cris(X/S)` lying over `V` form a covering sieve of `A`; and these
dominations of an object over `V` are cofiltered. Both statements hold for every morphism of
global crystalline situations.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.dominatedSieve`: the sieve on an object of
  `CRIS(X'/S)` of those refinements which, after change of divided power base, map to an object
  of `Cris(X/S)` lying over a prescribed open `V` of `X`.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.exists_affine_neighbourhood_toX_of_mem`:
  every point of the thickened scheme of an object of `CRIS(X/S)` whose structure map lands in an
  open `V` of `X` has an affine open neighbourhood whose part of `U` maps into an affine open of
  `X` contained in `V`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.dominatedSieve_mem`: `dominatedSieve` is a
  covering sieve, for every object whose structure map lands in `f^{-1}V`.
* `Crystalline.GlobalCrystallineSituation.Thickening.mem_of_hom`: lying over an open of `X` is
  inherited along morphisms of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.exists_cone_domination` and
  `Crystalline.GlobalCrystallineSituation.SmallSite.exists_cone_maps_domination`: the dominations
  of an object over `V` are cofiltered: two of them are refined by a third, and a pair of
  morphisms out of one is equalized by a refinement.

## Implementation notes

The covering is the relative form of
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.coversTop_ι` ([Stacks, Tag 07IJ])
with the open of `X` prescribed: the thickened scheme of `A` is covered by affine opens whose part
of `U` maps into an affine open `V' ⊆ V` of `X`, and the pushout along the affine map to `V'`
([Stacks, Tag 07RT]) is an object of `Cris(X/S)` lying over `V`. Cofilteredness is the absolute
statement `SmallSite.isCofilteredOrEmpty_structuredArrow_ι` together with
`Thickening.mem_of_hom`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

namespace Thickening

/-- **Lying over an open `V` of `X` is inherited along morphisms of `CRIS(X/S)`.** If `g : A ⟶ B`
is a morphism and the structure map of `B` lands in `V`, then so does the structure map of `A`. -/
theorem mem_of_hom {T : GlobalCrystallineSituation.{u}} {A B : Thickening T} (g : A ⟶ B)
    (V : T.X.Opens) (hB : ∀ z : B.thickening.source, B.toX.base z ∈ V)
    (z : A.thickening.source) :
    A.toX.base z ∈ V := by
  have h : A.toX.base z = B.toX.base (g.sourceHom.base z) := by
    rw [← g.toX_naturality]
    rfl
  exact h ▸ hB _

/-- **Every point of the thickened scheme of an object of `CRIS(X/S)` whose structure map lands in
an open `V` of `X` has an affine open neighbourhood whose part of `U` maps into an affine open of
`X` contained in `V`.** -/
theorem exists_affine_neighbourhood_toX_of_mem {T : GlobalCrystallineSituation.{u}}
    (A : Thickening T) (V : T.X.Opens) (hA : ∀ z : A.thickening.source, A.toX.base z ∈ V)
    (x : A.thickening.target.scheme) :
    ∃ (W : A.thickening.target.scheme.affineOpens) (V' : T.X.affineOpens),
      x ∈ W.1 ∧ V'.1 ≤ V ∧ A.thickening.immersion ⁻¹ᵁ W.1 ≤ A.toX ⁻¹ᵁ V'.1 := by
  obtain ⟨z, rfl⟩ := A.thickening.isThickening.2 x
  obtain ⟨V', hV', hzV, hsub⟩ := exists_isAffineOpen_mem_and_subset (hA z)
  have ho := (A.thickening.immersion.isClosedEmbedding.isEmbedding.isOpenEmbedding_of_surjective
    A.thickening.isThickening.2).isOpenMap
  set O : A.thickening.target.scheme.Opens :=
    ⟨A.thickening.immersion '' (A.toX ⁻¹ᵁ V'), ho _ (A.toX ⁻¹ᵁ V').2⟩ with hO
  obtain ⟨W, hW, hzW, hWO⟩ := exists_isAffineOpen_mem_and_subset
    (show A.thickening.immersion z ∈ O from ⟨z, hzV, rfl⟩)
  refine ⟨⟨W, hW⟩, ⟨V', hV'⟩, hzW, hsub, fun y hy ↦ ?_⟩
  obtain ⟨y', hy', he⟩ := hWO hy
  exact A.thickening.immersion.isClosedEmbedding.injective he ▸ hy'

end Thickening

namespace SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-- **The sieve of refinements dominated by an object of `Cris(X/S)` lying over `V`.** A morphism
`C ⟶ A` of `CRIS(X'/S)` belongs to it when `C`, read over `X/S` through change of divided power
base, admits a morphism to an object of `Cris(X/S)` whose structure map has image inside the open
`V` of `X`. -/
def dominatedSieve (V : S'.X.Opens) (A : Thickening S) : Sieve A where
  arrows C _ := ∃ B : CrystallineThickening S',
    (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
      Nonempty ((changeBase S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B)
  downward_closed := fun {_ _ _} h g ↦ by
    obtain ⟨B, hBV, ⟨k⟩⟩ := h
    exact ⟨B, hBV, ⟨(changeBase S S' fS fX hf).map g ≫ k⟩⟩

/-- **`dominatedSieve` is a covering sieve.** Let `V` be an open of `X` and let `A` be an object
of `CRIS(X'/S)` whose structure map `U ⟶ X'` lands, after composition with `f`, inside `V`. Then
`A` is covered by objects which, read over `X/S`, admit a morphism to an object of `Cris(X/S)`
lying over `V`. -/
theorem dominatedSieve_mem (V : S'.X.Opens) (A : Thickening S)
    (hA : ∀ z : A.thickening.source, fX.base (A.toX.base z) ∈ V) :
    dominatedSieve S S' fS fX hf V A ∈ topology S A := by
  choose W V' hxW hV'V hWV using Thickening.exists_affine_neighbourhood_toX_of_mem
    ((changeBase S S' fS fX hf).obj A) V hA
  set Wfam : ULift.{u + 1} A.thickening.target.scheme → A.thickening.target.scheme.Opens :=
    fun i ↦ (W i.down).1 with hWfam
  have hcov : Thickening.IsZariskiCovering (A.restrictOpenCover Wfam) :=
    A.isZariskiCovering_restrictOpenCover Wfam fun x ↦ ⟨⟨x⟩, hxW x⟩
  apply (topology S).superset_covering _
    (zariskiCovering_mem_topology S (A.restrictOpenCover Wfam) hcov)
  rw [Sieve.generate_le_iff]
  intro C g hg
  cases hg with
  | mk i =>
    have : IsAffine ((W i.down).1 : Scheme.{u}) := (W i.down).property
    have : IsAffine ((V' i.down).1 : Scheme.{u}) := (V' i.down).property
    have : IsAffine (A.restrictOpen (Wfam i)).thickening.target.scheme :=
      inferInstanceAs (IsAffine ((W i.down).1 : Scheme.{u}))
    have : IsAffine (A.restrictOpen (Wfam i)).thickening.source :=
      isAffine_of_isAffineHom (A.restrictOpen (Wfam i)).thickening.immersion
    have : IsAffine ((changeBase S S' fS fX hf).obj
        (A.restrictOpen (Wfam i))).thickening.source :=
      inferInstanceAs (IsAffine (A.restrictOpen (Wfam i)).thickening.source)
    have hrange : Set.range ((changeBase S S' fS fX hf).obj
          (A.restrictOpen (Wfam i))).toX ⊆ Set.range (V' i.down).1.ι := by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨_, hWV i.down z.property⟩, rfl⟩
    set lift := IsOpenImmersion.lift (V' i.down).1.ι
      ((changeBase S S' fS fX hf).obj (A.restrictOpen (Wfam i))).toX hrange with hlift
    obtain ⟨B, hBrange, hne⟩ := CrystallineThickening.exists_crystalline_hom_of_affine S'
      ((changeBase S S' fS fX hf).obj (A.restrictOpen (Wfam i))) (V' i.down).1 lift
      (IsOpenImmersion.lift_fac _ _ _)
    refine ⟨B, fun z ↦ ?_, hne⟩
    have hz := hBrange (Set.mem_range_self z)
    rw [Scheme.Opens.range_ι] at hz
    exact hV'V i.down hz

/-! ### Cofilteredness of the dominations over `V` -/

/-- **Two dominations over `V` of one object of `CRIS(X'/S)` are dominated over `V` by a third.**
Given an object `C` of `CRIS(X'/S)` and two morphisms from `C`, read over `X/S`, to objects `B₁`
and `B₂` of `Cris(X/S)`, with `B₁` lying over the open `V` of `X`, there is a third object `B` of
`Cris(X/S)` with morphisms to both, through which both factor, and `B` again lies over `V`. -/
theorem exists_cone_domination (V : S'.X.Opens) (C : Thickening S)
    {B₁ B₂ : CrystallineThickening S'}
    (h₁ : ∀ z : B₁.obj.thickening.source, B₁.obj.toX.base z ∈ V)
    (k₁ : (changeBase S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B₁)
    (k₂ : (changeBase S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B₂) :
    ∃ (B : CrystallineThickening S') (a : B ⟶ B₁) (b : B ⟶ B₂)
      (k : (changeBase S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B),
      (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
        k ≫ (CrystallineThickening.ι S').map a = k₁ ∧
        k ≫ (CrystallineThickening.ι S').map b = k₂ := by
  obtain ⟨W, a, b, -⟩ := (isCofilteredOrEmpty_structuredArrow_ι S'
    ((changeBase S S' fS fX hf).obj C)).cone_objs
      (StructuredArrow.mk k₁) (StructuredArrow.mk k₂)
  exact ⟨W.right, a.right, b.right, W.hom,
    Thickening.mem_of_hom ((CrystallineThickening.ι S').map a.right) V h₁,
    StructuredArrow.w a, StructuredArrow.w b⟩

/-- **A pair of morphisms out of a domination over `V` is equalized by a further domination over
`V`.** Given a domination `k₁` of `C` by `B₁` lying over `V` and two morphisms `a, b : B₁ ⟶ B₂`
of `Cris(X/S)` which `k₁` does not distinguish, there is a domination of `C` by an object `B`
over `V` factoring `k₁` through a morphism `e : B ⟶ B₁` with `e ≫ a = e ≫ b`. -/
theorem exists_cone_maps_domination (V : S'.X.Opens) (C : Thickening S)
    {B₁ B₂ : CrystallineThickening S'}
    (h₁ : ∀ z : B₁.obj.thickening.source, B₁.obj.toX.base z ∈ V)
    (k₁ : (changeBase S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B₁)
    (a b : B₁ ⟶ B₂)
    (hab : k₁ ≫ (CrystallineThickening.ι S').map a =
      k₁ ≫ (CrystallineThickening.ι S').map b) :
    ∃ (B : CrystallineThickening S') (e : B ⟶ B₁)
      (k : (changeBase S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B),
      (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
        k ≫ (CrystallineThickening.ι S').map e = k₁ ∧ e ≫ a = e ≫ b := by
  obtain ⟨W, h, hh⟩ := (isCofilteredOrEmpty_structuredArrow_ι S'
      ((changeBase S S' fS fX hf).obj C)).cone_maps
    (X := StructuredArrow.mk k₁)
    (Y := StructuredArrow.mk (k₁ ≫ (CrystallineThickening.ι S').map a))
    (StructuredArrow.homMk a rfl) (StructuredArrow.homMk b hab.symm)
  exact ⟨W.right, h.right, W.hom,
    Thickening.mem_of_hom ((CrystallineThickening.ι S').map h.right) V h₁,
    StructuredArrow.w h, congrArg CommaMorphism.right hh⟩

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
