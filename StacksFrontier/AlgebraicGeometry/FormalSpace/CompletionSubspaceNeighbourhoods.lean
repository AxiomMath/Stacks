module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Infinitesimal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhoodImmersion

/-!
# The completion along a closed subspace is the colimit of the neighbourhoods `Z_n`

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `Z ⊂ X` be a closed subspace. Stacks 0GXU defines the completion of `X` along `Z` as
the colimit `X^∧_Z = colim Z_n` in fppf sheaves, where `Z_n ⊂ X` is the `n`th order
infinitesimal neighbourhood of Stacks 05ZV, the closed subspace cut out by the `(n + 1)`st
power of the ideal sheaf of `Z`. In this library `Z_n` is
`AlgebraicGeometry.Space.nthOrderNeighbourhood`, and the completion
`AlgebraicGeometry.Space.completionSubspace` is the fppf sheafification of the subfunctor
`AlgebraicGeometry.Space.completionSubspaceSubfunctor`, described by a condition on the
inverse image of `Z` along a section. This file identifies the two.

## Main results

* `AlgebraicGeometry.Space.ker_rep_snd_nthOrderNeighbourhood`: on every étale scheme chart of
  `X` the ideal sheaf of `Z_n` is the `(n + 1)`st power of the ideal sheaf of `Z`.
* `AlgebraicGeometry.Space.mem_nthOrderNeighbourhood_iff_isUniversalNthOrderThickening` and
  `AlgebraicGeometry.Space.mem_nthOrderNeighbourhood_iff_isNthOrderThickening`: a section of
  `X` over an object `T` of the site factors through `Z_n` exactly when the inverse image of `Z`
  in `T` is (universally) an `n`th order thickening.
* `AlgebraicGeometry.Space.mem_completionSubspaceSubfunctor_iff`: a section lies in the
  completion subfunctor exactly when it factors through some `Z_n`, and
  `AlgebraicGeometry.Space.completionSubspaceSubfunctor_eq_iSup`: the completion subfunctor is
  the union of the `Z_n`.
* `AlgebraicGeometry.Space.isColimitNeighbourhoodCocone`: the completion subfunctor is the
  colimit of the presheaves `Z_n`, and
  `AlgebraicGeometry.Space.isColimitCompletionSubspaceCocone`: **Stacks 0GXU**, the completion
  `AlgebraicGeometry.Space.completionSubspace` is the colimit `colim Z_n` in fppf sheaves.

## References

* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-! ### The ideal sheaf of `Z_n` on a chart -/

/-- **On every étale scheme chart the ideal sheaf of `Z_n` is the `(n + 1)`st power of that of
`Z`.** Both are read on the affine opens of the chart, where they are the extensions of the
defining ideals of the corresponding affine étale charts of `X`, and there the defining ideal of
`Z_n` is the `(n + 1)`st power of that of `Z`. -/
theorem ker_rep_snd_nthOrderNeighbourhood (n : ℕ) (A : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map
        ((nthOrderNeighbourhood B S hS X Z n).2.2.rep.snd A.1.hom)).ker =
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker ^ (n + 1) := by
  rw [ker_rep_snd_eq_idealSheafDataOfChart, ker_rep_snd_eq_idealSheafDataOfChart]
  refine Scheme.IdealSheafData.ext (funext fun V ↦ ?_)
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  have hV : IsAffine (chartScheme (openChart B S hS X.1 A V.1)) := V.2
  have h : chartIdeal B S hS X (definingIdealSheaf B S hS X (nthOrderNeighbourhood B S hS X Z n))
        (openChart B S hS X.1 A V.1) =
      chartIdeal B S hS X (definingIdealSheaf B S hS X Z) (openChart B S hS X.1 A V.1) ^ (n + 1) :=
    definingIdealAt_nthOrderNeighbourhood_of_isAffine B S hS X Z n _ hV
  rw [ideal_idealSheafDataOfChart, ideal_idealSheafDataOfChart]
  unfold openChartIdeal
  rw [h, Ideal.map_pow]

/-! ### Sections of `Z_n` -/

/-- A section of `X` lying in `Z_n` has inverse image of `Z` a universal `n`th order thickening:
it factors through `Z_n`, inside which `Z` is an `n`th order thickening, and the order is
preserved by base change, Stacks 09ZX. -/
theorem isUniversalNthOrderThickening_of_mem_nthOrderNeighbourhood (n : ℕ)
    {U : BigFppfOver B S hS} {g : X.1.obj (op U)}
    (hg : g ∈ (nthOrderNeighbourhood B S hS X Z n).1.obj (op U)) :
    IsUniversalNthOrderThickening B S hS n U
      (Z.1.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)) := by
  intro V k
  obtain ⟨g', e⟩ : ∃ g' : yoneda.obj U ⟶ (nthOrderNeighbourhood B S hS X Z n).1.toFunctor,
      g' ≫ (nthOrderNeighbourhood B S hS X Z n).1.ι = yonedaEquiv.symm g :=
    ⟨yonedaEquiv.symm (⟨g, hg⟩ : (nthOrderNeighbourhood B S hS X Z n).1.toFunctor.obj (op U)),
      by ext; rfl⟩
  rw [← e, Subfunctor.preimage_comp, ← Subfunctor.preimage_comp]
  exact isNthOrderThickening_preimage B S hS
    (Y' := closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n))
    (X' := (schemeSpaceFunctor B S hS).obj V)
    (Z.1.preimage (nthOrderNeighbourhood B S hS X Z n).1.ι) (ObjectProperty.homMk (k ≫ g'))
    (isNthOrderThickening_preimage_nthOrderNeighbourhood B S hS X Z n)

/-- A section of `X` over `U` whose inverse image of `Z` is an `n`th order thickening of `U`
lies in `Z_n`. This is the algebraic-spaces form of Stacks 01HP,
`AlgebraicGeometry.Space.range_le_of_isNthOrderThickening`, applied to the identity of the
thickening, the ideal sheaf of `Z_n` being the `(n + 1)`st power of that of `Z` on every chart. -/
theorem mem_nthOrderNeighbourhood_of_isNthOrderThickening (n : ℕ)
    {U : BigFppfOver B S hS} {g : X.1.obj (op U)}
    (h : IsNthOrderThickening B S hS n ((schemeSpaceFunctor B S hS).obj U)
      (Z.1.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1))) :
    g ∈ (nthOrderNeighbourhood B S hS X Z n).1.obj (op U) := by
  set ĝ : yoneda.obj U ⟶ X.1 := yonedaEquiv.symm g
  have hrange : Subfunctor.range ((Z.1.preimage ĝ).ι ≫ ĝ) ≤ Z.1 := by
    rintro T _ ⟨x, rfl⟩
    exact x.2
  have hle := range_le_of_isNthOrderThickening B S hS
    (Y := (schemeSpaceFunctor B S hS).obj U) (U := X) Z (nthOrderNeighbourhood B S hS X Z n)
    (ker_rep_snd_nthOrderNeighbourhood B S hS X Z n) h ĝ
    (Subfunctor.lift ((Z.1.preimage ĝ).ι ≫ ĝ) hrange) (Subfunctor.lift_ι _ _).symm
  convert hle (op U) ⟨𝟙 U, rfl⟩ using 1
  exact (by simp : X.1.map (𝟙 U).op g = g).symm

/-- **A section factors through `Z_n` exactly when the inverse image of `Z` is an `n`th order
thickening.** For a section `g` of `X` over an object `U` of the site, `g` lies in the `n`th
order infinitesimal neighbourhood `Z_n` precisely when the inverse image of `Z` along `g` is an
`n`th order thickening of `U`. -/
theorem mem_nthOrderNeighbourhood_iff_isNthOrderThickening (n : ℕ) (U : BigFppfOver B S hS)
    (g : X.1.obj (op U)) :
    g ∈ (nthOrderNeighbourhood B S hS X Z n).1.obj (op U) ↔
      IsNthOrderThickening B S hS n ((schemeSpaceFunctor B S hS).obj U)
        (Z.1.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)) :=
  ⟨fun hg ↦ (isUniversalNthOrderThickening_of_mem_nthOrderNeighbourhood B S hS X Z n
      hg).isNthOrderThickening B S hS,
    mem_nthOrderNeighbourhood_of_isNthOrderThickening B S hS X Z n⟩

/-- **The level `n` condition of the completion subfunctor cuts out `Z_n`.** A section `g` of
`X` over an object `U` of the site has inverse image of `Z` a universal `n`th order thickening
exactly when it factors through the `n`th order infinitesimal neighbourhood `Z_n`, the closed
subspace of `X` cut out by the `(n + 1)`st power of the ideal sheaf of `Z` (Stacks 05ZV). -/
@[stacks 0GXU "identification with colim Z_n: the level n sections are those of Z_n"]
theorem mem_nthOrderNeighbourhood_iff_isUniversalNthOrderThickening (n : ℕ)
    (U : BigFppfOver B S hS) (g : X.1.obj (op U)) :
    g ∈ (nthOrderNeighbourhood B S hS X Z n).1.obj (op U) ↔
      IsUniversalNthOrderThickening B S hS n U
        (Z.1.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)) :=
  ⟨isUniversalNthOrderThickening_of_mem_nthOrderNeighbourhood B S hS X Z n,
    fun h ↦ mem_nthOrderNeighbourhood_of_isNthOrderThickening B S hS X Z n
      (h.isNthOrderThickening B S hS)⟩

/-- **The completion subfunctor is the union of the neighbourhoods `Z_n`, sectionwise.** A
section of the universe lift of `X` lies in the completion subfunctor of `X` along `Z` exactly
when it factors through some `Z_n`. -/
theorem mem_completionSubspaceSubfunctor_iff (U : (BigFppfOver B S hS)ᵒᵖ)
    (g : (X.1 ⋙ uliftFunctor.{u + 1}).obj U) :
    g ∈ (completionSubspaceSubfunctor B S hS X Z.1).obj U ↔
      ∃ n, g.down ∈ (nthOrderNeighbourhood B S hS X Z n).1.obj U := by
  show (∃ n, IsUniversalNthOrderThickening B S hS n U.unop
      (Z.1.preimage (yonedaEquiv.symm g.down : yoneda.obj U.unop ⟶ X.1))) ↔ _
  simp only [← mem_nthOrderNeighbourhood_iff_isUniversalNthOrderThickening]

/-! ### The union and the colimit -/

/-- The `n`th order infinitesimal neighbourhood `Z_n`, read as a subfunctor of the universe
lift of `X`. -/
def nthOrderNeighbourhoodULift (n : ℕ) : Subfunctor (X.1 ⋙ uliftFunctor.{u + 1}) where
  obj U := {g | g.down ∈ (nthOrderNeighbourhood B S hS X Z n).1.obj U}
  map i _ hg := (nthOrderNeighbourhood B S hS X Z n).1.map i hg

/-- The lifted neighbourhoods grow with their order. -/
theorem nthOrderNeighbourhoodULift_mono {m n : ℕ} (h : m ≤ n) :
    nthOrderNeighbourhoodULift B S hS X Z m ≤ nthOrderNeighbourhoodULift B S hS X Z n :=
  fun U _ hg ↦ nthOrderNeighbourhood_mono B S hS X Z h U hg

/-- Each lifted neighbourhood `Z_n` is contained in the completion subfunctor. -/
theorem nthOrderNeighbourhoodULift_le_completionSubspaceSubfunctor (n : ℕ) :
    nthOrderNeighbourhoodULift B S hS X Z n ≤ completionSubspaceSubfunctor B S hS X Z.1 :=
  fun U g hg ↦ (mem_completionSubspaceSubfunctor_iff B S hS X Z U g).2 ⟨n, hg⟩

/-- **The completion subfunctor is the union of the neighbourhoods `Z_n`.** -/
theorem completionSubspaceSubfunctor_eq_iSup :
    completionSubspaceSubfunctor B S hS X Z.1 = ⨆ n, nthOrderNeighbourhoodULift B S hS X Z n := by
  refine le_antisymm (fun U g hg ↦ ?_) (iSup_le
    (nthOrderNeighbourhoodULift_le_completionSubspaceSubfunctor B S hS X Z))
  obtain ⟨n, hn⟩ := (mem_completionSubspaceSubfunctor_iff B S hS X Z U g).1 hg
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨n, hn⟩

/-! The diagram of an increasing sequence of subfunctors, and its colimit -/

section Monotone

variable {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*} (G : ℕ → Subfunctor F) (hG : Monotone G)

/-- The diagram `n ↦ G n` of presheaves attached to an increasing sequence of subfunctors of a
presheaf, the transition maps being the inclusions. -/
@[simps]
def monotoneSubfunctorDiagram : ℕ ⥤ Cᵒᵖ ⥤ Type _ where
  obj n := (G n).toFunctor
  map h := Subfunctor.homOfLe (hG h.le)

/-- The cocone of inclusions of an increasing sequence of subfunctors into a subfunctor
containing all of them. -/
@[simps]
def monotoneSubfunctorCocone (H : Subfunctor F) (hle : ∀ n, G n ≤ H) :
    Cocone (monotoneSubfunctorDiagram G hG) where
  pt := H.toFunctor
  ι := { app n := Subfunctor.homOfLe (hle n) }

/-- A subfunctor which is sectionwise the union of an increasing sequence of subfunctors is
their colimit: colimits of presheaves are computed sectionwise, and an increasing union of sets
is their filtered colimit. -/
def isColimitMonotoneSubfunctorCocone (H : Subfunctor F) (hle : ∀ n, G n ≤ H)
    (hH : ∀ U x, x ∈ H.obj U → ∃ n, x ∈ (G n).obj U) :
    IsColimit (monotoneSubfunctorCocone G hG H hle) := by
  refine evaluationJointlyReflectsColimits _ fun U ↦ ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun i x y hxy ↦ ?_)
  · obtain ⟨n, hn⟩ := hH U x.1 x.2
    exact ⟨n, ⟨x.1, hn⟩, rfl⟩
  · have h := congrArg Subtype.val hxy
    exact ⟨i, 𝟙 i, Subtype.ext h⟩

end Monotone

/-- The diagram `n ↦ Z_n` of presheaves of `Type (u + 1)`, the transition maps being the
inclusions `Z_m ⊆ Z_n`. -/
abbrev nthOrderNeighbourhoodDiagram : ℕ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  monotoneSubfunctorDiagram (nthOrderNeighbourhoodULift B S hS X Z)
    fun _ _ h ↦ nthOrderNeighbourhoodULift_mono B S hS X Z h

/-- The cocone over the diagram of the neighbourhoods `Z_n` with point the completion
subfunctor, the legs being the inclusions. -/
abbrev neighbourhoodCocone : Cocone (nthOrderNeighbourhoodDiagram B S hS X Z) :=
  monotoneSubfunctorCocone _ _ (completionSubspaceSubfunctor B S hS X Z.1)
    (nthOrderNeighbourhoodULift_le_completionSubspaceSubfunctor B S hS X Z)

/-- **The completion subfunctor is the colimit of the neighbourhoods `Z_n`** in presheaves of
`Type (u + 1)`: sectionwise it is the increasing union of the `Z_n`. -/
def isColimitNeighbourhoodCocone : IsColimit (neighbourhoodCocone B S hS X Z) :=
  isColimitMonotoneSubfunctorCocone _ _ _ _
    fun U g hg ↦ (mem_completionSubspaceSubfunctor_iff B S hS X Z U g).1 hg

/-- The cocone of fppf sheaves obtained by sheafifying the cocone of the neighbourhoods `Z_n`.
Its point is the completion `X^∧_Z` (`AlgebraicGeometry.Space.completionSubspace`), by
`AlgebraicGeometry.Space.completionSubspaceCocone_pt`, and its stages are the sheafified
neighbourhoods `Z_n`. -/
abbrev completionSubspaceCocone :
    Cocone (nthOrderNeighbourhoodDiagram B S hS X Z ⋙
      plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :=
  (plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapCocone
    (neighbourhoodCocone B S hS X Z)

/-- The point of the sheafified cocone of the neighbourhoods is the completion `X^∧_Z`. -/
theorem completionSubspaceCocone_pt :
    (completionSubspaceCocone B S hS X Z).pt = completionSubspace B S hS X Z.1 :=
  rfl

/-- **Stacks 0GXU.** The completion `X^∧_Z = completionSubspace X Z` of an algebraic space `X`
along a closed subspace `Z` is the colimit `colim Z_n` in fppf sheaves of the `n`th order
infinitesimal neighbourhoods `Z_n` of Stacks 05ZV, the closed subspaces cut out by the
`(n + 1)`st powers of the ideal sheaf of `Z`: sheafification is a left adjoint, so it carries
the presheaf colimit `AlgebraicGeometry.Space.isColimitNeighbourhoodCocone` to a colimit. -/
@[stacks 0GXU "identification with colim Z_n in fppf sheaves"]
def isColimitCompletionSubspaceCocone : IsColimit (completionSubspaceCocone B S hS X Z) :=
  haveI := (plusPlusAdjunction (BigFppfOver.topology B S hS) (Type (u + 1))).leftAdjoint_preservesColimits
  isColimitOfPreserves (plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (isColimitNeighbourhoodCocone B S hS X Z)

end AlgebraicGeometry.Space

end
