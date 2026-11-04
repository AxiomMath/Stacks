module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Locus
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.RelativeDimensionDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The Cohen–Macaulay locus of a given relative dimension

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` which is locally of finite
presentation, and let `d` be a natural number. The set of points of `X` at which `f` is
Cohen–Macaulay and has relative dimension `d` is open in the point space `|X|`.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_comp`: a chart condition of Tag
  04NC at the image of a point passes to the precomposition with a morphism which is étale after
  every representable base change.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_comp_of_presheaf_etale`: the same for
  Cohen–Macaulayness at a point.
* `AlgebraicGeometry.Space.isOpen_setOf_isCohenMacaulayAt_and_hasRelativeDimensionAt`: the
  locus where a flat morphism locally of finite presentation is Cohen–Macaulay of relative
  dimension `d` is open.

## References

* [Stacks Project, Tag 0E10](https://stacks.math.columbia.edu/tag/0E10)
* [Stacks Project, Tag 0E11](https://stacks.math.columbia.edu/tag/0E11)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- A condition on germs which holds on every pointed étale chart of `f` at the image of a point
holds on every pointed étale chart of `g ≫ f` at that point, for `g` étale after every
representable base change. -/
theorem holdsOnEveryEtaleChartAtPoint_comp
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    {E F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : E ⟶ F) (f : F ⟶ G)
    (hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (x : points B S hS E)
    (h : HoldsOnEveryEtaleChartAtPoint B S hS Q f (pointsMap B S hS E g x)) :
    HoldsOnEveryEtaleChartAtPoint B S hS Q (g ≫ f) x := by
  intro c
  refine h { U := c.U
             V := c.V
             a := c.a ≫ g
             b := c.b
             h := c.h
             a_etale := MorphismProperty.comp_mem _ c.a g c.a_etale hg
             b_etale := c.b_etale
             comm := by rw [c.comm, Category.assoc]
             representative := c.representative
             point := c.point
             maps_to := ?_ }
  rw [pointsMap_comp_apply, c.maps_to]

/-- Cohen–Macaulayness at the image of a point passes to the precomposition with a morphism
which is étale after every representable base change. -/
theorem isCohenMacaulayAt_comp_of_presheaf_etale
    {E F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : E ⟶ F) (f : F ⟶ G)
    (hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (x : points B S hS E) (h : IsCohenMacaulayAt B S hS f (pointsMap B S hS E g x)) :
    IsCohenMacaulayAt B S hS (g ≫ f) x :=
  ⟨holdsOnEveryEtaleChartAtPoint_comp B S hS _ g f hg x h.1,
    holdsOnEveryEtaleChartAtPoint_comp B S hS _ g f hg x h.2⟩

/-- **The Cohen–Macaulay locus of relative dimension `d` is open.** For a flat morphism of
algebraic spaces over `S` which is locally of finite presentation, the set of points of the
source at which it is Cohen–Macaulay and has relative dimension `d` is open. -/
theorem isOpen_setOf_isCohenMacaulayAt_and_hasRelativeDimensionAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf_flat : IsFlat B S hS f) (hf_lfp : IsLocallyOfFinitePresentation B S hS f) (d : ℕ) :
    IsOpen {x : points B S hS X |
      IsCohenMacaulayAt B S hS f x ∧ HasRelativeDimensionAt (d : ℕ∞) B S hS f x} := by
  set W := {x : points B S hS X | IsCohenMacaulayAt B S hS f x}
  have hW : IsOpen W := isOpen_setOf_isCohenMacaulayAt B S hS hX hY f hf_flat hf_lfp
  set Z := openSubspaceOfPoints B S hS X W
  have hZ : IsOpenSubspace B S hS Z := isOpenSubspace_openSubspaceOfPoints B S hS hX W hW
  have hZet := presheaf_etale_of_isOpenImmersion B S hS hZ.2
  have hrange : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = W :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS W
  have hmem : ∀ z, pointsMap B S hS Z.toFunctor Z.ι z ∈ W := fun z => hrange ▸ ⟨z, rfl⟩
  have hlfp : IsLocallyOfFinitePresentation B S hS (Z.ι ≫ f) :=
    isLocallyOfFinitePresentation_comp B S hS hZ.1 hX hY Z.ι f
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hZ.2) hf_lfp
  have hCM : IsCohenMacaulay B S hS (Z.ι ≫ f) := fun z =>
    isCohenMacaulayAt_comp_of_presheaf_etale B S hS Z.ι f hZet z
      (hmem z)
  obtain ⟨Zd, hclopen, hcover, -, hdim⟩ :=
    exists_clopen_relativeDimension_decomposition B S hS hZ.1 hY (Z.ι ≫ f) hlfp hCM
  have hpiece : ∀ (e : ℕ) (z' : points B S hS (Zd e).toFunctor),
      HasRelativeDimensionAt (e : ℕ∞) B S hS f
        (pointsMap B S hS Z.toFunctor Z.ι
          (pointsMap B S hS (Zd e).toFunctor (Zd e).ι z')) := fun e z' => by
    have h1 := (hasRelativeDimensionAt_comp_iff B S hS (e : ℕ∞) (Zd e).ι (Z.ι ≫ f)
      (presheaf_etale_of_isOpenImmersion B S hS (hclopen e).1.2) (hclopen e).1.1 hY z').mp
      (hdim e z')
    exact (hasRelativeDimensionAt_comp_iff B S hS (e : ℕ∞) Z.ι f hZet hZ.1 hY _).mp h1
  have huniq : ∀ (x : points B S hS X) {e e' : ℕ},
      HasRelativeDimensionAt (e : ℕ∞) B S hS f x →
        HasRelativeDimensionAt (e' : ℕ∞) B S hS f x → e = e' := by
    intro x e e' he he'
    obtain ⟨c, hc⟩ := (holdsOnEveryEtaleChartAtPoint_iff_some B S hS
      (@HasFiberDimensionAt.{u} (e' : ℕ∞))
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e' : ℕ∞)) hX hY f x).mp he'
    have hce := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp hc
    have hcd := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp (he c)
    exact_mod_cast hcd.symm.trans hce
  have heq : {x : points B S hS X |
        IsCohenMacaulayAt B S hS f x ∧ HasRelativeDimensionAt (d : ℕ∞) B S hS f x} =
      pointsMap B S hS Z.toFunctor Z.ι ''
        Set.range (pointsMap B S hS (Zd d).toFunctor (Zd d).ι) := by
    ext x
    refine ⟨fun ⟨hxW, hxd⟩ => ?_, ?_⟩
    · obtain ⟨z, rfl⟩ : x ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := hrange ▸ hxW
      obtain ⟨e, z', rfl⟩ := hcover z
      obtain rfl : e = d := huniq _ (hpiece e z') hxd
      exact ⟨_, ⟨z', rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z', rfl⟩, rfl⟩
      exact ⟨hmem _, hpiece d z'⟩
  rw [heq]
  exact isOpenMap_pointsMap_of_isOpenImmersion B S hS Z.ι hZ.2 _
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS (Zd d).ι (hclopen d).1.2)

end AlgebraicGeometry.Space

end
