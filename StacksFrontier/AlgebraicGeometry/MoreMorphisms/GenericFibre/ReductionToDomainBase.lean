module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyReducedGenericFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingHypotheses
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FibreBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.IntegralSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.IsoTransport
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.UniversalHomeomorphismTransport

/-!
# Step A of Stacks Tag 0559: the reduction

Stacks Tag 0559 says that a finite type morphism `f : X ⟶ Y` onto an irreducible base whose
fibre over the generic point `η` of `Y` is geometrically irreducible has geometrically
irreducible fibres over a nonempty open subscheme of `Y`. The first step of its proof reduces
the statement to the case where the base is the spectrum of a domain and the generic fibre is in
addition geometrically reduced; the source may then also be taken integral, which is what Tag
0552 needs in order to compare `X` with the standard model of step F.

`AlgebraicGeometry.GeometricallyIrreducibleAfterShrinkingOverDomain` is that special case, and
`AlgebraicGeometry.geometricallyIrreducibleAfterShrinking_of_overDomain` is the reduction.

## The reduction

Tag 0550 produces a nonempty open `V ⊆ Y`, an integral affine scheme `Y'` and a finite universal
homeomorphism `g : Y' ⟶ V` such that, writing `a := g ≫ V.ι` and `P := X ×_Y Y'`, the reduction
`X' := P^{red}` is flat and of finite presentation over `Y'` with geometrically reduced fibre
over the generic point of `Y'`. Four observations finish the reduction.

* `a` has dense range and is an open map, so it carries the generic point `η'` of `Y'` to `η`,
  and it carries opens of `Y'` to opens of `Y`.
* The fibre of `X' ⟶ Y'` over `η'` is geometrically irreducible: the fibre of `P ⟶ Y'` over `η'`
  is the base change of `X_η` along `κ(η) ⟶ κ(η')`, and neither a base change by a field
  extension (Tag 054P) nor precomposition with the universal homeomorphism `X' ⟶ P` (Tag 054M)
  changes geometric irreducibility of a fibre.
* `X'` is therefore integral: it is reduced by construction, and it is irreducible because
  `X' ⟶ Y'` is flat and of finite presentation, hence universally open, so its fibre over `η'`
  is dense in `X'` and irreducible (Tag 004Z).
* `Y'` is integral and affine, so it is the spectrum of a domain, and the special case applies
  to `X' ⟶ Spec Γ(Y', ⊤)`. The resulting open of `Y'` is pushed forward to `Y` along `a`, the
  three transports above being reversible.

## Main results

* `AlgebraicGeometry.GeometricallyIrreducibleAfterShrinkingOverDomain`
* `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_universalHomeomorphismCover`
* `AlgebraicGeometry.geometricallyIrreducibleAfterShrinking_of_overDomain`

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), step A of the first
  proof
* [Stacks Project, Tag 0550](https://stacks.math.columbia.edu/tag/0550)
* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The case of **Stacks Project, Tag 0559** to which step A of its first proof reduces the
general statement: an integral scheme, flat and of finite presentation over the spectrum of a
domain, whose fibre over the generic point of the base is geometrically irreducible and
geometrically reduced, has geometrically irreducible fibres over a nonempty open subscheme of
the base. -/
def GeometricallyIrreducibleAfterShrinkingOverDomain : Prop :=
  ∀ (R : CommRingCat.{u}) [IsDomain R] {X : Scheme.{u}} (f : X ⟶ Spec R),
    IsIntegral X → LocallyOfFiniteType f → QuasiCompact f → Flat f → FinitePresentation f →
      GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec R))) →
      GeometricallyReduced (f.fiberToSpecResidueField (genericPoint (Spec R))) →
      ∃ V : (Spec R).Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V)

/-- Geometric irreducibility of a morphism restricted over an open subscheme of its target is
geometric irreducibility of all of its fibres over points of that open. -/
theorem geometricallyIrreducible_morphismRestrict_iff_forall {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) :
    GeometricallyIrreducible (f ∣_ V) ↔
      ∀ v : V.toScheme, GeometricallyIrreducible (f.fiberToSpecResidueField (V.ι v)) := by
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [GeometricallyIrreducible.iff_geometricallyIrreducible_fiber]
  exact forall_congr' fun v ↦
    prop_fiberToSpecResidueField_of_morphismRestrict (P := @GeometricallyIrreducible) f V v

/-- Geometric irreducibility of the fibre of `r ≫ pullback.fst a f` at a point `y'` is that of the
fibre of `f` at `a y'`, for a universal homeomorphism `r`. -/
private theorem geometricallyIrreducible_fiber_comp_fst_iff {X Y Y' X' : Scheme.{u}} (f : X ⟶ Y)
    (a : Y' ⟶ Y) (r : X' ⟶ pullback a f) [UniversalHomeomorphism r] (y' : Y') {y : Y}
    (hy : a y' = y) :
    GeometricallyIrreducible ((r ≫ pullback.fst a f).fiberToSpecResidueField y') ↔
      GeometricallyIrreducible (f.fiberToSpecResidueField y) :=
  (geometricallyIrreducible_fiber_comp_iff_of_universalHomeomorphism r (pullback.fst a f) y').trans
    (geometricallyIrreducible_fiber_pullbackFst_iff f a y' hy)

/-- **Step A of Stacks Tag 0559**, in the form in which Tag 0550 supplies its input. Let
`f : X ⟶ Y` be a finite type morphism onto an irreducible base with generic point `η` and with
geometrically irreducible fibre over `η`. Let `a : Y' ⟶ Y` be an open map with dense range whose
source is integral and affine, let `r : X' ⟶ Y' ×_Y X` be a universal homeomorphism with reduced
source, and assume `r ≫ pullback.fst a f` is flat, of finite presentation, and has
geometrically reduced fibres over the generic points of `Y'`. Granted the special case
`AlgebraicGeometry.GeometricallyIrreducibleAfterShrinkingOverDomain`, the morphism `f` has
geometrically irreducible fibres over a nonempty open subscheme of `Y`. -/
theorem exists_open_geometricallyIrreducible_of_universalHomeomorphismCover
    (H : GeometricallyIrreducibleAfterShrinkingOverDomain.{u})
    {X Y Y' X' : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y] [LocallyOfFiniteType f]
    [QuasiCompact f] {η : Y} (hη : IsGenericPoint η Set.univ)
    (hgen : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (a : Y' ⟶ Y) [IsIntegral Y'] [IsAffine Y'] (hao : IsOpenMap a)
    (had : Dense (Set.range a))
    (r : X' ⟶ pullback a f) [UniversalHomeomorphism r] [IsReduced X']
    (hflat : Flat (r ≫ pullback.fst a f))
    (hfp : FinitePresentation (r ≫ pullback.fst a f))
    (hredgen : ∀ η' : Y', IsGenericPoint η' Set.univ →
      GeometricallyReduced ((r ≫ pullback.fst a f).fiberToSpecResidueField η')) :
    ∃ W : Y.Opens, Nonempty W ∧ GeometricallyIrreducible (f ∣_ W) := by
  have hri : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hrr : MorphismProperty.RespectsIso @GeometricallyReduced.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hlfp : LocallyOfFinitePresentation (r ≫ pullback.fst a f) := hfp.1
  have hqc' : QuasiCompact (r ≫ pullback.fst a f) := hfp.2.1
  have hqs' : QuasiSeparated (r ≫ pullback.fst a f) := hfp.2.2
  -- The generic point of `Y'` and its image in `Y`.
  have hη' : IsGenericPoint (genericPoint Y') (Set.univ : Set Y') := by
    simpa using genericPoint_spec Y'
  have heq : a (genericPoint Y') = η :=
    (isGenericPoint_apply_of_denseRange a had hη').eq hη
  -- The fibre of `X' ⟶ Y'` over the generic point is geometrically irreducible.
  have h₁ : GeometricallyIrreducible
      ((r ≫ pullback.fst a f).fiberToSpecResidueField (genericPoint Y')) :=
    (geometricallyIrreducible_fiber_comp_fst_iff f a r (genericPoint Y') heq).mpr hgen
  -- Hence `X'` is integral.
  have hopen : IsOpenMap (r ≫ pullback.fst a f) := Scheme.Hom.isOpenMap _
  have : IrreducibleSpace ((r ≫ pullback.fst a f).fiber (genericPoint Y')) := by
    have := h₁
    exact GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f := (r ≫ pullback.fst a f).fiberToSpecResidueField (genericPoint Y'))
  have : IrreducibleSpace X' :=
    irreducibleSpace_of_isOpenMap_of_irreducibleSpace_fiber _ hopen (genericPoint Y') hη'
  have hX'int : IsIntegral X' := isIntegral_of_irreducibleSpace_of_isReduced X'
  -- Present `Y'` as the spectrum of a domain.
  let e : Y' ≅ Spec Γ(Y', ⊤) := Y'.isoSpec
  have hsur : Set.range e.hom = Set.univ := e.hom.homeomorph.surjective.range_eq
  have hgp : e.hom (genericPoint Y') = genericPoint (Spec Γ(Y', ⊤)) :=
    (isGenericPoint_apply_of_denseRange e.hom (by rw [hsur]; exact dense_univ) hη').eq
      (by simpa using genericPoint_spec (Spec Γ(Y', ⊤)))
  -- Apply the special case over `Spec Γ(Y', ⊤)`.
  obtain ⟨V'', hV''ne, hV''⟩ :=
    H Γ(Y', ⊤) ((r ≫ pullback.fst a f) ≫ e.hom) hX'int inferInstance inferInstance
      inferInstance ⟨inferInstance, inferInstance, inferInstance⟩
      (hgp ▸ (prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyIrreducible)
        (r ≫ pullback.fst a f) e (genericPoint Y')).mpr h₁)
      (hgp ▸ (prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyReduced)
        (r ≫ pullback.fst a f) e (genericPoint Y')).mpr (hredgen _ hη'))
  -- Transport the resulting open back to `Y'`, fibrewise.
  have key : ∀ y' : Y', e.hom y' ∈ V'' →
      GeometricallyIrreducible (f.fiberToSpecResidueField (a y')) := by
    intro y' hy'
    have h2 : GeometricallyIrreducible
        (((r ≫ pullback.fst a f) ≫ e.hom).fiberToSpecResidueField (e.hom y')) := by
      have := (geometricallyIrreducible_morphismRestrict_iff_forall _ V'').mp hV''
        ⟨e.hom y', hy'⟩
      simpa using this
    exact (geometricallyIrreducible_fiber_comp_fst_iff f a r y' rfl).mp
      ((prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyIrreducible)
        (r ≫ pullback.fst a f) e y').mp h2)
  -- Push the open forward to `Y`.
  obtain ⟨v''⟩ := hV''ne
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Y', e.hom y₀ = V''.ι v'' := by
    rw [← Set.mem_range, hsur]; trivial
  refine ⟨⟨a '' (e.hom ⁻¹' (V'' : Set (Spec Γ(Y', ⊤)))),
    hao _ (V''.isOpen.preimage e.hom.continuous)⟩, ⟨⟨a y₀, y₀, ?_, rfl⟩⟩, ?_⟩
  · rw [Set.mem_preimage, hy₀]
    exact v''.2
  · rw [geometricallyIrreducible_morphismRestrict_iff_forall]
    intro w
    obtain ⟨y', hy', hy'eq⟩ : ∃ y' : Y', e.hom y' ∈ V'' ∧ a y' = w.1 := by
      obtain ⟨y', hy', hy'eq⟩ := w.2
      exact ⟨y', hy', hy'eq⟩
    have hkey := key y' hy'
    rw [hy'eq] at hkey
    exact hkey

/-- **Step A of Stacks Tag 0559.** The conclusion of Tag 0559 follows from its special case over
the spectrum of a domain with integral source and geometrically reduced generic fibre. -/
theorem geometricallyIrreducibleAfterShrinking_of_overDomain
    (H : GeometricallyIrreducibleAfterShrinkingOverDomain.{u}) :
    GeometricallyIrreducibleAfterShrinking.{u} := by
  intro X Y f hYirr hft hqc η hη hgen
  have := hYirr
  have := hft
  have := hqc
  obtain ⟨V, hVne, Y', g, hgfin, hghom, hY'int, hY'aff, hrest⟩ :=
    exists_finiteUniversalHomeomorphism_geometricallyReduced_genericFiber f
  obtain ⟨hg'fin, hg'hom, hflat, hfp, hred⟩ := hrest
  have := hghom
  have := hY'int
  have := hY'aff
  have hgh : IsHomeomorph g := universalHomeomorphism_isHomeomorph g
  have hVdense : Dense ((V : Set Y)) :=
    (preirreducibleSpace_iff_open_dense Y).mp inferInstance V.isOpen hVne
  have hrange : Set.range (g ≫ V.ι) = (V : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hgh.surjective.range_eq,
      Set.image_univ, Scheme.Opens.range_ι]
  have : IsReduced (pullback (g ≫ V.ι) f).nilradical.subscheme :=
    isReduced_nilradical_subscheme _
  refine exists_open_geometricallyIrreducible_of_universalHomeomorphismCover H f hη hgen
    (g ≫ V.ι) ?_ (by rw [hrange]; exact hVdense)
    (pullback (g ≫ V.ι) f).nilradical.subschemeι hflat hfp hred
  exact V.ι.isOpenEmbedding.isOpenMap.comp hgh.isOpenMap

end AlgebraicGeometry

end
