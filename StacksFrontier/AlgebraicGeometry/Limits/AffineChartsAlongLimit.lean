module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine charts of a stage of a cofiltered limit of schemes

A quasi-compact scheme mapping to a scheme `X` admits a finite cover by affine opens each of
which lands in an affine open of `X`. When the quasi-compact scheme is a stage of a cofiltered
inverse system with affine transition morphisms, such a chart stays affine after every transition
and on the limit, and its ring of global sections on the limit is the filtered colimit of its
rings of global sections at the later stages.

## Main definitions

* `AlgebraicGeometry.isColimitΓMapCoconeOpensConeOp` exhibits the ring of global sections of the
  inverse image of an affine chart on the limit as the colimit of those at the later stages.

## Main results

* `AlgebraicGeometry.exists_finite_affineOpenCover_subordinate`: the finite affine cover
  subordinate to a morphism.
* `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_comp`: a morphism from an affine scheme into an
  affine open is, up to the identifications with spectra, the spectrum of its map on sections.

## Implementation notes

The inverse images of an open subscheme along the stages of a diagram and along its limit cone
are Mathlib's `AlgebraicGeometry.opensDiagram` and `AlgebraicGeometry.opensCone`, and the latter
is limiting by `AlgebraicGeometry.isLimitOpensCone`. Taking global sections of the opposite of
that limit cone gives the colimit, because every scheme in the diagram of inverse images of an
affine chart is affine and `Scheme.Γ` turns limits of affine schemes into colimits of rings.

The index category lives in the universe of the schemes, as in Mathlib's theory of cofiltered
limits with affine transition morphisms. With an index in a strictly larger universe and no
smallness hypothesis the conclusion fails, as the inverse system
`Stacks.AlgebraicGeometry.SmallnessNecessary.system` of spectra of fields shows: its limit is
empty although every stage is a nonempty affine scheme.

## References

* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- **A finite affine cover subordinate to a morphism.** A quasi-compact scheme mapping to a
scheme `X` is covered by finitely many affine opens, each contained in the inverse image of an
affine open of `X`. -/
theorem exists_finite_affineOpenCover_subordinate {Y X : Scheme.{u}} [CompactSpace Y]
    (p : Y ⟶ X) :
    ∃ (n : ℕ) (W : Fin n → X.Opens) (U : Fin n → Y.Opens),
      (∀ j, IsAffineOpen (W j)) ∧ (∀ j, IsAffineOpen (U j)) ∧ iSup U = ⊤ ∧
        ∀ j, U j ≤ p ⁻¹ᵁ W j := by
  classical
  have hlocal (y : Y) : ∃ (W : X.affineOpens) (U : Y.affineOpens), y ∈ U.1 ∧ U.1 ≤ p ⁻¹ᵁ W.1 := by
    obtain ⟨W, hW, hyW, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := p.base y) (U := ⊤) (Set.mem_univ _)
    obtain ⟨U, hU, hyU, hUpre⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := p ⁻¹ᵁ W) hyW
    exact ⟨⟨W, hW⟩, ⟨U, hU⟩, hyU, hUpre⟩
  choose W₀ U₀ hmem hsub₀ using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => ((U₀ y).1 : Set Y))
    (fun y => (U₀ y).1.isOpen) fun y _ => Set.mem_iUnion.mpr ⟨y, hmem y⟩
  refine ⟨t.card, fun j => (W₀ (t.equivFin.symm j)).1, fun j => (U₀ (t.equivFin.symm j)).1,
    fun j => (W₀ _).2, fun j => (U₀ _).2, le_antisymm le_top fun y _ => ?_,
    fun j => hsub₀ (t.equivFin.symm j)⟩
  obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨z, hzt⟩, by simpa using hyz⟩

/-- **A morphism from an affine scheme into an affine open is the spectrum of a ring map.** For
an affine open `W` of a scheme and a morphism `f` into it from an affine scheme, conjugating `f`
by the canonical identifications of both ends with spectra gives the spectrum of the map of rings
of sections of `f`. -/
theorem IsAffineOpen.isoSpec_inv_comp {X Y : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    [IsAffine Y] (f : Y ⟶ W.toScheme) :
    Y.isoSpec.inv ≫ f = Spec.map (W.topIso.inv ≫ f.appTop) ≫ hW.isoSpec.inv := by
  have : IsAffine W.toScheme := hW
  calc Y.isoSpec.inv ≫ f = Spec.map f.appTop ≫ W.toScheme.isoSpec.inv :=
        (Scheme.isoSpec_inv_naturality f).symm
    _ = Spec.map (W.topIso.inv ≫ f.appTop) ≫ hW.isoSpec.inv := by
        show Spec.map f.appTop ≫ W.toScheme.isoSpec.inv =
          Spec.map (W.topIso.inv ≫ f.appTop) ≫
            (Scheme.Spec.mapIso W.topIso.symm.op).inv ≫ W.toScheme.isoSpec.inv
        rw [Spec.map_comp,
          show Spec.map W.topIso.inv = (Scheme.Spec.mapIso W.topIso.symm.op).hom from rfl,
          Category.assoc, Iso.hom_inv_id_assoc]

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

/-- **Global sections of an affine chart on the limit are the colimit of those at the stages.**
For an affine open `U` of a stage of a cofiltered inverse system of schemes with affine
transition morphisms, the inverse images of `U` at the later stages form a diagram of affine
schemes whose limit is the inverse image of `U` on the limit, so their rings of global sections
form a filtered colimit. -/
@[sga "4 VII 5.1" "partial"]
noncomputable def isColimitΓMapCoconeOpensConeOp [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (i : I) {U : (D.obj i).Opens}
    (hU : IsAffineOpen U) : IsColimit (Scheme.Γ.mapCocone (opensCone D c i U).op) :=
  have (k : (Over i)ᵒᵖ) : IsAffine ((opensDiagram D i U).op.obj k).unop := hU.preimage _
  isColimitOfPreserves Scheme.Γ (isLimitOpensCone D c hc i U).op

end AlgebraicGeometry

end
