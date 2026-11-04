module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCoveringCofinality
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AlgebraSiteCartesianBase

/-!
# Covering sieves of the algebra site are refined by finite flat coverings

Let `B` be a chosen big `τ`-site over `Spec A`.  Its `A`-algebras carry the induced topology
`Stacks.Adequate.affineSubsiteTopology`, and `Stacks.Adequate.algebraSiteScheme` sends an algebra
of the site to the spectrum of its underlying ring.  This file proves that every covering sieve
of that topology is refined by a **finite** family of algebra maps which is a **flat** covering
on spectra.

That is the hypothesis `hRefine` of
`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'`, so it is what lets the
module extensions `C ↦ C ⊗[A] M` be recognized as sheaves on the algebra site.

The proof has three steps.  The affine-spectrum functor `Stacks.Adequate.affineSpecOver` at the
identity structure morphism exhibits the `A`-algebras of the site as a dense subsite, so a
covering sieve of the algebra site pushes forward to a covering sieve of the big site at an
*affine* object.  There `Stacks.Adequate.BigSite.affineCovCofinal` (Tag 03XA) refines it by a
finite jointly-surjective family of `τ`-covering morphisms between affine objects, and a
`τ`-covering morphism is flat for each of the five topologies.  Finally the family is transported
back along the affine-spectrum functor, which over the base `Spec A` is fully faithful: each
member, being affine, is isomorphic to the spectrum of an `A`-algebra of the site, fullness turns
the covering morphism into an algebra map, and faithfulness turns membership of its image in the
pushforward sieve back into membership in the original sieve.

## Main results

* `Stacks.Adequate.exists_iso_affineSpecOver_of_isAffine` — an affine object of a chosen big site
  over `Spec A` is isomorphic to the spectrum of an `A`-algebra of the site.  This is the
  essential surjectivity of the affine-spectrum functor onto the affine objects, extracted from
  the proof of `Stacks.Adequate.coverByImage_affineSpecOver_of_isAffine`.
* `Stacks.Adequate.exists_finite_flat_refinement_algebraSite` — **the main result**: a covering
  sieve of the algebra site contains a finite family which is a flat covering on spectra.

## Implementation notes

The refining family is indexed in `Type u` by `ULift`-ing the index type of the family produced
by `Stacks.Adequate.BigSite.affineCovCofinal`, which lives in `Type 0`; nothing about the family
depends on the index universe.

## References

* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- **An affine object of a chosen big site over `Spec A` is the spectrum of an `A`-algebra of
the site.**  By `AlgebraicGeometry.essImage_algSpec` an affine scheme over `Spec A` is the
spectrum of an `A`-algebra, and that algebra belongs to the site because
`AlgebraicGeometry.Scheme.size` is invariant under isomorphism.

This is the essential-surjectivity half of the statement that the affine-spectrum functor
identifies the `A`-algebras of the site with its affine objects; the full faithfulness half is
`Stacks.Adequate.affineSpecOver_full` and `Stacks.Adequate.affineSpecOver_faithful`. -/
public theorem exists_iso_affineSpecOver_of_isAffine {W : B.category}
    (hW : IsAffine W.left.obj) :
    ∃ D : algebraSite B, Nonempty ((affineSpecOver B A (𝟙 (Spec A))).obj D ≅ W) := by
  obtain ⟨R₀, ⟨e⟩⟩ := (essImage_algSpec (G := B.toOver.obj W)).mpr hW
  have hsize : schemeSizeBelow B.cutoff (Spec (CommRingCat.of (R₀.unop : Type u))) :=
    (Scheme.size_congr ((Over.forget (Spec A)).mapIso e)).trans_lt W.left.property
  refine ⟨op ⟨R₀.unop, hsize⟩, ⟨?_⟩⟩
  refine Over.isoMk (ObjectProperty.isoMk _ ((Over.forget (Spec A)).mapIso e)) ?_
  apply ObjectProperty.hom_ext
  exact (Over.w e.hom).trans (Category.comp_id _).symm

/-- Precomposing with an isomorphism does not shrink the range of a morphism of schemes: a point
hit by `b` is hit by `a ≫ b`, at the preimage under `a` of its witness. -/
private theorem mem_range_comp_of_isIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) [IsIso a]
    (b : Y ⟶ Z) {x : Z} (hx : x ∈ Set.range b) : x ∈ Set.range (a ≫ b) := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨inv a y, ?_⟩
  have h : a (inv a y) = y := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    simp
  rwa [Scheme.Hom.comp_apply, h]

/-- **Every covering sieve of the `A`-algebras of a chosen big site over `Spec A` is refined by a
finite flat covering.**  Precisely: a sieve covering for the induced topology
`Stacks.Adequate.affineSubsiteTopology` contains a family of algebra maps, finite in number,
whose spectra form a jointly surjective family of flat morphisms onto the spectrum of the
algebra.

The `A`-algebras of the site are a dense subsite of the big site
(`Stacks.Adequate.affineSpecOver_isDenseSubsite`), so the sieve pushes forward to a covering
sieve of the big site at the spectrum of the algebra, which is an affine object of the site.
Cofinality of the finite affine coverings there (`Stacks.Adequate.BigSite.affineCovCofinal`,
[Stacks, Tag 03XA]) refines that pushforward by a finite jointly surjective family of
`τ`-covering morphisms between affine objects, and such a morphism is flat for every one of the
five topologies by
`AlgebraicGeometry.coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation`.  Each
member of that family is affine, hence the spectrum of an `A`-algebra of the site; fullness of
the affine-spectrum functor over `Spec A` turns its structure morphism into an algebra map, and
faithfulness turns the refinement statement back into one about the original sieve. -/
public theorem exists_finite_flat_refinement_algebraSite
    {U : algebraSite B} (S : Sieve U) (hS : S ∈ affineSubsiteTopology B U) :
    ∃ E : CategoryTheory.PreZeroHypercover.{u} U, Finite E.I₀ ∧
      (E.map (algebraSiteScheme B)).presieve₀ ∈
        AlgebraicGeometry.Scheme.precoverage @AlgebraicGeometry.Flat
          ((algebraSiteScheme B).obj U) ∧ E.sieve₀ ≤ S := by
  classical
  have hpush : (S.functorPushforward (affineSpecOver B A (𝟙 (Spec A)))) ∈
      B.topology ((affineSpecOver B A (𝟙 (Spec A))).obj U) :=
    (Functor.IsDenseSubsite.functorPushforward_mem_iff
      (J := affineSubsiteTopology B) (K := B.topology)).mpr hS
  obtain ⟨E', hE'mem, hE'le⟩ :=
    B.affineCovCofinal _ (isAffine_algebraSiteScheme_obj B U) _ hpush
  obtain ⟨-, hfin, haff, hprop, hsurj⟩ := hE'mem
  choose D hD using fun i => exists_iso_affineSpecOver_of_isAffine B (haff i)
  have θ : ∀ i, (affineSpecOver B A (𝟙 (Spec A))).obj (D i) ≅ E'.1.X i := fun i => (hD i).some
  choose g hg using fun i =>
    (affineSpecOver B A (𝟙 (Spec A))).map_surjective ((θ i).hom ≫ E'.1.f i)
  have hmem : ∀ i, S.arrows (g i) := by
    intro i
    refine (Sieve.mem_functorPushforward_iff_of_full_of_faithful
      (F := affineSpecOver B A (𝟙 (Spec A))) S (g i)).mp ?_
    rw [hg i]
    exact (S.functorPushforward _).downward_closed (hE'le _ (E'.1.sieve₀_f i)) (θ i).hom
  refine ⟨⟨ULift.{u} E'.1.I₀, fun i => D i.down, fun i => g i.down⟩, ?_, ?_, ?_⟩
  · exact Finite.of_equiv _ Equiv.ulift.symm
  · have hmapL : ∀ i, (algebraSiteScheme B).map (g i) =
        (B.toOver ⋙ Over.forget (Spec A)).map (θ i).hom ≫
          (B.toOver ⋙ Over.forget (Spec A)).map (E'.1.f i) := by
      intro i
      rw [← Functor.map_comp, ← hg i]
      rfl
    refine (Scheme.presieve₀_mem_precoverage_iff _).mpr ⟨fun x => ?_, fun i => ?_⟩
    · obtain ⟨i, hx⟩ := hsurj x
      refine ⟨ULift.up i, ?_⟩
      show x ∈ Set.range ((algebraSiteScheme B).map (g i))
      rw [hmapL i]
      exact mem_range_comp_of_isIso _ _ hx
    · show Flat ((algebraSiteScheme B).map (g i.down))
      rw [hmapL i.down]
      have hflat : Flat ((B.toOver ⋙ Over.forget (Spec A)).map (E'.1.f i.down)) :=
        (coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation τ _
          (hprop i.down)).1
      infer_instance
  · rintro V f ⟨W, a, b, ⟨i⟩, rfl⟩
    exact S.downward_closed (hmem i.down) a

end Stacks.Adequate

end
