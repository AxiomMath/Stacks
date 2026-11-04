module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.FlatBaseChangeOnIntersection
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SectionsRingOnSubsetFunctorial

/-!
# Sections over an intersection of quasi-compact opens under flat base change

Let `p : X ⟶ Y` be the base change of a flat morphism `g` of affine schemes along `Y ⟶ S`, with
`Y` quasi-separated, and let `E ⊆ Y` be an intersection of a nonempty family of quasi-compact
opens. Then the ring of functions on `p⁻¹E` is the pushout of the ring of functions on `E` along
`g`, the comparison morphism being `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`.

## Main results

* `AlgebraicGeometry.isPushout_sectionsRingOnSubsetMap_of_flat`: the square of sections over `E`
  and over `p⁻¹E` is a pushout, the comparison being
  `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`, for a Cartesian square of spectra.
* `AlgebraicGeometry.isPushout_sectionsRingOnSubsetMap_of_flat_of_isAffine`: the same statement
  for a Cartesian square whose base and whose flat side are affine schemes.

## References

* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0APH](https://stacks.math.columbia.edu/tag/0APH)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Let `p : X ⟶ Y` be the base change of a flat morphism `g : Spec R ⟶ Spec A` along
`πY : Y ⟶ Spec A`, with `Y` quasi-separated, and let `E ⊆ Y` be an intersection of a nonempty
family of quasi-compact opens of `Y`. Then the square of restrictions of global functions to `E`
and to `p⁻¹E` is a pushout of rings, with comparison morphism
`AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap p E (p⁻¹E)`. -/
theorem isPushout_sectionsRingOnSubsetMap_of_flat {A R : CommRingCat.{u}} {Y X : Scheme.{u}}
    {πY : Y ⟶ Spec A} {g : Spec R ⟶ Spec A} {p : X ⟶ Y} {k : X ⟶ Spec R}
    (H : IsPullback p k πY g) [Flat g] [QuasiSeparatedSpace Y] {I : Type u} [Nonempty I]
    (V : I → Y.Opens) (hV : ∀ i, IsCompact (V i : Set Y))
    (E : Set Y) (hE : E = ⋂ i, (V i : Set Y)) :
    IsPushout (πY.appTop ≫ Y.topToSubset E) g.appTop
      (Scheme.sectionsRingOnSubsetMap p E (⇑p ⁻¹' E) (Set.Subset.refl _))
      (k.appTop ≫ X.topToSubset (⇑p ⁻¹' E)) := by
  classical
  have hEY : ∀ j, E ⊆ (V j : Set Y) := fun j ↦ hE ▸ Set.iInter_subset _ j
  let J : Type u := { U : Y.Opens // IsCompact (U : Set Y) ∧ E ⊆ (U : Set Y) }
  have : Nonempty J := ⟨⟨V (Classical.arbitrary I), hV _, hEY _⟩⟩
  have hJV : ∀ j : J, IsCompact ((j.1 : Y.Opens) : Set Y) := fun j ↦ j.2.1
  have hJdir : ∀ i j : J, ∃ l : J, ((l.1 : Y.Opens) : Set Y) ⊆
      ((i.1 : Y.Opens) : Set Y) ∩ ((j.1 : Y.Opens) : Set Y) := fun i j ↦
    ⟨⟨i.1 ⊓ j.1, i.2.1.inter_of_isOpen j.2.1 i.1.isOpen j.1.isOpen,
      Set.subset_inter i.2.2 j.2.2⟩, le_rfl⟩
  have hJE : E = ⋂ j : J, ((j.1 : Y.Opens) : Set Y) := by
    refine Set.Subset.antisymm (Set.subset_iInter fun j ↦ j.2.2) fun x hx ↦ ?_
    rw [hE]
    exact Set.mem_iInter.mpr fun i ↦ Set.mem_iInter.mp hx ⟨V i, hV i, hEY i⟩
  obtain ⟨w, hpush, hstage⟩ :=
    isPushout_sectionsRingOnSubset_of_flat H (fun j : J ↦ j.1) hJV E hJE
  obtain ⟨e, he⟩ :=
    colimit_sectionsRing_iso_sectionsRingOnSubset Y (fun j : J ↦ j.1) hJV hJdir E hJE
  have hw : w = Scheme.sectionsRingOnSubsetMap p E (⇑p ⁻¹' E) (Set.Subset.refl _) := by
    refine (cancel_epi e.hom).mp (colimit.hom_ext fun j ↦ ?_)
    rw [← Category.assoc, ← Category.assoc, he j, hstage j.val,
      Scheme.stageToSubset_comp_sectionsRingOnSubsetMap p (fun j : J ↦ j.1) E
        (fun j ↦ j.2.2) (⇑p ⁻¹' E) (Set.Subset.refl _) j]
  rwa [← hw]

/-- Let
```
  Z ---k---→ B
  |          |
  p          g
  ↓          ↓
  Y ---πY--→ S
```
be a Cartesian square of schemes with `S` and `B` affine, `g` flat and `Y` quasi-separated, and
let `E ⊆ Y` be an intersection of a nonempty family of quasi-compact opens of `Y`. Then the
square of restrictions of global functions to `E` and to `p⁻¹E` is a pushout of rings, with
comparison morphism `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap p E (p⁻¹E)`. -/
theorem isPushout_sectionsRingOnSubsetMap_of_flat_of_isAffine {S B Y Z : Scheme.{u}}
    [IsAffine S] [IsAffine B] {πY : Y ⟶ S} {g : B ⟶ S} {p : Z ⟶ Y} {k : Z ⟶ B}
    (H : IsPullback p k πY g) [Flat g] [QuasiSeparatedSpace Y] {I : Type u} [Nonempty I]
    (V : I → Y.Opens) (hV : ∀ i, IsCompact (V i : Set Y))
    (E : Set Y) (hE : E = ⋂ i, (V i : Set Y)) :
    IsPushout (πY.appTop ≫ Y.topToSubset E) g.appTop
      (Scheme.sectionsRingOnSubsetMap p E (⇑p ⁻¹' E) (Set.Subset.refl _))
      (k.appTop ≫ Z.topToSubset (⇑p ⁻¹' E)) := by
  have hg : Spec.map g.appTop = B.isoSpec.inv ≫ g ≫ S.isoSpec.hom := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality g, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have : Flat (Spec.map g.appTop) := by rw [hg]; infer_instance
  have H' : IsPullback p (k ≫ B.isoSpec.hom) (πY ≫ S.isoSpec.hom) (Spec.map g.appTop) :=
    (IsPullback.paste_horiz H.flip
      (IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality g⟩)).flip
  refine (isPushout_sectionsRingOnSubsetMap_of_flat H' V hV E hE).of_iso'
    (Scheme.ΓSpecIso Γ(S, ⊤)).symm (Iso.refl _) (Scheme.ΓSpecIso Γ(B, ⊤)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Scheme.isoSpec_hom, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Iso.refl_hom,
      Iso.symm_hom, Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc]
  · simp [Scheme.ΓSpecIso_inv_naturality]
  · simp
  · simp only [Scheme.isoSpec_hom, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Iso.refl_hom,
      Iso.symm_hom, Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc]

end AlgebraicGeometry

end

end
