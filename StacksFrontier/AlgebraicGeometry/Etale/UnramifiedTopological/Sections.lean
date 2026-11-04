module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal

/-!
# Sections of separated unramified morphisms

A section of an unramified morphism is an open immersion and a section of a separated morphism is
a closed immersion, so a section of a morphism which is both unramified and separated is an open
and closed immersion; in particular its image is open and closed.

If the target is connected, a section of a separated unramified morphism identifies the target
with a connected component of the source. Sections correspond canonically to the components on
which the morphism is an isomorphism, and two sections meeting at a point are equal. As a
consequence, two morphisms from a connected scheme to a separated unramified scheme over a base
agree as soon as they agree at one point, together with the induced maps of residue fields
there.

## Main results

* `AlgebraicGeometry.Unramified.section_isOpenImmersion`: a section of an unramified morphism is
  an open immersion.
* `AlgebraicGeometry.Unramified.section_isOpenImmersion_and_isClosedImmersion` and
  `AlgebraicGeometry.Unramified.isClopen_range_section`: a section of an unramified separated
  morphism is an open and closed immersion, and its image is open and closed.
* `AlgebraicGeometry.Unramified.section_isIso_onto_connectedComponent` identifies a section
  with a connected component.
* `AlgebraicGeometry.Unramified.sections_equiv_connectedComponents` gives the canonical
  correspondence between sections and components.
* `AlgebraicGeometry.Unramified.section_eq_of_common_point` gives pointwise uniqueness of
  sections.
* `AlgebraicGeometry.Unramified.eq_of_residueFieldMap_eq` gives equality of two morphisms which
  agree at a point and on its residue field.

## References

* [Stacks Project, Tag 024T](https://stacks.math.columbia.edu/tag/024T)
* [Stacks Project, Tag 024U](https://stacks.math.columbia.edu/tag/024U)
* [Stacks Project, Tag 024V](https://stacks.math.columbia.edu/tag/024V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Unramified

/-- A section of an unramified morphism is an open immersion. -/
@[stacks 024T "part (1)"]
public lemma section_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Unramified f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    IsOpenImmersion s := by
  have hdiag : @Unramified ≤ (@IsOpenImmersion : MorphismProperty Scheme).diagonal := by
    intro A B g hg
    show IsOpenImmersion (pullback.diagonal g)
    let : Unramified g := hg
    infer_instance
  let : MorphismProperty.HasOfPostcompProperty IsOpenImmersion @Unramified :=
    (MorphismProperty.hasOfPostcompProperty_iff_le_diagonal).2 hdiag
  exact MorphismProperty.of_postcomp (W := IsOpenImmersion) (W' := @Unramified)
    s f inferInstance (by rw [hs]; exact MorphismProperty.id_mem IsOpenImmersion Y)

private lemma section_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ f) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s f

/-- A section of an unramified separated morphism is both an open immersion and a closed
immersion. -/
@[stacks 024T "part (3)",
  ega "IV 17.9.3" "more general",
  sga "3 VIB 5.6.3" "(i) ⇒ (ii), special case"]
public theorem section_isOpenImmersion_and_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Unramified f] [IsSeparated f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    IsOpenImmersion s ∧ IsClosedImmersion s :=
  ⟨section_isOpenImmersion f s hs, section_isClosedImmersion f s hs⟩

/-- The image of a section of an unramified separated morphism is open and closed. -/
@[stacks 024T "part (3), the image"]
public theorem isClopen_range_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Unramified f] [IsSeparated f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    IsClopen (Set.range s) :=
  have := section_isOpenImmersion f s hs
  have := section_isClosedImmersion f s hs
  ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩

private lemma exists_eq_connectedComponent_of_clopen_connected {X : Type u}
    [TopologicalSpace X] {A : Set X} (hA : IsConnected A) (hne : A.Nonempty)
    (hclopen : IsClopen A) : ∃ x : X, A = connectedComponent x := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, (hA.subset_connectedComponent hx).antisymm (hclopen.connectedComponent_subset hx)⟩

private lemma exists_section_image_component {X Y : Scheme.{u}}
    [ConnectedSpace Y] (f : X ⟶ Y) [Unramified f] [IsSeparated f]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    ∃ (U : X.Opens) (sU : Y ⟶ U.toScheme),
      (∃ x : X, (U : Set X) = connectedComponent x) ∧ IsIso sU ∧ sU ≫ U.ι = s ∧
        (U : Set X) = Set.range (fun y : Y => s y) := by
  have : IsOpenImmersion s := section_isOpenImmersion f s hs
  have : IsClosedImmersion s := section_isClosedImmersion f s hs
  let U : X.Opens := s.opensRange
  let sU : Y ⟶ U.toScheme := s.isoOpensRange.hom
  have hconnected : _root_.IsConnected (Set.range s) := isConnected_range s.continuous
  have hU : ∃ x : X, (U : Set X) = connectedComponent x := by
    apply exists_eq_connectedComponent_of_clopen_connected
    · simpa [U, Scheme.Hom.opensRange] using hconnected
    · exact hconnected.1
    · exact ⟨(IsClosedImmersion.isClosedEmbedding s).isClosed_range,
        by simpa [U, Scheme.Hom.opensRange] using IsOpenImmersion.isOpen_range s⟩
  exact ⟨U, sU, hU, inferInstance, by simp [sU, U], rfl⟩

/-- A section of a separated unramified morphism onto a connected target is an isomorphism onto
a connected component of its source. -/
@[stacks 024U "sections are component isomorphisms",
  ega "IV 17.4.9" "section is comp. iso",
  ega "IV 17.9.4" "iso onto conn. component", sga "1 I 5.3" "section iso onto comp"]
public theorem section_isIso_onto_connectedComponent {X Y : Scheme.{u}}
    [ConnectedSpace Y] (f : X ⟶ Y) [Unramified f] [IsSeparated f]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    ∃ (U : X.Opens) (sU : Y ⟶ U.toScheme),
      (∃ x : X, (U : Set X) = connectedComponent x) ∧ IsIso sU ∧ sU ≫ U.ι = s := by
  obtain ⟨U, sU, hU, hsU, hfac, _⟩ := exists_section_image_component f s hs
  exact ⟨U, sU, hU, hsU, hfac⟩

private structure SectionImageComponentData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) where
  U : X.Opens
  sU : Y ⟶ U.toScheme
  component : ∃ x : X, (U : Set X) = connectedComponent x
  iso : IsIso sU
  factor : sU ≫ U.ι = s
  image : (U : Set X) = Set.range (fun y : Y => s y)

private noncomputable def sectionImageComponentData {X Y : Scheme.{u}}
    [ConnectedSpace Y] (f : X ⟶ Y) [Unramified f] [IsSeparated f]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) : SectionImageComponentData f s hs := by
  let h := exists_section_image_component f s hs
  obtain ⟨hcomp, hIso, hfac, himage⟩ := Classical.choose_spec (Classical.choose_spec h)
  exact ⟨_, _, hcomp, hIso, hfac, himage⟩

private lemma isIso_ι_comp_of_factor {X Y : Scheme.{u}} {f : X ⟶ Y} {s : Y ⟶ X}
    {U : X.Opens} {sU : Y ⟶ U.toScheme} [IsIso sU] (hs : s ≫ f = 𝟙 Y) (hfac : sU ≫ U.ι = s) :
    IsIso (U.ι ≫ f) :=
  IsIso.of_isIso_fac_left (f := sU) (g := U.ι ≫ f) (h := 𝟙 Y)
    (by rw [← Category.assoc, hfac, hs])

private lemma sectionImageComponent_hom_isIso {X Y : Scheme.{u}}
    {f : X ⟶ Y} [Unramified f] [IsSeparated f] {s : Y ⟶ X} {hs : s ≫ f = 𝟙 Y}
    (d : SectionImageComponentData f s hs) : IsIso (d.U.ι ≫ f) := by
  have := d.iso
  exact isIso_ι_comp_of_factor hs d.factor

private lemma sectionImageComponent_inv {X Y : Scheme.{u}}
    {f : X ⟶ Y} [Unramified f] [IsSeparated f] {s : Y ⟶ X} {hs : s ≫ f = 𝟙 Y}
    (d : SectionImageComponentData f s hs) [IsIso (d.U.ι ≫ f)] :
    inv (d.U.ι ≫ f) = d.sU :=
  IsIso.inv_eq_of_inv_hom_id (by rw [← Category.assoc, d.factor, hs])

/-- Sections correspond to the connected components on which the morphism is an isomorphism; the
component corresponding to a section is exactly its image. -/
@[stacks 024U "bijective correspondence",
  ega "IV 17.9.4" "bijection g ↦ g(Y)",
  ega "IV 17.4.9" "bijection g↦g(Y)", sga "1 I 5.3" "bijection with comps"]
public theorem sections_equiv_connectedComponents {X Y : Scheme.{u}}
    [ConnectedSpace Y] (f : X ⟶ Y) [Unramified f] [IsSeparated f] :
    ∃ e : {s : Y ⟶ X // s ≫ f = 𝟙 Y} ≃
      {U : X.Opens // (∃ x : X, (U : Set X) = connectedComponent x) ∧ IsIso (U.ι ≫ f)},
      ∀ s, ((e s).1 : Set X) = Set.range (fun y : Y => s.1 y) := by
  classical
  let e : {s : Y ⟶ X // s ≫ f = 𝟙 Y} ≃
      {U : X.Opens // (∃ x : X, (U : Set X) = connectedComponent x) ∧ IsIso (U.ι ≫ f)} := {
    toFun := fun s ↦ by
      let d := sectionImageComponentData f s.1 s.2
      exact ⟨d.U, d.component, sectionImageComponent_hom_isIso d⟩
    invFun := fun U ↦ by
      let g : U.1.toScheme ⟶ Y := U.1.ι ≫ f
      let : IsIso g := U.2.2
      refine ⟨inv g ≫ U.1.ι, ?_⟩
      simp [g, Category.assoc]
    left_inv := by
      intro s
      apply Subtype.ext
      let d := sectionImageComponentData f s.1 s.2
      let : IsIso (d.U.ι ≫ f) := sectionImageComponent_hom_isIso d
      show inv (d.U.ι ≫ f) ≫ d.U.ι = s.1
      rw [sectionImageComponent_inv d, d.factor]
    right_inv := by
      intro U
      apply Subtype.ext
      let g : U.1.toScheme ⟶ Y := U.1.ι ≫ f
      let : IsIso g := U.2.2
      have hs : (inv g ≫ U.1.ι) ≫ f = 𝟙 Y := by
        simp [g, Category.assoc]
      let d := sectionImageComponentData f (inv g ≫ U.1.ι) hs
      have hrange : Set.range (fun y : Y ↦ (inv g ≫ U.1.ι) y) = (U.1 : Set X) := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          show U.1.ι (inv g y) ∈ U.1
          exact (inv g y).property
        · intro hx
          let u : U.1.toScheme := ⟨x, hx⟩
          refine ⟨g u, ?_⟩
          show U.1.ι (g.homeomorph.symm (g.homeomorph u)) = x
          rw [g.homeomorph.symm_apply_apply u]
          rfl
      show d.U = U.1
      apply TopologicalSpace.Opens.ext
      exact d.image.trans hrange
    }
  exact ⟨e, fun s ↦ (sectionImageComponentData f s.1 s.2).image⟩

/-- At most one section of a separated unramified morphism passes through a given point of its
source. -/
@[stacks 024U "uniqueness through a point",
  ega "IV 17.4.9" "\"In particular\" clause",
  ega "IV 17.9.4" "injectivity of g↦g(Y)", sga "1 I 5.3" "determined by one point"]
public theorem section_eq_of_common_point {X Y : Scheme.{u}}
    [ConnectedSpace Y] (f : X ⟶ Y) [Unramified f] [IsSeparated f]
    (s t : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (ht : t ≫ f = 𝟙 Y)
    (x : X) (y z : Y) (hsy : s y = x) (htz : t z = x) : s = t := by
  obtain ⟨U, sU, ⟨a, ha⟩, hsU, hfac, hRangeU⟩ := exists_section_image_component f s hs
  obtain ⟨V, tU, ⟨b, hb⟩, -, hfacT, hRangeV⟩ := exists_section_image_component f t ht
  have hxU : x ∈ (U : Set X) := hRangeU.symm ▸ ⟨y, hsy⟩
  have hxV : x ∈ (V : Set X) := hRangeV.symm ▸ ⟨z, htz⟩
  have hxa : x ∈ connectedComponent a := ha ▸ hxU
  have hxb : x ∈ connectedComponent b := hb ▸ hxV
  have hUV : U = V := TopologicalSpace.Opens.ext (by
    show (U : Set X) = (V : Set X)
    rw [ha, hb, connectedComponent_eq hxa, connectedComponent_eq hxb])
  subst V
  have : IsIso (U.ι ≫ f) := isIso_ι_comp_of_factor hs hfac
  have hsEq : sU = tU := by
    apply (cancel_mono (U.ι ≫ f)).1
    rw [← Category.assoc, hfac, hs, ← Category.assoc, hfacT, ht]
  rw [← hfac, ← hfacT, hsEq]

/-- Two morphisms from a connected scheme to a separated unramified scheme over a base are equal
if they induce the same point and the same residue-field map there. -/
@[stacks 024V, sga "1 I 5.4"]
public theorem eq_of_residueFieldMap_eq {S X Y : Scheme.{u}} (π : X ⟶ S)
    [Unramified π] [IsSeparated π] [ConnectedSpace Y]
    (f g : Y ⟶ X) (hover : f ≫ π = g ≫ π) (y : Y) (hy : f y = g y)
    (hκ : f.residueFieldMap y = (X.residueFieldCongr hy).hom ≫ g.residueFieldMap y) :
    f = g := by
  let P := pullback π (f ≫ π)
  let p : P ⟶ Y := pullback.snd π (f ≫ π)
  have : Unramified p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback π (f ≫ π)) inferInstance
  have : IsSeparated p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback π (f ≫ π)) inferInstance
  let sf : Y ⟶ P := pullback.lift f (𝟙 Y) (by simp)
  let sg : Y ⟶ P := pullback.lift g (𝟙 Y) (by simp [hover])
  have hsf : sf ≫ p = 𝟙 Y := by rw [pullback.lift_snd]
  have hsg : sg ≫ p = 𝟙 Y := by rw [pullback.lift_snd]
  have hpoint : sf y = sg y := by
    have hmap : Y.fromSpecResidueField y ≫ f = Y.fromSpecResidueField y ≫ g := by
      calc
        Y.fromSpecResidueField y ≫ f =
            Spec.map (f.residueFieldMap y) ≫ X.fromSpecResidueField (f y) :=
          (f.SpecMap_residueFieldMap_fromSpecResidueField y).symm
        _ = Spec.map ((X.residueFieldCongr hy).hom ≫ g.residueFieldMap y) ≫
            X.fromSpecResidueField (f y) := by rw [hκ]
        _ = Spec.map (g.residueFieldMap y) ≫
            Spec.map (X.residueFieldCongr hy).hom ≫ X.fromSpecResidueField (f y) := by
          simp [Spec.map_comp, Category.assoc]
        _ = Spec.map (g.residueFieldMap y) ≫ X.fromSpecResidueField (g y) := by
          rw [X.residueFieldCongr_fromSpecResidueField hy]
        _ = Y.fromSpecResidueField y ≫ g :=
          g.SpecMap_residueFieldMap_fromSpecResidueField y
    have hu : Y.fromSpecResidueField y ≫ sf = Y.fromSpecResidueField y ≫ sg := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, sf, sg, pullback.lift_fst] using hmap
      · simp only [Category.assoc, sf, sg, pullback.lift_snd]
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using
      congrArg (fun k : Spec (Y.residueField y) ⟶ P ↦ k (default : Spec (Y.residueField y))) hu
  have hs : sf = sg :=
    section_eq_of_common_point p sf sg hsf hsg (sf y) y y rfl (by simp [hpoint])
  simpa only [sf, sg, pullback.lift_fst] using
    congrArg (fun k : Y ⟶ P ↦ k ≫ pullback.fst π (f ≫ π)) hs

end AlgebraicGeometry.Unramified

end
