module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Models over arbitrary stages: transporting them between stages

Let `D : I ⥤ Scheme` be a diagram of schemes with a cone `c`, where the universes of the index
category `I` are independent of the scheme universe. This file defines the predicate that a
morphism to `c.pt` is the base change along a cone leg of a quasi-compact, quasi-separated scheme
locally of finite presentation over a stage, and records the facts about quasi-compactness and
quasi-separatedness that are preserved when such a model is moved along an affine morphism.

## Main definitions

* `AlgebraicGeometry.LimitDescent.HasQcqsModel'`: a morphism to the limit is the base change along
  a cone leg of a quasi-compact, quasi-separated scheme locally of finite presentation over a
  stage.  This is the conclusion of Stacks Tag 0EY1, at an index category whose universes are
  independent of the scheme universe.

## Main results

* `AlgebraicGeometry.LimitDescent.compactSpace_quasiSeparatedSpace_of_isPullback`: a base change
  of a quasi-compact, quasi-separated scheme along an affine morphism is again quasi-compact and
  quasi-separated.
* `AlgebraicGeometry.LimitDescent.HasQcqsModel'.of_iso`: having such a model only depends on the
  isomorphism class of the morphism over the limit.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

universe v uI u

open CategoryTheory CategoryTheory.Limits CategoryTheory.InitiallySmall TopologicalSpace

namespace AlgebraicGeometry.LimitDescent

/-! ### Quasi-compactness and quasi-separatedness along an affine base change -/

/-- A base change of a quasi-compact, quasi-separated scheme along an affine morphism is
quasi-compact and quasi-separated. -/
@[sga "3 VIB 10.0" "more general", sga "4 VIII 5.1" "special case"]
public lemma compactSpace_quasiSeparatedSpace_of_isPullback {Y' Y S' S : Scheme.{u}} {r : Y' ⟶ Y}
    {p' : Y' ⟶ S'} {p : Y ⟶ S} {t : S' ⟶ S} (h : IsPullback r p' p t) (ht : IsAffineHom t)
    (h₁ : CompactSpace Y) (h₂ : QuasiSeparatedSpace Y) :
    CompactSpace Y' ∧ QuasiSeparatedSpace Y' := by
  have := ht
  have := h₁
  have := h₂
  have : IsAffineHom r := MorphismProperty.of_isPullback h.flip ht
  exact ⟨QuasiCompact.compactSpace_of_compactSpace r, quasiSeparatedSpace_of_quasiSeparated r⟩

/-- A morphism locally of finite presentation restricted to a quasi-compact open of its source is
again locally of finite presentation, and that open is quasi-compact and quasi-separated. -/
public lemma compactSpace_quasiSeparatedSpace_locallyOfFinitePresentation_ι_comp {Z T : Scheme.{u}}
    (q : Z ⟶ T) (hq : LocallyOfFinitePresentation q) [CompactSpace Z] [QuasiSeparatedSpace Z]
    (V : Z.Opens) (hV : IsCompact V.1) :
    CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧
      LocallyOfFinitePresentation (V.ι ≫ q) := by
  have := hq
  exact ⟨isCompact_iff_compactSpace.1 hV,
    QuasiSeparatedSpace.of_isOpenEmbedding V.ι.isOpenEmbedding,
    MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ inferInstance hq⟩

variable {I : Type uI} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-! ### Having a quasi-compact quasi-separated model over a stage -/

/-- `f : X ⟶ S` **has a quasi-compact quasi-separated model over a stage** if it is the base
change along one of the cone legs of a morphism, locally of finite presentation, whose source is
quasi-compact and quasi-separated.

This is the conclusion of Stacks Tag 0EY1; the index universes are independent of the scheme
universe. -/
public def HasQcqsModel' {X : Scheme.{u}} (f : X ⟶ c.pt) : Prop :=
  ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (g : X ⟶ Y),
    CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ LocallyOfFinitePresentation p ∧
      IsPullback g f p (c.π.app i)

/-- Having a quasi-compact quasi-separated model over a stage only depends on the isomorphism
class of `f` in the category of schemes over the limit. -/
public lemma HasQcqsModel'.of_iso {X X' : Scheme.{u}} {f : X ⟶ c.pt} {f' : X' ⟶ c.pt} (e : X' ≅ X)
    (he : e.hom ≫ f = f') (hm : HasQcqsModel' D c f) : HasQcqsModel' D c f' := by
  obtain ⟨i, Y, p, g, h₁, h₂, h₃, hpb⟩ := hm
  exact ⟨i, Y, p, e.hom ≫ g, h₁, h₂, h₃,
    hpb.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) (Category.comp_id _).symm
      (by rw [Iso.refl_hom, Category.comp_id]; exact he) (by simp) (by simp)⟩

end AlgebraicGeometry.LimitDescent
