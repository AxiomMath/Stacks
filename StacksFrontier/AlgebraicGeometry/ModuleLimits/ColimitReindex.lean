module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendResidue
public import Mathlib.CategoryTheory.Presentable.Directed

/-!
# Reindexing a filtered colimit presentation by a directed partially ordered set

[Stacks Project, Tag 01PK] says that a quasi-coherent module on a quasi-compact
quasi-separated scheme is a *directed* colimit of finitely presented modules; it follows from
[Stacks Project, Tag 01PJ], the same statement for a *filtered* index category, by reindexing a
filtered colimit by a directed partially ordered set (`CategoryTheory.IsFiltered.exists_directed`,
[Stacks Project, Tag 0032]).

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.QcohFilteredColimitFinitePresentation`:
  [Stacks Project, Tag 01PJ] as a proposition: every quasi-coherent module on a quasi-compact
  quasi-separated scheme is the colimit of a filtered diagram of finitely presented modules,
  indexed by a small category in the universe of the scheme.

## Main results

* `ModuleLimits.exists_directed_colimit_of_isFinitePresentation_of_filtered`:
  [Stacks Project, Tag 01PK] from [Stacks Project, Tag 01PJ].
* `ModuleLimits.exists_isFinitePresentation_pullback_iso_of_filteredColim_and_upToIso_map`:
  [Stacks Project, Tag 01ZR] (1) for a cofiltered system of quasi-compact quasi-separated
  schemes with affine transition morphisms, from Tag 01PJ and descent of morphisms up to an
  arbitrary identification.

## Implementation notes

The index category of the filtered form is `J : Type u` with a `SmallCategory J` instance, so
that `IsFiltered.exists_directed` produces a directed partial order again in `Type u`, the
universe the directed form is stated at. The reindexed cocone is the whiskering of the given one
along the final functor, and `Functor.Final.isColimitWhiskerEquiv` transports the colimiting
property back across it.

## References

* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- [Stacks Project, Tag 01PJ] as a proposition: every quasi-coherent module on a quasi-compact
quasi-separated scheme is the colimit of a filtered diagram of finitely presented modules. -/
def QcohFilteredColimitFinitePresentation : Prop :=
  ∀ (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] (N : Z.Modules),
    N.IsQuasicoherent →
    ∃ (J : Type u) (inst : SmallCategory J),
      let _ := inst
      ∃ (_ : IsFiltered J) (E : J ⥤ Z.Modules) (φ : E ⟶ (Functor.const J).obj N),
        (∀ j, (E.obj j).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk N φ))

/-- [Stacks Project, Tag 01PK] from [Stacks Project, Tag 01PJ]: if every quasi-coherent module
on a quasi-compact quasi-separated scheme is a filtered colimit of finitely presented modules,
then it is a colimit of finitely presented modules indexed by a nonempty directed partially
ordered set. -/
theorem exists_directed_colimit_of_isFinitePresentation_of_filtered
    (hfilt : QcohFilteredColimitFinitePresentation.{u})
    (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] (N : Z.Modules)
    (hN : N.IsQuasicoherent) :
    ∃ (J : Type u) (_ : PartialOrder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (E : J ⥤ Z.Modules) (φ : E ⟶ (Functor.const J).obj N),
      (∀ j, (E.obj j).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk N φ)) := by
  obtain ⟨J, _, _, E, φ, hfp, ⟨hcolim⟩⟩ := hfilt Z N hN
  obtain ⟨A, _, hdir, hne, e, hfinal⟩ := CategoryTheory.IsFiltered.exists_directed J
  have := hfinal
  refine ⟨A, inferInstance, hne, hdir, e ⋙ E, Functor.whiskerLeft e φ, fun a => hfp _, ?_⟩
  exact ⟨(Functor.Final.isColimitWhiskerEquiv e _).symm hcolim⟩

variable {I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- [Stacks Project, Tag 01ZR] (1) from [Stacks Project, Tag 01PJ] and descent of morphisms up
to an arbitrary identification (`hmap`): for a cofiltered limit `c` of quasi-compact
quasi-separated schemes with affine transition morphisms, every finitely presented module on the
limit is the pullback of a finitely presented module on some `D.obj i`. -/
theorem exists_isFinitePresentation_pullback_iso_of_filteredColim_and_upToIso_map
    [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hfilt : QcohFilteredColimitFinitePresentation.{u})
    (hmap : ∀ (i : I) (F G : (D.obj i).Modules),
      F.IsFinitePresentation → G.IsFinitePresentation →
      ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj G,
      ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G)
        (iF : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj F) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj F)
        (iG : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj G) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj G),
        (Scheme.Modules.pullback (c.π.app j)).map φj ≫ iG.hom = iF.hom ≫ φ)
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) :=
  exists_isFinitePresentation_pullback_iso_of_colim_and_upToIso_map D c hc
    (fun Z _ _ N hN => exists_directed_colimit_of_isFinitePresentation_of_filtered hfilt Z N hN)
    hmap F

end Stacks.AlgebraicGeometry.ModuleLimits

end
