module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# The cokernel of a map into a module of finite presentation, in the covering-family form

Let `R` be a sheaf of rings on a site and let `φ : ℱ ⟶ 𝒢` be a map of sheaves of `R`-modules with
`ℱ` of finite type and `𝒢` of finite presentation.  Then `Coker(φ)` is of finite presentation.
This is Stacks 0H98, which
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation` proves for Mathlib's
`SheafOfModules.IsFinitePresentation`; what is proved here is the same statement for the
covering-family conditions `SheafOfModules.IsFinitePresentationOnSite` and
`SheafOfModules.IsFiniteTypeOnSite` of Stacks 03DL(7) and 03DL(5).

## Main results

* `Stacks.SheafOfModules.isFinitePresentationOnSite_cokernel`: **the cokernel of a map from a
  sheaf of modules of finite type to one of finite presentation is of finite presentation**, both
  conditions read in the covering-family form.

## Implementation notes

The proof is the one of `Stacks.SheafOfModules.LocalCokernel.isFinitePresentation_cokernel`, with
the two renderings of each condition exchanged at the ends.  Entering, a module of finite
presentation on the site is of finite presentation in Mathlib's sense by
`SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'` and a module of finite type
on the site is of finite type in Mathlib's sense by
`Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`; leaving, a finite
`SheafOfModules.Presentation` is a finite global presentation by
`SheafOfModules.HasFiniteGlobalPresentation.of_presentation'`.  That is the same pair of
exchanges that
`Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite` makes.

Between them the argument is unchanged: the objects carrying a finite presentation of `Coker(φ)`
cover every object of the site, because a presentation of `𝒢` and a finite generating family of
`ℱ` are available over the members of a twofold refinement, and over such an object
`Stacks.SheafOfModules.LocalCokernel.exists_cover_finitePresentation_cokernel` presents
`Coker(φ)` on a covering sieve.

The covering family that `SheafOfModules.IsFinitePresentationOnSite` asks for is read off the
sieve of objects of that family exactly as in
`SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite`: its index type is the type of
arrows of the sieve, which lies in the universe the condition demands.

## References

* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Stacks 0H98 for the covering-family conditions of Stacks 03DL.**  The cokernel of a map
`φ : ℱ ⟶ 𝒢` of sheaves of modules on a site whose source is of finite type and whose target is of
finite presentation is of finite presentation.

The objects over which `Coker(φ)` carries a finite presentation cover every object of the site:
refine an object first by a covering carrying presentations of `𝒢` and then by one carrying
finite generating families of `ℱ`, and over a member of the refinement
`Stacks.SheafOfModules.LocalCokernel.exists_cover_finitePresentation_cokernel` presents
`Coker(φ)` on a covering sieve. -/
theorem isFinitePresentationOnSite_cokernel
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {F G : _root_.SheafOfModules.{w} R} (φ : F ⟶ G)
    (hF : F.IsFiniteTypeOnSite) (hG : G.IsFinitePresentationOnSite) :
    (cokernel φ).IsFinitePresentationOnSite := by
  classical
  have hGfp : G.IsFinitePresentation :=
    _root_.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' G hG
  have hFft : F.IsFiniteType := isFiniteType_of_isFiniteTypeOnSite F hF
  obtain ⟨qG, hqG⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData G
  let _ : qG.IsFinitePresentation := hqG
  obtain ⟨qF, hqF⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let _ : qF.IsFiniteType := hqF
  set Z : Set C := {Z : C | ∃ P : ((cokernel φ).over Z).Presentation, P.IsFinite} with hZdef
  have hlocal (U : C) (P : (G.over U).Presentation) (hP : P.IsFinite) :
      Sieve.ofObjects (Subtype.val : Z → C) U ∈ J U := by
    let _ : P.IsFinite := hP
    refine J.transitive (qF.coversTop U) _ ?_
    intro V f hf
    obtain ⟨j, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff _ f).mp hf
    obtain ⟨P', hP'⟩ := LocalCokernel.exists_finitePresentation_overMap G f P
    let _ : P'.IsFinite := hP'
    let _ := hqF.isFiniteType j
    obtain ⟨σ, hσ⟩ := LocalCokernel.exists_finiteGeneratingSections_overMap F g (qF.generators j)
    let _ : σ.IsFiniteType := hσ
    obtain ⟨S, hS, hfin⟩ := LocalCokernel.exists_cover_finitePresentation_cokernel φ V P' σ
    refine J.superset_covering ?_ hS
    intro W a ha
    exact ⟨⟨W, hfin a ha⟩, ⟨𝟙 W⟩⟩
  have hY : J.CoversTop (Subtype.val : Z → C) := by
    intro U
    refine J.transitive (qG.coversTop U) _ ?_
    intro V f hf
    obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff _ f).mp hf
    let _ := hqG.isFinite_presentation i
    obtain ⟨P, hP⟩ := LocalCokernel.exists_finitePresentation_overMap G g (qG.presentation i)
    refine J.superset_covering ?_ (hlocal V P hP)
    intro W a ha
    obtain ⟨b, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff _ a).mp ha
    exact ⟨b, ⟨c⟩⟩
  refine ⟨fun W => ?_⟩
  refine ⟨{g : Over W // (Sieve.ofObjects (Subtype.val : Z → C) W) g.hom},
    fun a => a.1.left, fun a => a.1.hom, ?_, ?_⟩
  · have hEq : Sieve.ofArrows
        (fun a : {g : Over W // (Sieve.ofObjects (Subtype.val : Z → C) W) g.hom} => a.1.left)
        (fun a => a.1.hom) = Sieve.ofObjects (Subtype.val : Z → C) W := by
      refine le_antisymm (fun X g hg => ?_) (fun X g hg => ?_)
      · rw [Sieve.mem_ofArrows_iff] at hg
        obtain ⟨a, b, rfl⟩ := hg
        exact (Sieve.ofObjects (Subtype.val : Z → C) W).downward_closed a.2 b
      · rw [Sieve.mem_ofArrows_iff]
        exact ⟨⟨Over.mk g, hg⟩, 𝟙 X, by simp⟩
    rw [hEq]
    exact hY W
  · intro a
    obtain ⟨b, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff _ a.1.hom).mp a.2
    let _ : b.2.choose.IsFinite := b.2.choose_spec
    obtain ⟨Q, hQ⟩ :=
      LocalCokernel.exists_finitePresentation_overMap (cokernel φ) c b.2.choose
    exact _root_.SheafOfModules.HasFiniteGlobalPresentation.of_presentation' Q hQ

end Stacks.SheafOfModules

end
