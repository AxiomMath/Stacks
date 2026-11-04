module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeAffine

/-!
# Descent of finite locally free modules through a limit of schemes

Let `S = lim Sᵢ` be the limit of a cofiltered system of quasi-compact quasi-separated schemes
with affine transition morphisms.  This file proves [Stacks Project, Tag 0B8W] (1): every finite
locally free `𝒪_S`-module is the pullback of a finite locally free `𝒪_{Sᵢ}`-module for some
`i`.

`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso_of_eventually`
already reduces the tag to the conjunction of Algebra, Lemmas 02JO and 00NX in the following
form: a sheaf of modules of finite presentation at a stage whose pullback to the limit is finite
locally free becomes finite locally free along some transition morphism.  That statement is
proved for a diagram of affine schemes in
`StacksDraft.AlgebraicGeometry.F3b.ModuleLimits.FiniteLocallyFreeAffine`; this file reduces the
general case to it and discharges the hypothesis, so the tag becomes unconditional.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_of_isLimit_qcqs`
  and its universe-unrestricted form `..._qcqs'`: Tags 02JO and 00NX in the sheaf-level form the
  proof of Tag 0B8W (1) uses them, for a cofiltered diagram of schemes with affine transition
  morphisms.  Only the stage carrying the module is required to be quasi-compact, and no stage
  is required to be quasi-separated, so these are stronger than what the tag needs.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso`:
  **Tag 0B8W (1)**, unconditionally.

## Implementation notes

The reduction is the one already used for Tag 01ZR (3) in
`StacksDraft.AlgebraicGeometry.F3b.ModuleLimits.EventualMapEq`, and the bookkeeping is the same.
Choose a finite affine open covering `V a` of the stage `D.obj i`; such a covering exists
because the stage is quasi-compact, and finiteness is what makes the stages produced for the
different members of the covering refinable to a single one.  For each `a` the diagram of
preimages `AlgebraicGeometry.EventualLimit.preimageDiagram D i (V a)`, indexed by
`CategoryTheory.Over i`, is a cofiltered diagram of *affine* schemes whose limit is the preimage
of `V a` in the limit (`AlgebraicGeometry.EventualLimit.isLimitPreimageCone`).  The restriction
of a pullback to an open is the pullback along the restricted morphism, by
`Stacks.Modules.restrictPullbackIso` in its `AlgebraicGeometry.Scheme.Hom.resLE` form, which is
what makes its restricted morphism literally the transition morphism of `preimageDiagram`; so
the hypothesis restricts to the member of the covering and the affine case applies there.

There is no glueing: finite local freeness is a local condition, so the covering is used only
through `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top`, and the passage
between that pointwise predicate and the class `AlgebraicGeometry.SheafOfModules.
IsFiniteLocallyFree` in which the tag is stated is
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff`.  As in `EventualMapEq`, the base
object of `Over i` is `Over.mk (𝟙 i)`, whose value under `preimageDiagram D i V` is
`D.map (𝟙 i) ⁻¹ᵁ V` rather than `V` itself; no isomorphism is transported to repair this, the
argument is run with that open throughout.

A single further ingredient is needed beyond the template: finite local freeness must be carried
from the index produced by the affine case to any index over it, which is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme` together with
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

section General

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- One member of the affine covering: the finite local freeness of the pullback of `Eᵢ` to the
limit restricts to the preimage of an affine open `V` of the stage, where the affine case
applies and produces an index over `i` at which the restriction of the pullback of `Eᵢ` to that
preimage is already finite locally free — and the same then holds at every index over it,
because finite local freeness is stable under pullback. -/
private theorem exists_over_isFiniteLocallyFree_restrict (hc : IsLimit c) (i : I)
    {V : (D.obj i).Opens} (hV : IsAffineOpen V)
    (Eᵢ : (D.obj i).Modules) [Eᵢ.IsFinitePresentation]
    (hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (c.π.app i)).obj Eᵢ)) :
    ∃ j : Over i, ∀ (k : Over i), (k ⟶ j) →
      SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i V).map
          (Over.homMk k.hom (by simp) : k ⟶ Over.mk (𝟙 i)))).obj
          ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj Eᵢ)) := by
  have haff : ∀ k : Over i, IsAffine ((EventualLimit.preimageDiagram D i V).obj k) :=
    EventualLimit.isAffine_preimageDiagram_obj D i hV
  have hdl : IsLimit (EventualLimit.preimageCone D c i V) :=
    EventualLimit.isLimitPreimageCone D c hc i V
  have hEfp : ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj
      Eᵢ).IsFinitePresentation := isFinitePresentation_restrict _ Eᵢ
  have hEfp2 : SheafOfModules.IsFinitePresentation
      (R := ((EventualLimit.preimageDiagram D i V).obj (Over.mk (𝟙 i))).ringCatSheaf)
      ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj Eᵢ) := hEfp
  have hle : c.π.app i ⁻¹ᵁ V ≤ c.π.app i ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V) :=
    Scheme.Hom.preimage_mono _ (by simp)
  have h0 : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.restrictFunctor (c.π.app i ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.pullback (c.π.app i)).obj Eᵢ)) :=
    (Scheme.Modules.isFiniteLocallyFree_iff _).mp
      (((Scheme.Modules.isFiniteLocallyFree_iff _).mpr hflf).restrict _)
  have hres : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback
        ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).obj
        ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj Eᵢ)) :=
    SheafOfModules.IsFiniteLocallyFree.of_iso (h := h0)
      ((Stacks.Modules.restrictPullbackIso (c.π.app i) hle).app Eᵢ)
  obtain ⟨j, e, hj⟩ := exists_isFiniteLocallyFree_pullback_of_isLimit
    (EventualLimit.preimageDiagram D i V) (EventualLimit.preimageCone D c i V) hdl
    (Over.mk (𝟙 i)) _ hres
  refine ⟨j, fun k m => ?_⟩
  have hcomp : (m ≫ e) = (Over.homMk k.hom (by simp) : k ⟶ Over.mk (𝟙 i)) := by
    apply Over.OverMorphism.ext
    simpa using Over.w (m ≫ e)
  rw [← hcomp, Functor.map_comp]
  have h1 := SheafOfModules.IsFiniteLocallyFree.pullback_scheme
    ((EventualLimit.preimageDiagram D i V).map m) _ hj
  exact SheafOfModules.IsFiniteLocallyFree.of_iso (h := h1)
    ((Scheme.Modules.pullbackComp ((EventualLimit.preimageDiagram D i V).map m)
      ((EventualLimit.preimageDiagram D i V).map e)).app _)

/-- **Tags 02JO and 00NX for sheaves of modules on a cofiltered limit of schemes.**  Let `c` be
a limit cone on a cofiltered diagram `D` of schemes with affine transition morphisms, let `Eᵢ`
be a sheaf of modules of finite presentation on a quasi-compact stage, and suppose its pullback
to the limit is finite locally free.  Then its pullback along some transition morphism is
already finite locally free.

Choose a finite affine open covering of the stage.  Over each member the diagram of preimages is
a cofiltered diagram of affine schemes with limit the corresponding open of the limit, so the
affine case applies there and produces an index; a common refinement of the finitely many
indices works simultaneously for all members of the covering, and finite local freeness is
local. -/
theorem exists_isFiniteLocallyFree_pullback_of_isLimit_qcqs (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)] (Eᵢ : (D.obj i).Modules) [Eᵢ.IsFinitePresentation]
    (hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (c.π.app i)).obj Eᵢ)) :
    ∃ (j : I) (e : j ⟶ i), SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (D.map e)).obj Eᵢ) := by
  classical
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  let V : 𝒰.I₀ → (D.obj i).Opens := fun a => (𝒰.f a).opensRange
  have hVa : ∀ a, IsAffineOpen (V a) := fun a => isAffineOpen_opensRange _
  have hcov : ∀ x : D.obj i, ∃ a, x ∈ V a := fun x =>
    𝒰.isOpenCover_opensRange.exists_mem x
  choose jj hjj using fun a =>
    exists_over_isFiniteLocallyFree_restrict D c hc i (hVa a) Eᵢ hflf
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.image jj Finset.univ)
  have hkm : ∀ a, k ⟶ jj a := fun a =>
    (hk (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some
  refine ⟨k.left, k.hom, ?_⟩
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mp
    (Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top
      (fun a => D.map k.hom ⁻¹ᵁ V a) ?_ fun a => ?_)
  · refine eq_top_iff.mpr fun x _ => ?_
    simp only [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨a, ha⟩ := hcov ((D.map k.hom).base x)
    exact ⟨a, ha⟩
  · refine (Scheme.Modules.isFiniteLocallyFree_iff _).mpr ?_
    refine SheafOfModules.IsFiniteLocallyFree.of_iso (h := hjj a k (hkm a))
      ((Stacks.Modules.restrictPullbackIso (D.map k.hom)
        (show D.map k.hom ⁻¹ᵁ V a ≤ D.map k.hom ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V a) from
          Scheme.Hom.preimage_mono _ (by simp))).app Eᵢ).symm

end General


section IndexHomUniverse

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

include c in
/-- `exists_isFiniteLocallyFree_pullback_of_isLimit_qcqs` with the index morphism universe
unrestricted, obtained by replacing the index category with
`CategoryTheory.Functor.FullImage D`. -/
theorem exists_isFiniteLocallyFree_pullback_of_isLimit_qcqs' (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)] (Eᵢ : (D.obj i).Modules) [Eᵢ.IsFinitePresentation]
    (hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (c.π.app i)).obj Eᵢ)) :
    ∃ (j : I) (e : j ⟶ i), SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (D.map e)).obj Eᵢ) := by
  have hcs : CompactSpace ((ι D).obj (⟨i⟩ : FullImage D)) := ‹CompactSpace (D.obj i)›
  have hfp : SheafOfModules.IsFinitePresentation
      (R := ((ι D).obj (⟨i⟩ : FullImage D)).ringCatSheaf) Eᵢ := ‹_›
  obtain ⟨j, gm, hj⟩ := exists_isFiniteLocallyFree_pullback_of_isLimit_qcqs (ι D) (cone D c)
    (isLimitCone D hc) ⟨i⟩ Eᵢ hflf
  refine ⟨j.as, hom D gm, ?_⟩
  rw [map_hom D gm]
  exact hj

include c in
/-- **Stacks Project, Tag 0B8W (1).**  Let `S = lim Sᵢ` be the limit of a cofiltered system of
quasi-compact quasi-separated schemes with affine transition morphisms.  Then every finite
locally free `𝒪_S`-module is the pullback of a finite locally free `𝒪_{Sᵢ}`-module for some
`i`.

This is `exists_isFiniteLocallyFree_pullback_iso_of_eventually` with its remaining
hypothesis — the conjunction of Algebra, Lemmas 02JO and 00NX in the form the source's proof
uses them — supplied by `exists_isFiniteLocallyFree_pullback_of_isLimit_qcqs'`. -/
@[stacks 0B8W "(1)"]
theorem exists_isFiniteLocallyFree_pullback_iso (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (E : c.pt.Modules) (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    ∃ (i : I) (Eᵢ : (D.obj i).Modules),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eᵢ ∧
        Nonempty (E ≅ (Scheme.Modules.pullback (c.π.app i)).obj Eᵢ) :=
  exists_isFiniteLocallyFree_pullback_iso_of_eventually D c hc
    (fun i Eᵢ hfp hpb => by
      have := hfp
      exact exists_isFiniteLocallyFree_pullback_of_isLimit_qcqs' D c hc i Eᵢ hpb) E hE

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
include c in
/-- **A finite locally free descent of a module on the limit can be re-read at any earlier
stage.**  This is `Stacks.AlgebraicGeometry.ModuleLimits.isoPullbackMapOfIsoPullback` together
with the stability of finite local freeness under pullback, in the existential form the descent
statements of [Stacks, Tag 0B8W] (1) are phrased in.

Neither cofilteredness of the index category nor affineness of the transition morphisms is
needed: the cone and the transition morphism `e` are the only inputs. -/
theorem exists_isFiniteLocallyFree_pullback_iso_of_hom {i j : I} (e : j ⟶ i)
    (Eᵢ : (D.obj i).Modules)
    (hEᵢ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eᵢ) {E : c.pt.Modules}
    (h : E ≅ (Scheme.Modules.pullback (c.π.app i)).obj Eᵢ) :
    ∃ Eⱼ : (D.obj j).Modules, SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eⱼ ∧
      Nonempty (E ≅ (Scheme.Modules.pullback (c.π.app j)).obj Eⱼ) :=
  ⟨(Scheme.Modules.pullback (D.map e)).obj Eᵢ,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (D.map e) Eᵢ hEᵢ,
    ⟨isoPullbackMapOfIsoPullback D c e h⟩⟩

include c in
/-- **Stacks Project, Tag 0B8W (1), with the stage forced below a prescribed one.**  Every finite
locally free module on the limit is the pullback of a finite locally free module from some stage
admitting a morphism to any stage named in advance.

This is the form in which the descent statement is applied to *several* systems indexed by one
and the same category — one per corner of a square, say.  The tag itself produces an unrelated
stage for each system, and nothing merges them; chaining this statement, each application taking
the previous application's stage as `i₀`, lands every one of finitely many modules on a single
common stage.  The merge is cofilteredness of the index category, through
`CategoryTheory.IsCofiltered.min`, and the transport of the already-descended modules to the
smaller stage is `exists_isFiniteLocallyFree_pullback_iso_of_hom`. -/
theorem exists_isFiniteLocallyFree_pullback_iso_under (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (E : c.pt.Modules) (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) (i₀ : I) :
    ∃ (i : I) (_ : i ⟶ i₀) (Eᵢ : (D.obj i).Modules),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eᵢ ∧
        Nonempty (E ≅ (Scheme.Modules.pullback (c.π.app i)).obj Eᵢ) := by
  obtain ⟨i, Eᵢ, hEᵢ, ⟨eE⟩⟩ := exists_isFiniteLocallyFree_pullback_iso D c hc E hE
  obtain ⟨Eⱼ, hEⱼ, hiso⟩ := exists_isFiniteLocallyFree_pullback_iso_of_hom D c
    (IsCofiltered.minToLeft i i₀) Eᵢ hEᵢ eE
  exact ⟨IsCofiltered.min i i₀, IsCofiltered.minToRight i i₀, Eⱼ, hEⱼ, hiso⟩

end IndexHomUniverse

end Stacks.AlgebraicGeometry.ModuleLimits

end
