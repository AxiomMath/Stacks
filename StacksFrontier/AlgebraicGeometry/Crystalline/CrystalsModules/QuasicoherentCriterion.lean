module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal

/-!
# Quasi-coherence on the big crystalline site is local on the ambient scheme

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation.  [Stacks, Tag 07IT] characterises quasi-coherence of `F` by two conditions read on the
restrictions `F_T` to the ambient schemes: that every `F_T` is a quasi-coherent `𝒪_T`-module, and
that `F` is a crystal.  Both halves of the source's proof begin with the same reduction, which
the source states as "both claims are local in the Zariski sense" in one direction and as "one
reduces to the case of affine `T`" in the other: quasi-coherence of `F` on the big crystalline
site is a Zariski-local condition on the ambient scheme of each object, and may therefore be
tested on objects whose ambient scheme is affine.

That reduction is what this file proves.  In one direction it is cocontinuity of the restriction
functor `Opens T ⥤ CRIS(X/S)`: a crystalline covering of `(U, T, δ)` is refined by the
restrictions of `(U, T, δ)` to an open cover of `T`, and a global presentation travels along the
refining morphism.  In the other direction it is that the restrictions of `(U, T, δ)` to an open
cover of `T` form a crystalline covering family, so a global presentation on each member makes
`F` quasi-coherent.

## The correction

[Stacks, Tag 07IT] is false as literally stated against this library, because the library's
`Crystalline.GlobalCrystallineSituation.IsCrystal` reads the crystal condition of
[Stacks, Tag 07IS] with the comparison maps of *presheaves* of modules, whereas the source reads
it with the comparison maps of sheaves of modules.  The two differ because the pullback of
sheaves of modules sheafifies the pullback of presheaves of modules: over an ambient scheme `T_A`
which is a countable disjoint union of copies of `Spec 𝔽_p`, the coproduct of countably many
copies of `𝒪_{X/S}` is quasi-coherent while its presheaf-level comparison maps over `T_A` are not
isomorphisms, a section of the coproduct being free to use a different summand on each component.
The crystal condition is therefore to be read at sheaf level, which is
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`, and the corrected statement of the tag is

> `M.IsQuasicoherentOnSite ↔ (IsLocallyQuasiCoherent M ∧ IsSheafCrystal M)`.

Nothing below depends on that choice: the reduction proved here is a statement about the
left-hand side alone, and it is stated for the corrected reading because that is the only reading
under which the tag is true.

## Main results

* `Crystalline.GlobalCrystallineSituation.exists_isAffine_hasGlobalPresentation_restrictOpen` —
  a quasi-coherent sheaf of `𝒪_{X/S}`-modules has, around every point of the ambient scheme of
  every object, an open neighbourhood with affine open subscheme on whose restriction the module
  has a global presentation.
* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_forall_exists_restrictOpen` —
  conversely, global presentations on the restrictions to a Zariski-local family of opens of each
  ambient scheme make the module quasi-coherent.
* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_forall_isAffine` — the same
  converse in the shape the second direction of the tag uses it: it suffices to present the module
  globally on the objects whose ambient scheme is affine.
* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_iff_locally_restrictOpen` —
  **the reduction step of [Stacks, Tag 07IT]**: quasi-coherence on the big crystalline site is
  Zariski-local on the ambient scheme, and may be tested on the restrictions to affine opens.

## Implementation notes

The forward direction pulls the covering sieve back along the structure morphism
`A.restrictOpen ⊤ ⟶ A`, which is an isomorphism, so that cocontinuity of
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctor` can be applied at the
object `⊤` of the opens of the ambient scheme; membership in `Opens.grothendieckTopology` then
reads off, for each point, an open neighbourhood whose restriction factors through a member of
the covering family, and
`Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap` carries the
global presentation along that factorisation.  The refinement to an affine open is
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset` followed by the same transport along the
morphism between the restrictions to two nested opens.

The backward direction indexes the covering family by the opens carrying a global presentation,
raised to `Type (u + 1)` since the quasi-coherence predicate asks for its index type in the
universe `max (u + 1) u` of the objects and morphisms of the site.  The family of restrictions is
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenCover`, a Zariski covering family
by `Crystalline.GlobalCrystallineSituation.Thickening.isZariskiCovering_restrictOpenCover`, and
the sieve it generates covers by
`Crystalline.GlobalCrystallineSituation.zariskiCovering_mem_topology`; that sieve is the sieve
generated by a family of arrows on the nose, both notions being abbreviations for the sieve
generated by a presieve of arrows.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **A quasi-coherent sheaf of `𝒪_{X/S}`-modules has a global presentation on the restriction of
every object to a small enough open of its ambient scheme.**  Quasi-coherence gives a crystalline
covering family of the object; cocontinuity of the restrictions to the opens of the ambient
scheme refines it by a family of such restrictions, and a global presentation travels along the
refining morphism. -/
theorem exists_hasGlobalPresentation_restrictOpen
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (hM : M.IsQuasicoherentOnSite)
    (A : Thickening S) (x : A.thickening.target.scheme) :
    ∃ V : A.thickening.target.scheme.Opens,
      x ∈ V ∧ (M.over (A.restrictOpen V)).HasGlobalPresentation := by
  obtain ⟨I, Y, f, hcov, hY⟩ := hM.locally_hasGlobalPresentation A
  have hpb : (Sieve.ofArrows Y f).pullback (A.restrictOpenHom ⊤) ∈
      topology S (A.restrictOpenFunctor.obj ⊤) :=
    (topology S).pullback_stable _ hcov
  obtain ⟨V, g, hg, hxV⟩ :=
    A.restrictOpenFunctor.cover_lift (Opens.grothendieckTopology ↥A.thickening.target.scheme)
      (topology S) hpb x (Opens.mem_top x)
  have hfac : A.restrictOpenFunctor.map g ≫ A.restrictOpenHom ⊤ = A.restrictOpenHom V :=
    Thickening.restrictOpenLE_restrictOpenHom A g.le
  have hV : (Sieve.ofArrows Y f).arrows (A.restrictOpenHom V) := by
    rw [← hfac]; exact hg
  obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff Y f _).1 hV
  exact ⟨V, hxV,
    Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap M a (hY i)⟩

/-- **A quasi-coherent sheaf of `𝒪_{X/S}`-modules has a global presentation on the restriction of
every object to a small enough *affine* open of its ambient scheme.**  This is the reduction to
the case of affine `T` used in the proof of [Stacks, Tag 07IT]: the ambient scheme of the
restriction of `(U, T, δ)` to an open `V` is the open subscheme `V`, so the conclusion says that
the restrictions to objects with affine ambient scheme carry global presentations and cover. -/
theorem exists_isAffine_hasGlobalPresentation_restrictOpen
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (hM : M.IsQuasicoherentOnSite)
    (A : Thickening S) (x : A.thickening.target.scheme) :
    ∃ V : A.thickening.target.scheme.Opens,
      IsAffine (A.restrictOpen V).thickening.target.scheme ∧ x ∈ V ∧
        (M.over (A.restrictOpen V)).HasGlobalPresentation := by
  obtain ⟨V, hxV, hV⟩ := exists_hasGlobalPresentation_restrictOpen M hM A x
  obtain ⟨W, hWaff, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  refine ⟨W, hWaff, hxW, ?_⟩
  exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap M
    (A.restrictOpenLE hWV) hV

/-- **Global presentations on the restrictions to a Zariski-local family of opens of each ambient
scheme make a sheaf of `𝒪_{X/S}`-modules quasi-coherent.**  The restrictions of an object to a
family of opens covering its ambient scheme form a Zariski covering family of the big crystalline
site, so the opens carrying a global presentation generate a covering sieve. -/
theorem isQuasicoherentOnSite_of_forall_exists_restrictOpen
    (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (h : ∀ (A : Thickening S) (x : A.thickening.target.scheme),
      ∃ V : A.thickening.target.scheme.Opens,
        x ∈ V ∧ (M.over (A.restrictOpen V)).HasGlobalPresentation) :
    M.IsQuasicoherentOnSite := by
  choose V hxV hV using h
  refine ⟨fun A ↦ ?_⟩
  refine ⟨ULift.{u + 1} ↥A.thickening.target.scheme,
    fun i : ULift.{u + 1} ↥A.thickening.target.scheme ↦ A.restrictOpen (V A i.down),
    fun i ↦ A.restrictOpenHom (V A i.down), ?_, fun i ↦ hV A i.down⟩
  exact zariskiCovering_mem_topology S
    (A.restrictOpenCover (ι := ULift.{u + 1} ↥A.thickening.target.scheme) fun i ↦ V A i.down)
    (Thickening.isZariskiCovering_restrictOpenCover A _ fun y ↦ ⟨ULift.up y, hxV A y⟩)

/-- **It suffices to present a sheaf of `𝒪_{X/S}`-modules globally on the objects whose ambient
scheme is affine.**  This is the shape in which the reduction is used by the direction "locally
quasi-coherent and a sheaf crystal implies quasi-coherent" of [Stacks, Tag 07IT]: every object is
covered by its restrictions to affine opens of its ambient scheme, and the ambient scheme of such
a restriction is the affine open subscheme. -/
theorem isQuasicoherentOnSite_of_forall_isAffine
    (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (h : ∀ B : Thickening S, IsAffine B.thickening.target.scheme →
      (M.over B).HasGlobalPresentation) :
    M.IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_forall_exists_restrictOpen M fun A x ↦ ?_
  obtain ⟨W, hWaff, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  exact ⟨W, hxW, h (A.restrictOpen W) hWaff⟩

/-- **The reduction step of [Stacks, Tag 07IT]: quasi-coherence on the big crystalline site is
Zariski-local on the ambient scheme.**  A sheaf of `𝒪_{X/S}`-modules is quasi-coherent exactly
when, around every point of the ambient scheme of every object, there is an open neighbourhood
with affine open subscheme on whose restriction the module has a global presentation. -/
theorem isQuasicoherentOnSite_iff_locally_restrictOpen
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    M.IsQuasicoherentOnSite ↔
      ∀ (A : Thickening S) (x : A.thickening.target.scheme),
        ∃ V : A.thickening.target.scheme.Opens,
          IsAffine (A.restrictOpen V).thickening.target.scheme ∧ x ∈ V ∧
            (M.over (A.restrictOpen V)).HasGlobalPresentation :=
  ⟨fun hM ↦ exists_isAffine_hasGlobalPresentation_restrictOpen M hM,
    fun h ↦ isQuasicoherentOnSite_of_forall_exists_restrictOpen M
      fun A x ↦ (h A x).imp fun _ hV ↦ ⟨hV.2.1, hV.2.2⟩⟩

end Crystalline.GlobalCrystallineSituation

end
