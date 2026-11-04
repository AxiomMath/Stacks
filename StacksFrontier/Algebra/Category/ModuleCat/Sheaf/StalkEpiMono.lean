module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# Epimorphisms of sheaves of modules on a space are detected on stalks

Let `(X, 𝒪)` be a ringed space and let `f : M ⟶ N` be a morphism of sheaves of `𝒪`-modules.
If the induced map `M_x → N_x` is surjective for every point `x` of `X`, then `f` is an
epimorphism, and conversely.

## Main results

* `Stacks.SheafOfModules.StalkEpiMono.epi_of_stalk_surjective`: a morphism of sheaves of
  modules surjective on every stalk is an epimorphism.
* `Stacks.SheafOfModules.StalkEpiMono.stalk_surjective_of_epi`: the converse.
* `Stacks.SheafOfModules.StalkEpiMono.epi_iff_stalk_surjective`: the two combined.
* `Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections`: the section-level criterion,
  asking that every section of the target be in the image of `f` after restriction to some
  neighbourhood of each of its points.
* `Stacks.SheafOfModules.StalkEpiMono.exists_sections_of_epi`: the converse of the latter.
* `Stacks.SheafOfModules.StalkEpiMono.epi_iff_moduleStalk_surjective` and its two halves
  `epi_of_moduleStalk_surjective`, `moduleStalk_surjective_of_epi`: the same criterion with the
  stalks read as modules over the stalks of the sheaf of rings.

## Implementation notes

The stalk of a sheaf of modules is taken here to be the stalk of the underlying presheaf of
abelian groups, `TopCat.Presheaf.stalk M.val.presheaf x`; Mathlib's
`PresheafOfModules.instModuleStalk` makes it a module over the stalk of `𝒪`, and surjectivity
of a map of modules is surjectivity of the underlying map of groups, so nothing is lost.

Both directions factor through local surjectivity.
`TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` identifies surjectivity on all
stalks with local surjectivity for the topology of opens, for presheaves valued in any
concrete category with filtered colimits; and
`Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective` identifies local surjectivity of
the underlying morphism of presheaves of abelian groups with being an epimorphism of sheaves of
modules. The two spellings of that underlying morphism, as the image of `f` under
`SheafOfModules.forget ⋙ PresheafOfModules.toPresheaf` and as
`(PresheafOfModules.toPresheaf 𝒪.obj).map f.val`, agree definitionally.

A morphism of modules over a scheme `X` lives in `AlgebraicGeometry.Scheme.Modules X`, which
copies the category instance of `SheafOfModules X.ringCatSheaf` without being syntactically
equal to it, so the two `Epi` propositions differ; `epi_of_moduleStalk_surjective` is
transported across by the cancellation property, as `⟨fun g₁ g₂ h ↦ (…).1 g₁ g₂ h⟩`.

## References

* [Stacks Project, Tag 007T](https://stacks.math.columbia.edu/tag/007T)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace Stacks.SheafOfModules.StalkEpiMono

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- The map on stalks at `x` induced by a morphism of sheaves of `𝒪`-modules, as a morphism of
the underlying abelian groups. -/
noncomputable def stalkMap {M N : SheafOfModules.{u} O} (f : M ⟶ N) (x : X) :
    TopCat.Presheaf.stalk M.val.presheaf x ⟶ TopCat.Presheaf.stalk N.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf O.obj).map f.val)

/-- The stalk map of a morphism of sheaves of modules sends the germ of a section to the germ
of its image. -/
lemma stalkMap_germ {M N : SheafOfModules.{u} O} (f : M ⟶ N) (x : X) (U : Opens X) (hx : x ∈ U)
    (s : M.val.presheaf.obj (op U)) :
    stalkMap f x (TopCat.Presheaf.germ M.val.presheaf U x hx s) =
      TopCat.Presheaf.germ N.val.presheaf U x hx
        (((PresheafOfModules.toPresheaf O.obj).map f.val).app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf O.obj).map f.val) s

/-- **A morphism of sheaves of modules surjective on every stalk is an epimorphism.** -/
theorem epi_of_stalk_surjective {M N : SheafOfModules.{u} O} (f : M ⟶ N)
    (h : ∀ x : X, Function.Surjective (stalkMap f x)) : Epi f :=
  EpiMono.epi_of_isLocallySurjective f
    ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).2 h)

/-- **An epimorphism of sheaves of modules is surjective on every stalk.** -/
theorem stalk_surjective_of_epi {M N : SheafOfModules.{u} O} (f : M ⟶ N) [Epi f] (x : X) :
    Function.Surjective (stalkMap f x) :=
  (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).1
    (EpiMono.isLocallySurjective_of_epi f) x

/-- **Stacks 007T (2) for sheaves of modules.** A morphism of sheaves of modules is an
epimorphism if and only if it is surjective on stalks at every point. -/
theorem epi_iff_stalk_surjective {M N : SheafOfModules.{u} O} (f : M ⟶ N) :
    Epi f ↔ ∀ x : X, Function.Surjective (stalkMap f x) :=
  ⟨fun _ x ↦ stalk_surjective_of_epi f x, epi_of_stalk_surjective f⟩

/-- **The section-level criterion for an epimorphism of sheaves of modules.** If every section
of `N` over an open `U` is, near each point of `U`, the image under `f` of a section of `M`,
then `f` is an epimorphism. -/
theorem epi_of_exists_sections {M N : SheafOfModules.{u} O} (f : M ⟶ N)
    (h : ∀ (U : Opens X) (t : N.val.obj (op U)) (x : X), x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V) (s : M.val.obj (op V)),
        f.val.app (op V) s = N.val.map (homOfLE hVU).op t) :
    Epi f := by
  refine EpiMono.epi_of_isLocallySurjective f
    ((TopCat.Presheaf.isLocallySurjective_iff _).2 fun U t x hx ↦ ?_)
  obtain ⟨V, hVU, hxV, s, hs⟩ := h U t x hx
  exact ⟨V, hVU, ⟨s, hs⟩, hxV⟩

/-- **Every section of the target of an epimorphism of sheaves of modules is locally in the
image.** This is the converse of `epi_of_exists_sections`. -/
theorem exists_sections_of_epi {M N : SheafOfModules.{u} O} (f : M ⟶ N) [Epi f]
    (U : Opens X) (t : N.val.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V) (s : M.val.obj (op V)),
      f.val.app (op V) s = N.val.map (homOfLE hVU).op t := by
  obtain ⟨V, hVU, ⟨s, hs⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).1 (EpiMono.isLocallySurjective_of_epi f) U t x hx
  exact ⟨V, hVU, hxV, s, hs⟩

/-! ### The stalk as a module over the stalk of the sheaf of rings -/

/-- **A morphism of sheaves of modules surjective on every stalk is an epimorphism**, with the
stalks read as modules over the stalks of the sheaf of rings. -/
theorem epi_of_moduleStalk_surjective {M N : SheafOfModules.{u} O} (f : M ⟶ N)
    (h : ∀ x : X, Function.Surjective
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).map f).hom) : Epi f :=
  epi_of_stalk_surjective f h

/-- **An epimorphism of sheaves of modules is surjective on every stalk**, with the stalks read
as modules over the stalks of the sheaf of rings. -/
theorem moduleStalk_surjective_of_epi {M N : SheafOfModules.{u} O} (f : M ⟶ N) [Epi f] (x : X) :
    Function.Surjective ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).map f).hom :=
  stalk_surjective_of_epi f x

/-- **Stacks 007T (2) for sheaves of modules**, with the stalks read as modules over the stalks
of the sheaf of rings. -/
theorem epi_iff_moduleStalk_surjective {M N : SheafOfModules.{u} O} (f : M ⟶ N) :
    Epi f ↔ ∀ x : X, Function.Surjective
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).map f).hom :=
  ⟨fun _ x ↦ moduleStalk_surjective_of_epi f x, epi_of_moduleStalk_surjective f⟩

end Stacks.SheafOfModules.StalkEpiMono

end
