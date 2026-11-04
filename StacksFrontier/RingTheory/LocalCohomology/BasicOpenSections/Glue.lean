module

public import StacksFrontier.RingTheory.LocalCohomology.BasicOpenSections

/-!
# Gluing locally fractional sections along a cover

The locally fractional sections `Stacks.LocalCohomology.moduleSections` of a module on the opens
of `Spec A` form a sheaf: that is `Stacks.LocalCohomology.associatedAbPresheaf_isSheaf`, stated
for the presheaf of abelian groups built from them. This file records the same fact in the
concrete `A`-linear form, as an isomorphism of `A`-modules

`Γ(⨆ᵢ Vᵢ, M̃) ≅ { (sᵢ) : ∀ i, Γ(Vᵢ, M̃) | sᵢ and sⱼ agree at every point of Vᵢ ∩ Vⱼ }`.

Nothing has to be sheafified to get it: a locally fractional section *is* a dependent function on
the points of the open, so a compatible family is glued by choosing, for each point of the union,
an index of the cover containing it; compatibility makes the choice irrelevant, and the glued
function agrees with `sᵢ` on all of `Vᵢ`, hence is locally a fraction there.

Together with `Stacks.LocalCohomology.isLocalizedModule_moduleSectionsMk_basicOpen` this describes
the sections on a union of standard opens `D(fᵢ)` as the compatible families of elements of the
localizations `M_{fᵢ}` — the sheaf-theoretic half of the degree-zero comparison of Stacks 0DWR,
with the module universe independent of the ring's.

## Main definitions

* `Stacks.LocalCohomology.moduleSectionsRestrict` — restriction of locally fractional sections to
  a smaller open, as an `A`-linear map.
* `Stacks.LocalCohomology.compatibleModuleSections` — the families of sections on a cover that
  agree at every common point.
* `Stacks.LocalCohomology.moduleSectionsCoverEquiv` — **the sheaf axiom**: restriction to the
  pieces of a cover is an isomorphism onto the compatible families.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 08D0](https://stacks.math.columbia.edu/tag/08D0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u v w

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (M : ModuleCat.{v} A)

/-- Restriction of locally fractional sections of `M̃` from an open `U` to a smaller open `V`, as
an `A`-linear map. -/
def moduleSectionsRestrict {U V : Opens (PrimeSpectrum.Top A)} (h : V ≤ U) :
    moduleSections M U →ₗ[A] moduleSections M V where
  toFun s := ⟨fun x ↦ s.1 ⟨x.1, h x.2⟩,
    (moduleIsFractionPrelocal M).sheafify.res (homOfLE h) s.1 s.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The restriction of a section `s` to `V` takes at a point of `V` the value of `s` there. -/
@[simp]
theorem moduleSectionsRestrict_apply {U V : Opens (PrimeSpectrum.Top A)} (h : V ≤ U)
    (s : moduleSections M U) (x : V) :
    (moduleSectionsRestrict M h s).1 x = s.1 ⟨x.1, h x.2⟩ :=
  rfl

/-- Restriction commutes with `m ↦ m / 1`: the constant fraction `m / 1` on an open restricts to
the constant fraction `m / 1` on a smaller one. -/
theorem moduleSectionsRestrict_comp_moduleSectionsMk {U V : Opens (PrimeSpectrum.Top A)}
    (h : V ≤ U) :
    (moduleSectionsRestrict M h).comp (moduleSectionsMk M U) = moduleSectionsMk M V :=
  rfl

variable {ι : Type w} (V : ι → Opens (PrimeSpectrum.Top A))

/-- The families of locally fractional sections on the opens of a family that agree at every
point lying in two of them. These are exactly the families that glue to a section on the
union. -/
def compatibleModuleSections : Submodule A (∀ i, moduleSections M (V i)) where
  carrier := {x | ∀ (i j : ι) (p : PrimeSpectrum A) (hi : p ∈ V i) (hj : p ∈ V j),
    (x i).1 ⟨p, hi⟩ = (x j).1 ⟨p, hj⟩}
  add_mem' hx hy i j p hi hj := congr($(hx i j p hi hj) + $(hy i j p hi hj))
  zero_mem' _ _ _ _ _ := rfl
  smul_mem' r {_x} hx i j p hi hj := congr(r • $(hx i j p hi hj))

/-- Restricting a section on the union of a family of opens to each member of the family gives a
compatible family. -/
def moduleSectionsCoverRestrict :
    moduleSections M (⨆ i, V i) →ₗ[A] compatibleModuleSections M V where
  toFun s := ⟨fun i ↦ moduleSectionsRestrict M (le_iSup V i) s, fun _ _ _ _ _ ↦ rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A section on a union is determined by its restrictions to the members of the union. -/
theorem moduleSectionsCoverRestrict_injective :
    Function.Injective (moduleSectionsCoverRestrict M V) := by
  intro s t hst
  refine Subtype.ext (funext fun p ↦ ?_)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp p.2
  exact congrFun (congrArg Subtype.val (congrFun (congrArg Subtype.val hst) i)) ⟨p.1, hi⟩

/-- A compatible family of sections on the members of a family of opens glues to a section on the
union. -/
theorem moduleSectionsCoverRestrict_surjective :
    Function.Surjective (moduleSectionsCoverRestrict M V) := by
  classical
  intro x
  choose idx hidx using fun p : (⨆ i, V i : Opens (PrimeSpectrum.Top A)) ↦ Opens.mem_iSup.mp p.2
  have key : ∀ (p : (⨆ i, V i : Opens (PrimeSpectrum.Top A))) (i : ι) (hp : p.1 ∈ V i),
      (x.1 (idx p)).1 ⟨p.1, hidx p⟩ = (x.1 i).1 ⟨p.1, hp⟩ :=
    fun p i hp ↦ x.2 (idx p) i p.1 (hidx p) hp
  refine ⟨⟨fun p ↦ (x.1 (idx p)).1 ⟨p.1, hidx p⟩, fun p ↦ ?_⟩,
    Subtype.ext (funext fun i ↦ Subtype.ext (funext fun y ↦ key ⟨y.1, le_iSup V i y.2⟩ i y.2))⟩
  obtain ⟨W, hpW, i, m, a, hma⟩ := (x.1 (idx p)).2 ⟨p.1, hidx p⟩
  have hWU : W ≤ ⨆ j, V j := i.le.trans (le_iSup V (idx p))
  refine ⟨W, hpW, homOfLE hWU, m, a, fun y ↦ ?_⟩
  obtain ⟨hay, hy⟩ := hma y
  exact ⟨hay, (key ⟨y.1, hWU y.2⟩ (idx p) (i.le y.2)).trans hy⟩

/-- **The sheaf axiom for locally fractional sections.** Restriction identifies the sections of
`M̃` on a union of opens with the families of sections on the members that agree at every common
point, as an isomorphism of `A`-modules. The module universe `v` is independent of the ring
universe `u`. -/
def moduleSectionsCoverEquiv :
    moduleSections M (⨆ i, V i) ≃ₗ[A] compatibleModuleSections M V :=
  LinearEquiv.ofBijective (moduleSectionsCoverRestrict M V)
    ⟨moduleSectionsCoverRestrict_injective M V, moduleSectionsCoverRestrict_surjective M V⟩

/-- The `i`-th component of the image of a section `s` is the restriction of `s` to `V i`. -/
@[simp]
theorem moduleSectionsCoverEquiv_apply (s : moduleSections M (⨆ i, V i)) (i : ι) :
    (moduleSectionsCoverEquiv M V s).1 i = moduleSectionsRestrict M (le_iSup V i) s :=
  rfl

end Stacks.LocalCohomology

end
