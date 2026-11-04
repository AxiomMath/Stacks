module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic

/-!
# An invertible module is trivial over the preimage of a small enough open

Let `π : X ⟶ Y` be a finite morphism of schemes, let `L` be an invertible `𝒪_X`-module and let
`y ∈ Y`. [Stacks, Tag 0BUT] asserts that some open neighbourhood `V ∋ y` has `L` trivial on
`π^{-1}(V)`.

The Stacks proof has two steps. First, because `π` is finite the fibre `π^{-1}(y)` is a *finite*
set of points, and on an affine scheme an invertible module has a global section `s` vanishing at
none of them — that is [Stacks, Tag 0F20], or the direct argument from exactness of global
sections on quasi-coherent modules ([Stacks, Tag 01IB]). Second, the nonvanishing locus `X_s` is
then an open neighbourhood of the whole fibre, and since a finite morphism is closed, some
neighbourhood of `y` has its preimage inside `X_s`, where `L` is trivialized by `s`.

**This file proves the second step, in full and unconditionally**, taking the section `s` of the
first step as a hypothesis. So what Tag 0BUT still owes is exactly Tag 0F20 for an affine
scheme, and nothing else; `StacksFrontier/AlgebraicGeometry/QuasiAffineNonvanishing/Basic.lean`
has the two inclusions of Tag 0F20 for a quasi-affine scheme modulo global generation of `L`,
which is where the remaining work is.

## Main results

* `Stacks.SheafOfModules.exists_isOpen_mem_preimage_subset`: the tube lemma for a closed map. An
  open set containing a whole fibre contains the preimage of a neighbourhood of the point.
* `Stacks.SheafOfModules.exists_mem_preimage_le_nonvanishingOpen`: its instance for a finite
  morphism of schemes and the nonvanishing locus of a global section.
* `Stacks.SheafOfModules.exists_isTrivial_preimage_of_fibre_subset_nonvanishingOpen`: **the
  second step of Tag 0BUT.** If a global section of an invertible module vanishes at no point of
  the fibre over `y`, then some open neighbourhood `V` of `y` has `L` restricted to the open
  subscheme `π^{-1}(V)` isomorphic to its structure sheaf.

## Implementation notes

The tube lemma is `V = Y ∖ π(X ∖ U)`: the complement is closed because `π` is a closed map, `y`
is in it because every point of `X` over `y` lies in `U`, and its preimage is inside `U` by
construction. A finite morphism of schemes is closed by `AlgebraicGeometry.Scheme.Hom.isClosedMap`,
so no separate properness input is needed. It is stated for a bare closed map and specialized,
because the hypothesis really is only closedness together with the fibre being inside the open —
nothing about finiteness of the fibre is used in this half.

The trivialization itself is not re-derived. `bijective_smul_eval_of_le_nonvanishingOpen` of
`StacksFrontier/AlgebraicGeometry/NonvanishingTrivialization/Basic.lean` already says that
`c ↦ c • s|_W` is bijective for *every* open `W` inside `X_s`, which is precisely the hypothesis
`Stacks.SheafOfModules.isoUnitOver` takes, and the restriction of a global section to a smaller
open is again its own evaluation there (`PresheafOfModules.sections_property`). So the whole
step is: find `V`, then read off the isomorphism on the localized site, then move it to the open
subscheme with
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit`.

That last restriction equality is rewritten in **term mode**, with `▸`, and not with `rw`. With
`rw` it fails as "the target expression is not type-correct under the `implicit` transparency
level", because `L : X.Modules` has to be read as a `SheafOfModules (structureSheafRing
X.toRingedSpace)` for `L.val` to elaborate and the two are not interchangeable at that
transparency. This is the same failure `StacksDraft/AlgebraicGeometry/F3b/
NonvanishingTrivialization/Basic.lean` records for its own germ computations, with the same fix,
and it is why no transparency attribute is needed here.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class the Tag 01CY
nonvanishing-locus API is stated in. A statement with its hypothesis in the other copy,
`AlgebraicGeometry.SheafOfModules.IsInvertible`, reaches this one through
`Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible` of
`StacksFrontier/AlgebraicGeometry/InvertibleBridge/Basic.lean`.

## References

* [Stacks Project, Tag 0BUT](https://stacks.math.columbia.edu/tag/0BUT)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

/-- **The tube lemma for a closed map.** If `f` is closed and the open set `U` contains the whole
fibre of `f` over `y`, then `y` has a neighbourhood whose preimage is contained in `U`. -/
theorem exists_isOpen_mem_preimage_subset {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : IsClosedMap f) {U : Set α} (hU : IsOpen U) {y : β}
    (hy : f ⁻¹' {y} ⊆ U) :
    ∃ V : Set β, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U := by
  refine ⟨(f '' Uᶜ)ᶜ, (hf _ hU.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx (hy rfl)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩

variable {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] (L : X.Modules)
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

/-- The tube lemma for a finite morphism of schemes and the nonvanishing locus of a global
section: if a global section of `L` vanishes at no point over `y`, then `y` has an open
neighbourhood whose preimage lies inside the nonvanishing locus. -/
theorem exists_mem_preimage_le_nonvanishingOpen (s : L.sections) (y : Y)
    (hy : ∀ x : X, π.base x = y → x ∈ nonvanishingOpen (X := X.toRingedSpace) L s) :
    ∃ V : Y.Opens, y ∈ V ∧ π ⁻¹ᵁ V ≤ nonvanishingOpen (X := X.toRingedSpace) L s := by
  obtain ⟨V, hVopen, hyV, hVsub⟩ := exists_isOpen_mem_preimage_subset π.isClosedMap
    (U := (nonvanishingOpen (X := X.toRingedSpace) L s : Set X))
    (nonvanishingOpen (X := X.toRingedSpace) L s).isOpen (y := y) (fun x hx => hy x hx)
  exact ⟨⟨V, hVopen⟩, hyV, hVsub⟩

/-- **The second step of Stacks Project, Tag 0BUT.** Let `π : X ⟶ Y` be a finite morphism of
schemes and `L` an invertible `𝒪_X`-module. If a global section `s` of `L` vanishes at no point
of the fibre over `y`, then some open neighbourhood `V` of `y` has `L` restricted to the open
subscheme `π^{-1}(V)` isomorphic to its structure sheaf.

What Tag 0BUT itself still owes beyond this is only the production of such an `s`, which is
Tag 0F20 for an affine scheme. -/
theorem exists_isTrivial_preimage_of_fibre_subset_nonvanishingOpen (s : L.sections) (y : Y)
    (hy : ∀ x : X, π.base x = y → x ∈ nonvanishingOpen (X := X.toRingedSpace) L s) :
    ∃ V : Y.Opens, y ∈ V ∧
      Nonempty (Scheme.Modules.restrict L (π ⁻¹ᵁ V).ι ≅
        SheafOfModules.unit ((π ⁻¹ᵁ V).toScheme.ringCatSheaf)) := by
  have hlocal : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => X.isLocalRing z
  obtain ⟨V, hyV, hVsub⟩ := exists_mem_preimage_le_nonvanishingOpen π L s y hy
  refine ⟨V, hyV, ⟨Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit _ L
    (isoUnitOver (X := X.toRingedSpace) L (π ⁻¹ᵁ V) (s.eval (op (π ⁻¹ᵁ V)))
      fun W hW => ?_)⟩⟩
  exact (PresheafOfModules.sections_property s (homOfLE hW).op).symm ▸
    bijective_smul_eval_of_le_nonvanishingOpen (X := X.toRingedSpace) L s W (hW.trans hVsub)

end Stacks.SheafOfModules

end
