module

public import Mathlib.AlgebraicGeometry.FunctionField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sections over an open are the intersection of the local rings

Let `X` be an integral scheme and `V ⊆ X` a nonempty open. Inside the function field `R(X)` the
subring `Γ(X, V)` is exactly the intersection of the local rings `𝒪_{X, x}` for `x ∈ V`: a
rational function regular at every point of `V` is a section over `V`. One inclusion is the
statement that the germ at a point factors the germ at the generic point; the other is the
sheaf condition, applied to the cover of `V` by the opens on which each given germ is
represented.

This is the fact the last paragraph of [Stacks, Tag 0BD7] uses to recognise a meromorphic
function on the base as a section of `𝒪_Y` over the open where it has no poles.

## Main results

* `AlgebraicGeometry.exists_germToFunctionField_eq_of_forall_mem_range`: an element of the
  function field lying in the image of every local ring `𝒪_{X, x}`, `x ∈ V`, is the germ at the
  generic point of a section over `V`.
* `AlgebraicGeometry.range_germToFunctionField_eq_iInter`: the resulting equality
  `Γ(X, V) = ⋂_{x ∈ V} 𝒪_{X, x}` of subsets of `R(X)`.

## Implementation notes

A `⊤`-only form of the first result exists as the `private` lemma
`AlgebraicGeometry.exists_global_of_mem_all_stalks` of
`StacksFrontier/AlgebraicGeometry/Properties/Normal.lean`, where it is used to prove Tag 0358. It
is deduced from the general statement below rather than duplicated; this file is kept to the
single import `Mathlib.AlgebraicGeometry.FunctionField` so that the general form is reachable
from any consumer, whatever its own import surface.

Mathlib has neither form. Its nearest statement is
`AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ`, which glues germwise *invertibility* of a
section already given; here there is no section to begin with and the germs are elements of the
local rings, so the gluing is of the representatives rather than of their inverses.

Compatibility of the representatives is checked by their images in the function field, using
injectivity of `Γ(X, W) ⟶ R(X)` on a nonempty open — the generic point lies in every nonempty
open, so each pairwise intersection is nonempty and the test applies. That is where integrality
is used; irreducibility alone would not give the injectivity.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0358](https://stacks.math.columbia.edu/tag/0358)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **A rational function regular at every point of `V` is a section over `V`.** For an integral
scheme `X` and a nonempty open `V`, an element of the function field that lies in the image of
the local ring at every point of `V` is the image of a section of `𝒪_X` over `V`.

Each germ is represented by a section on some open; intersecting with `V` and gluing over the
resulting cover of `V` produces the section, the representatives being compatible because they
have the same image in the function field and that image determines a section on a nonempty
open. -/
@[ega "I 8.2.1" "partial", ega "I 8.2.6" "partial"]
theorem exists_germToFunctionField_eq_of_forall_mem_range (X : Scheme.{u}) [IsIntegral X]
    (V : X.Opens) [Nonempty V] (z : X.functionField)
    (hz : ∀ x : V, ∃ a : X.presheaf.stalk x.1,
      algebraMap (X.presheaf.stalk x.1) X.functionField a = z) :
    ∃ a : Γ(X, V), X.germToFunctionField V a = z := by
  classical
  have hgmem : ∀ W : X.Opens, Nonempty W → genericPoint X ∈ W := fun W h =>
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)
  choose a ha using hz
  choose U hxU s hs using fun x : V => X.presheaf.exists_germ_eq (a x)
  have hxW : ∀ x : V, x.1 ∈ U x ⊓ V := fun x => ⟨hxU x, x.2⟩
  have hgW : ∀ x : V, genericPoint X ∈ (U x ⊓ V : X.Opens) :=
    fun x => hgmem _ ⟨⟨x.1, hxW x⟩⟩
  have hfield : ∀ x : V, X.presheaf.germ (U x ⊓ V) (genericPoint X) (hgW x)
      (X.presheaf.map (homOfLE (inf_le_left : U x ⊓ V ≤ U x)).op (s x)) = z := by
    intro x
    let : Nonempty (U x) := ⟨⟨x.1, hxU x⟩⟩
    rw [X.presheaf.germ_res_apply (homOfLE (inf_le_left : U x ⊓ V ≤ U x)) (genericPoint X)
      (hgW x) (s x), ← ha x, ← hs x]
    exact (X.algebraMap_germ_eq_germToFunctionField (hxU x) (s x)).symm
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun x : V => U x ⊓ V)
      (fun x : V => X.presheaf.map (homOfLE (inf_le_left : U x ⊓ V ≤ U x)).op (s x)) := by
    intro x y
    refine germ_injective_of_isIntegral X (genericPoint X)
      (show genericPoint X ∈ (U x ⊓ V) ⊓ (U y ⊓ V) from ⟨hgW x, hgW y⟩) ?_
    rw [X.presheaf.germ_res_apply (Opens.infLELeft (U x ⊓ V) (U y ⊓ V)) (genericPoint X)
        ⟨hgW x, hgW y⟩,
      X.presheaf.germ_res_apply (Opens.infLERight (U x ⊓ V) (U y ⊓ V)) (genericPoint X)
        ⟨hgW x, hgW y⟩]
    exact (hfield x).trans (hfield y).symm
  obtain ⟨g, hg, -⟩ :=
    X.sheaf.existsUnique_gluing' (fun x : V => U x ⊓ V) V
      (fun x => homOfLE (inf_le_right : U x ⊓ V ≤ V))
      (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩) _ hcompat
  refine ⟨g, ?_⟩
  obtain ⟨x⟩ : Nonempty V := inferInstance
  have h := hfield x
  rw [← hg x] at h
  rw [← h]
  exact (X.presheaf.germ_res_apply (homOfLE (inf_le_right : U x ⊓ V ≤ V)) (genericPoint X)
    (hgW x) g).symm

/-- **`Γ(X, V)` is the intersection of the local rings `𝒪_{X, x}` for `x ∈ V`**, as subsets of
the function field of an integral scheme. -/
theorem range_germToFunctionField_eq_iInter (X : Scheme.{u}) [IsIntegral X] (V : X.Opens)
    [Nonempty V] :
    Set.range (X.germToFunctionField V) =
      ⋂ x : V, Set.range (algebraMap (X.presheaf.stalk x.1) X.functionField) := by
  refine le_antisymm (fun z hz => Set.mem_iInter.mpr fun x => ?_) (fun z hz => ?_)
  · obtain ⟨a, rfl⟩ := hz
    exact ⟨X.presheaf.germ V x.1 x.2 a, X.algebraMap_germ_eq_germToFunctionField x.2 a⟩
  · exact exists_germToFunctionField_eq_of_forall_mem_range X V z
      fun x => Set.mem_iInter.mp hz x

end AlgebraicGeometry

end
