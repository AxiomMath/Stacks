module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FormallyEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unramified locus is open

Unramifiedness of a morphism of schemes at a point is witnessed by an affine open neighbourhood
of the point lying over an affine open of the target, on which the map of sections is an
unramified ring map. Every point of such a neighbourhood is then unramified for the *same*
witness, so the unramified locus is a union of open sets. The same argument applies to the
G-unramified locus.

Pointwise unramifiedness over an affine open of the target is moreover enough to make the map of
sections over that affine open formally unramified, hence étale once flatness and finite
presentation are available. That is the form in which the unramified locus is used to compute the
discriminant of a finite locally free morphism (Stacks Tag 0BJF).

## Main results

* `AlgebraicGeometry.isOpen_setOf_unramifiedAt` and
  `AlgebraicGeometry.isOpen_setOf_gUnramifiedAt`: the unramified and G-unramified loci are open.
* `AlgebraicGeometry.formallyUnramified_sections_of_unramifiedAt`: if every point of the source
  lying over an affine open `V` of the target is unramified, then the map of sections
  `Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)` is formally unramified, provided `f ⁻¹ᵁ V` is affine.
* `AlgebraicGeometry.etale_sections_of_unramifiedAt`: under the same hypothesis, together with
  flatness and finite presentation of the map of sections, that map is étale.

## Implementation notes

Openness is purely formal here, because `AlgebraicGeometry.UnramifiedAt` is stated as the
existence of an affine chart with an unramified map of sections rather than as a condition on the
local ring at the point; the chart witnessing one point witnesses all of its points. No finiteness
hypothesis is used, so the statements are more general than the source's, which assumes the
morphism locally of finite type.

The passage from pointwise unramifiedness to formal unramifiedness of the sections over a single
affine open goes through `AlgebraicGeometry.formallyUnramified_stalkMap_iff`, which compares the
stalk map at a point with the unramified locus of the sections over *any* affine chart around it.
Reading that equivalence first at the chart supplied by `UnramifiedAt` and then at the chart
`(V, f ⁻¹ᵁ V)` transfers the information between the two, with the stalk map as the intermediary;
this needs neither a Noetherian hypothesis nor a comparison of the two charts.

## References

* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Stacks Project, Tag 0475.** The locus where a morphism of schemes is unramified is open. -/
@[stacks 0475 "openness of the unramified locus", sga "1 I 3.3"]
theorem isOpen_setOf_unramifiedAt (f : X ⟶ Y) : IsOpen {x : X | UnramifiedAt f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, hU, hxU, V, hV, e, halg⟩
  exact ⟨U, fun y hy ↦ ⟨U, hU, hy, V, hV, e, halg⟩, U.2, hxU⟩

/-- **Stacks Project, Tag 0475.** The locus where a morphism of schemes is G-unramified is
open. -/
@[stacks 0475 "openness of the G-unramified locus", sga "1 I 3.3" "loc. finite presentation"]
theorem isOpen_setOf_gUnramifiedAt (f : X ⟶ Y) : IsOpen {x : X | GUnramifiedAt f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, hU, hxU, V, hV, e, halg⟩
  exact ⟨U, fun y hy ↦ ⟨U, hU, hy, V, hV, e, halg⟩, U.2, hxU⟩

/-- If every point of the source lying over an affine open `V` of the target is a point of
unramifiedness, and the inverse image of `V` is affine, then the map of sections over `V` is
formally unramified. -/
theorem formallyUnramified_sections_of_unramifiedAt (f : X ⟶ Y)
    {V : Y.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (h : ∀ x : X, f x ∈ V → UnramifiedAt f x) :
    letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
    Algebra.FormallyUnramified Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro q
  obtain ⟨x, hxq⟩ : ∃ x : (f ⁻¹ᵁ V), hU.primeIdealOf x = q :=
    ⟨(Scheme.homeoOfIso hU.isoSpec).symm q, (Scheme.homeoOfIso hU.isoSpec).apply_symm_apply q⟩
  rw [← hxq, ← formallyUnramified_stalkMap_iff V hV (f ⁻¹ᵁ V) hU le_rfl x.2]
  obtain ⟨U₀, hU₀, hxU₀, V₀, hV₀, e, halg⟩ := h x.1 x.2
  rw [formallyUnramified_stalkMap_iff V₀ hV₀ U₀ hU₀ e hxU₀]
  let : Algebra Γ(Y, V₀) Γ(X, U₀) := (f.appLE V₀ U₀ e).hom.toAlgebra
  let : Algebra.Unramified Γ(Y, V₀) Γ(X, U₀) := halg
  rw [Algebra.unramifiedLocus_eq_univ_iff.mpr Algebra.Unramified.formallyUnramified]
  trivial

/-- If every point of the source lying over an affine open `V` of the target is a point of
unramifiedness, and the map of sections over `V` is flat of finite presentation on an affine
inverse image, then that map of sections is étale. -/
@[ega "IV 17.6.1" "c ⇒ a, special case", ega "IV 17.7.10" "special case"]
theorem etale_sections_of_unramifiedAt (f : X ⟶ Y)
    {V : Y.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (h : ∀ x : X, f x ∈ V → UnramifiedAt f x)
    (hflat : letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
      Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
    (hfp : letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
      Algebra.FinitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) :
    letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
    Algebra.Etale Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  let : Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hflat
  let : Algebra.FinitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hfp
  let : Algebra.FormallyUnramified Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    formallyUnramified_sections_of_unramifiedAt f hV hU h
  let : Algebra.EssFiniteType Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    Algebra.EssFiniteType.of_finiteType _ _
  let : Algebra.FormallyEtale Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    Stacks.FormallyEtale.formallyEtale_of_flat
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry

end
