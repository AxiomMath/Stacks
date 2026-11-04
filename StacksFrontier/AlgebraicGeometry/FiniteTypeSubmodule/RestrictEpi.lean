module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectAffine

/-!
# Epimorphisms of modules on an open, tested on sections over opens of the ambient scheme

Let `f : A ⟶ B` be a morphism of `𝒪_X`-modules and let `W` be an open of `X`. This file
characterises the restriction of `f` to `W` being an epimorphism by a condition on the sections
of `A` and `B` over the opens of `X` contained in `W`: every section of `B` over such an open
lies, near every point of that open, in the image of `f`.

That form is what a local computation with a quasi-coherent module can actually supply, because
the opens it produces — basic opens of an affine open, say — are opens of `X`, not of the
subscheme `W`. Stating the criterion over the opens of `X` therefore removes the step of moving
between the opens of `W.toScheme` and the opens of `X` from every consumer. It also makes the
locality of epimorphisms on an open cover a corollary rather than a separate argument.

## Main results

* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.epi_of_isLocallySurjective_mapPresheaf`: a
  morphism of `𝒪_X`-modules whose underlying morphism of presheaves of abelian groups is locally
  surjective is an epimorphism. This is the converse of
  `AlgebraicGeometry.isLocallySurjective_mapPresheaf_of_epi`.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.epi_restrict_of_forall_exists_lift` and
  `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.exists_lift_of_epi_restrict`: the two directions
  of the criterion.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.epi_restrict_of_le_iSup`: being an epimorphism
  after restriction is local on a family of opens covering `W`.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isIso_restrictFunctor_map_of_mono_of_epi`: a
  monomorphism whose restriction is an epimorphism restricts to an isomorphism.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` carries its own `Category` instance, so `Epi` in `X.Modules`
is a different proposition from `Epi` in `SheafOfModules X.ringCatSheaf` about the same
morphism; the two are identified by the repository's `attribute [local implicit_reducible]`
idiom on `Scheme.Modules`, `Scheme.Modules.Hom` and `Scheme.Modules.instCategory`, exactly as
`AlgebraicGeometry.isLocallySurjective_mapPresheaf_of_epi` does for the other direction.

Both directions of the criterion go through the equality `Γ(B.restrict W.ι, O) = Γ(B, W.ι ''ᵁ O)`
of `AlgebraicGeometry.Scheme.Modules.restrictAppIso`, which holds by `rfl`. The transport that
would otherwise be needed is avoided by replacing an open `O ≤ W` of `X` by `W.ι ''ᵁ O'` for
`O' = W.ι ⁻¹ᵁ O` *before* any section is named, so that no `eqToHom` on a presheaf ever appears:
with the open in that shape the two spellings of a module of sections are the same term, and the
remaining equality of restriction maps holds because the homs of a lattice of opens are a
subsingleton.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.FiniteTypeSubmodule

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory in
/-- A morphism of `𝒪_X`-modules whose underlying morphism of presheaves of abelian groups is
locally surjective is an epimorphism. This is the converse of
`AlgebraicGeometry.isLocallySurjective_mapPresheaf_of_epi`, and like it it is the
site-level statement transported across the fact that `AlgebraicGeometry.Scheme.Modules` carries
its own `Category` instance. -/
theorem epi_of_isLocallySurjective_mapPresheaf {X : Scheme.{u}} {A B : X.Modules} (p : A ⟶ B)
    (h : TopCat.Presheaf.IsLocallySurjective (Scheme.Modules.Hom.mapPresheaf p)) : Epi p :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective p h

/-- An open of `X` contained in `W` is the image of an open of `W.toScheme`. -/
private theorem exists_ι_image_eq {X : Scheme.{u}} {W O : X.Opens} (hOW : O ≤ W) :
    ∃ O' : W.toScheme.Opens, W.ι ''ᵁ O' = O := by
  refine ⟨W.ι ⁻¹ᵁ O, ?_⟩
  simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using inf_eq_right.2 hOW

/-- If every section of `B` over an open of `X` contained in `W` is, near each point of that
open, in the image of `f`, then `f` restricted to `W` is an epimorphism. -/
theorem epi_restrict_of_forall_exists_lift {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    (W : X.Opens)
    (h : ∀ O : X.Opens, O ≤ W → ∀ (t : Γ(B, O)) (x : X), x ∈ O →
      ∃ (V : X.Opens) (hVO : V ≤ O), x ∈ V ∧
        ∃ s : Γ(A, V), f.app V s = B.presheaf.map (homOfLE hVO).op t) :
    Epi ((Scheme.Modules.restrictFunctor W.ι).map f) := by
  apply epi_of_isLocallySurjective_mapPresheaf
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro O t x hx
  obtain ⟨V, hVO, hxV, s, hs⟩ := h (W.ι ''ᵁ O) (W.ι_image_le O) t x.1
    ((Scheme.Opens.mem_ι_image_iff W).2 hx)
  have hVW : V ≤ W := hVO.trans (W.ι_image_le O)
  obtain ⟨V', rfl⟩ := exists_ι_image_eq hVW
  exact ⟨V', (W.ι.image_le_image_iff _ _).1 hVO, ⟨s, hs⟩, (Scheme.Opens.mem_ι_image_iff W).1 hxV⟩

/-- If `f` restricted to `W` is an epimorphism, then every section of `B` over an open of `X`
contained in `W` is, near each point of that open, in the image of `f`. -/
theorem exists_lift_of_epi_restrict {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    (W : X.Opens) (hf : Epi ((Scheme.Modules.restrictFunctor W.ι).map f))
    (O : X.Opens) (hOW : O ≤ W) (t : Γ(B, O)) (x : X) (hx : x ∈ O) :
    ∃ (V : X.Opens) (hVO : V ≤ O), x ∈ V ∧
      ∃ s : Γ(A, V), f.app V s = B.presheaf.map (homOfLE hVO).op t := by
  have hls := AlgebraicGeometry.isLocallySurjective_mapPresheaf_of_epi W.toScheme
    ((Scheme.Modules.restrictFunctor W.ι).map f)
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hls
  obtain ⟨O', rfl⟩ := exists_ι_image_eq hOW
  obtain ⟨V', hV'O, ⟨s, hs⟩, hxV'⟩ := hls O' t ⟨x, hOW hx⟩
    ((Scheme.Opens.mem_ι_image_iff W).1 hx)
  exact ⟨W.ι ''ᵁ V', Set.image_mono hV'O, (Scheme.Opens.mem_ι_image_iff W).2 hxV', s, hs⟩

/-- Being an epimorphism after restriction is local: if `f` restricted to each member of a
family of opens covering `W` is an epimorphism, so is `f` restricted to `W`. -/
theorem epi_restrict_of_le_iSup {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B) (W : X.Opens)
    {ι : Type*} (U : ι → X.Opens) (hcov : W ≤ ⨆ i, U i)
    (hf : ∀ i, Epi ((Scheme.Modules.restrictFunctor (U i).ι).map f)) :
    Epi ((Scheme.Modules.restrictFunctor W.ι).map f) := by
  refine epi_restrict_of_forall_exists_lift f W fun O hOW t x hx => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov (hOW hx))
  obtain ⟨V, hVO, hxV, s, hs⟩ := exists_lift_of_epi_restrict f (U i) (hf i) (O ⊓ U i)
    inf_le_right (B.presheaf.map (homOfLE (inf_le_left : O ⊓ U i ≤ O)).op t) x ⟨hx, hi⟩
  refine ⟨V, hVO.trans inf_le_left, hxV, s, hs.trans ?_⟩
  exact (congrArg (fun k : Γ(B, O) ⟶ Γ(B, V) => k.hom t)
    (B.presheaf.map_comp (homOfLE (inf_le_left : O ⊓ U i ≤ O)).op (homOfLE hVO).op)).symm

/-- A monomorphism whose restriction to `W` is an epimorphism restricts to an isomorphism. -/
theorem isIso_restrictFunctor_map_of_mono_of_epi {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    [Mono f] (W : X.Opens) (hf : Epi ((Scheme.Modules.restrictFunctor W.ι).map f)) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map f) :=
  have := mono_restrictFunctor_map W.ι f
  isIso_of_mono_of_epi _

end Stacks.AlgebraicGeometry.FiniteTypeSubmodule

end
