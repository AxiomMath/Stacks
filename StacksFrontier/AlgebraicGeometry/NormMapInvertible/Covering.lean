module

public import StacksFrontier.AlgebraicGeometry.QuasiAffineGlobalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Trivializing an invertible module over the preimage of an open

Let `f : X ⟶ Y` be a finite morphism of schemes and `L` an invertible `𝒪_X`-module. For every
point `y` of `Y` there is an open `V ∋ y` over whose preimage `f ⁻¹ᵁ V` the module `L` has a
generating section, i.e. a member of `Stacks.Cohomology.Generators.GeneratorSections`.

This is Stacks Tag 0BUT with its conclusion read as a generating section. Stacks Tag 0F20
(`Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite_sections`)
applies on the affine -- hence quasi-affine -- preimage of an affine open of `Y`; the
trivialization clause of Stacks Tag 01CY, in the elementary form
`Stacks.NonvanishingTrivialize.bijective_smul`, turns the section Tag 0F20 produces into a
generator; and Stacks Tag 0B8L (`Stacks.InvertiblePullback.isInvertibleModule_restrict`) keeps the
restriction invertible.

## Main results

* `Stacks.NormMapInvertible.generatorSectionsImage`: a generating section of `L|_P` over an open
  `W` of the open subscheme `P` is a generating section of `L` over the image open `P.ι ''ᵁ W`.
* `Stacks.NormMapInvertible.generatorSectionsNonvanishingOpen`: a global section of an invertible
  module generates it over its nonvanishing open.
* `Stacks.NormMapInvertible.exists_generatorSections_preimage`: the statement above.

## Implementation notes

`GeneratorSections` is stated for a `RingedSpace` and a module over `structureSheaf X.sheaf`,
while Stacks Tag 0F20 and the ampleness theory are stated for a `Scheme` and
`X.Modules`; the two are definitionally the same and the bridge is
`Stacks.NonvanishingSpelling`, whose scoped instances this file opens.

Invertibility of a restriction `L|_P` is not found by instance search: Stacks Tag 0B8L is stated
for `RingedSpaceModuleAdjunction.modulePullback`, and three spellings of the pullback of a module
sheaf have to be crossed to reach `AlgebraicGeometry.Scheme.Modules.restrict`. The two
isomorphisms doing so are `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`Stacks.ProjectiveBundleQuotients.pullbackIso`.

The passage from the open subscheme `P` back to `X` is not definitional.
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl`, so the abelian group
`Γ(L|_P, V)` *is* `Γ(L, P.ι ''ᵁ V)` and the ring `Γ(P, V)` *is* `Γ(X, P.ι ''ᵁ V)`; but the module
structure of `L|_P` acts through `(P.ι.appIso V).inv`, whose body is not exposed, so the two
scalar actions are not interchangeable by `exact`, by `rw` or by `rfl` -- not even after
`AlgebraicGeometry.Scheme.Opens.ι_appIso`, which cannot be rewritten inside an instance argument.
Instead, `Stacks.NormMapInvertible.bijective_smul_restrictAppIso` composes with the
*bijection* `(P.ι.appIso V).inv` and uses only
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply`.

## References

* [Stacks Project, Tag 0BUT](https://stacks.math.columbia.edu/tag/0BUT)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.NonvanishingSpelling Stacks.Cohomology.Generators
open Stacks.NonvanishingTrivialize

universe u

namespace Stacks.NormMapInvertible

/-! ### Invertibility of a restriction -/

/-- The restriction of an invertible `𝒪_X`-module to an open subscheme is invertible. This is
Stacks Tag 0B8L transported from the `RingedSpaceModuleAdjunction.modulePullback` spelling along
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`Stacks.ProjectiveBundleQuotients.pullbackIso`. -/
instance isInvertibleModule_restrict {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (P : X.Opens) : IsInvertibleModule P.toScheme (L.restrict P.ι) :=
  letI := Stacks.InvertiblePullback.isInvertibleModule_restrict P L
  Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _
    ((Scheme.Modules.restrictFunctorIsoPullback P.ι).app L ≪≫
      (Stacks.ProjectiveBundleQuotients.pullbackIso P.ι).app L).symm

/-! ### Transport along the inclusion of an open subscheme -/

/-- **The two scalar actions on the sections of a restriction agree.** The abelian group
`Γ(L|_P, V)` is `Γ(L, P.ι ''ᵁ V)` and the ring `Γ(P, V)` is `Γ(X, P.ι ''ᵁ V)`, but the module
structure of the restriction acts through `(P.ι.appIso V).inv`, which is the identity only by
`AlgebraicGeometry.Scheme.Opens.ι_appIso`. So bijectivity of multiplication by a section has to
be moved across `AlgebraicGeometry.Scheme.Modules.restrictAppIso` rather than transported by
`rfl`. -/
lemma bijective_smul_restrictAppIso {X : Scheme.{u}} (L : X.Modules) {P : X.Opens}
    {V : P.toScheme.Opens} (m : Γ(L.restrict P.ι, V))
    (hm : Function.Bijective fun r : Γ(P.toScheme, V) => (r • m : Γ(L.restrict P.ι, V))) :
    Function.Bijective fun r : Γ(X, P.ι ''ᵁ V) =>
      (r • (L.restrictAppIso P.ι V).hom m : Γ(L, P.ι ''ᵁ V)) := by
  have hα : Function.Bijective (P.ι.appIso V).inv :=
    ConcreteCategory.bijective_of_isIso _
  have hfun : (fun r : Γ(X, P.ι ''ᵁ V) =>
          (r • (L.restrictAppIso P.ι V).hom m : Γ(L, P.ι ''ᵁ V))) ∘
        (P.ι.appIso V).inv =
      (L.restrictAppIso P.ι V).hom ∘
        (fun r : Γ(P.toScheme, V) => (r • m : Γ(L.restrict P.ι, V))) :=
    funext fun r => (Scheme.Modules.smul_restrictAppIso_hom_apply P.ι L V r m).symm
  have hcomp : Function.Bijective
      ((fun r : Γ(X, P.ι ''ᵁ V) =>
        (r • (L.restrictAppIso P.ι V).hom m : Γ(L, P.ι ''ᵁ V))) ∘
          (P.ι.appIso V).inv) := by
    rw [hfun]
    exact (ConcreteCategory.bijective_of_isIso _).comp hm
  exact (Function.Bijective.of_comp_iff _ hα).mp hcomp

/-- **A generating section of `L|_P` over `W` gives a generating section of `L` over
`P.ι ''ᵁ W`.** The section is carried across
`AlgebraicGeometry.Scheme.Modules.restrictAppIso`, and an open `V ≤ P.ι ''ᵁ W` of `X` is seen as
the image of the open `P.ι ⁻¹ᵁ V` of `P`. -/
def generatorSectionsImage {X : Scheme.{u}} (L : X.Modules) {P : X.Opens}
    {W : P.toScheme.Opens}
    (g : GeneratorSections P.toScheme.toRingedSpace (L.restrict P.ι) W) :
    GeneratorSections X.toRingedSpace L (P.ι ''ᵁ W) := by
  refine ⟨(L.restrictAppIso P.ι W).hom g.val, fun V h => ?_⟩
  have himg : P.ι ''ᵁ (P.ι ⁻¹ᵁ V) = V := by
    refine Opens.ext (Set.ext fun x => ⟨?_, fun hx => ⟨⟨x, ?_⟩, hx, rfl⟩⟩)
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · obtain ⟨z, -, rfl⟩ := h hx
      exact z.2
  have hle : P.ι ⁻¹ᵁ V ≤ W := by
    intro z hz
    obtain ⟨z', hz'W, hzz'⟩ := h hz
    exact (Subtype.ext hzz' : z' = z) ▸ hz'W
  set V' : P.toScheme.Opens := P.ι ⁻¹ᵁ V with hV'
  clear_value V'
  clear hV'
  cases himg
  have hb := bijective_smul_restrictAppIso L
    ((L.restrict P.ι).val.restrictₛₗ (homOfLE hle).op g.val)
    (g.property V' hle)
  rw [show (L.restrictAppIso P.ι V').hom
        ((L.restrict P.ι).val.restrictₛₗ (homOfLE hle).op g.val) =
      L.val.restrictₛₗ (homOfLE h).op ((L.restrictAppIso P.ι W).hom g.val) from ?_] at hb
  · exact hb
  · simp only [PresheafOfModules.restrictₛₗ_apply]
    exact Scheme.Modules.map_restrictAppIso_hom_apply P.ι L (homOfLE hle).op g.val

/-! ### Generating sections on a nonvanishing open -/

/-- **A global section generates an invertible module over its nonvanishing open.** This is the
trivialization clause of Stacks Tag 01CY in the shape `GeneratorSections` asks for: the content
is `Stacks.NonvanishingTrivialize.bijective_smul`, and the restriction of the global section to a
smaller open is its value there. -/
@[ega "II 6.5.3" "sufficiency"]
def generatorSectionsNonvanishingOpen {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (s : (toSheafOfModules X L).sections) :
    GeneratorSections X.toRingedSpace L
      (nonvanishingOpen X.toRingedSpace (toSheafOfModules X L) s) := by
  refine ⟨s.eval (op (nonvanishingOpen X.toRingedSpace (toSheafOfModules X L) s)),
    fun V h => ?_⟩
  rw [show L.val.restrictₛₗ (homOfLE h).op
      (s.eval (op (nonvanishingOpen X.toRingedSpace (toSheafOfModules X L) s))) =
      s.eval (op V) from s.property (homOfLE h).op]
  exact bijective_smul (L := toSheafOfModules X L) s (W := V) h

/-! ### Stacks Tag 0BUT, in the form the norm map needs -/

/-- **An invertible module on the source of a finite morphism is generated over the preimage of
an open neighbourhood of any point of the target.**

This is Stacks Tag 0BUT with its conclusion read as a generating section rather than as an
abstract triviality. On an affine open `U ∋ y` the preimage `B = f ⁻¹ᵁ U` is affine, hence
quasi-affine, and the fibre of `f ∣_ U` over `y` is finite because `f` is finite; Stacks Tag 0F20
produces a global section of `L|_B` whose nonvanishing open `W` contains that fibre, and over `W`
the section generates by Stacks Tag 01CY. The image `P = B.ι ''ᵁ W` therefore contains the whole
fibre `f ⁻¹ {y}`, and since a finite morphism is closed the set of points of `Y` all of whose
preimages lie in `P` is an open `V ∋ y` with `f ⁻¹ᵁ V ≤ P`. -/
theorem exists_generatorSections_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (L : X.Modules) [IsInvertibleModule X L] (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧ Nonempty (GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V)) := by
  classical
  obtain ⟨-, ⟨U, hUaff, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let UY : Y.Opens := U
  have hUaffY : IsAffineOpen UY := hUaff
  let B : X.Opens := f ⁻¹ᵁ UY
  have : IsAffine B.toScheme := hUaffY.preimage f
  let LB : B.toScheme.Modules := L.restrict B.ι
  let g : B.toScheme ⟶ UY.toScheme := f ∣_ UY
  let y' : UY.toScheme := ⟨y, hyU⟩
  obtain ⟨s, -, hEW, -⟩ :=
    Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite_sections
      (X := B.toScheme) LB (g.finite_preimage_singleton y') ⊤ (fun _ _ => trivial)
  set W : B.toScheme.Opens :=
    nonvanishingOpen B.toScheme.toRingedSpace (toSheafOfModules B.toScheme LB) s with hW
  -- A generating section of `L` over the image of `W`.
  let P : X.Opens := B.ι ''ᵁ W
  have hgen : GeneratorSections X.toRingedSpace L P :=
    generatorSectionsImage L (W := W) (hW ▸ generatorSectionsNonvanishingOpen LB s)
  -- The whole fibre over `y` lies in `P`.
  have hfib : f.base ⁻¹' {y} ⊆ (P : Set X) := by
    intro x hx
    have hxB : x ∈ B := by
      change f.base x ∈ UY
      rw [show f.base x = y from hx]
      exact hyU
    have hz : (⟨x, hxB⟩ : B.toScheme) ∈ g.base ⁻¹' {y'} := by
      refine Subtype.ext ?_
      rw [morphismRestrict_base_coe f UY ⟨x, hxB⟩]
      exact hx
    exact ⟨⟨x, hxB⟩, hEW hz, rfl⟩
  -- A finite morphism is closed, so the complement of the image of the complement of `P` is open.
  have hclosed : IsClosed (f.base '' (P : Set X)ᶜ) :=
    f.isClosedMap _ P.2.isClosed_compl
  refine ⟨⟨(f.base '' (P : Set X)ᶜ)ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨x, hxP, hxy⟩
    exact hxP (hfib hxy)
  · have hVP : f ⁻¹ᵁ (⟨(f.base '' (P : Set X)ᶜ)ᶜ, hclosed.isOpen_compl⟩ : Y.Opens) ≤ P := by
      intro x hx
      by_contra hxP
      exact hx ⟨x, hxP, rfl⟩
    exact ⟨generatorSectionsRestrict X.toRingedSpace L hVP hgen⟩

end Stacks.NormMapInvertible

end
