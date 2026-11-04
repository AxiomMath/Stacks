module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion

/-!
# Composing relative flatness of a module, and descending it to the base

Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, let `F` be an `𝒪_X`-module
and let `x̄` be a geometric point of `X`, with image `ȳ` in `Y`.  Flatness of `F` at `x̄` over
`Y` is condition (2) of Stacks 05VU, flatness of the geometric stalk `F_{x̄}` over the étale
local ring `𝒪_{Y, ȳ}`, and flatness of `Y` at `ȳ` over `Z` is Stacks 03ML (2).  Stacks 05VX
has three parts:

1. if `F` is flat at `x̄` over `Y` and `Y` is flat at `ȳ` over `Z`, then `F` is flat at `x̄`
   over `Z`;
2. if `F` is flat at `x̄` over `Y`, the fibre `x̄^* F` is nonzero and `F` is flat at `x̄` over
   `Z`, then `Y` is flat at `ȳ` over `Z`;
3. if `F_{x̄}` is a faithfully flat `𝒪_{Y, ȳ}`-module and `F` is flat at `x̄` over `Z`, then
   `Y` is flat at `ȳ` over `Z`.

## Main definitions

* `AlgebraicGeometry.Space.IsFaithfullyFlatOverAtGeometricPoint`: faithful flatness of the
  geometric stalk `F_{x̄}` over the étale local ring `𝒪_{Y, ȳ}` of the target, the hypothesis
  of part (3).

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_comp`: part (1).
* `AlgebraicGeometry.Space.isFlatAt_of_nontrivial_fibre_of_isFlatOverAtGeometricPoint`:
  part (2).
* `AlgebraicGeometry.Space.isFlatAt_of_isFaithfullyFlatOverAtGeometricPoint`: part (3).

## Implementation notes

Through Stacks 05VU and Stacks 04NG all three parts are statements
about the homomorphisms of étale local rings
`𝒪_{Z, z̄} → 𝒪_{Y, ȳ} → 𝒪_{X, x̄}` of Stacks 04NG and the module `F_{x̄}` over the last of them:
part (1) is transitivity of flatness (Algebra 00HC), part (3) is flat permanence (Algebra 039V)
and part (2) reduces to part (3) because a flat module over a local ring with nonzero fibre is
faithfully flat (Algebra 00HP).  That the two homomorphisms compose to the one induced by
`X ⟶ Z` is `AlgebraicGeometry.Space.etaleLocalRingMap_comp`, and it is what makes the scalar
tower `𝒪_{Z, z̄} → 𝒪_{Y, ȳ} → F_{x̄}` hold.

The fibre `x̄^* F` of part (2) is the quotient `F_{x̄} ⧸ 𝔪_{x̄} F_{x̄}` by the maximal ideal of
`𝒪_{X, x̄}`: a geometric point of `X` is a representative of its image point with values in an
algebraically closed field, and the pullback of a quasi-coherent module along such a
representative is the fibre of its geometric stalk.  Passing from that fibre to the fibre over
`𝒪_{Y, ȳ}`, which is what Algebra 00HP asks about, uses only that the homomorphism
`𝒪_{Y, ȳ} → 𝒪_{X, x̄}` is local
(`AlgebraicGeometry.Space.isLocalHom_etaleLocalRingMap`).

No quasi-coherence hypothesis is needed: all three parts are statements about the geometric
stalk alone, and quasi-coherence enters only in identifying that stalk's fibre with a pullback
of `F`, which is not part of the formal statements.

## References

* [Stacks Project, Tag 05VX](https://stacks.math.columbia.edu/tag/05VX)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 039V](https://stacks.math.columbia.edu/tag/039V)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Faithful flatness of the geometric stalk `F_{x̄}` of an `𝒪_X`-module over the étale local
ring `𝒪_{Y, ȳ}` of the target at the image geometric point `ȳ = f ∘ x̄`, the scalars being
restricted along the canonical homomorphism of étale local rings of Stacks 04NG. -/
noncomputable def IsFaithfullyFlatOverAtGeometricPoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, m} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1) : Prop :=
  letI : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  Module.FaithfullyFlat (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
    (geometricModuleStalk B S hS X xbar F)

/-- For an `A'`-module `M` and ring maps `β : C →+* A`, `α : A →+* A'` with `γ = α ∘ β`, restrict
scalars of `M` along `α` and `γ`: flatness of `A` over `C` and of `M` over `A` give flatness of
`M` over `C`, and flatness of `M` over `C` and faithful flatness of `M` over `A` give flatness
of `A` over `C`. -/
private theorem flat_comp_and_flat_of_faithfullyFlat_compHom {C A A' : Type*} (M : Type*)
    [CommRing C] [CommRing A] [CommRing A'] [AddCommGroup M] [Module A' M] {β : C →+* A}
    {α : A →+* A'} {γ : C →+* A'} (h : γ = α.comp β) :
    letI : Algebra C A := β.toAlgebra
    letI : Module A M := Module.compHom M α
    letI : Module C M := Module.compHom M γ
    (Module.Flat C A → Module.Flat A M → Module.Flat C M) ∧
      (Module.Flat C M → Module.FaithfullyFlat A M → Module.Flat C A) := by
  let : Algebra C A := β.toAlgebra
  let : Module A M := Module.compHom M α
  let : Module C M := Module.compHom M γ
  have : IsScalarTower C A M := IsScalarTower.of_algebraMap_smul fun c n => by
    change α (β c) • n = γ c • n
    rw [h]
    rfl
  exact ⟨fun _ _ => Module.Flat.trans C A M, fun _ _ =>
    Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat M⟩

/-- If an `𝒪_X`-module `F` is flat at a geometric point `x̄` of `X` over `Y` and `Y` is flat
over `Z` at the image `ȳ` of `x̄`, then `F` is flat at `x̄` over `Z`.

Over the étale local rings this is transitivity of flatness: `F_{x̄}` is flat over `𝒪_{Y, ȳ}`
and `𝒪_{Y, ȳ}` is flat over `𝒪_{Z, z̄}`. -/
@[stacks 05VX "part (1): flatness of a module at a point composes with flatness of the base"]
theorem isFlatOverAtGeometricPoint_comp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Modules.{u, m} B S hS X.1 X.2)
    (xbar : GeometricPoint B S hS X.1)
    (hF : IsFlatOverAtGeometricPoint B S hS f F xbar)
    (hg : IsFlatAt B S hS g.hom (geometricPointMap f.hom xbar).image) :
    IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar := by
  exact (flat_comp_and_flat_of_faithfullyFlat_compHom _
    (etaleLocalRingMap_comp X.2 Y.2 f.hom g.hom xbar).symm).1
    ((isFlatAt_iff_etaleLocalRingMap_flat Y.2 Z.2 g.hom (geometricPointMap f.hom xbar)).mp hg) hF

/-- If the geometric stalk `F_{x̄}` of an `𝒪_X`-module at a geometric point `x̄` of `X` is a
faithfully flat module over the étale local ring `𝒪_{Y, ȳ}` of the image `ȳ` of `x̄`, and `F` is
flat at `x̄` over `Z`, then `Y` is flat over `Z` at `ȳ`.

Over the étale local rings this is flat permanence (Stacks 039V): `F_{x̄}` is flat over
`𝒪_{Z, z̄}` and faithfully flat over `𝒪_{Y, ȳ}`, hence `𝒪_{Y, ȳ}` is flat over `𝒪_{Z, z̄}`. -/
@[stacks 05VX "part (3): flatness of the base at a point descends from a faithfully flat
  geometric stalk"]
theorem isFlatAt_of_isFaithfullyFlatOverAtGeometricPoint {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Modules.{u, m} B S hS X.1 X.2)
    (xbar : GeometricPoint B S hS X.1)
    (hff : IsFaithfullyFlatOverAtGeometricPoint B S hS f F xbar)
    (hfg : IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar) :
    IsFlatAt B S hS g.hom (geometricPointMap f.hom xbar).image := by
  exact (isFlatAt_iff_etaleLocalRingMap_flat Y.2 Z.2 g.hom (geometricPointMap f.hom xbar)).mpr
    ((flat_comp_and_flat_of_faithfullyFlat_compHom _
      (etaleLocalRingMap_comp X.2 Y.2 f.hom g.hom xbar).symm).2 hfg hff)

/-- Let `F` be an `𝒪_X`-module and let `x̄` be a geometric point of `X` with image `ȳ` in `Y`.
If `F` is flat at `x̄` over `Y`, the fibre of `F` at `x̄` is nonzero and `F` is flat at `x̄` over
`Z`, then `Y` is flat over `Z` at `ȳ`.

The fibre of `F` at `x̄` is the quotient `F_{x̄} ⧸ 𝔪_{x̄} F_{x̄}` of the geometric stalk by the
maximal ideal of `𝒪_{X, x̄}`; it is the pullback `x̄^* F` of `F` along `x̄`, regarded as a
representative of its image point with values in an algebraically closed field.  Since
`𝒪_{Y, ȳ} → 𝒪_{X, x̄}` is a local homomorphism, nonvanishing of that fibre forces the fibre of
`F_{x̄}` over `𝒪_{Y, ȳ}` to be nonzero as well, so that `F_{x̄}` is a faithfully flat
`𝒪_{Y, ȳ}`-module (Stacks 00HP) and part (3) applies. -/
@[stacks 05VX "part (2): flatness of the base at a point descends from a module flat over
  both and with nonzero fibre at a representative of the point"]
theorem isFlatAt_of_nontrivial_fibre_of_isFlatOverAtGeometricPoint
    {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Modules.{u, m} B S hS X.1 X.2)
    (xbar : GeometricPoint B S hS X.1)
    (hf : IsFlatOverAtGeometricPoint B S hS f F xbar)
    (hfibre :
      letI := isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
      Nontrivial ((geometricModuleStalk B S hS X xbar F) ⧸
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)) •
          (⊤ : Submodule (etaleLocalRing B S hS X.1 xbar)
            (geometricModuleStalk B S hS X xbar F))))
    (hfg : IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar) :
    IsFlatAt B S hS g.hom (geometricPointMap f.hom xbar).image := by
  let ybar := geometricPointMap f.hom xbar
  let A := etaleLocalRing B S hS Y.1 ybar
  let A' := etaleLocalRing B S hS X.1 xbar
  let M := geometricModuleStalk B S hS X xbar F
  let α : A →+* A' := etaleLocalRingMap X.2 f.hom xbar
  let : IsLocalRing A := isLocalRing_etaleLocalRing B S hS Y.1 Y.2 ybar
  let : IsLocalRing A' := isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  let : Module A M := Module.compHom M α
  have hlocal : IsLocalHom α := isLocalHom_etaleLocalRingMap B S hS X.2 Y.2 f.hom xbar
  have hflat : Module.Flat A M := hf
  -- The fibre of `M` over `𝒪_{X, x̄}` is a quotient of its fibre over `𝒪_{Y, ȳ}`, so the
  -- latter is nonzero too.
  have hne' : (IsLocalRing.maximalIdeal A') • (⊤ : Submodule A' M) ≠ ⊤ := fun htop =>
    not_subsingleton_iff_nontrivial.mpr hfibre (Submodule.Quotient.subsingleton_iff.mpr htop)
  have hne : (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) ≠ ⊤ := by
    intro htop
    refine hne' (eq_top_iff.mpr fun n _ => ?_)
    have hn : n ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) := by
      rw [htop]; exact Submodule.mem_top
    refine Submodule.smul_induction_on hn (fun a ha p _ => ?_)
      (fun p q hp hq => Submodule.add_mem _ hp hq)
    show α a • p ∈ _
    exact Submodule.smul_mem_smul
      (IsLocalRing.map_maximalIdeal_le α (Ideal.mem_map_of_mem _ ha)) Submodule.mem_top
  have hff : IsFaithfullyFlatOverAtGeometricPoint B S hS f F xbar := by
    rw [show IsFaithfullyFlatOverAtGeometricPoint B S hS f F xbar =
      Module.FaithfullyFlat A M from rfl, Module.faithfullyFlat_iff]
    refine ⟨hflat, fun n hn => ?_⟩
    rw [IsLocalRing.eq_maximalIdeal hn]
    exact hne
  exact isFlatAt_of_isFaithfullyFlatOverAtGeometricPoint B S hS f g F xbar hff hfg

end AlgebraicGeometry.Space

end
