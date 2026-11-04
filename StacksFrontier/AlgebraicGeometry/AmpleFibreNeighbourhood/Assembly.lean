module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeAffineOpen
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# The assembly of Stacks Tag 0D2N from a morphism to projective space over the base

[Stacks, Tag 0D2N] says that an invertible module on a proper scheme over a Noetherian base,
ample on the fibre over a point `y`, is relatively ample over some open neighbourhood of `y`. The
proof produces a morphism `φ : X ⟶ ℙⁿ_Y` over `Y` with `ℒ ^⊗ d ≅ φ^* 𝒪(1)` whose fibres over the
fibre of `ℙⁿ_Y` at `y` are finite, and then runs the second half of the argument over a shrunken
base. This file is the passage from such a `φ` to the conclusion: everything of Tag 0D2N that
follows once `φ` exists.

## Main results

* `Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_morphismRestrict`: **the
  pending-free half of Tag 0D2N.** Given a proper `f : X ⟶ Y` onto a locally Noetherian base, an
  invertible `ℒ`, a factorization `f = φ ≫ (ℙⁿ_Y ↘ Y)` with `ℒ ^⊗ d ≅ φ^* 𝒪(1)` for some
  `d ≥ 1`, and a point `y` over which the set-theoretic fibres of `φ` are finite, there is an open
  `V ∋ y` with `ℒ|_{f⁻¹V}` ample relative to `f ∣_ V`.
* `Stacks.AmpleFibreNeighbourhood.restrictToProjectiveSpaceOver`: the restriction of `φ` to a
  morphism `f⁻¹V ⟶ ℙⁿ_V`, with its two compatibilities and its affineness.
* `Stacks.AmpleFibreNeighbourhood.restrictToProjectiveSpaceOverTwistIso`: the isomorphism
  `(ℒ|_{f⁻¹V}) ^⊗ d ≅ (φ|_V)^* 𝒪(1)` carried across that restriction.

## The route

The second half of Tag 0D2N is proved, as
`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_of_isAffineHom_toProjectiveSpaceOver`: an
invertible module a positive power of which is `𝒪(1)` pulled back along an **affine** morphism to
projective space over the base is relatively ample. What that statement wants is a morphism into
`ℙⁿ_V` for the *shrunken* base `V`, and what the fibre argument produces is a morphism into
`ℙⁿ_Y` that is finite only over the preimage of some `V`. The steps between them:

1. **Shrinking.** `Stacks.AmpleFibreNeighbourhood.exists_isFinite_morphismRestrict_preimage` —
   [Stacks, Tag 02OH] at every point of one fibre at once — produces the open `V ∋ y` together
   with finiteness of `φ ∣_ ((ℙⁿ_Y ↘ Y)⁻¹V)`. Its hypotheses are properness of `φ`, local
   Noetherianness of `ℙⁿ_Y` and universal closedness of `ℙⁿ_Y ⟶ Y`. Properness of `φ` is
   `AlgebraicGeometry.IsProper.of_comp` against separatedness of `ℙⁿ_Y ⟶ Y`, which comes free
   from the instance `AlgebraicGeometry.projectiveSpaceOver.isProper`; that instance also
   supplies the universal closedness, and
   `AlgebraicGeometry.projectiveSpaceOver_isLocallyNoetherian` the local Noetherianness.

2. **`(ℙⁿ_Y ↘ Y)⁻¹V ≅ ℙⁿ_V`, and `𝒪(1)` across it — both already in the library, and neither is built
   here.** The identification is
   `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.preimageProjectiveSpaceIso`, with
   its two compatibilities `preimageProjectiveSpaceIso_hom_comp_structureMorphism` (the structure
   morphism) and `preimageProjectiveSpaceIso_hom_comp_ι` (the morphism `ℙⁿ_V ⟶ ℙⁿ_Y`); both sides
   are pullbacks of `ℙⁿ_Y ⟶ Y` along `V ⟶ Y`, so the iso and its laws are
   `CategoryTheory.IsPullback.isoIsPullback` and its two projection laws. The twisting sheaf
   across the base-change morphism is
   `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverPullbackIso`, for an
   arbitrary morphism of base schemes and an arbitrary degree; at `d = 1` the twist is the
   hyperplane sheaf on the nose, by
   `Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver_one`, which is `rfl`. So this file
   consumes those four declarations and adds nothing in their place.

3. **The restriction of `φ` and of the given isomorphism.** `φ|_V` is `φ ∣_ ((ℙⁿ_Y ↘ Y)⁻¹V)`
   followed by the identification of step 2. It is affine because finite morphisms are affine
   (`AlgebraicGeometry.IsFinite` extends `AlgebraicGeometry.IsAffineHom`) and isomorphisms are;
   it lies over `V` by the first compatibility together with
   `AlgebraicGeometry.morphismRestrict_comp`; and the twist is carried across by the second
   compatibility, `twistOverPullbackIso`, and pseudofunctoriality of the module pullback
   (`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso` and `pullbackModuleCongr`), the power
   being moved through the open immersion by
   `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`. Every comparison here is assembled as a
   term rather than by rewriting: `rw` does not cross the `X.Modules` and
   `SheafOfModules X.ringCatSheaf` spellings.

## What this file does not do

**No `@[stacks 0D2N]` attribute is attached here**, although Tag 0D2N is now proved: it is
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre`
(`AmpleFibreNeighbourhood/RelativelyAmpleNeighbourhood.lean`), and this file is one step of its
proof rather than its conclusion.  What is taken as a hypothesis here is the *existence* of `φ`
— the first half of the source's proof, which lifts the sections defining the immersion
`X_y ⟶ ℙⁿ_{κ(y)}` to a neighbourhood using assertion (B) of [Stacks, Tag 0D2M], and which is
proved as `Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_fiberι_eq`
(`AmpleFibreNeighbourhood/FibreSectionLift.lean`) — together with the finiteness of its fibres.
That finiteness is in the point-set form that
`Stacks.AmpleFibreNeighbourhood.exists_isFinite_morphismRestrict_preimage` consumes; it is what
the source's "finite over the fibre" means, and it is discharged from an immersion of the fibre
by `Stacks.AmpleFibreNeighbourhood.subsingleton_preimage_of_fibreFactorization`.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.AmpleProjectiveImmersion
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-! ### Restricting a morphism to projective space over an open of the base -/

section Restrict

variable (n : ℕ) {X S : Scheme.{u}} (φ : X ⟶ projectiveSpaceOver n S) (V : S.Opens)

/-- **A morphism `X ⟶ ℙⁿ_S` restricts, over an open `V ⊆ S`, to a morphism into `ℙⁿ_V`.** It is
the restriction `φ ∣_ ((ℙⁿ_S ↘ S)⁻¹V)` followed by the identification
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.preimageProjectiveSpaceIso` of that
preimage with `ℙⁿ_V`. -/
def restrictToProjectiveSpaceOver :
    (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).toScheme ⟶ projectiveSpaceOver n V.toScheme :=
  φ ∣_ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V) ≫ (preimageProjectiveSpaceIso n V).hom

/-- `Stacks.AmpleFibreNeighbourhood.restrictToProjectiveSpaceOver` lies over `V`: its composite
with the structure morphism of `ℙⁿ_V` is the restriction of `φ ≫ (ℙⁿ_S ↘ S)`. -/
theorem restrictToProjectiveSpaceOver_over :
    restrictToProjectiveSpaceOver n φ V ≫
        (projectiveSpaceOver n V.toScheme ↘ V.toScheme) =
      (φ ≫ (projectiveSpaceOver n S ↘ S)) ∣_ V := by
  rw [restrictToProjectiveSpaceOver, Category.assoc,
    preimageProjectiveSpaceIso_hom_comp_structureMorphism, morphismRestrict_comp]

/-- `Stacks.AmpleFibreNeighbourhood.restrictToProjectiveSpaceOver` is `φ` itself once `ℙⁿ_V` is
pushed into `ℙⁿ_S`. This is the equation the hyperplane sheaf is transported along. -/
theorem restrictToProjectiveSpaceOver_comp_projectiveSpaceOverMap :
    restrictToProjectiveSpaceOver n φ V ≫ projectiveSpaceOverMap n V.ι =
      (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).ι ≫ φ := by
  rw [restrictToProjectiveSpaceOver, Category.assoc,
    preimageProjectiveSpaceIso_hom_comp_ι, morphismRestrict_ι]

/-- **If `φ` is affine over the preimage of `V` then its restriction into `ℙⁿ_V` is affine.** The
identification of `(ℙⁿ_S ↘ S)⁻¹V` with `ℙⁿ_V` is an isomorphism, and affine morphisms contain the
isomorphisms and are stable under composition. -/
theorem isAffineHom_restrictToProjectiveSpaceOver
    [IsAffineHom (φ ∣_ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V))] :
    IsAffineHom (restrictToProjectiveSpaceOver n φ V) := by
  show IsAffineHom (φ ∣_ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V) ≫
    (preimageProjectiveSpaceIso n V).hom)
  infer_instance

/-- **The hyperplane sheaf carried across the restriction of `φ`.** If `ℒ ^⊗ d ≅ φ^* 𝒪(1)` on
`X`, then `(ℒ|_{φ⁻¹(ℙⁿ_S ↘ S)⁻¹V}) ^⊗ d` is `𝒪(1)` on `ℙⁿ_V` pulled back along
`Stacks.AmpleFibreNeighbourhood.restrictToProjectiveSpaceOver`.

The power is moved through the open immersion by
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`; the given isomorphism is pulled back;
pseudofunctoriality (`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso` and
`pullbackModuleCongr`) rewrites the two pullbacks of `𝒪(1)` along the two sides of
`Stacks.AmpleFibreNeighbourhood.restrictToProjectiveSpaceOver_comp_projectiveSpaceOverMap`; and
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverPullbackIso` at `d = 1`
identifies `𝒪(1)` on `ℙⁿ_S` pulled back along `ℙⁿ_V ⟶ ℙⁿ_S` with `𝒪(1)` on `ℙⁿ_V`, the degree-one
twist being the hyperplane sheaf by `Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver_one`,
which is `rfl`. -/
def restrictToProjectiveSpaceOverTwistIso (d : ℕ) (L : X.Modules) [IsInvertibleModule X L]
    (e : tensorPowModule X L (d : ℤ) ≅ pullbackModule φ (projectiveSpaceTwistingSheaf n S)) :
    tensorPowModule (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).toScheme
        (pullbackModule (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).ι L) (d : ℤ) ≅
      pullbackModule (restrictToProjectiveSpaceOver n φ V)
        (projectiveSpaceTwistingSheaf n V.toScheme) :=
  (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso
      (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).ι L d).symm ≪≫
    (Scheme.Modules.pullback (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).ι).mapIso e ≪≫
    (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso
        (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).ι φ
        (projectiveSpaceTwistingSheaf n S)).symm ≪≫
    Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
      (restrictToProjectiveSpaceOver_comp_projectiveSpaceOverMap n φ V).symm
      (projectiveSpaceTwistingSheaf n S) ≪≫
    Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso (restrictToProjectiveSpaceOver n φ V)
      (projectiveSpaceOverMap n V.ι) (projectiveSpaceTwistingSheaf n S) ≪≫
    (Scheme.Modules.pullback (restrictToProjectiveSpaceOver n φ V)).mapIso
      (twistOverPullbackIso n V.ι 1)

end Restrict

/-! ### The pending-free half of Stacks Tag 0D2N -/

/-- **The assembly of [Stacks, Tag 0D2N] from a morphism to projective space over the base.** Let
`f : X ⟶ S` be proper with `S` locally Noetherian, let `ℒ` be an invertible `𝒪_X`-module, let `f`
factor as `φ : X ⟶ ℙⁿ_S` followed by the structure morphism with `ℒ ^⊗ d ≅ φ^* 𝒪(1)` for some
`d ≥ 1`, and let `y : S` be a point over which every set-theoretic fibre of `φ` is finite. Then
`y` has an open neighbourhood `V` over which `ℒ` is relatively ample: `ℒ|_{f⁻¹V}` is ample
relative to `f ∣_ V`.

This is everything of the proof of [Stacks, Tag 0D2N] after the morphism `φ` has been produced.
`Stacks.AmpleFibreNeighbourhood.exists_isFinite_morphismRestrict_preimage` — [Stacks, Tag 02OH]
along the whole fibre — shrinks the base to an open `V` over whose preimage `φ` is finite, hence
affine; `Stacks.AmpleFibreNeighbourhood.restrictToProjectiveSpaceOver` and
`Stacks.AmpleFibreNeighbourhood.restrictToProjectiveSpaceOverTwistIso` move `φ` and the
isomorphism over to `ℙⁿ_V`; and
`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_of_isAffineHom_toProjectiveSpaceOver` is the
conclusion. Properness of `φ` is `AlgebraicGeometry.IsProper.of_comp`, the structure morphism of
`ℙⁿ_S` being separated because it is proper.

**No `@[stacks 0D2N]` attribute is attached**: the construction of `φ` and the finiteness of its
fibres, which are the first half of the source's proof, are hypotheses here.  The tag itself is
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre`
(`AmpleFibreNeighbourhood/RelativelyAmpleNeighbourhood.lean`). -/
theorem exists_mem_isRelativelyAmple_morphismRestrict {X S : Scheme.{u}} {f : X ⟶ S}
    (L : X.Modules) [IsInvertibleModule X L] [IsProper f] [IsLocallyNoetherian S]
    {n d : ℕ} (hd : 1 ≤ d) (φ : X ⟶ projectiveSpaceOver n S)
    (hφ : φ ≫ (projectiveSpaceOver n S ↘ S) = f)
    (e : tensorPowModule X L (d : ℤ) ≅ pullbackModule φ (projectiveSpaceTwistingSheaf n S))
    (y : S)
    (hfin : ∀ z : projectiveSpaceOver n S, (projectiveSpaceOver n S ↘ S).base z = y →
      (φ ⁻¹' {z}).Finite) :
    ∃ V : S.Opens, y ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  subst hφ
  have : IsProper φ := IsProper.of_comp φ (projectiveSpaceOver n S ↘ S)
  have : IsLocallyNoetherian (projectiveSpaceOver n S) :=
    projectiveSpaceOver_isLocallyNoetherian n S
  obtain ⟨V, hyV, hfinite⟩ :=
    exists_isFinite_morphismRestrict_preimage φ (projectiveSpaceOver n S ↘ S) y hfin
  have := hfinite
  have : IsInvertibleModule (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).toScheme
      (pullbackModule (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).ι L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ L
  have : IsAffineHom (restrictToProjectiveSpaceOver n φ V) :=
    isAffineHom_restrictToProjectiveSpaceOver n φ V
  refine ⟨V, hyV, ?_⟩
  exact isRelativelyAmple_of_isAffineHom_toProjectiveSpaceOver
    (pullbackModule (φ ⁻¹ᵁ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)).ι L) hd
    (restrictToProjectiveSpaceOver n φ V) (restrictToProjectiveSpaceOver_over n φ V)
    (restrictToProjectiveSpaceOverTwistIso n φ V d L e)

end Stacks.AmpleFibreNeighbourhood

end
