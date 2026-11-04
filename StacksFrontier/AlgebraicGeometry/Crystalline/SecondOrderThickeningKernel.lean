module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondExteriorPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningOrder
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre

/-!
# Quasi-coherence of the kernel of `𝒪_{T''} → 𝒪_{T'}`

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`.
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningOrder` presents the structure
sheaf `𝒪_{T''} = 𝒪_T ⊕ Ω ⊕ Ω ⊕ Ω²` of the second-order universal thickening as a square-zero
extension of the structure sheaf `𝒪_{T'} = 𝒪_T ⊕ Ω` of the first-order one, with kernel
`K = 0 ⊕ 0 ⊕ Ω ⊕ Ω²`.  This module builds `K` as a sheaf of `𝒪_{T'}`-modules on the realized
scheme `T'` and proves that it is quasi-coherent, which is the `quasicoherent` field of the
square-zero extension datum that realizes `T''` as a scheme over `T'`.

Additively `K` is `Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`, but its `𝒪_{T'}`-module structure is *twisted* by the
exterior product:
`(g, ω₁) · (ω₂, η) = (g ω₂, g η + ω₁ ∧ ω₂)`.
It is therefore not a module pulled back from `T`, and `Crystalline.dpSecondExteriorPower` being
quasi-coherent does not by itself settle the question.  What settles it is that `K` is an
*extension*: the twisted multiplication kills the second coordinate of the scalar on the
subsheaf `0 ⊕ Ω²` and on the quotient `Ω`, so

`0 ⟶ i_* Ω²_{T/Y,δ} ⟶ K ⟶ i_* Ω_{T/Y,δ} ⟶ 0`

is a short exact sequence of `𝒪_{T'}`-modules whose outer terms are direct images along the
closed immersion `i : T ⟶ T'` of quasi-coherent modules, and quasi-coherent modules on a scheme
are closed under extensions.

## Main definitions

* `Crystalline.SecondOrderKer` — the sections of `K` over an open, with the twisted
  `𝒪_{T'}`-module structure.
* `Crystalline.secondOrderKerSheaf` — `K` as a sheaf of `𝒪_{T'}`-modules on `T'`.
* `Crystalline.secondOrderKerSub` and `Crystalline.secondOrderKerQuot` — the direct images
  `i_* Ω²_{T/Y,δ}` and `i_* Ω_{T/Y,δ}` along `i : T ⟶ T'`, the outer terms of the extension.
* `Crystalline.secondOrderKerι` and `Crystalline.secondOrderKerπ` — the two morphisms of the
  extension, `η ↦ (0, η)` and `(ω, η) ↦ ω`.
* `Crystalline.secondOrderKerShortComplex` — the extension as a short complex.

## Main results

* `Crystalline.secondOrderKerShortComplex_shortExact` — the extension is short exact, proved on
  sections: the inclusion is injective, a section with vanishing first coordinate is in its
  image, and the projection is surjective.
* `Crystalline.secondOrderKerSheaf_isQuasicoherent` — **`K` is a quasi-coherent
  `𝒪_{T'}`-module.**
* `Crystalline.secondOrderKerSmul_coords` and the `simp` lemmas around it — the twisted scalar
  multiplication, read on coordinates.

## What is and is not proved

This module supplies the second of the three inputs named in the "What is and is not proved"
note of `StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningOrder`, and nothing
else; no `stacks` attribute is claimed, because quasi-coherence of `K` is an input to a clause
of [Stacks, Tag 07J3] rather than one of its assertions.

**The outer terms are direct images, not modules on `T`.**  `Crystalline.secondOrderKerSub` is
`(Scheme.Modules.pushforward i).obj (dpSecondExteriorPower T Y f)`, whose sections over an open
are the sections of `Ω²_{T/Y,δ}` there with `𝒪_{T'}` acting through its first coordinate.  Its
quasi-coherence is [Stacks, Tag 02KG] — direct image along an affine morphism preserves
quasi-coherence, and a closed immersion is affine — applied to
`Crystalline.dpSecondExteriorPower_isQuasicoherent` [Stacks, Tag 07IY and Tag 01CG].  The same
for `Crystalline.secondOrderKerQuot` and `Crystalline.dpDifferentialsSheaf_isQuasicoherent`.

**The extension is not split.**  There is no `𝒪_{T'}`-linear splitting of
`Crystalline.secondOrderKerπ`: a candidate `ω ↦ (ω, c ω)` would have to satisfy
`c (g ω) = g · c ω + ω₁ ∧ ω` for every second coordinate `ω₁` of a scalar, which forces
`ω₁ ∧ ω = 0`.  So the extension-closure of quasi-coherence
(`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_X₂_of_shortExact`, part of the
weak Serre subcategory structure of [Stacks, Tag 0754]) is used in an essential way, and not as
a convenience over a direct-sum decomposition.

**The third input is untouched.**  Nothing here bears on the scheme-level order of the
thickening `T → T''`.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01IE](https://stacks.math.columbia.edu/tag/01IE)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-! ### The sections of the kernel -/

/-- **The sections of the kernel `K` of `𝒪_{T''} → 𝒪_{T'}` over an open.**  A pair consisting of
a divided power differential and a divided power two-form — the third and fourth coordinates of a
section of `𝒪_{T''}` whose first two vanish.  The two coordinates are kept in a structure so
that the twisted `𝒪_{T'}`-module structure of `Crystalline.secondOrderKerModule` does not compete
with the componentwise one on the product. -/
public structure SecondOrderKer (W : (Opens ↑T.scheme)ᵒᵖ) where
  /-- The two coordinates of a section of the kernel. -/
  coords : ↑((dpDifferentialsModules T Y f).obj W) ×
    ↑((dpSecondExteriorModules T Y f).obj W)

section Coords

variable {T Y f}

/-- The first coordinate of the unit section of `𝒪_{T'}`, in the spelling the kernel's scalars
use. -/
@[simp] private theorem firstOrderFst_one (W : (Opens ↑T.scheme)ᵒᵖ) :
    sqZeroExtFst (1 : ↑((firstOrderThickeningPresheaf T Y f).obj W)) = 1 := rfl

/-- The second coordinate of the unit section of `𝒪_{T'}`. -/
@[simp] private theorem firstOrderSnd_one (W : (Opens ↑T.scheme)ᵒᵖ) :
    sqZeroExtSnd (1 : ↑((firstOrderThickeningPresheaf T Y f).obj W)) = 0 := rfl

/-- The first coordinate of the zero section of `𝒪_{T'}`. -/
@[simp] private theorem firstOrderFst_zero (W : (Opens ↑T.scheme)ᵒᵖ) :
    sqZeroExtFst (0 : ↑((firstOrderThickeningPresheaf T Y f).obj W)) = 0 := rfl

/-- The second coordinate of the zero section of `𝒪_{T'}`. -/
@[simp] private theorem firstOrderSnd_zero (W : (Opens ↑T.scheme)ᵒᵖ) :
    sqZeroExtSnd (0 : ↑((firstOrderThickeningPresheaf T Y f).obj W)) = 0 := rfl

/-- The first coordinate of a sum of sections of `𝒪_{T'}`. -/
@[simp] private theorem firstOrderFst_add {W : (Opens ↑T.scheme)ᵒᵖ}
    (c d : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    sqZeroExtFst (c + d) = sqZeroExtFst c + sqZeroExtFst d := rfl

/-- The second coordinate of a sum of sections of `𝒪_{T'}`. -/
@[simp] private theorem firstOrderSnd_add {W : (Opens ↑T.scheme)ᵒᵖ}
    (c d : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    sqZeroExtSnd (c + d) = sqZeroExtSnd c + sqZeroExtSnd d := rfl

/-- The first coordinate of a product of sections of `𝒪_{T'}`. -/
@[simp] private theorem firstOrderFst_mul {W : (Opens ↑T.scheme)ᵒᵖ}
    (c d : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    sqZeroExtFst (c * d) = sqZeroExtFst c * sqZeroExtFst d := rfl

/-- The second coordinate of a product of sections of `𝒪_{T'}`, by the Leibniz rule of the
square-zero multiplication. -/
@[simp] private theorem firstOrderSnd_mul {W : (Opens ↑T.scheme)ᵒᵖ}
    (c d : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    sqZeroExtSnd (c * d) =
      sqZeroExtFst c • sqZeroExtSnd d + sqZeroExtFst d • sqZeroExtSnd c := rfl

/-- The first coordinate of a restricted section of `𝒪_{T'}`. -/
@[simp] private theorem firstOrderFst_map {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (c : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    sqZeroExtFst (((firstOrderThickeningPresheaf T Y f).map i).hom c) =
      (T.scheme.sheaf.obj.map i).hom (sqZeroExtFst c) := rfl

/-- The second coordinate of a restricted section of `𝒪_{T'}`. -/
@[simp] private theorem firstOrderSnd_map {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (c : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    sqZeroExtSnd (((firstOrderThickeningPresheaf T Y f).map i).hom c) =
      (dpDifferentialsModules T Y f).map i (sqZeroExtSnd c) := rfl

/-- A section of the kernel is its pair of coordinates. -/
public def SecondOrderKer.equiv (W : (Opens ↑T.scheme)ᵒᵖ) :
    SecondOrderKer T Y f W ≃ ↑((dpDifferentialsModules T Y f).obj W) ×
      ↑((dpSecondExteriorModules T Y f).obj W) where
  toFun := SecondOrderKer.coords
  invFun := SecondOrderKer.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- The additive group structure on the sections of the kernel, transported from the product
of its two coordinates. -/
public instance (W : (Opens ↑T.scheme)ᵒᵖ) : AddCommGroup (SecondOrderKer T Y f W) :=
  Equiv.addCommGroup (SecondOrderKer.equiv W)

/-- The section of the kernel with the given two coordinates. -/
public def secondOrderKerMk {W : (Opens ↑T.scheme)ᵒᵖ}
    (ω : ↑((dpDifferentialsModules T Y f).obj W))
    (η : ↑((dpSecondExteriorModules T Y f).obj W)) : SecondOrderKer T Y f W := ⟨(ω, η)⟩

/-- The differential coordinate of a section of the kernel. -/
public def secondOrderKerFst {W : (Opens ↑T.scheme)ᵒᵖ} (x : SecondOrderKer T Y f W) :
    ↑((dpDifferentialsModules T Y f).obj W) := x.coords.1

/-- The two-form coordinate of a section of the kernel. -/
public def secondOrderKerSnd {W : (Opens ↑T.scheme)ᵒᵖ} (x : SecondOrderKer T Y f W) :
    ↑((dpSecondExteriorModules T Y f).obj W) := x.coords.2

/-- The differential coordinate of `secondOrderKerMk ω η` is `ω`. -/
@[simp] public theorem secondOrderKerFst_mk {W : (Opens ↑T.scheme)ᵒᵖ}
    (ω : ↑((dpDifferentialsModules T Y f).obj W))
    (η : ↑((dpSecondExteriorModules T Y f).obj W)) :
    secondOrderKerFst (secondOrderKerMk (T := T) (Y := Y) (f := f) ω η) = ω := rfl

/-- The two-form coordinate of `secondOrderKerMk ω η` is `η`. -/
@[simp] public theorem secondOrderKerSnd_mk {W : (Opens ↑T.scheme)ᵒᵖ}
    (ω : ↑((dpDifferentialsModules T Y f).obj W))
    (η : ↑((dpSecondExteriorModules T Y f).obj W)) :
    secondOrderKerSnd (secondOrderKerMk (T := T) (Y := Y) (f := f) ω η) = η := rfl

/-- Two sections of the kernel with the same coordinates are equal. -/
public theorem secondOrderKer_ext {W : (Opens ↑T.scheme)ᵒᵖ} {x y : SecondOrderKer T Y f W}
    (h₁ : secondOrderKerFst x = secondOrderKerFst y)
    (h₂ : secondOrderKerSnd x = secondOrderKerSnd y) : x = y :=
  (SecondOrderKer.equiv W).injective (Prod.ext h₁ h₂)

/-- The differential coordinate is additive. -/
@[simp] public theorem secondOrderKerFst_add {W : (Opens ↑T.scheme)ᵒᵖ}
    (x y : SecondOrderKer T Y f W) :
    secondOrderKerFst (x + y) = secondOrderKerFst x + secondOrderKerFst y := rfl

/-- The two-form coordinate is additive. -/
@[simp] public theorem secondOrderKerSnd_add {W : (Opens ↑T.scheme)ᵒᵖ}
    (x y : SecondOrderKer T Y f W) :
    secondOrderKerSnd (x + y) = secondOrderKerSnd x + secondOrderKerSnd y := rfl

/-- The differential coordinate of `0` is `0`. -/
@[simp] public theorem secondOrderKerFst_zero {W : (Opens ↑T.scheme)ᵒᵖ} :
    secondOrderKerFst (0 : SecondOrderKer T Y f W) = 0 := rfl

/-- The two-form coordinate of `0` is `0`. -/
@[simp] public theorem secondOrderKerSnd_zero {W : (Opens ↑T.scheme)ᵒᵖ} :
    secondOrderKerSnd (0 : SecondOrderKer T Y f W) = 0 := rfl

/-- **The twisted scalar multiplication on the kernel.**  A scalar `(g, ω₁)` acts on `(ω₂, η)` by
`(g ω₂, g η + ω₁ ∧ ω₂)`; the correction term is the exterior product of the differential
coordinate of the scalar with the differential coordinate of the section, which is what the
multiplication of `𝒪_{T''}` produces in the top coordinate. -/
public instance (W : (Opens ↑T.scheme)ᵒᵖ) :
    SMul ↑((firstOrderThickeningPresheaf T Y f).obj W) (SecondOrderKer T Y f W) :=
  ⟨fun c x => secondOrderKerMk (sqZeroExtFst c • secondOrderKerFst x)
    (sqZeroExtFst c • secondOrderKerSnd x +
      bilinearApp (dpWedge T Y f) W (sqZeroExtSnd c) (secondOrderKerFst x))⟩

/-- The differential coordinate of `c • x` is `g ω₂` for `c = (g, ω₁)` and `x = (ω₂, η)`. -/
@[simp] public theorem secondOrderKerFst_smul {W : (Opens ↑T.scheme)ᵒᵖ}
    (c : ↑((firstOrderThickeningPresheaf T Y f).obj W)) (x : SecondOrderKer T Y f W) :
    secondOrderKerFst (c • x) = sqZeroExtFst c • secondOrderKerFst x := rfl

/-- The two-form coordinate of `c • x` is the twisted one: `g η + ω₁ ∧ ω₂` for `c = (g, ω₁)` and
`x = (ω₂, η)`. -/
@[simp] public theorem secondOrderKerSnd_smul {W : (Opens ↑T.scheme)ᵒᵖ}
    (c : ↑((firstOrderThickeningPresheaf T Y f).obj W)) (x : SecondOrderKer T Y f W) :
    secondOrderKerSnd (c • x) = sqZeroExtFst c • secondOrderKerSnd x +
      bilinearApp (dpWedge T Y f) W (sqZeroExtSnd c) (secondOrderKerFst x) := rfl

/-- **The kernel is an `𝒪_{T'}`-module for the twisted multiplication.**  Associativity is the
Leibniz rule for the square-zero multiplication of `𝒪_{T'}` together with bilinearity of the
exterior product, and unitality holds because the unit of `𝒪_{T'}` has vanishing differential
coordinate. -/
public instance secondOrderKerModule (W : (Opens ↑T.scheme)ᵒᵖ) :
    Module ↑((firstOrderThickeningPresheaf T Y f).obj W) (SecondOrderKer T Y f W) where
  one_smul x := by
    refine secondOrderKer_ext ?_ ?_ <;>
      simp only [secondOrderKerFst_smul, secondOrderKerSnd_smul, firstOrderFst_one,
        firstOrderSnd_one, one_smul, bilinearApp_zero_left, add_zero]
  mul_smul c d x := by
    refine secondOrderKer_ext ?_ ?_
    · simp only [secondOrderKerFst_smul, firstOrderFst_mul, mul_smul]
    · simp only [secondOrderKerFst_smul, secondOrderKerSnd_smul, firstOrderFst_mul,
        firstOrderSnd_mul, mul_smul, bilinearApp_add_left, bilinearApp_smul_left,
        bilinearApp_smul_right, smul_add]
      abel
  smul_zero c := by
    refine secondOrderKer_ext ?_ ?_ <;>
      simp only [secondOrderKerFst_smul, secondOrderKerSnd_smul, secondOrderKerFst_zero,
        secondOrderKerSnd_zero, smul_zero, bilinearApp_zero_right, add_zero]
  smul_add c x y := by
    refine secondOrderKer_ext ?_ ?_
    · simp only [secondOrderKerFst_smul, secondOrderKerFst_add, smul_add]
    · simp only [secondOrderKerSnd_smul, secondOrderKerFst_add, secondOrderKerSnd_add,
        smul_add, bilinearApp_add_right]
      abel
  add_smul c d x := by
    refine secondOrderKer_ext ?_ ?_
    · simp only [secondOrderKerFst_smul, secondOrderKerFst_add, firstOrderFst_add, add_smul]
    · simp only [secondOrderKerSnd_smul, secondOrderKerSnd_add, firstOrderFst_add,
        firstOrderSnd_add, add_smul, bilinearApp_add_left]
      abel
  zero_smul x := by
    refine secondOrderKer_ext ?_ ?_ <;>
      simp only [secondOrderKerFst_smul, secondOrderKerSnd_smul, secondOrderKerFst_zero,
        secondOrderKerSnd_zero, firstOrderFst_zero, firstOrderSnd_zero, zero_smul,
        bilinearApp_zero_left, add_zero]

/-- **The restriction map of the kernel**: restrict both coordinates. -/
public def secondOrderKerRestrict {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W') :
    SecondOrderKer T Y f W →+ SecondOrderKer T Y f W' :=
  AddMonoidHom.mk'
    (fun x => secondOrderKerMk ((dpDifferentialsModules T Y f).map i (secondOrderKerFst x))
      ((dpSecondExteriorModules T Y f).map i (secondOrderKerSnd x)))
    (fun _ _ => secondOrderKer_ext (map_add _ _ _) (map_add _ _ _))

/-- The differential coordinate of a restricted section is the restricted coordinate. -/
@[simp] public theorem secondOrderKerFst_restrict {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (x : SecondOrderKer T Y f W) :
    secondOrderKerFst (secondOrderKerRestrict i x) =
      (dpDifferentialsModules T Y f).map i (secondOrderKerFst x) := rfl

/-- The two-form coordinate of a restricted section is the restricted coordinate. -/
@[simp] public theorem secondOrderKerSnd_restrict {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (x : SecondOrderKer T Y f W) :
    secondOrderKerSnd (secondOrderKerRestrict i x) =
      (dpSecondExteriorModules T Y f).map i (secondOrderKerSnd x) := rfl

/-- **The restriction maps of the kernel are semilinear** for the twisted multiplication, the
exterior product commuting with restriction. -/
public theorem secondOrderKerRestrict_smul {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (c : ↑((firstOrderThickeningPresheaf T Y f).obj W)) (x : SecondOrderKer T Y f W) :
    secondOrderKerRestrict i (c • x) =
      ((firstOrderThickeningPresheaf T Y f).map i).hom c • secondOrderKerRestrict i x := by
  refine secondOrderKer_ext ?_ ?_
  · rw [secondOrderKerFst_restrict, secondOrderKerFst_smul, secondOrderKerFst_smul,
      secondOrderKerFst_restrict, firstOrderFst_map]
    exact (dpDifferentialsModules T Y f).map_smul i (sqZeroExtFst c) (secondOrderKerFst x)
  · rw [secondOrderKerSnd_restrict, secondOrderKerSnd_smul, secondOrderKerSnd_smul,
      secondOrderKerSnd_restrict, secondOrderKerFst_restrict, firstOrderFst_map,
      firstOrderSnd_map, map_add]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact (dpSecondExteriorModules T Y f).map_smul i (sqZeroExtFst c) (secondOrderKerSnd x)
    · exact (dpWedge T Y f).naturality i (sqZeroExtSnd c) (secondOrderKerFst x)

end Coords

/-! ### The kernel as a sheaf of modules on `T'` -/

/-- The kernel as a presheaf of abelian groups on the space of `T'`, which is the space of
`T`. -/
public def secondOrderKerAbPresheaf :
    (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ ⥤ Ab.{u} where
  obj W := AddCommGrpCat.of (SecondOrderKer T Y f (firstOrderThickeningOpen T Y f W))
  map i := AddCommGrpCat.ofHom (secondOrderKerRestrict i)
  map_id W := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => secondOrderKer_ext ?_ ?_)
    · exact PresheafOfModules.map_id_apply (dpDifferentialsModules T Y f) _ _
    · exact PresheafOfModules.map_id_apply (dpSecondExteriorModules T Y f) _ _
  map_comp i j := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => secondOrderKer_ext ?_ ?_)
    · exact map_comp_apply _ i j _
    · exact map_comp_apply _ i j _

/-- The twisted module structure on the sections of the kernel, named so that instance
resolution finds it through the definition of `Crystalline.secondOrderKerAbPresheaf`. -/
public instance secondOrderKerAbModule (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) :
    Module ↑((firstOrderThickeningScheme T Y f).ringCatSheaf.obj.obj W)
      ↑((secondOrderKerAbPresheaf T Y f).obj W) :=
  inferInstanceAs (Module ↑((firstOrderThickeningPresheaf T Y f).obj
      (firstOrderThickeningOpen T Y f W))
    (SecondOrderKer T Y f (firstOrderThickeningOpen T Y f W)))

/-- **The kernel as a presheaf of `𝒪_{T'}`-modules.** -/
public def secondOrderKerModules :
    (firstOrderThickeningScheme T Y f).PresheafOfModules :=
  PresheafOfModules.ofPresheaf (secondOrderKerAbPresheaf T Y f)
    (fun _ _ i c x => secondOrderKerRestrict_smul i c x)

/-- **The kernel is a sheaf**, because additively it is the product of the two sheaves
`Ω_{T/Y,δ}` and `Ω²_{T/Y,δ}`: a compatible family of sections glues coordinatewise. -/
public theorem isSheaf_secondOrderKerAbPresheaf :
    TopCat.Presheaf.IsSheaf (secondOrderKerAbPresheaf T Y f) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have h₁ : TopCat.Presheaf.IsCompatible (dpDifferentialsModules T Y f).presheaf U
      (fun i => secondOrderKerFst (sf i)) := fun i j => congrArg secondOrderKerFst (hsf i j)
  have h₂ : TopCat.Presheaf.IsCompatible (dpSecondExteriorModules T Y f).presheaf U
      (fun i => secondOrderKerSnd (sf i)) := fun i j => congrArg secondOrderKerSnd (hsf i j)
  obtain ⟨ω, hω, hωU⟩ := (dpDifferentialsSheaf T Y f).isSheaf.isSheafUniqueGluing U _ h₁
  obtain ⟨η, hη, hηU⟩ := (dpSecondExteriorPower T Y f).isSheaf.isSheafUniqueGluing U _ h₂
  exact ⟨secondOrderKerMk ω η, fun i => secondOrderKer_ext (hω i) (hη i), fun s hs =>
    secondOrderKer_ext (hωU _ fun i => congrArg secondOrderKerFst (hs i))
      (hηU _ fun i => congrArg secondOrderKerSnd (hs i))⟩

/-- **The kernel `K = 0 ⊕ 0 ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}` of `𝒪_{T''} → 𝒪_{T'}`, as a sheaf of
`𝒪_{T'}`-modules on the scheme `T'`.** -/
public def secondOrderKerSheaf : (firstOrderThickeningScheme T Y f).Modules :=
  ⟨secondOrderKerModules T Y f, isSheaf_secondOrderKerAbPresheaf T Y f⟩

/-- The sections of `secondOrderKerSheaf` over `W` are the sections of the kernel over the
corresponding open of `T`. -/
@[simp] public theorem secondOrderKerSheaf_val_obj
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) :
    (↑((secondOrderKerSheaf T Y f).val.obj W) : Type u) =
      SecondOrderKer T Y f (firstOrderThickeningOpen T Y f W) := rfl

/-! ### The two outer terms of the extension -/

/-- **`i_* Ω²_{T/Y,δ}`**, the direct image of the second exterior power along the immersion
`i : T ⟶ T'`: the sections of `Ω²_{T/Y,δ}` with `𝒪_{T'}` acting through its first coordinate.
This is the subsheaf `0 ⊕ Ω²` of the kernel. -/
public abbrev secondOrderKerSub : (firstOrderThickeningScheme T Y f).Modules :=
  (Scheme.Modules.pushforward (firstOrderThickeningι T Y f)).obj (dpSecondExteriorPower T Y f)

/-- **`i_* Ω_{T/Y,δ}`**, the direct image of the divided power differentials along the immersion
`i : T ⟶ T'`.  This is the quotient of the kernel by `Crystalline.secondOrderKerSub`. -/
public abbrev secondOrderKerQuot : (firstOrderThickeningScheme T Y f).Modules :=
  (Scheme.Modules.pushforward (firstOrderThickeningι T Y f)).obj (dpDifferentialsSheaf T Y f)

/-- **`i_* Ω²_{T/Y,δ}` is quasi-coherent**: `Ω²_{T/Y,δ}` is, and direct image along the closed
immersion `i`, which is an affine morphism, preserves quasi-coherence [Stacks, Tag 02KG]. -/
public instance secondOrderKerSub_isQuasicoherent :
    (secondOrderKerSub T Y f).IsQuasicoherent := inferInstance

/-- **`i_* Ω_{T/Y,δ}` is quasi-coherent**, by [Stacks, Tag 07IY] and [Stacks, Tag 02KG]. -/
public instance secondOrderKerQuot_isQuasicoherent :
    (secondOrderKerQuot T Y f).IsQuasicoherent := inferInstance

/-! ### The extension -/

/-- The inclusion `η ↦ (0, η)` of the subsheaf into the kernel, on presheaves of abelian
groups. -/
public def secondOrderKerιAb :
    (secondOrderKerSub T Y f).val.presheaf ⟶ (secondOrderKerSheaf T Y f).val.presheaf where
  app _ := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun η => secondOrderKerMk (T := T) (Y := Y) (f := f) 0 η)
    (fun _ _ => secondOrderKer_ext (add_zero (0 : _)).symm rfl))
  naturality _ _ _ := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ =>
    secondOrderKer_ext (map_zero _).symm rfl)

/-- The inclusion `η ↦ (0, η)`, read on sections. -/
@[simp] public theorem secondOrderKerιAb_app
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ)
    (η : ↑((secondOrderKerSub T Y f).val.presheaf.obj W)) :
    (secondOrderKerιAb T Y f).app W η =
      secondOrderKerMk (T := T) (Y := Y) (f := f)
        (W := firstOrderThickeningOpen T Y f W) 0 η := rfl

/-- **The inclusion `i_* Ω² ⟶ K`, `η ↦ (0, η)`**, as a morphism of sheaves of `𝒪_{T'}`-modules.
It is linear because the twist `ω₁ ∧ ω₂` vanishes when the differential coordinate `ω₂` does. -/
public def secondOrderKerι : secondOrderKerSub T Y f ⟶ secondOrderKerSheaf T Y f where
  val := PresheafOfModules.homMk (secondOrderKerιAb T Y f) (fun _ _ _ =>
    secondOrderKer_ext (smul_zero _).symm (left_eq_add.mpr (bilinearApp_zero_right _)))

/-- The projection `(ω, η) ↦ ω` of the kernel onto the quotient, on presheaves of abelian
groups. -/
public def secondOrderKerπAb :
    (secondOrderKerSheaf T Y f).val.presheaf ⟶ (secondOrderKerQuot T Y f).val.presheaf where
  app _ := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun x => secondOrderKerFst (T := T) (Y := Y) (f := f) x) (fun _ _ => rfl))
  naturality _ _ _ := rfl

/-- The projection `(ω, η) ↦ ω`, read on sections. -/
@[simp] public theorem secondOrderKerπAb_app
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ)
    (x : SecondOrderKer T Y f (firstOrderThickeningOpen T Y f W)) :
    (secondOrderKerπAb T Y f).app W x = secondOrderKerFst x := rfl

/-- **The projection `K ⟶ i_* Ω`, `(ω, η) ↦ ω`**, as a morphism of sheaves of `𝒪_{T'}`-modules.
It is linear because the twist affects only the two-form coordinate. -/
public def secondOrderKerπ : secondOrderKerSheaf T Y f ⟶ secondOrderKerQuot T Y f where
  val := PresheafOfModules.homMk (secondOrderKerπAb T Y f) (fun _ _ _ => rfl)

/-- The composite of the inclusion and the projection vanishes: a section of the subsheaf has
vanishing differential coordinate. -/
public theorem secondOrderKerι_comp_π :
    secondOrderKerι T Y f ≫ secondOrderKerπ T Y f = 0 := by
  apply (SheafOfModules.forget _).map_injective
  apply (PresheafOfModules.toPresheaf _).map_injective
  ext W η
  rfl

/-- **The extension `0 ⟶ i_* Ω² ⟶ K ⟶ i_* Ω ⟶ 0`**, as a short complex of `𝒪_{T'}`-modules. -/
public abbrev secondOrderKerShortComplex :
    ShortComplex (firstOrderThickeningScheme T Y f).Modules :=
  ShortComplex.mk (secondOrderKerι T Y f) (secondOrderKerπ T Y f) (secondOrderKerι_comp_π T Y f)

/-- **The extension is short exact**, verified on sections over every open: `η ↦ (0, η)` is
injective, a section with vanishing differential coordinate is `(0, η)`, and `(ω, η) ↦ ω` is
surjective. -/
public theorem secondOrderKerShortComplex_shortExact :
    (secondOrderKerShortComplex T Y f).ShortExact :=
  SheafOfModules.shortExact_of_sectionwise' (secondOrderKerShortComplex T Y f)
    (fun _ _ _ h => congrArg secondOrderKerSnd h)
    (fun _ x hx => ⟨secondOrderKerSnd x, secondOrderKer_ext hx.symm rfl⟩)
    (fun W ω => ⟨secondOrderKerMk (T := T) (Y := Y) (f := f) (W := W) ω 0, rfl⟩)

/-- **The kernel of `𝒪_{T''} → 𝒪_{T'}` is a quasi-coherent `𝒪_{T'}`-module.**  It is an
extension of `i_* Ω_{T/Y,δ}` by `i_* Ω²_{T/Y,δ}`, both quasi-coherent, and quasi-coherent modules
on a scheme are closed under extensions [Stacks, Tag 01IE and Tag 0754].  This is the
`quasicoherent` field of the square-zero extension datum presenting `T''` over `T'`. -/
public theorem secondOrderKerSheaf_isQuasicoherent :
    (secondOrderKerSheaf T Y f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_X₂_of_shortExact
    (secondOrderKerShortComplex_shortExact T Y f)
    (secondOrderKerSub_isQuasicoherent T Y f) (secondOrderKerQuot_isQuasicoherent T Y f)

end Crystalline

end
