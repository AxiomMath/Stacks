module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPolesLeibnizSections
public import StacksFrontier.AlgebraicGeometry.Flatness.StalkIdealSheaf

/-!
# Local equations of an effective Cartier divisor from trivializations of its ideal sheaf

Let `Y ⊆ X` be the closed subscheme cut out by `I : X.IdealSheafData`, with ideal sheaf
`ℐ = Stacks.Divisors.negativeTwist I`. A sectionwise trivialization of `ℐ` over an open `U`
(`Stacks.SheafDescent.Trivialization`) is an `𝒪_X(W)`-linear isomorphism `θ_W : ℐ(W) ≅ 𝒪_X(W)`
for every open `W ≤ U`, compatible with restriction. Its basis element `b = θ_U⁻¹(1)` maps to a
section `t ∈ 𝒪_X(U)`, the **local equation** of `Y` on `U` attached to the trivialization.

This file records what the rest of the construction of the de Rham complex of log poles uses
about such a local equation:

* every local section `a` of `ℐ` over `W ≤ U` is `θ_W(a) · t` in `𝒪_X(W)`, with no gluing:
  `Stacks.Divisors.IdealTrivialization.negativeTwistSection_eq_mul`;
* two local equations differ by a unit on the intersection of their opens:
  `Stacks.Divisors.IdealTrivialization.equationAt_eq_mul_unit`;
* at a point `y` of `Y` the germ of `t` generates the kernel of `𝒪_{X, y} → 𝒪_{Y, y}`, so `t` is
  a local equation in the sense of [Stacks, Tag 0FMV]:
  `Stacks.Divisors.IdealTrivialization.ker_stalkMap_eq_span_germ_equation`;
* at a point of `U` off `Y` the germ of `t` is a unit:
  `Stacks.Divisors.IdealTrivialization.isUnit_germ_equation_of_not_mem`;
* for an effective Cartier divisor such trivializations exist around every point of `X`:
  `Stacks.Divisors.IdealTrivialization.exists_mem_nonempty`
  (`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.IdealTrivializationCover`).

## Implementation notes

The section rings of `𝒪_X` appear in three definitionally equal spellings: `Γ(X, W)`,
`X.ringCatSheaf.obj.obj (op W)` (the scalars of `X.Modules`) and the codomain of `θ`. The
statements below use the first for the local equation itself, which is the spelling of
[Stacks, Tag 0FMV] (`AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex`), and cross to the
others by `show` where a product or a scalar action has to be formed.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- A sectionwise trivialization over `U` of the ideal sheaf `ℐ` of the closed subscheme cut out
by `I`. -/
abbrev IdealTrivialization (U : X.Opens) : Type u :=
  Stacks.SheafDescent.Trivialization X.toRingedSpace.presheaf (negativeTwist I).val U

namespace IdealTrivialization

variable {I} {U : X.Opens} (e : IdealTrivialization I U)

/-- The basis element of `ℐ` over an open `W ≤ U`: the restriction of the section sent to `1` by
the trivialization. -/
def basisLE {W : X.Opens} (h : W ≤ U) : (negativeTwist I).val.obj (op W) :=
  e.basisAt (homOfLE h)

/-- **The local equation** over an open `W ≤ U`: the image in `𝒪_X(W)` of the basis element. -/
def equationAt {W : X.Opens} (h : W ≤ U) : Γ(X, W) :=
  Scheme.Hom.negativeTwistSection I W (e.basisLE h)

/-- The local equation over `U` itself. -/
abbrev equation : Γ(X, U) := e.equationAt le_rfl

/-- The local equation, in the spelling `X.ringCatSheaf.obj.obj (op W)` of the scalars of the
sections of an `X.Modules`, so that it acts on them. -/
abbrev equationAtR {W : X.Opens} (h : W ≤ U) : X.ringCatSheaf.obj.obj (op W) :=
  e.equationAt h

/-- The coordinate of a section of `ℐ` over `W ≤ U` with respect to the basis element. -/
def coordLE {W : X.Opens} (h : W ≤ U) (a : (negativeTwist I).val.obj (op W)) : Γ(X, W) :=
  e.θ W (homOfLE h) a

/-- The coordinate, in the spelling of the scalars of the sections of an `X.Modules`. -/
abbrev coordLER {W : X.Opens} (h : W ≤ U) (a : (negativeTwist I).val.obj (op W)) :
    X.ringCatSheaf.obj.obj (op W) :=
  e.coordLE h a

/-- Every section of `ℐ` over `W ≤ U` is its coordinate times the basis element. -/
theorem eq_smul_basisLE {W : X.Opens} (h : W ≤ U) (a : (negativeTwist I).val.obj (op W)) :
    a = e.θ W (homOfLE h) a • e.basisLE h :=
  e.eq_smul_basisAt (homOfLE h) a

/-- **Every local section of `ℐ` is a multiple of the local equation**, with the coordinate as
coefficient: `a = θ_W(a) · t` in `𝒪_X(W)`. -/
theorem negativeTwistSection_eq_mul {W : X.Opens} (h : W ≤ U)
    (a : (negativeTwist I).val.obj (op W)) :
    Scheme.Hom.negativeTwistSection I W a =
      e.coordLE h a * e.equationAt h :=
  Stacks.CartierAffineLocal.apply_eq_mul (e.θ W (homOfLE h))
    (Scheme.Hom.negativeTwistInclusion I W) (e.basisLE h) (e.eq_smul_basisLE h) a

/-- The basis elements are compatible with restriction. -/
theorem basisLE_res {W W' : X.Opens} (h : W ≤ U) (h' : W' ≤ W) :
    (negativeTwist I).val.map (homOfLE h').op (e.basisLE h) = e.basisLE (h'.trans h) := by
  show (negativeTwist I).val.map (homOfLE h').op
      ((negativeTwist I).val.map (homOfLE h).op e.basis) =
    (negativeTwist I).val.map (homOfLE (h'.trans h)).op e.basis
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- The local equations are compatible with restriction. -/
theorem equationAt_res {W W' : X.Opens} (h : W ≤ U) (h' : W' ≤ W) :
    X.presheaf.map (homOfLE h').op (e.equationAt h) = e.equationAt (h'.trans h) := by
  rw [equationAt, equationAt, ← e.basisLE_res h h']
  exact (PresheafOfModules.naturality_apply (Stacks.Divisors.idealInclusion I).val
    (homOfLE h').op (e.basisLE h)).symm

/-- The local equation restricts to the local equation on smaller opens. -/
theorem equationAt_eq_res {W : X.Opens} (h : W ≤ U) :
    e.equationAt h = X.presheaf.map (homOfLE h).op e.equation :=
  (e.equationAt_res le_rfl h).symm

/-- The local equation is a nonzerodivisor in `𝒪_X(W)`. -/
theorem mul_equationAt_eq_zero {W : X.Opens} (h : W ≤ U) (r : Γ(X, W))
    (hr : r * e.equationAt h = 0) : r = 0 :=
  Stacks.CartierAffineLocal.eq_zero_of_mul_eq_zero (e.θ W (homOfLE h))
    (Scheme.Hom.negativeTwistInclusion I W) (Scheme.Hom.injective_negativeTwistInclusion I W)
    (e.basisLE h) (e.θ_basisAt (homOfLE h)) r hr

/-- **Over an affine open inside `U` the ideal of `Y` is generated by the local equation.** -/
theorem ideal_eq_span_equationAt (V : X.affineOpens) (h : (V : X.Opens) ≤ U) :
    I.ideal V = Ideal.span {e.equationAt h} := by
  refine Stacks.CartierAffineLocal.eq_span_singleton_of_exists _ _ fun r => ?_
  rw [Stacks.CartierAffineLocal.mem_ideal_iff_exists]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, e.negativeTwistSection_eq_mul h a⟩
  · rintro ⟨c, rfl⟩
    exact ⟨(e.θ V.1 (homOfLE h)).symm c, (e.negativeTwistSection_eq_mul h _).trans
      (congrArg (· * e.equationAt h) ((e.θ V.1 (homOfLE h)).apply_symm_apply c))⟩

/-- The germ at `x ∈ V ≤ W` of the local equation over `V` is that of the one over `W`. -/
private theorem germ_equationAt_of_le {W V : X.Opens} (h : W ≤ U) (hVW : V ≤ W) {x : X}
    (hx : x ∈ V) :
    (X.presheaf.germ V x hx).hom (e.equationAt (hVW.trans h)) =
      (X.presheaf.germ W x (hVW hx)).hom (e.equationAt h) := by
  rw [← e.equationAt_res h hVW]
  exact X.presheaf.germ_res_apply (homOfLE hVW) x hx (e.equationAt h)

/-- **At a point of `Y`, the germ of the local equation generates the ideal of `Y` in the local
ring**: it is the kernel of `𝒪_{X, y} → 𝒪_{Y, y}`. So the local equation of a trivialization is a
local equation of `Y` at `y` in the sense of [Stacks, Tag 0FMV]. -/
theorem ker_stalkMap_eq_span_germ_equation {W : X.Opens} (h : W ≤ U) (y : I.subscheme)
    (hy : I.subschemeι y ∈ W) :
    RingHom.ker (I.subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ W (I.subschemeι y) hy).hom (e.equationAt h)} := by
  obtain ⟨V, hxV, hVW⟩ := Stacks.CartierAffineLocal.exists_affineOpens_le W hy
  have hsurj : Function.Surjective
      (I.subschemeι.appLE (V : X.Opens) (I.subschemeι ⁻¹ᵁ (V : X.Opens)) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact Scheme.Hom.app_surjective _ (V : X.Opens) V.2
  rw [Stacks.Flatness.ker_stalkMap_eq_map_germ I.subschemeι V.2 (V.2.preimage I.subschemeι)
      le_rfl hxV hxV hsurj,
    Scheme.Hom.appLE_eq_app, I.ker_subschemeι_app V, e.ideal_eq_span_equationAt V (hVW.trans h),
    Ideal.map_span, Set.image_singleton, e.germ_equationAt_of_le h hVW hxV]

/-- **Off `Y`, the germ of the local equation is a unit.** -/
theorem isUnit_germ_equation_of_not_mem {W : X.Opens} (h : W ≤ U) (x : X) (hx : x ∈ W)
    (hxY : x ∉ I.support) :
    IsUnit ((X.presheaf.germ W x hx).hom (e.equationAt h)) := by
  obtain ⟨V, hxV, hVW⟩ := Stacks.CartierAffineLocal.exists_affineOpens_le W hx
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV, Scheme.mem_zeroLocus_iff] at hxY
  push Not at hxY
  obtain ⟨s, hs, hxs⟩ := hxY
  rw [e.ideal_eq_span_equationAt V (hVW.trans h), SetLike.mem_coe,
    Ideal.mem_span_singleton'] at hs
  obtain ⟨c, rfl⟩ := hs
  rw [Scheme.mem_basicOpen X _ x hxV, map_mul, e.germ_equationAt_of_le h hVW hxV] at hxs
  exact isUnit_of_mul_isUnit_right hxs

end IdealTrivialization

end Stacks.Divisors

end
