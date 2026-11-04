module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExt
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FirstOrderExtension

/-!
# The first-order universal thickening of a divided power scheme

Let `(T, J, δ)` be a divided power scheme over a scheme `Y` and let `Ω_{T/Y,δ}` be its sheaf of
divided power differentials, with universal divided power derivation `d_{T/Y,δ}`.  The structure
sheaf of the *first-order universal thickening* `T'` of `T` is

`𝒪_{T'} = 𝒪_T ⊕ Ω_{T/Y,δ}`,

a sheaf of commutative rings in which `Ω_{T/Y,δ}` is an ideal of square zero, and the ideal
`J' = J ⊕ Ω_{T/Y,δ}` carries the divided power structure

`δ'_{k+1}(g, ω) = (δ_{k+1} g, δ_k g · ω)`, `δ'_0(g, ω) = 1`.

Two maps of sheaves of rings `p₀, p₁ : 𝒪_T → 𝒪_{T'}` are given by `g ↦ (g, 0)` and by
`g ↦ (g, d_{T/Y,δ} g)`; both, and the projection `𝒪_{T'} → 𝒪_T`, are compatible with the divided
powers of `J` and `J'`.  The projection has square-zero kernel, canonically the summand
`Ω_{T/Y,δ}`, so `T → T'` is a first-order thickening, and the difference `p₁ - p₀` is the
universal divided power derivation followed by that inclusion.

For an object `(U, T, δ)` of the big crystalline category `CRIS(X/S)` of a global crystalline
situation, taking `Y` to be the divided power base and `f` the structure morphism of `T` over it
gives the thickening `T'` of [Stacks, Tag 07J2], since `Ω_{T/S,δ}` is the restriction of
`Ω_{X/S}` to `T` by [Stacks, Tag 07IZ].

## Main definitions

* `Crystalline.firstOrderThickeningSheaf` — the structure sheaf `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/Y,δ}`.
* `Crystalline.firstOrderThickeningIdeal` — the ideal `J' = J ⊕ Ω_{T/Y,δ}` of its sections.
* `Crystalline.firstOrderThickeningDividedPowers` — the divided power structure `δ'` on `J'`.
* `Crystalline.firstOrderThickeningDPRing` — the resulting presheaf of divided power rings.
* `Crystalline.firstOrderThickeningP₀`, `Crystalline.firstOrderThickeningP₁` and
  `Crystalline.firstOrderThickeningProj` — the two maps `𝒪_T → 𝒪_{T'}` and the projection.
* `Crystalline.firstOrderThickeningKernelEquiv` — the identification of the ideal of
  `T → T'` with `Ω_{T/Y,δ}`.

## Main results

* `Crystalline.firstOrderThickening_mul_eq_zero` — `Ω_{T/Y,δ}` is an ideal of square zero.
* `Crystalline.firstOrderThickening_restriction_isDPMorphism` — `δ'` is compatible with every
  restriction map, so `(𝒪_{T'}, J', δ')` is a presheaf of divided power rings.
* `Crystalline.firstOrderThickeningP₀_isDPMorphism`,
  `Crystalline.firstOrderThickeningP₁_isDPMorphism` and
  `Crystalline.firstOrderThickeningProj_isDPMorphism` — the two maps and the projection are
  compatible with the divided powers on `J` and `J'`.
* `Crystalline.firstOrderThickeningP₀_comp_proj` and
  `Crystalline.firstOrderThickeningP₁_comp_proj` — both maps split the projection.
* `Crystalline.firstOrderThickeningP₁_sub_P₀` — the difference of the two maps is the universal
  divided power derivation, included as the square-zero summand.
* `Crystalline.firstOrderThickening_ker_sq` — the ideal of `T → T'` has square zero.

## Implementation notes

The square-zero extension of a presheaf of commutative rings by a presheaf of modules is
`PresheafOfModules.sqZeroExtPresheaf`, which already supplies the ring structure on sections, the
restriction maps, the sheaf property, the inclusion and the projection; what is added here is the
divided power ideal, its divided power structure and the derivation-shifted inclusion.  The
divided powers on the sections over an open come from
`Crystalline.squareZeroDividedPowers`, the invariant construction of the divided powers of a
square-zero extension, applied through the additive identification of the sections of `𝒪_{T'}`
with pairs.

Degree zero is `1` and not the degenerate reading `(δ_0 g, δ_{-1} g · ω)` of the displayed
formula: the displayed formula is used only in degrees written `k + 1`, where the shifted index
is `k` and no truncated subtraction occurs.  In degree one it gives back `(g, ω)`, as a divided
power structure requires, because `δ_1 g = g` and `δ_0 g = 1`.

Everything in this module is stated for the sheaf of rings `𝒪_{T'}` and its ideal, which is
where the content of the construction lies.  The realization of `𝒪_{T'}` as the structure sheaf
of a *scheme* `T'`, and of `(U, T', δ')` as an object of the crystalline category, is
`StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickeningScheme.lean`; it goes through
`Stacks.Thickenings.squareZeroExtension_realization`, which takes a square-zero extension whose
kernel is quasi-coherent, the kernel here being `Ω_{T/Y,δ}` and its quasi-coherence
`Crystalline.dpDifferentialsSheaf_isQuasicoherent`.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07HH](https://stacks.math.columbia.edu/tag/07HH)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- The sheaf `Ω_{T/Y,δ}` of divided power differentials, read as a presheaf of modules over the
structure sheaf of `T` in its `CommRingCat`-valued form. -/
public abbrev dpDifferentialsModules :
    PresheafOfModules.{u} (T.scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  (Scheme.Modules.toPresheafOfModules T.scheme).obj (dpDifferentialsSheaf T Y f)

/-- The structure sheaf `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/Y,δ}` of the first-order universal thickening, as a
presheaf of commutative rings in which the differentials form an ideal of square zero. -/
public abbrev firstOrderThickeningPresheaf : (Opens ↑T.scheme)ᵒᵖ ⥤ CommRingCat.{u} :=
  sqZeroExtPresheaf (dpDifferentialsModules T Y f)

/-- **The structure sheaf of the first-order universal thickening** `T'` of a divided power
scheme `T` over `Y`: the square-zero extension `𝒪_T ⊕ Ω_{T/Y,δ}` of the structure sheaf of `T`
by its sheaf of divided power differentials. -/
@[stacks 07J2 "the structure sheaf of the first-order thickening"]
public def firstOrderThickeningSheaf : TopCat.Sheaf CommRingCat.{u} ↑T.scheme :=
  ⟨firstOrderThickeningPresheaf T Y f,
    isSheaf_sqZeroExtPresheaf (dpDifferentialsModules T Y f) T.scheme.sheaf.property
      (dpDifferentialsSheaf T Y f).isSheaf⟩

/-- The underlying presheaf of `firstOrderThickeningSheaf` is `firstOrderThickeningPresheaf`. -/
@[simp]
public theorem firstOrderThickeningSheaf_obj :
    (firstOrderThickeningSheaf T Y f).obj = firstOrderThickeningPresheaf T Y f := rfl

/-- The sections of `𝒪_{T'}` over an open, additively identified with pairs consisting of a
section of `𝒪_T` and a divided power differential. -/
public def firstOrderThickeningEquiv (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((firstOrderThickeningPresheaf T Y f).obj W) ≃+
      ↑(T.scheme.sheaf.obj.obj W) × ↑((dpDifferentialsModules T Y f).obj W) where
  toFun x := (sqZeroExtFst x, sqZeroExtSnd x)
  invFun y := sqZeroExtMk y.1 y.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **The ideal `J' = J ⊕ Ω_{T/Y,δ}`** of the sections of `𝒪_{T'}` over an open: the sections
whose component in `𝒪_T` lies in the divided power ideal of `T`. -/
@[stacks 07J2 "the extended ideal J' = J ⊕ Ω"]
public def firstOrderThickeningIdeal (W : (Opens ↑T.scheme)ᵒᵖ) :
    Ideal ↑((firstOrderThickeningPresheaf T Y f).obj W) :=
  Ideal.comap ((sqZeroExtProj (dpDifferentialsModules T Y f)).app W).hom
    (sectionIdeal T.scheme.sheaf T.ideal W)

/-- Membership in the extended ideal is membership of the first coordinate in the divided power
ideal of `T`. -/
public theorem mem_firstOrderThickeningIdeal_iff (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    x ∈ firstOrderThickeningIdeal T Y f W ↔
      sqZeroExtFst x ∈ sectionIdeal T.scheme.sheaf T.ideal W := Iff.rfl

/-- Multiplication of sections of `𝒪_{T'}` in the coordinates of the square-zero extension. -/
public theorem firstOrderThickeningEquiv_mul (W : (Opens ↑T.scheme)ᵒᵖ)
    (b b' : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    firstOrderThickeningEquiv T Y f W (b * b') =
      ((firstOrderThickeningEquiv T Y f W b).1 * (firstOrderThickeningEquiv T Y f W b').1,
        (firstOrderThickeningEquiv T Y f W b).1 • (firstOrderThickeningEquiv T Y f W b').2 +
          (firstOrderThickeningEquiv T Y f W b').1 •
            (firstOrderThickeningEquiv T Y f W b).2) := rfl

/-- The inclusion `g ↦ (g, 0)` in the coordinates of the square-zero extension. -/
public theorem firstOrderThickeningEquiv_inl (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    firstOrderThickeningEquiv T Y f W
        (((sqZeroExtInl (dpDifferentialsModules T Y f)).app W).hom a) = (a, 0) := rfl

/-- **The divided power structure `δ'` on the ideal `J' = J ⊕ Ω_{T/Y,δ}`**, given in degree
`k + 1` by `(g, ω) ↦ (δ_{k+1} g, δ_k g · ω)` and in degree zero by `1`. -/
@[stacks 07J2 "the divided power structure on J'"]
public def firstOrderThickeningDividedPowers (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers (firstOrderThickeningIdeal T Y f W) :=
  squareZeroDividedPowers (T.dividedPowers.dividedPowers W)
    (firstOrderThickeningEquiv T Y f W) (firstOrderThickeningIdeal T Y f W)
    ((sqZeroExtInl (dpDifferentialsModules T Y f)).app W).hom
    (firstOrderThickeningEquiv_inl T Y f W) (firstOrderThickeningEquiv_mul T Y f W)
    (fun _ => Iff.rfl)

/-- The divided powers of `J'` are `1` in degree zero. -/
public theorem firstOrderThickeningDividedPowers_dpow_zero (W : (Opens ↑T.scheme)ᵒᵖ)
    {x : ↑((firstOrderThickeningPresheaf T Y f).obj W)}
    (hx : x ∈ firstOrderThickeningIdeal T Y f W) :
    (firstOrderThickeningDividedPowers T Y f W).dpow 0 x = 1 :=
  squareZeroDpow_zero (T.dividedPowers.dividedPowers W) (firstOrderThickeningEquiv T Y f W)
    (firstOrderThickeningIdeal T Y f W) hx

/-- **The divided power formula on `J'` in positive degree**: `δ'_{k+1}(g, ω)` is
`(δ_{k+1} g, δ_k g · ω)`. -/
public theorem firstOrderThickeningDividedPowers_dpow_succ (W : (Opens ↑T.scheme)ᵒᵖ) (k : ℕ)
    {x : ↑((firstOrderThickeningPresheaf T Y f).obj W)}
    (hx : x ∈ firstOrderThickeningIdeal T Y f W) :
    (firstOrderThickeningDividedPowers T Y f W).dpow (k + 1) x =
      sqZeroExtMk ((T.dividedPowers.dividedPowers W).dpow (k + 1) (sqZeroExtFst x))
        ((T.dividedPowers.dividedPowers W).dpow k (sqZeroExtFst x) • sqZeroExtSnd x) :=
  squareZeroDpow_succ (T.dividedPowers.dividedPowers W) (firstOrderThickeningEquiv T Y f W)
    (firstOrderThickeningIdeal T Y f W) k hx

/-- **The sheaf of divided power differentials is an ideal of square zero in `𝒪_{T'}`.** -/
@[stacks 07J2 "the differentials are an ideal of square zero"]
public theorem firstOrderThickening_mul_eq_zero (W : (Opens ↑T.scheme)ᵒᵖ)
    {x y : ↑((firstOrderThickeningPresheaf T Y f).obj W)}
    (hx : sqZeroExtFst x = 0) (hy : sqZeroExtFst y = 0) : x * y = 0 :=
  squareZero_mul_eq_zero (firstOrderThickeningEquiv T Y f W)
    (firstOrderThickeningEquiv_mul T Y f W) hx hy

/-- Restriction of a section of `𝒪_{T'}` in the coordinates of the square-zero extension. -/
public theorem firstOrderThickeningEquiv_map {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    firstOrderThickeningEquiv T Y f W' (((firstOrderThickeningPresheaf T Y f).map i).hom x) =
      ((T.scheme.sheaf.obj.map i).hom (firstOrderThickeningEquiv T Y f W x).1,
        (dpDifferentialsModules T Y f).map i (firstOrderThickeningEquiv T Y f W x).2) := rfl

/-- Restriction of a section of `𝒪_{T'}` written in coordinates. -/
public theorem map_firstOrderThickeningEquiv_symm {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (y : ↑(T.scheme.sheaf.obj.obj W) × ↑((dpDifferentialsModules T Y f).obj W)) :
    ((firstOrderThickeningPresheaf T Y f).map i).hom
        ((firstOrderThickeningEquiv T Y f W).symm y) =
      (firstOrderThickeningEquiv T Y f W').symm
        ((T.scheme.sheaf.obj.map i).hom y.1, (dpDifferentialsModules T Y f).map i y.2) := rfl

/-- **Every restriction map of `𝒪_{T'}` is compatible with the divided powers of `J'`**, so the
rings of sections of `𝒪_{T'}` with the ideals `J'` and the structures `δ'` form a presheaf of
divided power rings. -/
@[stacks 07J2 "the divided powers on J' are compatible with restriction"]
public theorem firstOrderThickening_restriction_isDPMorphism
    {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W') :
    DividedPowers.IsDPMorphism (firstOrderThickeningDividedPowers T Y f W)
      (firstOrderThickeningDividedPowers T Y f W')
      (((firstOrderThickeningPresheaf T Y f).map i).hom) := by
  have hnat := T.dividedPowers.naturality i
  have hres : ∀ b : ↑(T.scheme.sheaf.obj.obj W),
      b ∈ sectionIdeal T.scheme.sheaf T.ideal W →
      (T.scheme.sheaf.obj.map i).hom b ∈ sectionIdeal T.scheme.sheaf T.ideal W' :=
    fun _ hb => T.ideal.toSubmodule.map_mem i hb
  have hmemres : ∀ y : ↑((firstOrderThickeningPresheaf T Y f).obj W),
      y ∈ firstOrderThickeningIdeal T Y f W →
      ((firstOrderThickeningPresheaf T Y f).map i).hom y ∈
        firstOrderThickeningIdeal T Y f W' :=
    fun y hy => hres (sqZeroExtFst y) hy
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun x hx => hmemres x hx, ?_⟩
  intro n x hx
  have ha : sqZeroExtFst x ∈ sectionIdeal T.scheme.sheaf T.ideal W := hx
  match n with
  | 0 =>
      rw [firstOrderThickeningDividedPowers_dpow_zero T Y f W' (hmemres x hx),
        firstOrderThickeningDividedPowers_dpow_zero T Y f W hx, map_one]
  | k + 1 =>
      rw [firstOrderThickeningDividedPowers_dpow_succ T Y f W' k (hmemres x hx),
        firstOrderThickeningDividedPowers_dpow_succ T Y f W k hx]
      exact sqZeroExt_ext (hnat.dpow_comp (n := k + 1) _ ha)
        ((congrArg (· • (dpDifferentialsModules T Y f).map i (sqZeroExtSnd x))
          (hnat.dpow_comp (n := k) _ ha)).trans
            ((dpDifferentialsModules T Y f).map_smul i _ _).symm)

/-- **The presheaf of divided power rings `(𝒪_{T'}, J', δ')`** of the first-order universal
thickening. -/
public def firstOrderThickeningDPRing : (Opens ↑T.scheme)ᵒᵖ ⥤ DividedPowerRing.{u} where
  obj W := .of ↑((firstOrderThickeningPresheaf T Y f).obj W) (firstOrderThickeningIdeal T Y f W)
    (firstOrderThickeningDividedPowers T Y f W)
  map i := DividedPowers.DPMorphism.mk' (firstOrderThickening_restriction_isDPMorphism T Y f i)
  map_id W := by
    change DividedPowers.DPMorphism.mk'
        (firstOrderThickening_restriction_isDPMorphism T Y f (𝟙 W)) =
      DividedPowers.DPMorphism.id (firstOrderThickeningDividedPowers T Y f W)
    ext x
    change ((firstOrderThickeningPresheaf T Y f).map (𝟙 W)).hom x = x
    rw [(firstOrderThickeningPresheaf T Y f).map_id]
    rfl
  map_comp {W W' W''} i j := by
    change DividedPowers.DPMorphism.mk'
        (firstOrderThickening_restriction_isDPMorphism T Y f (i ≫ j)) =
      (DividedPowers.DPMorphism.mk'
        (firstOrderThickening_restriction_isDPMorphism T Y f j)).comp
        (DividedPowers.DPMorphism.mk'
          (firstOrderThickening_restriction_isDPMorphism T Y f i))
    ext x
    change ((firstOrderThickeningPresheaf T Y f).map (i ≫ j)).hom x =
      ((firstOrderThickeningPresheaf T Y f).map j).hom
        (((firstOrderThickeningPresheaf T Y f).map i).hom x)
    rw [(firstOrderThickeningPresheaf T Y f).map_comp]
    rfl

/-- **The first of the two maps `𝒪_T → 𝒪_{T'}`**, the inclusion `g ↦ (g, 0)`. -/
@[stacks 07J2 "the map p₀"]
public def firstOrderThickeningP₀ : T.scheme.sheaf.obj ⟶ firstOrderThickeningPresheaf T Y f :=
  sqZeroExtInl (dpDifferentialsModules T Y f)

/-- **The second of the two maps `𝒪_T → 𝒪_{T'}`**, the inclusion shifted by the universal
divided power derivation: `g ↦ (g, d_{T/Y,δ} g)`. -/
@[stacks 07J2 "the map p₁"]
public def firstOrderThickeningP₁ : T.scheme.sheaf.obj ⟶ firstOrderThickeningPresheaf T Y f where
  app W := sqZeroExtLift (dpDifferentialsModules T Y f) (𝟙 (T.scheme.sheaf.obj.obj W))
    (AddMonoidHom.mk' (sheafApp T Y f W.unop) (sheafApp_add T Y f W.unop))
    (sheafApp_mul T Y f W.unop)
  naturality _ _ i := CommRingCat.hom_ext (RingHom.ext fun a =>
    sqZeroExt_ext rfl (sheafApp_naturality T Y f i.unop a).symm)

/-- **The projection `𝒪_{T'} → 𝒪_T`**, forgetting the differential component. -/
@[stacks 07J2 "the quotient map"]
public def firstOrderThickeningProj : firstOrderThickeningPresheaf T Y f ⟶ T.scheme.sheaf.obj :=
  sqZeroExtProj (dpDifferentialsModules T Y f)

/-- The `𝒪_T`-component of `p₀ a` is `a`. -/
@[simp]
public theorem firstOrderThickeningP₀_app_apply (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    sqZeroExtFst (((firstOrderThickeningP₀ T Y f).app W).hom a) = a := rfl

/-- The differential component of `p₀ a` is zero. -/
@[simp]
public theorem firstOrderThickeningP₀_app_snd (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    sqZeroExtSnd (((firstOrderThickeningP₀ T Y f).app W).hom a) = 0 := rfl

/-- The `𝒪_T`-component of `p₁ a` is `a`. -/
@[simp]
public theorem firstOrderThickeningP₁_app_fst (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    sqZeroExtFst (((firstOrderThickeningP₁ T Y f).app W).hom a) = a := rfl

/-- The differential component of `p₁ a` is the divided power differential `d_{T/Y,δ} a`. -/
@[simp]
public theorem firstOrderThickeningP₁_app_snd (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    sqZeroExtSnd (((firstOrderThickeningP₁ T Y f).app W).hom a) = sheafApp T Y f W.unop a := rfl

/-- The projection `𝒪_{T'} → 𝒪_T` sends a section to its `𝒪_T`-component. -/
@[simp]
public theorem firstOrderThickeningProj_app_apply (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    ((firstOrderThickeningProj T Y f).app W).hom x = sqZeroExtFst x := rfl

/-- **`p₀` is compatible with the divided power structures on `J` and `J'`.** -/
@[stacks 07J2 "p₀ is compatible with the divided powers"]
public theorem firstOrderThickeningP₀_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (T.dividedPowers.dividedPowers W)
      (firstOrderThickeningDividedPowers T Y f W)
      (((firstOrderThickeningP₀ T Y f).app W).hom) :=
  isDPMorphism_squareZero_of_graph (T.dividedPowers.dividedPowers W)
    (firstOrderThickeningEquiv T Y f W) (firstOrderThickeningIdeal T Y f W)
    ((sqZeroExtInl (dpDifferentialsModules T Y f)).app W).hom
    (firstOrderThickeningEquiv_inl T Y f W) (firstOrderThickeningEquiv_mul T Y f W)
    (fun _ => Iff.rfl) (((firstOrderThickeningP₀ T Y f).app W).hom) (fun _ => 0)
    (fun _ => rfl) (fun _ _ _ => (smul_zero _).symm)

/-- **`p₁` is compatible with the divided power structures on `J` and `J'`**, because the
universal divided power derivation obeys the divided power chain rule. -/
@[stacks 07J2 "p₁ is compatible with the divided powers"]
public theorem firstOrderThickeningP₁_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (T.dividedPowers.dividedPowers W)
      (firstOrderThickeningDividedPowers T Y f W)
      (((firstOrderThickeningP₁ T Y f).app W).hom) :=
  isDPMorphism_squareZero_of_graph (T.dividedPowers.dividedPowers W)
    (firstOrderThickeningEquiv T Y f W) (firstOrderThickeningIdeal T Y f W)
    ((sqZeroExtInl (dpDifferentialsModules T Y f)).app W).hom
    (firstOrderThickeningEquiv_inl T Y f W) (firstOrderThickeningEquiv_mul T Y f W)
    (fun _ => Iff.rfl) (((firstOrderThickeningP₁ T Y f).app W).hom)
    (sheafApp T Y f W.unop) (fun _ => rfl)
    (fun k a ha => sheafApp_dpow T Y f W.unop k a ha)

/-- **The projection `𝒪_{T'} → 𝒪_T` is compatible with the divided power structures on `J'`
and `J`.** -/
@[stacks 07J2 "the quotient map is compatible with the divided powers"]
public theorem firstOrderThickeningProj_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (firstOrderThickeningDividedPowers T Y f W)
      (T.dividedPowers.dividedPowers W) (((firstOrderThickeningProj T Y f).app W).hom) :=
  isDPMorphism_squareZero_fst (T.dividedPowers.dividedPowers W)
    (firstOrderThickeningEquiv T Y f W) (firstOrderThickeningIdeal T Y f W)
    ((sqZeroExtInl (dpDifferentialsModules T Y f)).app W).hom
    (firstOrderThickeningEquiv_inl T Y f W) (firstOrderThickeningEquiv_mul T Y f W)
    (fun _ => Iff.rfl) (((firstOrderThickeningProj T Y f).app W).hom) (fun _ => rfl)

/-- The inclusion `p₀` splits the projection. -/
public theorem firstOrderThickeningP₀_comp_proj :
    firstOrderThickeningP₀ T Y f ≫ firstOrderThickeningProj T Y f = 𝟙 _ :=
  NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

/-- The derivation-shifted inclusion `p₁` splits the projection. -/
public theorem firstOrderThickeningP₁_comp_proj :
    firstOrderThickeningP₁ T Y f ≫ firstOrderThickeningProj T Y f = 𝟙 _ :=
  NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

/-- **The difference of the two maps `𝒪_T → 𝒪_{T'}` is the universal divided power derivation**,
followed by the inclusion of `Ω_{T/Y,δ}` as the square-zero summand. -/
@[stacks 07J2 "p₁ - p₀ is the universal derivation"]
public theorem firstOrderThickeningP₁_sub_P₀ (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    ((firstOrderThickeningP₁ T Y f).app W).hom a - ((firstOrderThickeningP₀ T Y f).app W).hom a =
      sqZeroExtMk 0 (sheafApp T Y f W.unop a) :=
  sqZeroExt_ext (sub_self a) (sub_zero (sheafApp T Y f W.unop a))

/-- A section of `𝒪_{T'}` is killed by the projection exactly when it is a differential. -/
public theorem mem_ker_firstOrderThickeningProj_iff (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    x ∈ RingHom.ker (((firstOrderThickeningProj T Y f).app W).hom) ↔ sqZeroExtFst x = 0 :=
  RingHom.mem_ker

/-- **The ideal of the first-order thickening `T → T'` is the sheaf of divided power
differentials**: the kernel of `𝒪_{T'} → 𝒪_T` over an open is canonically `Ω_{T/Y,δ}`. -/
@[stacks 07J2 "the ideal of the thickening is the differentials"]
public def firstOrderThickeningKernelEquiv (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((dpDifferentialsModules T Y f).obj W) ≃+
      RingHom.ker (((firstOrderThickeningProj T Y f).app W).hom) where
  toFun ω := ⟨sqZeroExtMk 0 ω, RingHom.mem_ker.mpr rfl⟩
  invFun x := sqZeroExtSnd x.1
  left_inv _ := rfl
  right_inv x := Subtype.ext (sqZeroExt_ext (RingHom.mem_ker.mp x.2).symm rfl)
  map_add' _ _ := Subtype.ext (sqZeroExt_ext (add_zero (0 : ↑(T.scheme.sheaf.obj.obj W))).symm rfl)

/-- **The difference of the two maps `𝒪_T → 𝒪_{T'}` is the universal divided power derivation
followed by the inclusion of the ideal of `T → T'`.** -/
public theorem firstOrderThickeningP₁_sub_P₀_eq_kernel (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    ((firstOrderThickeningP₁ T Y f).app W).hom a - ((firstOrderThickeningP₀ T Y f).app W).hom a =
      ↑(firstOrderThickeningKernelEquiv T Y f W (sheafApp T Y f W.unop a)) :=
  firstOrderThickeningP₁_sub_P₀ T Y f W a

/-- **`T → T'` is a first-order thickening**: the ideal of the projection `𝒪_{T'} → 𝒪_T` has
square zero on every open. -/
@[stacks 07J2 "T → T' is a first-order thickening"]
public theorem firstOrderThickening_ker_sq (W : (Opens ↑T.scheme)ᵒᵖ) :
    RingHom.ker (((firstOrderThickeningProj T Y f).app W).hom) ^ 2 = ⊥ := by
  rw [pow_two]
  refine le_antisymm (Ideal.mul_le.mpr fun x hx y hy => ?_) bot_le
  exact Ideal.mem_bot.mpr (firstOrderThickening_mul_eq_zero T Y f W
    ((mem_ker_firstOrderThickeningProj_iff T Y f W x).mp hx)
    ((mem_ker_firstOrderThickeningProj_iff T Y f W y).mp hy))

end Crystalline

end
