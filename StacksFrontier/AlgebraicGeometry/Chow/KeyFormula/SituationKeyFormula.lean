module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.LocalReduction
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SymbolComparison
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension

/-!
# The key formula for the situation of Stacks 0AYB

Let `X` be an integral, locally Noetherian scheme locally of finite type over the base of
chapter 42, let `L` and `N` be invertible `𝒪_X`-modules with nonzero meromorphic sections `s` and
`t`, and let `ℱ` be a term of `Stacks.Chow.KeyFormulaSituation L N`: a locally finite family
`{Z_i}` of prime divisors containing every prime divisor along which `s` or `t` fails to
generate, with chosen generators `s_i` of `L_{ξ_i}` and `t_i` of `N_{ξ_i}`. Then the key formula
Stacks 0AYC holds for the cycle-level data `ℱ.toKeyFormulaData` the situation determines:

`∑ (Z_i → X)_* (ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i))
  = ∑ (Z_i → X)_* div_{Z_i}(∂_{B_i}(f_i, g_i))`.

No hypothesis is added: the dimension function of Stacks 02JW is not needed as an input, the
universal catenarity of the base being part of `Stacks.Chow.ChowSituation`.

## The proof

Both sides are supported at the codimension-one points of the members of the family
(`Stacks.Chow.KeyFormulaData.keyFormula_iff_forall_component_coheight_one`), and such a point `x`
of `X` has codimension two: the relative dimension drops by one from the generic point of `X` to
`ξ_i`, and by one again from `ξ_i` to `x`.

At such a point pick trivializations of `L` and `N` on a neighbourhood of `x` and read `s` and `t`
in them: a single pair `(a, b)` of rational functions expresses both at every generization of `x`,
and the reciprocity law of Stacks 0EAX makes the family sum of the tame-symbol orders
`ord_{A/𝔮_i}(∂_{A_{𝔮_i}}(a, b))` vanish, the prime divisors outside the family contributing
nothing. The ratios of the situation differ from that pair by units of `B_i = 𝒪_{X, ξ_i}`:
`f_i = u_i a` and `g_i = v_i b`. By Stacks 0EAN the resulting correction to the `i`-th summand is

`ord_{B_i}(b) · ord_{Z_i, x}(ū_i) - ord_{B_i}(a) · ord_{Z_i, x}(v̄_i)`,

the symbol of two units contributing nothing, and by Stacks 02SH on `Z_i`
(`Stacks.Chow.orderOfVanishing_restrictStalk_smul`) the order of vanishing of `ū_i` at `x` is
minus the coefficient of `div_{L|Z_i}(s_i|Z_i)` there, because the trivializing germ restricts to
a generator of `L|Z_i` at `x` and so has vanishing divisor. That correction is exactly the `i`-th
summand of the left hand side.

## Main results

* `Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData` — **Stacks 0AYC for the situation
  of Stacks 0AYB**.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0EAN](https://stacks.math.columbia.edu/tag/0EAN)
* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange

universe u

namespace Stacks.Chow

open Stacks.Divisors

attribute [local instance] isIntegral_integralComponentAt
attribute [local instance] isLocallyNoetherian_integralComponentSubscheme

/-! ### Orders of vanishing of products, powers and inverses -/

section Ord

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] {y : Y}

/-- The order of vanishing of the constant `1` is zero. -/
private theorem ord_one_eq_zero : Y.ord 1 y = 0 := by
  have h : Y.ord ((1 : Y.functionField) * 1) y =
      Y.ord (1 : Y.functionField) y + Y.ord (1 : Y.functionField) y :=
    Scheme.ord_mul one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- The order of vanishing of an inverse is the negative of the order of vanishing. -/
private theorem ord_inv_eq_neg {f : Y.functionField} (hf : f ≠ 0) :
    Y.ord f⁻¹ y = -Y.ord f y := by
  have h : Y.ord (f * f⁻¹) y = Y.ord f y + Y.ord f⁻¹ y := Scheme.ord_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one_eq_zero] at h
  omega

end Ord

/-! ### The residue field at a codimension-one point and the component through it -/

section Residue

variable {X : Scheme.{u}}

/-- The germ map `𝒪_{X, ξ} → 𝒪_{Z, η_Z} = R(Z)` of the closed immersion of an integral closed
subscheme `Z` at its generic point, with that point named through an equality `ι(η_Z) = ξ`. -/
private abbrev restrictScalarHom (W : X.IdealSheafData) [IsIntegral W.subscheme] {ξ : X}
    (hξ : W.subschemeι.base (genericPoint W.subscheme) = ξ) :
    X.presheaf.stalk ξ ⟶ W.subscheme.presheaf.stalk (genericPoint W.subscheme) :=
  hξ ▸ W.subschemeι.stalkMap (genericPoint W.subscheme)

/-- **The restriction of a germ to the component is its residue.** The germ map of the closed
immersion of `Z` at the generic point, read in the residue field of `Z` there and transported
to `κ(ξ)`, is the residue map of `𝒪_{X, ξ}`. -/
private theorem residue_restrictScalarHom (W : X.IdealSheafData) [IsIntegral W.subscheme]
    {ξ : X} (hξ : W.subschemeι.base (genericPoint W.subscheme) = ξ)
    (u : X.presheaf.stalk ξ) :
    (RingEquiv.ofBijective
          (W.subschemeι.residueFieldMap (genericPoint W.subscheme)).hom
          (bijective_residueFieldMap_of_isClosedImmersion _ _)).symm
        (W.subscheme.residue (genericPoint W.subscheme) ((restrictScalarHom W hξ).hom u)) =
      (X.residueFieldCongr hξ).commRingCatIsoToRingEquiv.symm (X.residue ξ u) := by
  subst hξ
  have hsq := ConcreteCategory.congr_hom
    (Scheme.residue_residueFieldMap W.subschemeι (genericPoint W.subscheme)) u
  rw [RingEquiv.symm_apply_eq]
  exact hsq.symm.trans rfl

/-- **The image in `R(Z_ξ)` of a germ at `ξ` is its residue, read through `κ(ξ) = R(Z_ξ)`.** -/
private theorem functionFieldIntegralComponentEquiv_restrictScalarHom (ξ : X)
    (u : X.presheaf.stalk ξ) :
    functionFieldIntegralComponentEquiv ξ
        ((restrictScalarHom (integralComponentAt ξ) (ξ := ξ)
          (genericPointOf_integralComponentAt ξ)).hom u) =
      IsLocalRing.residue (X.presheaf.stalk ξ) u := by
  have h1 := pointClosureFunctionFieldEquiv_eq_residue ξ
    ((restrictScalarHom (integralComponentAt ξ) (ξ := ξ)
      (genericPointOf_integralComponentAt ξ)).hom u)
  have h2 := residue_restrictScalarHom (integralComponentAt ξ) (ξ := ξ)
    (genericPointOf_integralComponentAt ξ) u
  refine (h1.trans (congrArg _ h2)).trans ?_
  exact RingEquiv.apply_symm_apply _ _

/-- A point in the image of the integral component at `ξ` lies in the closure of `ξ`. -/
private theorem mem_closure_of_mem_range_subschemeι {ξ x : X}
    (hx : x ∈ Set.range (integralComponentAt ξ).subschemeι.base) :
    x ∈ closure ({ξ} : Set X) := by
  rwa [(integralComponentAt ξ).range_subschemeι, coe_support_integralComponentAt] at hx

end Residue

/-! ### The restriction of a trivializing germ generates -/

section Restrict

variable {X : Scheme.{u}} (W : X.IdealSheafData) [IsIntegral W.subscheme] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **The restriction of a germ at `ξ` is the generic value of its restriction at any point of
`Z`.** Both sides are the germ at the generic point of `Z` of the pullback to `Z` of a section
representing the germ. -/
private theorem restrictStalk_germ {ξ : X}
    (hξ : W.subschemeι.base (genericPoint W.subscheme) = ξ) (V : X.Opens) (hξV : ξ ∈ V)
    (t : Γ(L, V)) (z : W.subscheme) (hzV : W.subschemeι.base z ∈ V) :
    restrictStalk W L hξ (L.presheaf.germ V ξ hξV t) =
      toGenericStalk (restrictModule W L) z
        (pullbackStalk W.subschemeι L z
          (L.presheaf.germ V (W.subschemeι.base z) hzV t)) := by
  have hηV : W.subschemeι.base (genericPoint W.subscheme) ∈ V := by rw [hξ]; exact hξV
  have h1 : restrictStalk W L hξ (L.presheaf.germ V ξ hξV t) =
      ((Scheme.Modules.pullback W.subschemeι).obj L).presheaf.germ
        (W.subschemeι ⁻¹ᵁ V) (genericPoint W.subscheme) hηV
        (pullbackUnitSections W.subschemeι L V t) :=
    pullbackStalkAt_germ W.subschemeι L (genericPoint W.subscheme) hξ V hηV t
  have h2 : pullbackStalk W.subschemeι L z (L.presheaf.germ V (W.subschemeι.base z) hzV t) =
      ((Scheme.Modules.pullback W.subschemeι).obj L).presheaf.germ (W.subschemeι ⁻¹ᵁ V) z hzV
        (pullbackUnitSections W.subschemeι L V t) :=
    pullbackStalk_germ W.subschemeι L z V hzV t
  have h3 := toGenericStalk_germ (L := restrictModule W L) (x := z)
    (W := W.subschemeι ⁻¹ᵁ V) hzV hηV (pullbackUnitSections W.subschemeι L V t)
  rw [h2, h3]
  exact h1

/-- **The divisor of the restriction of a trivializing germ vanishes at a point of `Z` where it
trivializes.** The restriction of the germ generates the restricted module there, so the constant
`1` is a coordinate of it and its order of vanishing is zero. -/
private theorem orderOfVanishing_restrictStalk_germ_eq_zero [IsIntegral X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian W.subscheme] {ξ : X}
    (hξ : W.subschemeι.base (genericPoint W.subscheme) = ξ) (V : X.Opens) (hξV : ξ ∈ V)
    (t : Γ(L, V)) (ht : ∀ (y : X) (hy : y ∈ V), IsStalkBasis L y (L.presheaf.germ V y hy t))
    (Y : PrimeDivisor W.subscheme) (hYV : W.subschemeι.base Y.genericPoint ∈ V) :
    orderOfVanishing (restrictModule W L) (restrictStalk W L hξ (L.presheaf.germ V ξ hξV t))
        Y = 0 := by
  have hcoord : IsCoordinateAt (restrictModule W L) Y.genericPoint
      (restrictStalk W L hξ (L.presheaf.germ V ξ hξV t)) 1 :=
    ⟨pullbackStalk W.subschemeι L Y.genericPoint
        (L.presheaf.germ V (W.subschemeι.base Y.genericPoint) hYV t),
      (ht _ hYV).pullbackStalk, by
        rw [one_smul]
        exact restrictStalk_germ W L hξ V hξV t Y.genericPoint hYV⟩
  rw [orderOfVanishing_eq (isTrivializedNear_restrictModule W L Y.genericPoint) hcoord]
  exact ord_one_eq_zero

/-- **The divisor of the restricted generator is minus the divisor of the correcting unit.**
If the chosen generator `s` of `L_ξ` and the germ at `ξ` of a section trivializing `L` near a
point `x` of `Z` differ by the unit `u`, then the order of vanishing of `s|_Z` at a prime divisor
of `Z` through `x` is minus the order of vanishing of `u|_Z` there: the trivializing germ
restricts to a generator, so its own divisor vanishes there. -/
private theorem orderOfVanishing_restrictStalk_eq_neg_ord [IsIntegral X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian W.subscheme] {ξ : X}
    (hξ : W.subschemeι.base (genericPoint W.subscheme) = ξ) (V : X.Opens) (hξV : ξ ∈ V)
    (t : Γ(L, V)) (ht : ∀ (y : X) (hy : y ∈ V), IsStalkBasis L y (L.presheaf.germ V y hy t))
    (Y : PrimeDivisor W.subscheme) (hYV : W.subschemeι.base Y.genericPoint ∈ V)
    {s : L.presheaf.stalk ξ} (hs : IsStalkBasis L ξ s)
    {u : X.presheaf.stalk ξ} (hu : IsUnit u)
    (hmu : L.presheaf.germ V ξ hξV t = u • s) :
    orderOfVanishing (restrictModule W L) (restrictStalk W L hξ s) Y =
      -W.subscheme.ord ((restrictScalarHom W hξ).hom u) Y.genericPoint := by
  have hbasis := isStalkBasis_restrictStalk W L hξ hs
  have hs0 : restrictStalk W L hξ s ≠ 0 := by
    intro h0
    have h01 : (0 : W.subscheme.presheaf.stalk (genericPoint W.subscheme)) = 1 :=
      hbasis.injective (by simp only [h0, smul_zero])
    exact zero_ne_one (α := W.subscheme.functionField) h01
  have h : orderOfVanishing (restrictModule W L) (restrictStalk W L hξ (u • s)) Y =
      W.subscheme.ord ((restrictScalarHom W hξ).hom u) Y.genericPoint +
        orderOfVanishing (restrictModule W L) (restrictStalk W L hξ s) Y :=
    orderOfVanishing_restrictStalk_smul W L hξ hu hs hs0
  rw [← hmu, orderOfVanishing_restrictStalk_germ_eq_zero W L hξ V hξV t ht Y hYV] at h
  omega

end Restrict

/-! ### The order of vanishing on the component through a point -/

section OrdAt

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The order of vanishing at `x` of a unit of `κ(ξ)`, read as a rational function on the integral
closed subscheme `Z_ξ` through the identification `κ(ξ) = R(Z_ξ)`. -/
private def ordAt (ξ : X) {x : X} (hmem : x ∈ closure ({ξ} : Set X))
    (T : (IsLocalRing.ResidueField (X.presheaf.stalk ξ))ˣ) : ℤ :=
  (integralComponentAt ξ).subscheme.ord
    ((functionFieldIntegralComponentEquiv ξ).symm
      (T : IsLocalRing.ResidueField (X.presheaf.stalk ξ))) (pointClosurePoint ξ hmem)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- A unit of `κ(ξ)` is a nonzero rational function on `Z_ξ`. -/
private theorem functionFieldIntegralComponentEquiv_symm_ne_zero (ξ : X)
    (T : (IsLocalRing.ResidueField (X.presheaf.stalk ξ))ˣ) :
    (functionFieldIntegralComponentEquiv ξ).symm
        (T : IsLocalRing.ResidueField (X.presheaf.stalk ξ)) ≠ 0 :=
  fun h ↦ T.ne_zero ((functionFieldIntegralComponentEquiv ξ).symm.injective (by rw [h, map_zero]))

omit [IsIntegral X] in
/-- The order of vanishing on `Z_ξ` is additive. -/
private theorem ordAt_mul (ξ : X) {x : X} (hmem : x ∈ closure ({ξ} : Set X))
    (T T' : (IsLocalRing.ResidueField (X.presheaf.stalk ξ))ˣ) :
    ordAt ξ hmem (T * T') = ordAt ξ hmem T + ordAt ξ hmem T' := by
  simp only [ordAt, Units.val_mul, map_mul]
  exact Scheme.ord_mul (functionFieldIntegralComponentEquiv_symm_ne_zero ξ T)
    (functionFieldIntegralComponentEquiv_symm_ne_zero ξ T')

omit [IsIntegral X] in
/-- The order of vanishing on `Z_ξ` of an inverse is the negative of the order of vanishing. -/
private theorem ordAt_inv (ξ : X) {x : X} (hmem : x ∈ closure ({ξ} : Set X))
    (T : (IsLocalRing.ResidueField (X.presheaf.stalk ξ))ˣ) :
    ordAt ξ hmem T⁻¹ = -ordAt ξ hmem T := by
  simp only [ordAt, Units.val_inv_eq_inv_val, map_inv₀]
  exact ord_inv_eq_neg (functionFieldIntegralComponentEquiv_symm_ne_zero ξ T)

omit [IsIntegral X] in
/-- The order of vanishing on `Z_ξ` of a power is the multiple of the order of vanishing. -/
private theorem ordAt_pow (ξ : X) {x : X} (hmem : x ∈ closure ({ξ} : Set X))
    (T : (IsLocalRing.ResidueField (X.presheaf.stalk ξ))ˣ) (n : ℕ) :
    ordAt ξ hmem (T ^ n) = n * ordAt ξ hmem T := by
  simp only [ordAt, Units.val_pow_eq_pow_val, map_pow]
  exact Scheme.ord_pow (functionFieldIntegralComponentEquiv_symm_ne_zero ξ T) n _

omit [IsIntegral X] in
/-- Away from codimension one on `Z_ξ` the order of vanishing is zero. -/
private theorem ordAt_eq_zero_of_coheight_ne_one (ξ : X) {x : X}
    (hmem : x ∈ closure ({ξ} : Set X)) (hz : coheight (pointClosurePoint ξ hmem) ≠ 1)
    (T : (IsLocalRing.ResidueField (X.presheaf.stalk ξ))ˣ) : ordAt ξ hmem T = 0 := by
  simp only [ordAt]
  exact Scheme.ord_eq_zero_of_coheight_neq_one hz _

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The image in `R(Z_ξ)` of a germ at `ξ` is the rational function its residue names. -/
private theorem functionFieldIntegralComponentEquiv_symm_residue (ξ : X)
    (u : X.presheaf.stalk ξ) :
    (functionFieldIntegralComponentEquiv ξ).symm (IsLocalRing.residue (X.presheaf.stalk ξ) u) =
      (restrictScalarHom (integralComponentAt ξ) (ξ := ξ)
        (genericPointOf_integralComponentAt ξ)).hom u := by
  rw [← functionFieldIntegralComponentEquiv_restrictScalarHom ξ u, RingEquiv.symm_apply_apply]

variable {L : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The restricted divisor of the chosen generator, at a point where the module is
trivialized.** It is minus the order of vanishing of the correcting unit, read as a rational
function on `Z_ξ`. -/
private theorem ordAt_residue_eq_neg_restrictedWeilDivisorAt (C : ChowSituation.{u})
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {ξ : X} (V : X.Opens) (hξV : ξ ∈ V) (t : Γ(L, V))
    (ht : ∀ (y : X) (hy : y ∈ V), IsStalkBasis L y (L.presheaf.germ V y hy t))
    {x : X} (hmem : x ∈ closure ({ξ} : Set X)) (hxV : x ∈ V)
    (hz1 : coheight (pointClosurePoint ξ hmem) = 1)
    {s : L.presheaf.stalk ξ} (hs : IsStalkBasis L ξ s)
    {u : X.presheaf.stalk ξ} (hu : IsUnit u)
    (hmu : L.presheaf.germ V ξ hξV t = u • s) :
    ordAt ξ hmem
        (Units.map (IsLocalRing.residue (X.presheaf.stalk ξ)).toMonoidHom hu.unit) =
      -weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p ξ s) (pointClosurePoint ξ hmem) := by
  have hYgen : (PrimeDivisor.ofCoheightOne (pointClosurePoint ξ hmem) hz1).genericPoint =
      pointClosurePoint ξ hmem :=
    PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hYV : (integralComponentAt ξ).subschemeι.base
      (PrimeDivisor.ofCoheightOne (pointClosurePoint ξ hmem) hz1).genericPoint ∈ V := by
    rw [hYgen, subschemeι_pointClosurePoint]
    exact hxV
  have h1 : weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p ξ s)
        (pointClosurePoint ξ hmem) =
      orderOfVanishing (restrictModule (integralComponentAt ξ) L)
        (restrictStalk (integralComponentAt ξ) L (genericPointOf_integralComponentAt ξ) s)
        (PrimeDivisor.ofCoheightOne (pointClosurePoint ξ hmem) hz1) := by
    have h := weilDivisorCoeff_genericPoint (restrictedWeilDivisorAt C p ξ s).val
      (PrimeDivisor.ofCoheightOne (pointClosurePoint ξ hmem) hz1)
    rw [hYgen] at h
    exact h
  have h2 := orderOfVanishing_restrictStalk_eq_neg_ord (integralComponentAt ξ) L
    (genericPointOf_integralComponentAt ξ) V hξV t ht
    (PrimeDivisor.ofCoheightOne (pointClosurePoint ξ hmem) hz1) hYV hs hu hmu
  have hval : ((Units.map (IsLocalRing.residue (X.presheaf.stalk ξ)).toMonoidHom hu.unit :
        (IsLocalRing.ResidueField (X.presheaf.stalk ξ))ˣ) :
      IsLocalRing.ResidueField (X.presheaf.stalk ξ)) =
      IsLocalRing.residue (X.presheaf.stalk ξ) u := by
    rw [Units.coe_map, hu.unit_spec]
    rfl
  rw [h1, h2, neg_neg, hYgen]
  simp only [ordAt, hval, functionFieldIntegralComponentEquiv_symm_residue]

end OrdAt

/-! ### The tame symbol on a unit of the local ring -/

section Symbol

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **Stacks 0EAN at a codimension-one point.** The tame symbol of a unit `u` of `B_ξ` against a
nonzero rational function `g` is the residue of `u` raised to `ord_{B_ξ}(g)`, so the order of
vanishing on `Z_ξ` of that symbol is `ord_{B_ξ}(g)` times the order of vanishing of the residue
of `u`. -/
private theorem ordAt_tameSymbolAtCoheightOne_isUnit_left {ξ : X} (hξ1 : coheight ξ = 1)
    {u : X.presheaf.stalk ξ} (hu : IsUnit u) {U G : X.functionFieldˣ}
    (hU : (U : X.functionField) = algebraMap (X.presheaf.stalk ξ) X.functionField u)
    {x : X} (hmem : x ∈ closure ({ξ} : Set X)) :
    ordAt ξ hmem (tameSymbolAtCoheightOne hξ1 U G) =
      X.ord (G : X.functionField) ξ *
        ordAt ξ hmem
          (Units.map (IsLocalRing.residue (X.presheaf.stalk ξ)).toMonoidHom hu.unit) := by
  obtain ⟨b, c, m, k, hb, hc, hbc, hm, hk⟩ := exists_ringOrd_presentation hξ1 G.ne_zero
  have hdim1 : ringKrullDim (X.presheaf.stalk ξ) = 1 :=
    ringKrullDim_stalk_eq_one_of_coheight_eq_one hξ1
  have : Ring.KrullDimLE 1 (X.presheaf.stalk ξ) := krullDimLE_one_stalk_of_coheight_eq_one hξ1
  have hbmem : b ∈ nonZeroDivisors (X.presheaf.stalk ξ) := mem_nonZeroDivisors_of_ne_zero hb
  have hcmem : c ∈ nonZeroDivisors (X.presheaf.stalk ξ) := mem_nonZeroDivisors_of_ne_zero hc
  have hcff : algebraMap (X.presheaf.stalk ξ) X.functionField c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk ξ) X.functionField)).mpr hc
  have hGpres : G = regularFractionUnit (Q := X.functionField) ⟨b, hbmem⟩ *
      (regularFractionUnit (Q := X.functionField) ⟨c, hcmem⟩)⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_inv_eq_inv_val, regularFractionUnit_val, regularFractionUnit_val,
      ← hbc, mul_comm (algebraMap (X.presheaf.stalk ξ) X.functionField c)
        (G : X.functionField), mul_assoc, mul_inv_cancel₀ hcff, mul_one]
  have hUpres : U = regularFractionUnit (Q := X.functionField) ⟨u, hu.mem_nonZeroDivisors⟩ *
      (regularFractionUnit (Q := X.functionField)
        (1 : nonZeroDivisors (X.presheaf.stalk ξ)))⁻¹ := by
    rw [map_one, inv_one, mul_one]
    exact Units.ext (by rw [hU, regularFractionUnit_val])
  have hsym : tameSymbolAtCoheightOne hξ1 U G =
      Units.map (IsLocalRing.residue (X.presheaf.stalk ξ)).toMonoidHom hu.unit ^ m *
        (Units.map (IsLocalRing.residue (X.presheaf.stalk ξ)).toMonoidHom hu.unit ^ k)⁻¹ := by
    change (regularTameSymbolOfKrullDimOne hdim1).extend X.functionField U G = _
    rw [RegularTameSymbol.extend_eq _ X.functionField ⟨u, hu.mem_nonZeroDivisors⟩ 1
        ⟨b, hbmem⟩ ⟨c, hcmem⟩ hUpres hGpres,
      RegularTameSymbol.one_left, RegularTameSymbol.one_left, inv_one, mul_one, mul_one,
      (regularTameSymbolOfKrullDimOne hdim1).unit_left ⟨u, hu.mem_nonZeroDivisors⟩ ⟨b, hbmem⟩
        hu.unit hu.unit_spec.symm,
      (regularTameSymbolOfKrullDimOne hdim1).unit_left ⟨u, hu.mem_nonZeroDivisors⟩ ⟨c, hcmem⟩
        hu.unit hu.unit_spec.symm,
      show (Ring.ord (X.presheaf.stalk ξ) b).toNat = m by rw [hm]; simp,
      show (Ring.ord (X.presheaf.stalk ξ) c).toNat = k by rw [hk]; simp]
  rw [hsym, ordAt_mul, ordAt_inv, ordAt_pow, ordAt_pow,
    ord_eq_sub_ringOrd hξ1 hb hc hbc hm hk]
  ring

end Symbol


/-! ### The local identity at a codimension-two point -/

section Local

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A sum over an index type whose terms vanish outside a subtype is the sum over that
subtype. -/
theorem finsum_eq_finsum_subtype {ι : Type u} {P : ι → Prop} (h : ι → ℤ)
    (hvanish : ∀ i, ¬ P i → h i = 0) :
    ∑ᶠ i : ι, h i = ∑ᶠ j : {i : ι // P i}, h j.1 := by
  rw [finsum_subtype_eq_finsum_cond]
  exact finsum_congr fun i ↦ by by_cases hP : P i <;> simp [hP, hvanish]

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The pushforward of a cycle on the component at `ξ` vanishes at a point that `ξ` does not
specialize to. -/
private theorem closedSubschemeCyclePushforward_eq_zero_of_not_specializes
    (C : ChowSituation.{u}) (p : X ⟶ C.S) (ξ : X)
    (c : AlgebraicCycle (integralComponentAt ξ).subscheme ℤ) {x : X} (hx : ¬ ξ ⤳ x) :
    closedSubschemeCyclePushforward C p (integralComponentAt ξ) c x = 0 := by
  exact closedSubschemeCyclePushforward_apply_of_notMem_range C p _ c fun hmem ↦
    hx (specializes_iff_mem_closure.mpr (mem_closure_of_mem_range_subschemeι hmem))

omit [IsLocallyNoetherian X] in
/-- **A codimension-one point of a prime divisor has codimension two in the ambient scheme.**
The relative dimension of Stacks 02JW drops by one from the generic point of `X` to the generic
point `ξ` of the prime divisor, and by one again from `ξ` to the given point, the base of the
Chow situation being universally catenary. -/
private theorem coheight_eq_two_of_coheight_pointClosurePoint_eq_one (C : ChowSituation.{u})
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {ξ x : X} (hξ1 : coheight ξ = 1)
    (hmem : x ∈ closure ({ξ} : Set X))
    (hz1 : coheight (pointClosurePoint ξ hmem) = 1) : coheight x = 2 := by
  have hn : schemeDeltaDimension C p =
      ((relativeDimension C.dimensionFunction p (genericPoint X) : ℤ) : EInt) :=
    schemeDeltaDimension_eq_genericPoint C p
  have hspec : ξ ⤳ x := specializes_iff_mem_closure.mpr hmem
  have hξδ : relativeDimension C.dimensionFunction p ξ =
      relativeDimension C.dimensionFunction p (genericPoint X) - 1 :=
    relativeDimension_eq_sub_one_of_coheight_eq_one C p hn hξ1
  obtain ⟨m, hdrop, hlocal⟩ := relativeDimension_drop_of_specialization
    C.isUniversallyCatenary C.dimensionFunction p hspec
  have hlocal' : ringKrullDim ((integralComponentAt ξ).subscheme.presheaf.stalk
      (pointClosurePoint ξ hmem)) = ((m : ℕ∞) : WithBot ℕ∞) := hlocal
  have hm1 : m = 1 := by
    have hco : ((m : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
      rw [← hlocal', AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hz1]
    exact_mod_cast hco
  rw [hm1] at hdrop
  have hmax : IsMax (genericPoint X) := fun b _ ↦ genericPoint_specializes b
  have hne : x ≠ ξ := by
    intro h
    rw [h] at hdrop
    omega
  have hle : x ≤ ξ := Scheme.le_iff_specializes.mpr hspec
  have hub : coheight x ≤ ((2 : ℕ) : ℕ∞) := by
    refine Order.coheight_le_coe_iff.mpr fun y hy ↦ ?_
    by_cases hyη : y = genericPoint X
    · rw [hyη, Order.coheight_eq_zero.mpr hmax]
      exact_mod_cast Nat.zero_lt_two
    · have h1 : relativeDimension C.dimensionFunction p y ≤
          relativeDimension C.dimensionFunction p (genericPoint X) - 1 :=
        relativeDimension_le_sub_one_of_ne_genericPoint C p hn hyη
      have h2 : deltaDimensionFunction C p x < deltaDimensionFunction C p y :=
        (deltaDimensionFunction C p).strictAnti_specializes hy.le (ne_of_gt hy)
      rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply] at h2
      have h3 : relativeDimension C.dimensionFunction p y =
          relativeDimension C.dimensionFunction p (genericPoint X) - 1 := by omega
      rw [(relativeDimension_eq_sub_one_iff_coheight_eq_one C p hn y).mp h3]
      exact_mod_cast Nat.one_lt_two
  have hlb : ((2 : ℕ) : ℕ∞) ≤ coheight x := by
    have hlt : x < ξ :=
      lt_iff_le_not_ge.mpr ⟨hle, fun h ↦ hne (Specializes.antisymm h hle).eq⟩
    simpa [hξ1, one_add_one_eq_two] using Order.coheight_add_one_le hlt
  exact_mod_cast le_antisymm hub hlb

end Local

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N) (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]

omit [IsLocallyNoetherian X] [LocallyOfFiniteType p] in
/-- Only finitely many members of the family pass through a point: the family is locally
finite. -/
private theorem finite_componentPoint_specializes (x : X) :
    Finite {i : ℱ.Index // ℱ.componentPoint i ⤳ x} := by
  have hfin := ℱ.locallyFinite_component.point_finite x
  refine (hfin.subset ?_).to_subtype
  intro i hi
  rw [Set.mem_ofPred_eq, (ℱ.component i).support_eq_closure]
  exact specializes_iff_mem_closure.mp hi

/-- The `i`-th summand of the left hand side of the key formula, written out. -/
private theorem componentDifference_toKeyFormulaData
    (i : (ℱ.toKeyFormulaData C p).Index)
    (z : ((ℱ.toKeyFormulaData C p).component i).subscheme) :
    (ℱ.toKeyFormulaData C p).componentDifference i z =
      ℱ.orderL i * weilDivisorAlgebraicCycle
          (restrictedWeilDivisorAt C p (ℱ.componentPoint i) (ℱ.localGeneratorN i)) z -
        ℱ.orderN i * weilDivisorAlgebraicCycle
          (restrictedWeilDivisorAt C p (ℱ.componentPoint i) (ℱ.localGeneratorL i)) z := by
  rw [KeyFormulaData.componentDifference_apply]
  rfl

omit [IsLocallyNoetherian X] in
/-- **Two generators of `L_ξ` differing by a unit give coordinates differing by that unit.** If
the rational function `r` expresses a meromorphic section of `L` against the generator `s` of
`L_ξ`, and `a` expresses the same section against the generator `w = u s`, then `r = a u`
in `R(X)ˣ`. -/
private theorem mk0_eq_mk0_mul_unit {ξ : X} {s w : L.presheaf.stalk ξ}
    (hs : IsStalkBasis L ξ s) {σ : L.presheaf.stalk (genericPoint X)}
    {r : X.functionField} (hr0 : r ≠ 0) (hr : r • toGenericStalk L ξ s = σ)
    {a : X.functionField} (ha0 : a ≠ 0) (ha : σ = a • toGenericStalk L ξ w)
    {u : X.presheaf.stalk ξ} {U : X.functionFieldˣ}
    (hU : (U : X.functionField) = algebraMap (X.presheaf.stalk ξ) X.functionField u)
    (hw : w = u • s) :
    Units.mk0 r hr0 = Units.mk0 a ha0 * U := by
  have hinv := isInvertible_presheaf L
  have hval : r = a * algebraMap (X.presheaf.stalk ξ) X.functionField u := by
    refine (hs.toGenericStalk (isTrivializedNear_of_isInvertible L ξ)).injective ?_
    change r • toGenericStalk L ξ s = _
    rw [hr, ha, hw, toGenericStalk_smul, mul_smul]
  exact Units.ext (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0, hU, hval])

/-- **The tame symbol of the situation expands into four symbols.** If the ratios `f_i` and `g_i`
factor as `f_i = A U` and `g_i = B V` in `R(X)ˣ`, then the symbol `∂_{B_i}(f_i, g_i)` is the
product of the four symbols `∂(A, B)`, `∂(A, V)`, `∂(U, B)` and `∂(U, V)`. -/
private theorem tameSymbol_eq_mul {i : ℱ.Index} (hξ1 : coheight (ℱ.componentPoint i) = 1)
    {A B U V : X.functionFieldˣ}
    (hL : Units.mk0 (ℱ.ratioL i) (ℱ.ratioL_ne_zero i) = A * U)
    (hN : Units.mk0 (ℱ.ratioN i) (ℱ.ratioN_ne_zero i) = B * V) :
    ℱ.tameSymbol i =
      tameSymbolAtCoheightOne hξ1 A B * tameSymbolAtCoheightOne hξ1 A V *
        (tameSymbolAtCoheightOne hξ1 U B * tameSymbolAtCoheightOne hξ1 U V) := by
  change tameSymbolAtCoheightOne hξ1 (Units.mk0 (ℱ.ratioL i) (ℱ.ratioL_ne_zero i))
    (Units.mk0 (ℱ.ratioN i) (ℱ.ratioN_ne_zero i)) = _
  rw [hL, hN, (tameSymbolAtCoheightOne hξ1).map_mul_left,
    (tameSymbolAtCoheightOne hξ1).map_mul_right, (tameSymbolAtCoheightOne hξ1).map_mul_right]

/-- **The tame symbol of two units of `B_ξ` has no order of vanishing on `Z_ξ`.** By Stacks 0EAN
the symbol is a power of the residue of the left unit, the exponent being the order of vanishing
of the right one, which is zero. -/
private theorem ordAt_tameSymbolAtCoheightOne_isUnit_isUnit {ξ : X} (hξ1 : coheight ξ = 1)
    {u v : X.presheaf.stalk ξ} (hu : IsUnit u) (hv : IsUnit v) {U V : X.functionFieldˣ}
    (hU : (U : X.functionField) = algebraMap (X.presheaf.stalk ξ) X.functionField u)
    (hV : (V : X.functionField) = algebraMap (X.presheaf.stalk ξ) X.functionField v)
    {x : X} (hmem : x ∈ closure ({ξ} : Set X)) :
    ordAt ξ hmem (tameSymbolAtCoheightOne hξ1 U V) = 0 := by
  rw [ordAt_tameSymbolAtCoheightOne_isUnit_left hξ1 hu hU hmem, hV,
    Scheme.ord_algebraMap_of_isUnit hξ1 hv, zero_mul]

/-- **The order of vanishing of a correcting tame symbol, the unit on the left.** For a unit `u`
of `B_ξ` relating the chosen generator `s` of `L_ξ` to the germ of a section trivializing `L`
near a codimension-one point of `Z_ξ`, the order of vanishing on `Z_ξ` of `∂_{B_ξ}(u, G)` is
`ord_{B_ξ}(G)` times minus the coefficient there of `div_{L|Z_ξ}(s|Z_ξ)`: Stacks 0EAN followed
by Stacks 02SH. -/
private theorem ordAt_tameSymbolAtCoheightOne_unit_left {ξ : X} (hξ1 : coheight ξ = 1)
    (V : X.Opens) (hξV : ξ ∈ V) (t : Γ(L, V))
    (ht : ∀ (y : X) (hy : y ∈ V), IsStalkBasis L y (L.presheaf.germ V y hy t))
    {x : X} (hmem : x ∈ closure ({ξ} : Set X)) (hxV : x ∈ V)
    (hz1 : coheight (pointClosurePoint ξ hmem) = 1)
    {s : L.presheaf.stalk ξ} (hs : IsStalkBasis L ξ s)
    {u : X.presheaf.stalk ξ} (hu : IsUnit u)
    (hmu : L.presheaf.germ V ξ hξV t = u • s) {U G : X.functionFieldˣ}
    (hU : (U : X.functionField) = algebraMap (X.presheaf.stalk ξ) X.functionField u) :
    ordAt ξ hmem (tameSymbolAtCoheightOne hξ1 U G) =
      X.ord (G : X.functionField) ξ *
        -weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p ξ s)
          (pointClosurePoint ξ hmem) := by
  rw [ordAt_tameSymbolAtCoheightOne_isUnit_left hξ1 hu hU hmem,
    ordAt_residue_eq_neg_restrictedWeilDivisorAt C p V hξV t ht hmem hxV hz1 hs hu hmu]

/-- **The order of vanishing of a correcting tame symbol, the unit on the right.** The symbol is
antisymmetric, so this is minus the value of
`Stacks.Chow.KeyFormulaSituation.ordAt_tameSymbolAtCoheightOne_unit_left`. -/
private theorem ordAt_tameSymbolAtCoheightOne_unit_right {ξ : X} (hξ1 : coheight ξ = 1)
    (V : X.Opens) (hξV : ξ ∈ V) (t : Γ(L, V))
    (ht : ∀ (y : X) (hy : y ∈ V), IsStalkBasis L y (L.presheaf.germ V y hy t))
    {x : X} (hmem : x ∈ closure ({ξ} : Set X)) (hxV : x ∈ V)
    (hz1 : coheight (pointClosurePoint ξ hmem) = 1)
    {s : L.presheaf.stalk ξ} (hs : IsStalkBasis L ξ s)
    {u : X.presheaf.stalk ξ} (hu : IsUnit u)
    (hmu : L.presheaf.germ V ξ hξV t = u • s) {F G : X.functionFieldˣ}
    (hG : (G : X.functionField) = algebraMap (X.presheaf.stalk ξ) X.functionField u) :
    ordAt ξ hmem (tameSymbolAtCoheightOne hξ1 F G) =
      -(X.ord (F : X.functionField) ξ *
        -weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p ξ s)
          (pointClosurePoint ξ hmem)) := by
  rw [(tameSymbolAtCoheightOne hξ1).symm_eq_inv, ordAt_inv,
    ordAt_tameSymbolAtCoheightOne_unit_left C p hξ1 V hξV t ht hmem hxV hz1 hs hu hmu hG]

/-- **The local identity at one member of the family.** At a point `x` of the member `Z_i`, the
order of vanishing of the tame symbol `∂_{B_i}(f_i, g_i)` on `Z_i` is the coefficient at `x` of
`ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i)` plus the order of
vanishing of the tame symbol of the pair of coordinates read from trivializations near `x`.

The two ratios of the situation differ from those coordinates by units of `B_i`; by Stacks 0EAN
the correcting symbols are powers of the residues of those units, and by Stacks 02SH the orders
of vanishing of those residues on `Z_i` are minus the restricted divisors, the trivializing germs
restricting to generators at `x`. -/
private theorem ordAt_tameSymbol_eq {x : X} {i : ℱ.Index}
    (hmem : x ∈ closure ({ℱ.componentPoint i} : Set X))
    {VL : X.Opens} (hxVL : x ∈ VL) {tL : Γ(L, VL)}
    (htL : ∀ (y : X) (hy : y ∈ VL), IsStalkBasis L y (L.presheaf.germ VL y hy tL))
    {a : X.functionField} (ha0 : a ≠ 0)
    (ha : ∀ (y : X) (hy : y ∈ VL),
      ℱ.sectionL = a • toGenericStalk L y (L.presheaf.germ VL y hy tL))
    {VN : X.Opens} (hxVN : x ∈ VN) {tN : Γ(N, VN)}
    (htN : ∀ (y : X) (hy : y ∈ VN), IsStalkBasis N y (N.presheaf.germ VN y hy tN))
    {b : X.functionField} (hb0 : b ≠ 0)
    (hb : ∀ (y : X) (hy : y ∈ VN),
      ℱ.sectionN = b • toGenericStalk N y (N.presheaf.germ VN y hy tN)) :
    ordAt (ℱ.componentPoint i) hmem (ℱ.tameSymbol i) =
      (ℱ.orderL i * weilDivisorAlgebraicCycle
            (restrictedWeilDivisorAt C p (ℱ.componentPoint i) (ℱ.localGeneratorN i))
            (pointClosurePoint (ℱ.componentPoint i) hmem) -
          ℱ.orderN i * weilDivisorAlgebraicCycle
            (restrictedWeilDivisorAt C p (ℱ.componentPoint i) (ℱ.localGeneratorL i))
            (pointClosurePoint (ℱ.componentPoint i) hmem)) +
        ordAt (ℱ.componentPoint i) hmem
          (tameSymbolAtCoheightOne (ℱ.coheight_componentPoint i) (Units.mk0 a ha0)
            (Units.mk0 b hb0)) := by
  have hinvL := isInvertible_presheaf L
  have hinvN := isInvertible_presheaf N
  have hξ1 : coheight (ℱ.componentPoint i) = 1 := ℱ.coheight_componentPoint i
  have hspec : ℱ.componentPoint i ⤳ x := specializes_iff_mem_closure.mpr hmem
  have hξVL : ℱ.componentPoint i ∈ VL := hspec.mem_open VL.isOpen hxVL
  have hξVN : ℱ.componentPoint i ∈ VN := hspec.mem_open VN.isOpen hxVN
  have hordL : ℱ.orderL i = X.ord a (ℱ.componentPoint i) :=
    orderOfVanishing_eq (isTrivializedNear_of_isInvertible L _)
      (ha := ⟨_, htL _ hξVL, ha _ hξVL⟩)
  have hordN : ℱ.orderN i = X.ord b (ℱ.componentPoint i) :=
    orderOfVanishing_eq (isTrivializedNear_of_isInvertible N _)
      (ha := ⟨_, htN _ hξVN, hb _ hξVN⟩)
  obtain ⟨u, hu, hmu⟩ := exists_isUnit_smul_eq (ℱ.isStalkBasis_localGeneratorL i) (htL _ hξVL)
  obtain ⟨v, hv, hmv⟩ := exists_isUnit_smul_eq (ℱ.isStalkBasis_localGeneratorN i) (htN _ hξVN)
  -- the correcting units, read in the function field
  obtain ⟨U, hUval⟩ : ∃ U : X.functionFieldˣ, (U : X.functionField) =
      algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField u :=
    ⟨(hu.map _).unit, (hu.map _).unit_spec⟩
  obtain ⟨V, hVval⟩ : ∃ V : X.functionFieldˣ, (V : X.functionField) =
      algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField v :=
    ⟨(hv.map _).unit, (hv.map _).unit_spec⟩
  -- the four-term expansion of the symbol
  have hsplit := ℱ.tameSymbol_eq_mul hξ1
    (mk0_eq_mk0_mul_unit (ℱ.isStalkBasis_localGeneratorL i) (ℱ.ratioL_ne_zero i)
      (ℱ.ratioL_smul_localGeneratorL i) ha0 (ha _ hξVL) hUval hmu)
    (mk0_eq_mk0_mul_unit (ℱ.isStalkBasis_localGeneratorN i) (ℱ.ratioN_ne_zero i)
      (ℱ.ratioN_smul_localGeneratorN i) hb0 (hb _ hξVN) hVval hmv)
  by_cases hz1 : coheight (pointClosurePoint (ℱ.componentPoint i) hmem) = 1
  · -- the three unit terms, computed by Stacks 0EAN and Stacks 02SH
    rw [hsplit, ordAt_mul, ordAt_mul, ordAt_mul,
      ordAt_tameSymbolAtCoheightOne_isUnit_isUnit hξ1 hu hv hUval hVval hmem,
      ordAt_tameSymbolAtCoheightOne_unit_left C p hξ1 VL hξVL tL htL hmem hxVL hz1
        (ℱ.isStalkBasis_localGeneratorL i) hu hmu hUval,
      ordAt_tameSymbolAtCoheightOne_unit_right C p hξ1 VN hξVN tN htN hmem hxVN hz1
        (ℱ.isStalkBasis_localGeneratorN i) hv hmv hVval,
      Units.val_mk0, Units.val_mk0, ← hordL, ← hordN]
    ring
  · -- away from codimension one on `Z_i` every term vanishes
    simp only [weilDivisorAlgebraicCycle_apply, ordAt_eq_zero_of_coheight_ne_one _ hmem hz1,
      weilDivisorCoeff_eq_zero_of_coheight_ne_one _ hz1]
    ring

omit [IsLocallyNoetherian X] in
/-- **A trivialization near a point, with one coordinate serving every point of it.** Near any
point `L` has a section whose germ generates the stalk at each point of its domain, and a single
rational function expresses the meromorphic section `σ` against all of those generators. -/
private theorem exists_isStalkBasis_coordinate (x : X)
    (σ : L.presheaf.stalk (genericPoint X)) :
    ∃ (V : X.Opens) (_ : x ∈ V) (t : Γ(L, V)),
      (∀ (y : X) (hy : y ∈ V), IsStalkBasis L y (L.presheaf.germ V y hy t)) ∧
        ∃ a : X.functionField, ∀ (y : X) (hy : y ∈ V),
          σ = a • toGenericStalk L y (L.presheaf.germ V y hy t) := by
  have hinv := isInvertible_presheaf L
  obtain ⟨V, hxV, t, ht⟩ := isTrivializedNear_of_isInvertible L x
  have hηV : genericPoint X ∈ V := genericPoint_mem_of_mem hxV
  obtain ⟨a, ha⟩ := (IsStalkBasis.toGenericStalk ⟨V, hxV, t, ht⟩ (ht x hxV)).surjective σ
  refine ⟨V, hxV, t, ht, a, fun y hy ↦ ?_⟩
  rw [toGenericStalk_germ hy hηV, ← toGenericStalk_germ hxV hηV]
  exact ha.symm

/-- **The left hand side at a point is carried by the members of the family through it.** The
coefficient at `x` of the pushforward of the cycles `ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) -
ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i)` is the sum of their coefficients at `x`, read on the members
`Z_i` passing through `x`; a member missing `x` contributes nothing. -/
private theorem leftCoeff_eq_finsum_componentDifference (x : X) :
    (ℱ.toKeyFormulaData C p).leftCoeff C p x =
      ∑ᶠ j : {i : ℱ.Index // ℱ.componentPoint i ⤳ x},
        (ℱ.toKeyFormulaData C p).componentDifference j.1
          (pointClosurePoint (ℱ.componentPoint j.1)
            (specializes_iff_mem_closure.mp j.2)) := by
  have h1 : (ℱ.toKeyFormulaData C p).leftCoeff C p x =
      ∑ᶠ i : ℱ.Index, closedSubschemeCyclePushforward C p
        ((ℱ.toKeyFormulaData C p).component i)
        ((ℱ.toKeyFormulaData C p).componentDifference i) x := rfl
  rw [h1, finsum_eq_finsum_subtype (P := fun i ↦ ℱ.componentPoint i ⤳ x) _ fun i hi ↦ ?_]
  · refine finsum_congr fun j ↦ ?_
    have hxj : ((ℱ.toKeyFormulaData C p).component j.1).subschemeι.base
        (pointClosurePoint (ℱ.componentPoint j.1)
          (specializes_iff_mem_closure.mp j.2)) = x :=
      subschemeι_pointClosurePoint _ _
    have h := closedSubschemeCyclePushforward_apply C p
      ((ℱ.toKeyFormulaData C p).component j.1)
      ((ℱ.toKeyFormulaData C p).componentDifference j.1)
      (pointClosurePoint (ℱ.componentPoint j.1) (specializes_iff_mem_closure.mp j.2))
    rw [hxj] at h
    exact h
  · exact closedSubschemeCyclePushforward_eq_zero_of_not_specializes C p _ _ hi

/-- **The right hand side at a codimension-two point is carried by the members of the family
through it.** The coefficient at `x` of the sum of the principal divisors of the tame symbols
`∂_{B_i}(f_i, g_i)` is the sum over the members `Z_i` through `x` of the orders of vanishing of
those symbols on them. -/
private theorem tameSymbolCoeff_eq_finsum_ordAt {x : X} (hx2 : coheight x = 2) :
    (ℱ.toKeyFormulaData C p).tameSymbolCoeff C p x =
      ∑ᶠ j : {i : ℱ.Index // ℱ.componentPoint i ⤳ x},
        ordAt (ℱ.componentPoint j.1) (specializes_iff_mem_closure.mp j.2)
          (ℱ.tameSymbol j.1) := by
  have h1 : (ℱ.toKeyFormulaData C p).tameSymbolCoeff C p x =
      ∑ᶠ i : ℱ.Index, principalDivisorPushforward C p
        ((ℱ.toKeyFormulaData C p).component i)
        ((ℱ.toKeyFormulaData C p).isIntegral_component i)
        ((ℱ.toKeyFormulaData C p).tameSymbol i) x :=
    (ℱ.toKeyFormulaData C p).tameSymbolCoeff_eq_finsum C p x
  rw [h1, finsum_eq_finsum_subtype (P := fun i ↦ ℱ.componentPoint i ⤳ x) _ fun i hi ↦ ?_]
  · refine finsum_congr fun j ↦ ?_
    rw [← ℱ.fracTameSymbolOrderAt_component_eq_principalDivisorPushforward C p
      (ringKrullDim_stalk_eq_two_of_coheight_eq_two hx2) j,
      fracTameSymbolOrderAt_canonical_eq_ord_tameSymbolAtCoheightOne
        (ringKrullDim_stalk_eq_two_of_coheight_eq_two hx2) (ℱ.componentHeightOnePrime j)
        (ℱ.pointOfHeightOnePrime_componentHeightOnePrime j) (ℱ.coheight_componentPoint j.1)
        (specializes_iff_mem_closure.mp j.2)]
    rfl
  · rw [principalDivisorPushforward_eq]
    exact closedSubschemeCyclePushforward_eq_zero_of_not_specializes C p _ _ hi

/-- **The reciprocity law of Stacks 0EAX at a pair of coordinates.** For coordinates `a` of `s`
and `b` of `t` at every generization of a codimension-two point `x`, the orders of vanishing of
the symbol `∂(a, b)` on the members of the family through `x` sum to zero. -/
private theorem finsum_ordAt_tameSymbolAtCoheightOne_eq_zero {x : X} (hx2 : coheight x = 2)
    {a : X.functionField} (ha0 : a ≠ 0) {b : X.functionField} (hb0 : b ≠ 0)
    (hcoordL : ∀ y : X, y ⤳ x → IsCoordinateAt L y ℱ.sectionL a)
    (hcoordN : ∀ y : X, y ⤳ x → IsCoordinateAt N y ℱ.sectionN b) :
    ∑ᶠ j : {i : ℱ.Index // ℱ.componentPoint i ⤳ x},
        ordAt (ℱ.componentPoint j.1) (specializes_iff_mem_closure.mp j.2)
          (tameSymbolAtCoheightOne (ℱ.coheight_componentPoint j.1) (Units.mk0 a ha0)
            (Units.mk0 b hb0)) = 0 := by
  have hreci := ℱ.finsum_fracTameSymbolOrderAt_component_eq_zero hx2 hcoordL hcoordN
    (F := Units.map ((functionFieldEquivFractionRing x).toRingEquiv :
      X.functionField →+* FractionRing (X.presheaf.stalk x)).toMonoidHom (Units.mk0 a ha0))
    (G := Units.map ((functionFieldEquivFractionRing x).toRingEquiv :
      X.functionField →+* FractionRing (X.presheaf.stalk x)).toMonoidHom (Units.mk0 b hb0))
    rfl rfl
  rw [← hreci]
  refine finsum_congr fun j ↦ ?_
  exact (fracTameSymbolOrderAt_canonical_eq_ord_tameSymbolAtCoheightOne
    (ringKrullDim_stalk_eq_two_of_coheight_eq_two hx2) (ℱ.componentHeightOnePrime j)
    (ℱ.pointOfHeightOnePrime_componentHeightOnePrime j) (ℱ.coheight_componentPoint j.1)
    (specializes_iff_mem_closure.mp j.2) (Units.mk0 a ha0) (Units.mk0 b hb0)).symm

/-- **The two coefficients of the key formula agree at a codimension-two point.** -/
private theorem leftCoeff_eq_tameSymbolCoeff {x : X} (hx2 : coheight x = 2) :
    (ℱ.toKeyFormulaData C p).leftCoeff C p x =
      (ℱ.toKeyFormulaData C p).tameSymbolCoeff C p x := by
  -- the trivializations near `x` and the two coordinates they produce
  obtain ⟨VL, hxVL, tL, htL, a, ha⟩ := exists_isStalkBasis_coordinate x ℱ.sectionL
  obtain ⟨VN, hxVN, tN, htN, b, hb⟩ := exists_isStalkBasis_coordinate x ℱ.sectionN
  have hcoordL : ∀ y : X, y ⤳ x → IsCoordinateAt L y ℱ.sectionL a := fun y hy ↦
    ⟨_, htL y (hy.mem_open VL.isOpen hxVL), ha y (hy.mem_open VL.isOpen hxVL)⟩
  have hcoordN : ∀ y : X, y ⤳ x → IsCoordinateAt N y ℱ.sectionN b := fun y hy ↦
    ⟨_, htN y (hy.mem_open VN.isOpen hxVN), hb y (hy.mem_open VN.isOpen hxVN)⟩
  have ha0 : a ≠ 0 := (hcoordL x (specializes_refl x)).ne_zero ℱ.sectionL_ne_zero
  have hb0 : b ≠ 0 := (hcoordN x (specializes_refl x)).ne_zero ℱ.sectionN_ne_zero
  have : Finite {i : ℱ.Index // ℱ.componentPoint i ⤳ x} :=
    ℱ.finite_componentPoint_specializes x
  -- the two sides, summed over the members through `x`
  rw [ℱ.leftCoeff_eq_finsum_componentDifference C p x,
    ℱ.tameSymbolCoeff_eq_finsum_ordAt C p hx2]
  -- the local identity at each member, and the reciprocity law of Stacks 0EAX
  rw [finsum_congr fun j ↦ ℱ.ordAt_tameSymbol_eq C p
      (specializes_iff_mem_closure.mp j.2) hxVL htL ha0 ha hxVN htN hb0 hb]
  rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _),
    ℱ.finsum_ordAt_tameSymbolAtCoheightOne_eq_zero hx2 ha0 hb0 hcoordL hcoordN, add_zero]
  exact finsum_congr fun j ↦ ℱ.componentDifference_toKeyFormulaData C p j.1
    (pointClosurePoint (ℱ.componentPoint j.1) (specializes_iff_mem_closure.mp j.2))

/-- **Stacks 0AYC for the situation of Stacks 0AYB.** The key formula holds for the cycle-level
data of the sheaf-level situation: the difference of the two Chern-class cycles is the locally
finite sum of the principal divisors of the tame symbols `∂_{B_i}(f_i, g_i)` on the members of the
family.

At a codimension-two point `x` of a member of the family the two coefficients are compared by the
local reciprocity law Stacks 0EAX on `A = 𝒪_{X, x}`, read at the pair of coordinates of `s` and
`t` taken from trivializations of `L` and `N` near `x`: that sum vanishes, the members of the
family carry all of it, and the difference between its summands and the summands of the right
hand side of the key formula is the change-of-generator correction of Stacks 0EAN and Stacks
02SH, which is the left hand side. See the module documentation. -/
@[stacks 0AYC "the key formula itself, for the sheaf-level situation of Stacks 0AYB: the \
difference of the two Chern-class cycles equals the sum of the principal divisors of the tame \
symbols"]
theorem keyFormula_toKeyFormulaData : (ℱ.toKeyFormulaData C p).KeyFormula C p := by
  rw [KeyFormulaData.keyFormula_iff_forall_component_coheight_one]
  intro i₀ z₀ hz₀
  have hmem₀ : ((ℱ.toKeyFormulaData C p).component i₀).subschemeι.base z₀ ∈
      closure ({ℱ.componentPoint i₀} : Set X) := mem_closure_of_mem_range_subschemeι ⟨z₀, rfl⟩
  refine ℱ.leftCoeff_eq_tameSymbolCoeff C p
    (coheight_eq_two_of_coheight_pointClosurePoint_eq_one C p
      (ℱ.coheight_componentPoint i₀) hmem₀ ?_)
  have hz₀eq : pointClosurePoint (ℱ.componentPoint i₀) hmem₀ = z₀ :=
    Subtype.ext (((ℱ.toKeyFormulaData C p).component i₀).subschemeι_apply z₀)
  rw [hz₀eq]
  exact hz₀

end KeyFormulaSituation

end Stacks.Chow

end
