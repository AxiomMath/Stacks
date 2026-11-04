module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.EquationsQuotient

/-!
# Restricting the input of the Gysin map to an equation chart

The Gysin map of [Stacks, Tag 0G83] is built from *global* equations: it consumes
`Stacks.Gysin.IsCutOutByEquations i f` for `f : I → Γ(X, 𝒪_X)`. The gluing of [Stacks, Tag 0G86]
has only *local* equations, one family `f : I → Γ(X, W)` per chart `W`, so to call Tag 0G83 on a
chart one must move the whole situation onto the open subscheme `W`. This file provides the two
pieces that make that move:

* the chart-local form of the hypothesis, `Stacks.Gysin.IsCutOutByEquationsOn i W f`, and its
  transport along the restricted closed immersion `i ∣_ W`, which turns it into the *global*
  hypothesis `Stacks.Gysin.IsCutOutByEquations (i ∣_ W)` on `W.toScheme`;
* the identification `(Ω^n_{X/S})|_W ≅ Ω^n_{W/S}` of relative differential forms in every degree
  `n`, the degree-`n` analogue of `Stacks.AlgebraicGeometry.DifferentialsRestrict.restrictIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.DifferentialsRestrict.restrictFormsIso`: for a commutative square
  whose horizontal arrows are an open immersion `f : X' ⟶ X` and an étale `g : S' ⟶ S`, the
  identification `(Ω^n_{X/S})|_{X'} ≅ Ω^n_{X'/S'}` in every degree.
* `Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictIso`: the
  special case `(Ω^n_{X/S})|_W ≅ Ω^n_{W/S}` of an open subscheme over the same base, and
  `relativeDifferentialFormsRestrictIsoOfEq`, the same with the structural morphism of `W`
  presented as an arbitrary morphism equal to `W.ι ≫ π`.
* `Stacks.Gysin.IsCutOutByEquationsOn`: the chart-local form of
  `Stacks.Gysin.IsCutOutByEquations` — the equations live on an open `W` and cut out the closed
  subscheme over the opens contained in `W`.
* `Stacks.Gysin.restrictEquations`: the chart-local equations read as global sections of the
  open subscheme `W`.

## Main results

* `Stacks.Gysin.IsCutOutByEquationsOn.morphismRestrict`: **the transport.** If `f : I → Γ(X, W)`
  cuts out `Z` over the opens contained in `W`, then `Stacks.Gysin.restrictEquations W f` cuts
  out the closed subscheme `i ∣_ W` of `W.toScheme` in the sense of
  `Stacks.Gysin.IsCutOutByEquations`, so `AlgebraicGeometry.Scheme.Hom.gysinMap` applies on
  `W.toScheme`.
* `Stacks.Gysin.IsCutOutByEquations.on`: the converse direction for a global family, which is
  the chart `W = ⊤` and, more generally, any chart of a globally cut out subscheme.

## Implementation notes

The chart-local hypothesis is phrased on the opens of `X` contained in `W` rather than on the
opens of `W.toScheme`, because that is the form a chart of
`Stacks.Gysin.GysinChartData` comes in: its fields are indexed by `V : X.Opens` together with
`V ≤ ambient a`. The transport is then the order isomorphism between the opens of `W.toScheme`
and the opens of `X` below `W`, which is `W.ι ''ᵁ ·` one way and `W.ι ⁻¹ᵁ ·` the other
(`AlgebraicGeometry.IsOpenImmersion.opensEquiv`). Nothing deeper happens: the `exists_eq_sum`
field of `Stacks.Gysin.IsCutOutByEquations` is already quantified over *all* opens, so the
content of the transport is only the bookkeeping of restriction maps, and every such
bookkeeping step is `CategoryTheory.Subsingleton.elim` in the poset `X.Opens`.

The forms isomorphism is the composite named in [Stacks, Tag 0FLV]: restriction along an open
immersion is the inverse image (`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`),
and on inverse images the canonical map
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` of a square with étale horizontal
arrows is an isomorphism in every degree. Only this étale case is used, so no hypothesis on `π`
is needed.

## References

* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.DifferentialsRestrict

open AlgebraicGeometry.Scheme.Hom

variable {X' X S' S : Scheme.{u}}

/-- The comparison `(Ω^n_{X/S})|_{X'} ⟶ Ω^n_{X'/S'}` attached to a commutative square whose
left-hand arrow `f : X' ⟶ X` is an open immersion: restriction along `f` is the inverse image
along `f`, and on inverse images this is the canonical map
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` of the square. -/
def toRestrictForms (f : X' ⟶ X) [IsOpenImmersion f] (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
    (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    Scheme.Modules.restrict (relativeDifferentialForms p n) f ⟶
      relativeDifferentialForms p' n :=
  (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (relativeDifferentialForms p n) ≫
    relativeDifferentialFormsMap f p p' g hcomm n

/-- **Stacks Project, Tag 0FLV.** If the two horizontal arrows of the square are étale — and an
open immersion is étale — then `toRestrictForms` is an isomorphism in every degree. -/
theorem isIso_toRestrictForms (f : X' ⟶ X) [IsOpenImmersion f] (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) [Etale g] (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    IsIso (toRestrictForms f p p' g hcomm n) := by
  have hmap : IsIso (relativeDifferentialFormsMap f p p' g hcomm n) :=
    isIso_relativeDifferentialFormsMap_of_etale f p p' g hcomm n
  rw [toRestrictForms]
  infer_instance

/-- **Stacks Project, Tag 0FLV: the restriction of the relative differential `n`-forms along an
open immersion is the relative differential `n`-forms of the restricted morphism**, in every
degree `n`. This is the degree-`n` analogue of
`Stacks.AlgebraicGeometry.DifferentialsRestrict.restrictIso`, which is the case of the module of
relative differentials itself. -/
def restrictFormsIso (f : X' ⟶ X) [IsOpenImmersion f] (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
    [Etale g] (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    Scheme.Modules.restrict (relativeDifferentialForms p n) f ≅
      relativeDifferentialForms p' n :=
  letI := isIso_toRestrictForms f p p' g hcomm n
  asIso (toRestrictForms f p p' g hcomm n)

/-- The forward map of `restrictFormsIso` is `toRestrictForms`. -/
@[simp]
theorem restrictFormsIso_hom (f : X' ⟶ X) [IsOpenImmersion f] (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) [Etale g] (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    (restrictFormsIso f p p' g hcomm n).hom = toRestrictForms f p p' g hcomm n :=
  rfl

variable (π : X ⟶ S) (W : X.Opens)

/-- **`(Ω^n_{X/S})|_W ≅ Ω^n_{W/S}` for an open subscheme `W` of `X`**, with the structural
morphism of `W` presented as an arbitrary morphism `π'` equal to `W.ι ≫ π`. The square has
`𝟙 S` on the base, which is étale. -/
def relativeDifferentialFormsRestrictIsoOfEq {π' : W.toScheme ⟶ S} (hπ' : W.ι ≫ π = π')
    (n : ℤ) :
    Scheme.Modules.restrict (relativeDifferentialForms π n) W.ι ≅
      relativeDifferentialForms π' n :=
  restrictFormsIso W.ι π π' (𝟙 S) (by rw [hπ', Category.comp_id]) n

/-- **`(Ω^n_{X/S})|_W ≅ Ω^n_{W/S}` for an open subscheme `W` of `X`**, in every degree `n`. -/
def relativeDifferentialFormsRestrictIso (n : ℤ) :
    Scheme.Modules.restrict (relativeDifferentialForms π n) W.ι ≅
      relativeDifferentialForms (W.ι ≫ π) n :=
  relativeDifferentialFormsRestrictIsoOfEq π W rfl n

/-- **`(Ω^n_{X/S})|_U ≅ Ω^n_{U/V}` for open subschemes `U ⊆ X` and `V ⊆ S` with `f U ⊆ V`**, in
every degree `n`: the degree-`n` analogue of
`Stacks.AlgebraicGeometry.DifferentialsRestrict.restrictIso` at its own generality. -/
def relativeDifferentialFormsResLEIso (f : X ⟶ S) (V : S.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ V) (n : ℤ) :
    Scheme.Modules.restrict (relativeDifferentialForms f n) U.ι ≅
      relativeDifferentialForms (f.resLE V U e) n :=
  restrictFormsIso U.ι f (f.resLE V U e) V.ι (Scheme.Hom.resLE_comp_ι f e).symm n

end Stacks.AlgebraicGeometry.DifferentialsRestrict

namespace Stacks.Gysin

variable {X Z : Scheme.{u}}

/-- Two restriction maps of the structure sheaf between the same two opens agree, because the
morphisms of the poset `X.Opens` between two opens form a subsingleton. -/
theorem presheaf_map_congr {Y : Scheme.{u}} {U U' : Y.Opens} (g g' : op U ⟶ op U')
    (y : Γ(Y, U)) : Y.presheaf.map g y = Y.presheaf.map g' y :=
  congrArg (fun t => Y.presheaf.map t y) (Subsingleton.elim g g')

/-- A section of `𝒪_X` vanishing on the closed subscheme still vanishes on it after any
restriction. -/
theorem app_map_eq_zero (i : Z ⟶ X) {U U' : X.Opens} (g : op U ⟶ op U') {r : Γ(X, U)}
    (hr : (i.app U) r = 0) : (i.app U') (X.presheaf.map g r) = 0 := by
  have h := congrArg (fun φ : Γ(X, U) ⟶ Γ(Z, i ⁻¹ᵁ U') => ConcreteCategory.hom φ r)
    (i.naturality g)
  simp only [ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  rw [hr]
  exact map_zero _

/-- Two successive restriction maps of the structure sheaf compose to one. -/
theorem presheaf_map_comp_apply {Y : Scheme.{u}} {U V T : Y.Opens} (g : op U ⟶ op V)
    (g' : op V ⟶ op T) (y : Γ(Y, U)) :
    Y.presheaf.map g' (Y.presheaf.map g y) = Y.presheaf.map (g ≫ g') y :=
  (congrArg (fun φ : Γ(Y, U) ⟶ Γ(Y, T) => ConcreteCategory.hom φ y)
    (Y.presheaf.map_comp g g')).symm

/-- A restriction map of the structure sheaf is any composite of restriction maps with the same
source and target. -/
private theorem presheaf_map_eq_map_map {Y : Scheme.{u}} {U V T : Y.Opens} (g : op U ⟶ op T)
    (g₁ : op U ⟶ op V) (g₂ : op V ⟶ op T) (y : Γ(Y, U)) :
    Y.presheaf.map g y = Y.presheaf.map g₂ (Y.presheaf.map g₁ y) :=
  (presheaf_map_congr g (g₁ ≫ g₂) y).trans (presheaf_map_comp_apply g₁ g₂ y).symm

/-- A section killed by an isomorphism `eqToHom` of restriction maps is zero. -/
theorem eq_zero_of_map_eqToHom_eq_zero {Y : Scheme.{u}} {U U' : Y.Opens} (e : U' = U)
    {y : Γ(Y, U)} (hy : Y.presheaf.map (eqToHom e).op y = 0) : y = 0 := by
  subst e
  simpa using hy

/-- **The sections of a restricted closed immersion are the sections of the original one.** The
comorphism of `i ∣_ W` on an open `U` of `W` is the comorphism of `i` on the corresponding open
`W.ι ''ᵁ U` of `X`, followed by the identification of the two names of its target. -/
theorem app_morphismRestrict_apply (i : Z ⟶ X) (W : X.Opens) (U : W.toScheme.Opens)
    (a : Γ(W.toScheme, U)) :
    ((i ∣_ W).app U) a =
      Z.presheaf.map (eqToHom (image_morphismRestrict_preimage i W U)).op
        ((i.app (W.ι ''ᵁ U)) a) :=
  congrArg
    (fun φ : Γ(X, W.ι ''ᵁ U) ⟶ Γ(Z, (i ⁻¹ᵁ W).ι ''ᵁ ((i ∣_ W) ⁻¹ᵁ U)) =>
      ConcreteCategory.hom φ a)
    (morphismRestrict_app i W U)

/-- **The equations cut out the closed subscheme over an open `W`.** This is the chart-local form
of `Stacks.Gysin.IsCutOutByEquations`: the ideal sheaf of `i : Z ⟶ X` is generated, over the
opens contained in `W`, by the functions `f j ∈ Γ(X, W)` — each restricts to zero on `Z`, and a
function on an open `U ≤ W` restricting to zero on `Z` is, in a neighbourhood of every point of
`U`, a combination of them. -/
structure IsCutOutByEquationsOn (i : Z ⟶ X) (W : X.Opens) {I : Type*} [Fintype I]
    (f : I → Γ(X, W)) : Prop where
  /-- The equations vanish on the closed subscheme. -/
  app_eq_zero : ∀ j, (i.app W) (f j) = 0
  /-- A function on an open contained in `W` vanishing on the closed subscheme is locally a
  combination of the equations. -/
  exists_eq_sum : ∀ (U : X.Opens) (hUW : U ≤ W) (a : Γ(X, U)), (i.app U) a = 0 → ∀ x ∈ U,
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ c : I → Γ(X, V),
      X.presheaf.map (homOfLE hVU).op a =
        ∑ j, c j * X.presheaf.map (homOfLE (hVU.trans hUW)).op (f j)

/-- The chart-local equations `f : I → Γ(X, W)` read as global sections of the open subscheme
`W.toScheme`, which is where [Stacks, Tag 0G83] wants them. -/
def restrictEquations (W : X.Opens) {I : Type*} (f : I → Γ(X, W)) : I → Γ(W.toScheme, ⊤) :=
  fun j => X.presheaf.map (eqToHom W.ι_image_top).op (f j)

/-- The `j`-th restricted equation is the restriction of `f j` along the identification
`W.ι ''ᵁ ⊤ = W`. -/
theorem restrictEquations_apply (W : X.Opens) {I : Type*} (f : I → Γ(X, W)) (j : I) :
    restrictEquations W f j = X.presheaf.map (eqToHom W.ι_image_top).op (f j) :=
  rfl

/-- **Global equations cut out the closed subscheme over every open.** The chart-local
hypothesis of `IsCutOutByEquationsOn` for the family restricted to `W`. -/
theorem IsCutOutByEquations.on {i : Z ⟶ X} {I : Type*} [Fintype I] {f : I → Γ(X, ⊤)}
    (h : IsCutOutByEquations i f) (W : X.Opens) :
    IsCutOutByEquationsOn i W
      (fun j => X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (f j)) where
  app_eq_zero j := app_map_eq_zero i _ (h.appTop_eq_zero j)
  exists_eq_sum U _ a ha x hx := by
    obtain ⟨V, hVU, hxV, c, hc⟩ := h.exists_eq_sum U a ha x hx
    refine ⟨V, hVU, hxV, c, hc.trans (Finset.sum_congr rfl fun j _ => ?_)⟩
    refine congrArg (fun y => c j * y) ?_
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact presheaf_map_congr _ _ (f j)

/-- **Transport of the chart-local hypothesis along the restricted closed immersion.** If
`f : I → Γ(X, W)` cuts out `Z` over the opens contained in `W`, then the same functions, read as
global sections of `W.toScheme`, cut out the closed subscheme `i ∣_ W` of `W.toScheme` in the
*global* sense of `Stacks.Gysin.IsCutOutByEquations`. This is what lets
`AlgebraicGeometry.Scheme.Hom.gysinMap` of [Stacks, Tag 0G83] be applied on an equation chart:
`IsClosedImmersion (i ∣_ W)` is automatic. -/
theorem IsCutOutByEquationsOn.morphismRestrict {i : Z ⟶ X} {W : X.Opens} {I : Type*} [Fintype I]
    {f : I → Γ(X, W)} (h : IsCutOutByEquationsOn i W f) :
    IsCutOutByEquations (i ∣_ W) (restrictEquations W f) where
  appTop_eq_zero j := by
    refine (app_morphismRestrict_apply i W ⊤ (restrictEquations W f j)).trans ?_
    have h0 : (i.app (W.ι ''ᵁ ⊤)) (restrictEquations W f j) = 0 :=
      app_map_eq_zero i (eqToHom W.ι_image_top).op (h.app_eq_zero j)
    rw [h0]
    exact map_zero _
  exists_eq_sum U a ha x hx := by
    have hUW : W.ι ''ᵁ U ≤ W := W.ι_image_le U
    have ha' : (i.app (W.ι ''ᵁ U)) a = 0 :=
      eq_zero_of_map_eqToHom_eq_zero _ ((app_morphismRestrict_apply i W U a).symm.trans ha)
    have hx' : (x.1 : X) ∈ W.ι ''ᵁ U := (Scheme.Opens.mem_ι_image_iff W).2 hx
    obtain ⟨V₀, hV₀, hxV₀, c, hc⟩ := h.exists_eq_sum (W.ι ''ᵁ U) hUW a ha' x.1 hx'
    have hVeq : W.ι ''ᵁ (W.ι ⁻¹ᵁ V₀) = V₀ := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
      exact hV₀.trans hUW
    have hVU : W.ι ⁻¹ᵁ V₀ ≤ U := by
      refine (Scheme.Hom.image_le_image_iff W.ι _ _).1 ?_
      rw [hVeq]
      exact hV₀
    have hL : W.toScheme.presheaf.map (homOfLE hVU).op a =
        X.presheaf.map (eqToHom hVeq).op (X.presheaf.map (homOfLE hV₀).op a) :=
      presheaf_map_eq_map_map (W.ι.opensFunctor.map (homOfLE hVU)).op _ _ a
    have hR : ∀ j, W.toScheme.presheaf.map (homOfLE (le_top : W.ι ⁻¹ᵁ V₀ ≤ ⊤)).op
          (restrictEquations W f j) =
        X.presheaf.map (eqToHom hVeq).op (X.presheaf.map (homOfLE (hV₀.trans hUW)).op (f j)) :=
      fun j => (presheaf_map_comp_apply _ _ (f j)).trans (presheaf_map_eq_map_map _ _ _ (f j))
    have hgoal : X.presheaf.map (eqToHom hVeq).op (X.presheaf.map (homOfLE hV₀).op a) =
        ∑ j, X.presheaf.map (eqToHom hVeq).op (c j) *
          X.presheaf.map (eqToHom hVeq).op
            (X.presheaf.map (homOfLE (hV₀.trans hUW)).op (f j)) := by
      rw [hc, map_sum]
      exact Finset.sum_congr rfl fun j _ => map_mul _ _ _
    refine ⟨W.ι ⁻¹ᵁ V₀, hVU, hxV₀, fun j => X.presheaf.map (eqToHom hVeq).op (c j), ?_⟩
    refine hL.trans (hgoal.trans (Finset.sum_congr rfl fun j _ => ?_))
    exact congrArg (fun y => X.presheaf.map (eqToHom hVeq).op (c j) * y) (hR j).symm

end Stacks.Gysin

end
