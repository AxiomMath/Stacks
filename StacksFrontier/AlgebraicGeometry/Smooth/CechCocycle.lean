module

public import StacksFrontier.AlgebraicGeometry.Smooth.CechHomBridge
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothCard

/-!
# Restricting the chart-local difference of two lifts and changing the chart

Let `f : X ⟶ S` be a morphism of schemes locally of finite presentation, let `i : T ⟶ T'` be a
first-order thickening with `T'` affine and let `a : T ⟶ X`, `h : T' ⟶ S` present a lifting
problem for `f`. The Čech differential of the family of chart-local differences of the local
solutions of step (I) of [Stacks Project, Tag 02H6] compares, at a triple overlap, three
differences formed over three *different* basic opens and in two *different* charts. Bringing
them into one chart over one basic open is a single operation performed in two stages, and this
file is that operation.

## Main results

* `Stacks.Smooth.liftDiffDerivation_spec_restrict_chart`: let `D(c') ≤ D(c)` be basic opens of
  `T'`, let `b₁`, `b₂` solve the lifting problem restricted to `D(c)` inside a chart `W` of `f`
  and let `θ` induce their chart-local difference in that chart. Let `W₂` be another chart of
  `f`, containing the image of the *restricted* solutions but not necessarily of `b₁`, `b₂`
  themselves, and let `ψ` be a linear map over `D(c')` restricting `θ`. Then `ψ` induces the
  chart-local difference of the restricted solutions in the chart `W₂`.

## Implementation notes

The two stages cannot be exchanged. Over `D(c)` the solutions need not map into `W₂` at all —
in the Čech situation `W₂` is the chart attached to a third index — so chart independence is
unavailable there; and over `D(c')` the difference is only reachable from `θ` through the
restriction `ψ`. So one restricts first, by `Stacks.Smooth.conormalResLE_liftDiffDerivation`,
and changes chart afterwards, by `Stacks.Smooth.liftDiffDerivation_spec_chart_independent`.

The restricted solutions are taken as separate variables `b₁'`, `b₂'` together with the
equations identifying them with `T'.homOfLE hcc' ≫ b₁` and `T'.homOfLE hcc' ≫ b₂`, discharged by
`subst`. This is what lets the conclusion be stated for the solutions in the form in which the
Čech argument has them — a restriction of a solution of the original problem along a single
`AlgebraicGeometry.Scheme.homOfLE` — rather than as an iterated restriction, which could not be
rewritten afterwards because the solution occurs in the dependent arguments of
`Stacks.Smooth.liftDiffDerivation`.

Everything else the conclusion mentions is a proposition, so the hypotheses are listed rather
than derived: a derived proof and a supplied one are interchangeable by proof irrelevance, and
listing them keeps the statement free of inline proof terms.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.RingTheory.CechAcyclicity

universe u

namespace Stacks.Smooth

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) [IsAffine T'] {i : T ⟶ T'}
  (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}
  {V V₂ : S.Opens} {W W₂ : X.Opens}

/-- **Restricting the chart-local difference of two lifts and changing the chart.** Let
`D(c') ≤ D(c)` be basic opens of the affine scheme `T'`, let `b₁`, `b₂` solve the lifting problem
restricted to `D(c)`, both mapping into the affine chart `W` of `f` over the affine open `V` of
`S`, and let `θ` be a `Γ(T, i ⁻¹ᵁ D(c))`-linear map inducing their chart-local difference in the
chart `W`. Let `W₂` be a chart of `f` over an affine open `V₂` of `S`, and suppose the solutions
`b₁'`, `b₂'` obtained by restricting `b₁`, `b₂` to `D(c')` map into `W₂`. Then a linear map `ψ`
over `D(c')` restricting `θ` along `Stacks.Smooth.conormalResLE` induces the chart-local
difference of `b₁'` and `b₂'` in the chart `W₂`.

This is the comparison the Čech differential of [Stacks Project, Tag 02H6] needs at a triple
overlap: the three differences being compared there live over three different basic opens and in
the charts of two different indices, and only after restricting to the triple overlap do all
three solutions map into one chart. -/
theorem liftDiffDerivation_spec_restrict_chart [LocallyOfFinitePresentation f]
    (c c' : Γ(T', (⊤ : T'.Opens))) (hcc' : T'.basicOpen c' ≤ T'.basicOpen c)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hW₂V₂ : W₂ ≤ f ⁻¹ᵁ V₂)
    (hUW : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W)
    (hUWt : (⊤ : ((i ⁻¹ᵁ T'.basicOpen c : T.Opens) : Scheme.{u}).Opens) ≤
      ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ⁻¹ᵁ W)
    (hV' : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen c).ι ≫ h) ⁻¹ᵁ V)
    (hcomm : ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ≫ f
      = (i ∣_ T'.basicOpen c) ≫ ((T'.basicOpen c).ι ≫ h))
    {b₁ b₂ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}) ⟶ X}
    (hb₁f : b₁ ≫ f = (T'.basicOpen c).ι ≫ h) (hb₂f : b₂ ≫ f = (T'.basicOpen c).ι ≫ h)
    (hb₁a : (i ∣_ T'.basicOpen c) ≫ b₁ = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a)
    (hb₂a : (i ∣_ T'.basicOpen c) ≫ b₂ = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a)
    (hb₁ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W)
    {b₁' b₂' : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) ⟶ X}
    (e₁ : T'.homOfLE hcc' ≫ b₁ = b₁') (e₂ : T'.homOfLE hcc' ≫ b₂ = b₂')
    (hUW₂' : i ⁻¹ᵁ T'.basicOpen c' ≤ a ⁻¹ᵁ W₂)
    (hUWt₂' : (⊤ : ((i ⁻¹ᵁ T'.basicOpen c' : T.Opens) : Scheme.{u}).Opens) ≤
      ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) ⁻¹ᵁ W₂)
    (hV₂' : (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen c').ι ≫ h) ⁻¹ᵁ V₂)
    (hcomm' : ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) ≫ f
      = (i ∣_ T'.basicOpen c') ≫ ((T'.basicOpen c').ι ≫ h))
    (hb₁f' : b₁' ≫ f = (T'.basicOpen c').ι ≫ h) (hb₂f' : b₂' ≫ f = (T'.basicOpen c').ι ≫ h)
    (hb₁a' : (i ∣_ T'.basicOpen c') ≫ b₁' = (i ⁻¹ᵁ T'.basicOpen c').ι ≫ a)
    (hb₂a' : (i ∣_ T'.basicOpen c') ≫ b₂' = (i ⁻¹ᵁ T'.basicOpen c').ι ≫ a)
    (hb₁₂' : (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens) ≤ b₁' ⁻¹ᵁ W₂)
    (hb₂₂' : (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens) ≤ b₂' ⁻¹ᵁ W₂)
    (θ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c) →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c)]
        RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    (hθ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI := algebraAppLE f hWV
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
      letI := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      ∀ bb : Γ(X, W), θ (pullbackD f a W hUW bb) =
        liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
          hWV hUWt hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ bb)
    (ψ : letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c'
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
        (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
      Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c') →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c')]
        RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
    (hψ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c'
      letI := moduleOfLE (pullbackCotangentSheaf f a)
        (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
      ∀ y, ψ (restrictₗ (pullbackCotangentSheaf f a)
          (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx) y)
        = conormalResLE hi hcc' (θ y)) :
    letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c'
    letI := algebraAppLE f hW₂V₂
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
    letI := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hUWt₂'
      (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hW₂V₂ hUWt₂'
      (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hW₂V₂ hUWt₂'
      (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
      (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
    ∀ bb : Γ(X, W₂), ψ (pullbackD f a W₂ hUW₂' bb) =
      liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
        hW₂V₂ hUWt₂' hV₂' hcomm' hb₁f' hb₂f' hb₁a' hb₂a' hb₁₂' hb₂₂' bb := by
  subst e₁
  subst e₂
  have hpre : i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c := fun _ hx ↦ hcc' hx
  have hb₁'' : (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens)
      ≤ (T'.homOfLE hcc' ≫ b₁) ⁻¹ᵁ W := fun _ _ ↦ hb₁ (Set.mem_univ _)
  have hb₂'' : (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens)
      ≤ (T'.homOfLE hcc' ≫ b₂) ⁻¹ᵁ W := fun _ _ ↦ hb₂ (Set.mem_univ _)
  have hUW'' : i ⁻¹ᵁ T'.basicOpen c' ≤ a ⁻¹ᵁ W := fun _ hx ↦ hUW (hcc' hx)
  have hUWt'' : (⊤ : ((i ⁻¹ᵁ T'.basicOpen c' : T.Opens) : Scheme.{u}).Opens)
      ≤ ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) ⁻¹ᵁ W := by
    intro x _
    rw [← hb₁a']
    exact hb₁'' (Set.mem_univ _)
  have hV'' : (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens)
      ≤ ((T'.basicOpen c').ι ≫ h) ⁻¹ᵁ V := fun x _ ↦
    hV' (Set.mem_univ (⟨x.1, hcc' x.2⟩ : ((T'.basicOpen c : T'.Opens) : Scheme.{u})))
  let := algebraAppLE f hWV
  let := algebraAppLE f hW₂V₂
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c')
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hUWt''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hUWt₂'
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hWV hUWt''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hW₂V₂ hUWt₂'
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hWV hUWt''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hW₂V₂ hUWt₂'
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c) (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c') (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfLE (pullbackCotangentSheaf f a) hpre
  have hstep : ∀ (W' : X.Opens) (e : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W')
      (e' : i ⁻¹ᵁ T'.basicOpen c' ≤ a ⁻¹ᵁ W') (y : Γ(X, W')),
      ψ (pullbackD f a W' e' y) = conormalResLE hi hcc' (θ (pullbackD f a W' e y)) :=
    fun W' e e' y ↦ (congrArg ψ (map_pullbackD f a W' e e' hpre y)).symm.trans
      (hψ (pullbackD f a W' e y))
  have hspecW : ∀ bb : Γ(X, W), ψ (pullbackD f a W hUW'' bb)
      = liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
          hWV hUWt'' hV'' hcomm' hb₁f' hb₂f' hb₁a' hb₂a' hb₁'' hb₂'' bb := fun bb ↦
    (hstep W hUW hUW'' bb).trans
      ((congrArg (fun z ↦ conormalResLE hi hcc' z) (hθ bb)).trans
        (conormalResLE_liftDiffDerivation f hi hcc' hWV hUWt hUWt'' hV' hV'' hcomm hcomm'
          hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ hb₁f' hb₂f' hb₁a' hb₂a' hb₁'' hb₂'' bb))
  exact liftDiffDerivation_spec_chart_independent f hi c' hV hW hWV hW₂V₂ hUW'' hUW₂' hUWt''
    hUWt₂' hV'' hV₂' hcomm' hb₁f' hb₂f' hb₁a' hb₂a' hb₁'' hb₂'' hb₁₂' hb₂₂' ψ hspecW

/-! ### From a linear map out of the sections of `a^*Ω_{X/S}` back to a derivation -/

section OfLinearMap

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens} {W : X.Opens} {U : T.Opens}

/-- The scalar tower `Γ(X, W) → Γ(T, U) → M` for a module `M` over the global sections of the
open subscheme `U`, with its `Γ(T, U)`-action read through
`AlgebraicGeometry.Scheme.Opens.topIso` and its `Γ(X, W)`-action through the restricted morphism
`U.ι ≫ a`. It rests on the comparison `Stacks.Smooth.appLE_comp_topIso_inv` of the two ways of
reading the sections of `a` over the chart `W` on the open subscheme `U`. -/
theorem isScalarTower_moduleOfAppLE_topIso (hUW : U ≤ a ⁻¹ᵁ W)
    (hUW' : (⊤ : (U : Scheme.{u}).Opens) ≤ (U.ι ≫ a) ⁻¹ᵁ W) (M : Type*) [AddCommGroup M]
    [Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M] :
    letI := algebraAppLE a hUW
    letI := moduleOfTopIso U M
    letI := moduleOfAppLE (U.ι ≫ a) hUW' M
    IsScalarTower Γ(X, W) Γ(T, U) M := by
  let := algebraAppLE a hUW
  let := moduleOfTopIso U M
  let := moduleOfAppLE (U.ι ≫ a) hUW' M
  refine IsScalarTower.of_algebraMap_smul fun r m ↦ ?_
  show U.topIso.inv.hom ((a.appLE W U hUW).hom r) • m
    = ((U.ι ≫ a).appLE W (⊤ : (U : Scheme.{u}).Opens) hUW').hom r • m
  rw [← CommRingCat.comp_apply, appLE_comp_topIso_inv a U hUW hUW']

/-- **The derivation induced by a linear map out of the sections of `a^*Ω_{X/S}`.** A
`Γ(T, U)`-linear map `Γ(a^*Ω_{X/S}, U) ⟶ M`, for `M` a module over the global sections of the
open subscheme `U`, composed with `Stacks.Smooth.pullbackD`, is a `Γ(S, V)`-derivation of
`Γ(X, W)` with values in `M`.

This inverts `Stacks.Smooth.existsUnique_linearMap_of_leibniz_opensTop`, and the module
structures are exactly those of `Stacks.Smooth.liftDiffDerivation` for a thickening restricted to
an affine open, so the derivation produced here is one that
`Stacks.Smooth.exists_lift_of_derivation` consumes. -/
noncomputable def derivationOfLinearMapOpensTop (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W)
    (hUW' : (⊤ : (U : Scheme.{u}).Opens) ≤ (U.ι ≫ a) ⁻¹ᵁ W) (M : Type u) [AddCommGroup M]
    [Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M]
    (θ : letI := moduleOfTopIso U M
      Γ(pullbackCotangentSheaf f a, U) →ₗ[Γ(T, U)] M) :
    letI := algebraAppLE f hWV
    letI := moduleOfAppLE (U.ι ≫ a) hUW' M
    letI := moduleOfAppLEBase f (U.ι ≫ a) hWV hUW' M
    Derivation Γ(S, V) Γ(X, W) M :=
  letI := algebraAppLE f hWV
  letI := algebraAppLE a hUW
  letI := moduleOfTopIso U M
  letI := moduleOfAppLE (U.ι ≫ a) hUW' M
  letI := moduleOfAppLEBase f (U.ι ≫ a) hWV hUW' M
  letI := isScalarTower_moduleOfAppLE_topIso a hUW hUW' M
  letI := isScalarTowerOfAppLEBase f (U.ι ≫ a) hWV hUW' M
  letI := moduleAppLE a (pullbackCotangentSheaf f a) hUW
  letI := moduleAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  letI := isScalarTowerAppLE a (pullbackCotangentSheaf f a) hUW
  letI := isScalarTowerAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  (θ.restrictScalars Γ(X, W)).compDer (pullbackCotangentDerivation f a W hWV hUW)

/-- The value of `Stacks.Smooth.derivationOfLinearMapOpensTop` on a section of `𝒪_X` over the
chart is the linear map applied to the pullback of its universal differential. -/
theorem derivationOfLinearMapOpensTop_apply (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W)
    (hUW' : (⊤ : (U : Scheme.{u}).Opens) ≤ (U.ι ≫ a) ⁻¹ᵁ W) (M : Type u) [AddCommGroup M]
    [Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M]
    (θ : letI := moduleOfTopIso U M
      Γ(pullbackCotangentSheaf f a, U) →ₗ[Γ(T, U)] M) (bb : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := moduleOfTopIso U M
    letI := moduleOfAppLE (U.ι ≫ a) hUW' M
    letI := moduleOfAppLEBase f (U.ι ≫ a) hWV hUW' M
    derivationOfLinearMapOpensTop f a hWV hUW hUW' M θ bb = θ (pullbackD f a W hUW bb) :=
  rfl

end OfLinearMap

/-! ### The sections cutting out the members of the Čech covering -/

section CechSection

/-- A multiple of a section cuts out a smaller basic open. -/
theorem basicOpen_le_of_dvd {Y : Scheme.{u}} {O : Y.Opens} {d e : Γ(Y, O)} (hde : d ∣ e) :
    Y.basicOpen e ≤ Y.basicOpen d := by
  obtain ⟨k, rfl⟩ := hde
  rw [Scheme.basicOpen_mul]
  exact inf_le_left

/-- **The section of `𝒪_{T'}` cutting out the member of the Čech covering indexed by a tuple.**
For `g : Fin n → Γ(T', ⊤)` and a tuple `x : Fin m → Fin n` this is `1 * g (x 0) ⋯ g (x (m-1))`,
the section whose image under `i.appTop` is the element of `Γ(T, ⊤)` at which the corresponding
term of `Stacks.RingTheory.CechAcyclicity.CechTerm` localizes.

The factor `1` is not cosmetic: the Čech complex twisted by `f` localizes at `f * tupleProd g x`,
and the untwisted complex is the case `f = 1`, so this is the shape the image has to take. -/
def cechSection {T' : Scheme.{u}} {n : ℕ} (g : Fin n → Γ(T', (⊤ : T'.Opens))) {m : ℕ}
    (x : Fin m → Fin n) : Γ(T', (⊤ : T'.Opens)) :=
  1 * tupleProd g x

/-- The image of `Stacks.Smooth.cechSection` under `i.appTop` is the index of the corresponding
untwisted Čech term. -/
theorem appTop_cechSection {T T' : Scheme.{u}} (i : T ⟶ T') {n : ℕ}
    (g : Fin n → Γ(T', (⊤ : T'.Opens))) {m : ℕ} (x : Fin m → Fin n) :
    i.appTop.hom (cechSection g x) = 1 * tupleProd (fun j ↦ i.appTop.hom (g j)) x := by
  rw [cechSection, map_mul, map_one, tupleProd, tupleProd, map_prod]

/-- Each entry of the tuple divides `Stacks.Smooth.cechSection`, so the member of the covering it
cuts out lies in the corresponding basic open. -/
theorem basicOpen_cechSection_le {T' : Scheme.{u}} {n : ℕ} (g : Fin n → Γ(T', (⊤ : T'.Opens)))
    {m : ℕ} (x : Fin m → Fin n) (k : Fin m) :
    T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g (x k)) :=
  basicOpen_le_of_dvd (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) 1)

/-- The member of the covering attached to a tuple lies in the member attached to each of its
faces. -/
theorem basicOpen_cechSection_le_face {T' : Scheme.{u}} {n : ℕ}
    (g : Fin n → Γ(T', (⊤ : T'.Opens))) {m : ℕ} (y : Fin (m + 1) → Fin n) (j : Fin (m + 1)) :
    T'.basicOpen (cechSection g y)
      ≤ T'.basicOpen (cechSection g fun l ↦ y (j.succAbove l)) :=
  basicOpen_le_of_dvd ⟨g (y j), by
    rw [cechSection, cechSection, tupleProd_succAbove g y j]; ring⟩

/-- The member of the covering attached to a one-element tuple is the basic open of the
corresponding section. -/
theorem basicOpen_cechSection_single {T' : Scheme.{u}} {n : ℕ}
    (g : Fin n → Γ(T', (⊤ : T'.Opens))) (c : Fin 1 → Fin n) :
    T'.basicOpen (cechSection g c) = T'.basicOpen (g (c 0)) := by
  rw [cechSection, tupleProd, Fin.prod_univ_one, one_mul]

/-- The member of the covering attached to a two-element tuple is the intersection of the two
basic opens. -/
theorem basicOpen_cechSection_double {T' : Scheme.{u}} {n : ℕ}
    (g : Fin n → Γ(T', (⊤ : T'.Opens))) (x : Fin 2 → Fin n) :
    T'.basicOpen (cechSection g x)
      = T'.basicOpen (g (x 0)) ⊓ T'.basicOpen (g (x 1)) := by
  rw [cechSection, tupleProd, Fin.prod_univ_two, one_mul, Scheme.basicOpen_mul]

end CechSection

/-! ### Value-level torsor identities, and the linear map over a basic open -/

section Values

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {W : X.Opens} [IsAffine T']
  {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}
  (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (hV' : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ V)
  {b₁ b₂ b₃ : T' ⟶ X}

/-- **The cocycle identity for the differences of solutions of a lifting problem, on values.**
This is `Stacks.Smooth.liftDiffDerivation_add` evaluated at a section, which is the form the Čech
computation uses: the three differences are compared as elements of the conormal module rather
than as derivations. -/
theorem liftDiffDerivation_add_apply (hcomm : a ≫ f = i ≫ h) (hb₁f : b₁ ≫ f = h)
    (hb₂f : b₂ ≫ f = h) (hb₃f : b₃ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₃a : i ≫ b₃ = a) (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W)
    (hb₃ : (⊤ : T'.Opens) ≤ b₃ ⁻¹ᵁ W) (x : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    (liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₃f hb₁a hb₃a hb₁ hb₃ x :
        RingHom.ker i.appTop.hom)
      = liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x +
        liftDiffDerivation f hi hWV hUW hV' hcomm hb₂f hb₃f hb₂a hb₃a hb₂ hb₃ x := by
  let := algebraAppLE f hWV
  let := thickeningKerModule hi
  let := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  refine Subtype.ext ?_
  rw [AddMemClass.coe_add, liftDiffDerivation_apply, liftDiffDerivation_apply,
    liftDiffDerivation_apply]
  ring

/-- **The difference of two solutions of a lifting problem changes sign when they are
exchanged**, on values. -/
theorem liftDiffDerivation_neg_apply (hcomm : a ≫ f = i ≫ h) (hb₁f : b₁ ≫ f = h)
    (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W) (x : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    (liftDiffDerivation f hi hWV hUW hV' hcomm hb₂f hb₁f hb₂a hb₁a hb₂ hb₁ x :
        RingHom.ker i.appTop.hom)
      = -liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x := by
  let := algebraAppLE f hWV
  let := thickeningKerModule hi
  let := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  refine Subtype.ext ?_
  rw [NegMemClass.coe_neg, liftDiffDerivation_apply, liftDiffDerivation_apply]
  ring

end Values

section BasicOpenTheta

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) [IsAffine T'] {i : T ⟶ T'}
  (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}
  {V : S.Opens} {W : X.Opens}

/-- **The chart-local difference of two lifts over a basic open, as a linear map.** This is
`Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation` at `U' = D(c)`, with the affineness of
`D(c)` and of its preimage supplied and the uniqueness clause discarded; the existence statement
is all the Čech argument needs. -/
theorem exists_linearMap_liftDiffDerivation_basicOpen (c : Γ(T', (⊤ : T'.Opens)))
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V)
    (hUW : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W)
    (hUWt : (⊤ : ((i ⁻¹ᵁ T'.basicOpen c : T.Opens) : Scheme.{u}).Opens) ≤
      ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ⁻¹ᵁ W)
    (hV' : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen c).ι ≫ h) ⁻¹ᵁ V)
    (hcomm : ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ≫ f
      = (i ∣_ T'.basicOpen c) ≫ ((T'.basicOpen c).ι ≫ h))
    {b₁ b₂ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}) ⟶ X}
    (hb₁f : b₁ ≫ f = (T'.basicOpen c).ι ≫ h) (hb₂f : b₂ ≫ f = (T'.basicOpen c).ι ≫ h)
    (hb₁a : (i ∣_ T'.basicOpen c) ≫ b₁ = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a)
    (hb₂a : (i ∣_ T'.basicOpen c) ≫ b₂ = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a)
    (hb₁ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI := algebraAppLE f hWV
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    ∃ θ : Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c) →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c)]
        RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom,
      ∀ bb : Γ(X, W), θ (pullbackD f a W hUW bb) =
        liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
          hWV hUWt hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ bb :=
  let : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
    (isAffineOpen_top T').basicOpen c
  (existsUnique_linearMap_liftDiffDerivation f hi (isAffine_preimage_of_isAffine hi
    (T'.basicOpen c)) hV hW hWV hUW hUWt hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂).exists

end BasicOpenTheta

end Stacks.Smooth

end
