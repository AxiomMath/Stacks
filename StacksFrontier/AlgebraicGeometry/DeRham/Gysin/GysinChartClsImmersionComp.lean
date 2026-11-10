module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartClsLocality
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartRestrictionComp

/-!
# The class map of Tag 0G7Q is local along an arbitrary open immersion

The class map of [Stacks, Tag 0G7Q] is local along an arbitrary open immersion: along a composite
`l ≫ g` of open immersions it is the class map along `g`, restricted along `l`. In particular the
class map of a chart is local along the chart-to-chart leg `AlgebraicGeometry.Scheme.homOfLE`, both
as a map of modules and on the sections over an open.

## Main results

* `Stacks.Gysin.openImmersionClsHom_comp`: **the class map of [Stacks, Tag 0G7Q] along a
  composite of two open immersions** is the class map along the outer one, restricted along the
  inner one.
* `Stacks.Gysin.openImmersionClsHom_congr`: the class map transports along an equality of open
  immersions, through `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`.
* `Stacks.Gysin.chartClsHom_homOfLE`: **the class map of a chart is local along the chart-to-chart
  leg `AlgebraicGeometry.Scheme.homOfLE`** — the statement the two-chart comparison of
  [Stacks, Tag 0G86] consumes. For `V' ≤ W` in `X.Opens`, the class map of the chart `V'` with the
  equations of `W` restricted to `V'` is the class map of the chart `W`, restricted along
  `X.homOfLE`.
* `Stacks.Gysin.chartCls_homOfLE`: the same locality on the sections over an open `V ≤ W`.

## Implementation notes

`openImmersionClsHom_comp` is `openImmersionClsHom_comp_ι` with `U.ι` replaced by an arbitrary
open immersion `l`, using the base change
`Stacks.Gysin.map_supportedFractionSource_comp_supportCohomologyRestrictIso` of
[Stacks, Tag 0G7U] and the transitivity `Stacks.Gysin.supportCohomologyOpenImmersionIso_inv_comp`
of the excision along an arbitrary open immersion.

`chartClsHom_homOfLE` is that composite law at `l := X.homOfLE e`, whose composite leg is
`X.homOfLE e ≫ W.ι = V'.ι` by `AlgebraicGeometry.Scheme.homOfLE_ι`, transported by
`openImmersionClsHom_congr`; the chart's own equations are identified by
`Stacks.Gysin.restrictEquations_homOfLE`.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.LocalCohomologyExcision (chartOpen ι_image_chartOpen)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y Y' Z X S : Scheme.{u}}

/-! ### The class map along a composite of open immersions -/

/-- **The class map of [Stacks, Tag 0G7Q] along a composite of two open immersions.**  For
`l : Y ⟶ Y'` and `g : Y' ⟶ X` open immersions, the class map along `l ≫ g` of the equations of
`g` pulled back along `l` is the class map along `g`, restricted along `l`, with
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` mediating at the source and at the target.

This is the open-immersion case of [Stacks, Tag 0G7U] assembled onto the transport by excision.
Its two inputs are the base change of the class map,
`Stacks.Gysin.map_supportedFractionSource_comp_supportCohomologyRestrictIso`, applied at the
scheme `Y'` and the leg `l`, and the transitivity of the excision along a composite of open
immersions, `Stacks.Gysin.supportCohomologyOpenImmersionIso_inv_comp`; what joins them is the
functoriality of [Stacks, Tag 0G7T] in the coefficient module,
`Stacks.Perfect.SupportedFraction.supportedFractionSource_natural`, which moves the comparison of
the two restrictions of the forms across the class map. -/
theorem openImmersionClsHom_comp (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (l : Y ⟶ Y') (g : Y' ⟶ X) [IsOpenImmersion l] [IsOpenImmersion g]
    (f : Fin (d + 1) → Γ(Y', ⊤))
    (hT : IsClosed (g ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ g ⁻¹' Set.range i.base)
    (hTl : IsClosed (l ⁻¹' (g ⁻¹' Set.range i.base)))
    (hTfl : equationsClosedSet (fun j => l.appTop (f j)) ⊆
      l ⁻¹' (g ⁻¹' Set.range i.base)) :
    openImmersionClsHom i π p (l ≫ g) (fun j => l.appTop (f j)) hTl hTfl =
      (Scheme.Modules.restrictFunctorComp l g).hom.app
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫
        (Scheme.Modules.restrictFunctor l).map (openImmersionClsHom i π p g f hT hTf) ≫
          (Scheme.Modules.restrictFunctorComp l g).inv.app (gysinTarget i π (d + 1) p) := by
  have : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  have hbc := (Iso.eq_comp_inv (supportCohomologyOpenImmersionIso l hT hTl ((d + 1 : ℕ) : ℤ)
      ((Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))))).mpr
    (map_supportedFractionSource_comp_supportCohomologyRestrictIso l
      ((Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) f hT hTf hTl hTfl)
  have : ((Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.restrictFunctor l).obj
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).IsQuasicoherent :=
    inferInstanceAs (((Scheme.Modules.restrictFunctor l).obj
      ((Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))))).IsQuasicoherent)
  have hnat := supportedFractionSource_natural (fun j => l.appTop (f j))
    ((Scheme.Modules.restrictFunctorComp l g).hom.app
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hTl hTfl
  refine Eq.trans (congrArg (fun ψ => supportedFractionSource (fun j => l.appTop (f j))
      ((Scheme.Modules.restrictFunctor (l ≫ g)).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hTl hTfl ≫ ψ)
    (supportCohomologyOpenImmersionIso_inv_comp l g (isClosed_range_base i) hT hTl
      ((d + 1 : ℕ) : ℤ) (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))))) ?_
  refine Eq.trans (chaseNat _ _ _ _ _ _ _ hnat) (Eq.symm ?_)
  refine Eq.trans (congrArg (fun ψ => (Scheme.Modules.restrictFunctorComp l g).hom.app
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫ ψ ≫
    (Scheme.Modules.restrictFunctorComp l g).inv.app (gysinTarget i π (d + 1) p))
    ((Scheme.Modules.restrictFunctor l).map_comp _ _)) ?_
  exact congrArg (fun ψ => (Scheme.Modules.restrictFunctorComp l g).hom.app
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫
    (ψ ≫ (Scheme.Modules.restrictFunctor l).map
        (supportCohomologyOpenImmersionIso g (isClosed_range_base i) hT ((d + 1 : ℕ) : ℤ)
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv) ≫
    (Scheme.Modules.restrictFunctorComp l g).inv.app (gysinTarget i π (d + 1) p)) hbc

/-! ### Transport along an equality of open immersions -/

/-- **The class map of [Stacks, Tag 0G7Q] along an open immersion transports along an equality of
open immersions.**  Two equal open immersions `Y ⟶ X` have equal restriction functors only up to
the reindexing `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`; this says the class map
commutes with it. The equations are untouched, being global sections of `Y`. -/
theorem openImmersionClsHom_congr (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    {g g' : Y ⟶ X} [inst : IsOpenImmersion g] [inst' : IsOpenImmersion g'] (h : g = g')
    (f : Fin (d + 1) → Γ(Y, ⊤))
    (hT : IsClosed (g ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ g ⁻¹' Set.range i.base)
    (hT' : IsClosed (g' ⁻¹' Set.range i.base))
    (hTf' : equationsClosedSet f ⊆ g' ⁻¹' Set.range i.base) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫
        openImmersionClsHom i π p g' f hT' hTf' =
      openImmersionClsHom i π p g f hT hTf ≫
        (Scheme.Modules.restrictFunctorCongr h).hom.app (gysinTarget i π (d + 1) p) := by
  subst h
  obtain rfl : inst = inst' := rfl
  obtain rfl : hT = hT' := rfl
  obtain rfl : hTf = hTf' := rfl
  rw [restrictFunctorCongr_rfl]
  simp only [NatTrans.id_app, Category.id_comp, Category.comp_id]

/-! ### The class map of a chart is local along the chart-to-chart leg -/

/-- **The class map of a chart depends on the equations only through the family.**  Two equal
families give the same class map, the closedness hypotheses being proofs of one proposition once
the families are identified. -/
theorem chartClsHom_congr_equations (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens) {f f' : Fin (d + 1) → Γ(W.toScheme, ⊤)} (hff' : f = f')
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (hTf' : equationsClosedSet f' ⊆ W.ι ⁻¹' Set.range i.base) :
    chartClsHom i π p W f hT hTf = chartClsHom i π p W f' hT hTf' := by
  subst hff'
  rfl

/-- **The class map of a chart is local along the chart-to-chart leg
`AlgebraicGeometry.Scheme.homOfLE`.**  For `W' ≤ W` in `X.Opens` and equations `f` of the chart
`W`, the class map of the chart `W'` with `f` restricted to `W'` is the class map of the chart
`W`, restricted along `X.homOfLE`, with `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`
mediating at the source and at the target and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` along
`AlgebraicGeometry.Scheme.homOfLE_ι` identifying the composite leg with `W'.ι`.

**This is the statement the two-chart comparison of [Stacks, Tag 0G86] consumes.**
`Stacks.Gysin.openImmersionClsHom_comp_ι` is the same locality for an open `U` of `W.toScheme`,
whose composite leg is `U.ι ≫ W.ι`, whereas a chart-to-chart leg is `X.homOfLE e`, the canonical
inclusion of an open subscheme only up to an isomorphism of schemes.

It is `openImmersionClsHom_comp` at `l := X.homOfLE e`, `g := W.ι`, transported along
`AlgebraicGeometry.Scheme.homOfLE_ι` by `openImmersionClsHom_congr`; the smaller chart's own
equations are `Stacks.Gysin.restrictEquations_homOfLE`. -/
theorem chartClsHom_homOfLE (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    {W' W : X.Opens} (e : W' ≤ W) (f : Fin (d + 1) → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTfW : equationsClosedSet (restrictEquations W f) ⊆ W.ι ⁻¹' Set.range i.base)
    (hTW' : IsClosed (W'.ι ⁻¹' Set.range i.base))
    (hTe : IsClosed (X.homOfLE e ⁻¹' (W.ι ⁻¹' Set.range i.base)))
    (hTfW' : equationsClosedSet
        (restrictEquations W' (fun k => X.presheaf.map (homOfLE e).op (f k))) ⊆
      W'.ι ⁻¹' Set.range i.base)
    (hTfe : equationsClosedSet (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) ⊆
      X.homOfLE e ⁻¹' (W.ι ⁻¹' Set.range i.base)) :
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫
        chartClsHom i π p W'
          (restrictEquations W' (fun k => X.presheaf.map (homOfLE e).op (f k)))
          hTW' hTfW' =
      ((Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).hom.app
            (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE e)).map
              (chartClsHom i π p W (restrictEquations W f) hTW hTfW) ≫
            (Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).inv.app
              (gysinTarget i π (d + 1) p)) ≫
        (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app
          (gysinTarget i π (d + 1) p) := by
  have hfam : (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) =
      restrictEquations W' (fun k => X.presheaf.map (homOfLE e).op (f k)) :=
    funext fun j => (restrictEquations_homOfLE e f j).symm
  have hTfe' : equationsClosedSet
      (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) ⊆
        W'.ι ⁻¹' Set.range i.base := by
    rw [hfam]; exact hTfW'
  rw [chartClsHom_congr_equations i π p W' hfam.symm hTW' hTfW' hTfe']
  exact (openImmersionClsHom_congr i π p (X.homOfLE_ι e)
    (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) hTe hTfe hTW' hTfe').trans
    (congrArg (· ≫ (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app
      (gysinTarget i π (d + 1) p))
      (openImmersionClsHom_comp i π p (X.homOfLE e) W.ι (restrictEquations W f)
        hTW hTfW hTe hTfe))

/-! ### The class map of a chart on the sections over an open, at two charts -/

/-- **Two restriction maps of a module presheaf between the same pair of opens agree**, the
opposite category of opens being thin. -/
theorem mpmap_congr {Y : Scheme.{u}} (M : Y.Modules) {U U' : Y.Opens}
    (g g' : op U ⟶ op U') (z : Γ(M, U)) :
    (M.presheaf.map g) z = (M.presheaf.map g') z := by
  obtain rfl : g = g' := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rfl

/-- **A composite of two restriction maps of a module presheaf is a restriction map.** -/
theorem collapse {Y : Scheme.{u}} (M : Y.Modules) {U₁ U₂ U₃ : Y.Opens}
    (g₁ : op U₁ ⟶ op U₂) (g₂ : op U₂ ⟶ op U₃) (g : op U₁ ⟶ op U₃) (z : Γ(M, U₁)) :
    (M.presheaf.map g₂) ((M.presheaf.map g₁) z) = (M.presheaf.map g) z := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  exact mpmap_congr M _ _ z

/-- **The open of a chart corresponding to a smaller chart is the image of the whole of that
smaller chart.**  For `V ≤ W` in `X.Opens` the range of `AlgebraicGeometry.Scheme.homOfLE` is
`W.ι ⁻¹ᵁ V`, which is `Stacks.Perfect.LocalCohomologyExcision.chartOpen W e`. -/
theorem image_chartOpen_self {V W : X.Opens} (e : V ≤ W) :
    X.homOfLE e ''ᵁ chartOpen V le_rfl = chartOpen W e := by
  rw [show chartOpen V le_rfl = ⊤ from Scheme.Opens.ι_preimage_self V,
    Scheme.Hom.image_top_eq_opensRange, Scheme.opensRange_homOfLE]
  rfl

/-- `Stacks.Gysin.chartCls` with the open of the chart and the identification of its image
supplied, rather than derived from the containment. -/
def chartClsOn (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ) (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (O : W.toScheme.Opens) (hO : W.ι ''ᵁ O = V) :
    Γ(Scheme.Hom.relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V) →+
      Γ(Stacks.Gysin.gysinTarget i π (d + 1) p, V) :=
  (((Stacks.Gysin.gysinTarget i π (d + 1) p).presheaf.map (homOfLE hO.ge).op).hom).comp
    ((((Stacks.Gysin.chartClsHom i π p W f hT hTf).val.app (op O)).hom.toAddMonoidHom).comp
      (((Scheme.Hom.relativeDifferentialForms π
        ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).presheaf.map (homOfLE hO.le).op).hom))

/-- `Stacks.Gysin.chartCls` on the sections over `V ≤ W` is `chartClsOn` at the open
`Stacks.Perfect.LocalCohomologyExcision.chartOpen W hV` of the chart `W`. -/
theorem chartCls_eq_chartClsOn (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) :
    Stacks.Gysin.chartCls i π p W f hT hTf V hV =
      chartClsOn i π p W f hT hTf V (chartOpen W hV) (ι_image_chartOpen W hV) := rfl

/-- `chartClsOn` does not depend on the choice of the open `O` of the chart whose image is `V`. -/
theorem chartClsOn_congr (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (O O' : W.toScheme.Opens) (hO : W.ι ''ᵁ O = V) (hO' : W.ι ''ᵁ O' = V) :
    chartClsOn i π p W f hT hTf V O hO = chartClsOn i π p W f hT hTf V O' hO' := by
  obtain rfl : O = O' := W.ι.image_injective (hO.trans hO'.symm)
  rfl

/-- Over a scheme `Y`, two conjugations by restriction maps of maps `A` and `B` on sections of
module presheaves agree on `y` once `B` and a conjugate of `A` agree on the restriction of `y` to
a common refinement `UC`. -/
theorem sandwich {Y : Scheme.{u}} (R G : Y.Modules) {V UA UB UC UD : Y.Opens}
    (A : Γ(R, UA) → Γ(G, UA)) (B : Γ(R, UB) → Γ(G, UB)) (y : Γ(R, V))
    (γ : op UC ⟶ op UB) (γ₁ : op UC ⟶ op UA) (γ₂ : op UA ⟶ op UD) (γ₃ : op UD ⟶ op UB)
    (δ : op V ⟶ op UC)
    (a₁ : op V ⟶ op UA) (a₂ : op UA ⟶ op V) (b₁ : op V ⟶ op UB) (b₂ : op UB ⟶ op V)
    (E : B ((R.presheaf.map γ) ((R.presheaf.map δ) y)) =
      (G.presheaf.map γ₃) ((G.presheaf.map γ₂)
        (A ((R.presheaf.map γ₁) ((R.presheaf.map δ) y))))) :
    (G.presheaf.map a₂) (A ((R.presheaf.map a₁) y)) =
      (G.presheaf.map b₂) (B ((R.presheaf.map b₁) y)) := by
  rw [← collapse R δ γ b₁ y, E, collapse R δ γ₁ a₁ y, collapse G γ₂ γ₃ (γ₂ ≫ γ₃),
    collapse G (γ₂ ≫ γ₃) b₂ a₂]

/-- **The class map of a chart on the sections over an open is local along the chart-to-chart
leg.** For `V ≤ W` in `X.Opens` and equations `f` over `W`, the class map of the chart `W` on the
sections over `V` agrees with the class map of the chart `V`, with `f` restricted to `V`. -/
theorem chartCls_homOfLE (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    {V W : X.Opens} (e : V ≤ W) (f : Fin (d + 1) → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTfW : equationsClosedSet (restrictEquations W f) ⊆ W.ι ⁻¹' Set.range i.base)
    (hTV : IsClosed (V.ι ⁻¹' Set.range i.base))
    (hTfV : equationsClosedSet
        (restrictEquations V (fun k => X.presheaf.map (homOfLE e).op (f k))) ⊆
      V.ι ⁻¹' Set.range i.base)
    (y : Γ(Scheme.Hom.relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    chartCls i π p W (restrictEquations W f) hTW hTfW V e y =
      chartCls i π p V (restrictEquations V (fun k => X.presheaf.map (homOfLE e).op (f k)))
        hTV hTfV V le_rfl y := by
  have hTe : IsClosed (X.homOfLE e ⁻¹' (W.ι ⁻¹' Set.range i.base)) :=
    Stacks.Perfect.CechDerivedSupportImmersion.isClosed_restrictClosedSubset
      (X.homOfLE e) hTW
  have hTfe := Stacks.Perfect.CechDerivedSupportImmersion.equationsClosedSet_restrict_subset
    (X.homOfLE e) (restrictEquations W f) hTfW
  have heq := chartClsHom_homOfLE i π p e f hTW hTfW hTV hTe hTfV hTfe
  have hA : W.ι ''ᵁ (X.homOfLE e ''ᵁ chartOpen V le_rfl) = V :=
    (congrArg (fun U => W.ι ''ᵁ U) (image_chartOpen_self e)).trans (ι_image_chartOpen W e)
  have hC : (X.homOfLE e ≫ W.ι) ''ᵁ chartOpen V le_rfl = V :=
    (Scheme.Hom.comp_image (X.homOfLE e) W.ι (chartOpen V le_rfl)).trans hA
  change chartClsOn i π p W (restrictEquations W f) hTW hTfW V (chartOpen W e)
      (ι_image_chartOpen W e) y = _
  rw [chartClsOn_congr i π p W (restrictEquations W f) hTW hTfW V (chartOpen W e)
    (X.homOfLE e ''ᵁ chartOpen V le_rfl) (ι_image_chartOpen W e) hA]
  have E := congrArg (fun ψ :
      (Scheme.Modules.restrictFunctor (X.homOfLE e ≫ W.ι)).obj
          (Scheme.Hom.relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ⟶
        (Scheme.Modules.restrictFunctor V.ι).obj (gysinTarget i π (d + 1) p) =>
    (Scheme.Modules.Hom.app ψ (chartOpen V le_rfl))
      (((Scheme.Hom.relativeDifferentialForms π
        ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).presheaf.map (homOfLE hC.le).op) y)) heq
  simp only at E
  exact sandwich (Scheme.Hom.relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))
    (gysinTarget i π (d + 1) p)
    (fun z => (Scheme.Modules.Hom.app
      (chartClsHom i π p W (restrictEquations W f) hTW hTfW)
      (X.homOfLE e ''ᵁ chartOpen V le_rfl)) z)
    (fun z => (Scheme.Modules.Hom.app
      (chartClsHom i π p V
        (restrictEquations V (fun k => X.presheaf.map (homOfLE e).op (f k))) hTV hTfV)
      (chartOpen V le_rfl)) z)
    y _ _ _ _ (homOfLE hC.le).op _ _ _ _ E

end Stacks.Gysin

end
