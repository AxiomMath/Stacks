module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# Tor independence on a Cartesian affine-open chart

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian diagram of schemes with `X` and `S'` Tor independent over `S`. On a Cartesian
affine-open chart the four coordinate rings `R = 𝒪_S(V)`, `A = 𝒪_X(U)`, `R' = 𝒪_{S'}(V')` and
`A' = 𝒪_{X'}(U')` form a pushout square; this module shows that `A` and `R'` are then Tor
independent over `R`, and deduces that the ring-level derived base-change comparison
`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'` is invertible on the whole unbounded derived category of `A`-modules.

## Main results

* `AlgebraicGeometry.BaseChangeChart.torIndependent`: the coordinate rings `A` and `R'` of a
  Cartesian affine-open chart are Tor independent over `R`.
* `AlgebraicGeometry.BaseChangeChart.isIso_derivedBaseChangeComparison`: the comparison of
  Stacks 065Z between derived base change over `R` and derived base change over `A` is an
  isomorphism on the chart, for every choice of models of the two total derived
  extension-of-scalars functors.

## Implementation notes

Tor independence of the schemes is read on the chart through the affine criterion
`AlgebraicGeometry.torIndependent_tfae`, which speaks of the rings of sections over a triple of
affine opens `U ⊆ X`, `V' ⊆ S'`, `V ⊆ S`. A chart records those opens as open immersions from
spectra instead, so the two presentations of each coordinate ring are compared by the canonical
isomorphisms `Γ(X, U) ≅ A` and `Γ(S, V) ≅ R`, and `torIndependent_congr` transports Tor
independence along them. `chart_sections_square` is the compatibility of those isomorphisms with
the structure maps, which is what makes the transport a transport of algebras.

`isIso_derivedBaseChangeComparison` takes the two derived functors and their comparisons as
parameters because Stacks 0661 does: a consumer presenting derived extension of scalars by
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` discharges the two
`Functor.IsLeftDerivedFunctor` hypotheses from that structure's own field, which instance search
would not find.

*What is not proved here.* This is the Tor-independence input of Stacks 08IB and not the tag's
conclusion: nothing below says that the derived base-change map of Stacks 08HY is an isomorphism.
Globalizing the chartwise comparison to that map is Stacks 0DJ9, which the library does not
carry.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.TorIndependence

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Tor independence of `f` and `g` read on the rings of sections over a triple of affine opens
`U ⊆ X`, `V ⊆ Y` lying over `W ⊆ S`. -/
private theorem affineOpen_ringTorIndependent {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hTor : TorIndependent f g) (U : X.Opens) (hU : IsAffineOpen U)
    (V : Y.Opens) (hV : IsAffineOpen V) (W : S.Opens) (hW : IsAffineOpen W)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    letI : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
    letI : Algebra Γ(S, W) Γ(Y, V) := (g.appLE W V hVW).hom.toAlgebra
    RingTheory.TorIndependence.TorIndependent Γ(S, W) Γ(X, U) Γ(Y, V) := by
  let _ : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  let _ : Algebra Γ(S, W) Γ(Y, V) := (g.appLE W V hVW).hom.toAlgebra
  have hCrit : ∀ (U₀ : X.Opens) (_ : IsAffineOpen U₀) (V₀ : Y.Opens) (_ : IsAffineOpen V₀)
      (W₀ : S.Opens) (_ : IsAffineOpen W₀) (h₁ : U₀ ≤ f ⁻¹ᵁ W₀) (h₂ : V₀ ≤ g ⁻¹ᵁ W₀),
      let : Algebra Γ(S, W₀) Γ(X, U₀) := (f.appLE W₀ U₀ h₁).hom.toAlgebra
      let : Algebra Γ(S, W₀) Γ(Y, V₀) := (g.appLE W₀ V₀ h₂).hom.toAlgebra
      Algebra.TorIndependent Γ(S, W₀) Γ(X, U₀) Γ(Y, V₀) :=
    ((torIndependent_tfae f g).out 1 2).mp hTor
  exact (RingTheory.TorIndependence.torIndependent_iff_isZero_tor
    Γ(S, W) Γ(X, U) Γ(Y, V)).2 (hCrit U hU V hV W hW hUW hVW)

private lemma appLE_congr_hom {X S : Scheme.{u}} {f₁ f₂ : X ⟶ S} (hf : f₁ = f₂)
    {U : S.Opens} {V : X.Opens} (h₁ : V ≤ f₁ ⁻¹ᵁ U) (h₂ : V ≤ f₂ ⁻¹ᵁ U) :
    f₁.appLE U V h₁ = f₂.appLE U V h₂ := by
  subst hf
  rfl

/-- Restricting along `j` to the whole of `Y` and then along `k` is restricting along `k ≫ j`. -/
private lemma appLE_top_comp_appTop {Z Y S : Scheme.{u}} (k : Z ⟶ Y) (j : Y ⟶ S)
    (W : S.Opens) (h : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ W) (h' : (⊤ : Z.Opens) ≤ (k ≫ j) ⁻¹ᵁ W) :
    j.appLE W ⊤ h ≫ k.appTop = (k ≫ j).appLE W ⊤ h' := by
  have hc := Scheme.Hom.appLE_comp_appLE k j W ⊤ (k ⁻¹ᵁ ⊤) h le_rfl
  rwa [Scheme.Hom.appLE_eq_app] at hc

/-- A chart square `i ≫ f = Spec.map a ≫ j` sends the open `U = i(⊤)` into `f⁻¹(j(⊤))`. -/
private lemma chart_image_le {X S : Scheme.{u}} {A R : CommRingCat.{u}}
    (f : X ⟶ S) (i : Spec A ⟶ X) (j : Spec R ⟶ S)
    [IsOpenImmersion i] [IsOpenImmersion j] (a : R ⟶ A)
    (w : i ≫ f = Spec.map a ≫ j) : i ''ᵁ ⊤ ≤ f ⁻¹ᵁ (j ''ᵁ ⊤) := by
  rintro _ ⟨x, _, rfl⟩
  exact ⟨(Spec.map a).base x, trivial, congrArg (fun k : Spec A ⟶ S => k.base x) w.symm⟩

/-- On a chart square, the map `Γ(S, j(⊤)) ⟶ Γ(X, i(⊤))` induced by `f` is identified with the
ring map `a` under the canonical isomorphisms `Γ(X, i(⊤)) ≅ A` and `Γ(S, j(⊤)) ≅ R`. -/
private lemma chart_sections_square {X S : Scheme.{u}} {A R : CommRingCat.{u}}
    (f : X ⟶ S) (i : Spec A ⟶ X) (j : Spec R ⟶ S)
    [IsOpenImmersion i] [IsOpenImmersion j] (a : R ⟶ A)
    (w : i ≫ f = Spec.map a ≫ j) :
    f.appLE (j ''ᵁ ⊤) (i ''ᵁ ⊤) (chart_image_le f i j a w) ≫
      (i.appIso ⊤).hom ≫ (Scheme.ΓSpecIso A).hom =
    (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso R).hom ≫ a := by
  rw [← Scheme.ΓSpecIso_naturality a, ← Category.assoc,
    Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom',
    Scheme.Hom.appLE_comp_appLE, ← Category.assoc,
    appLE_top_comp_appTop, appLE_congr_hom w]
  all_goals simp

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The coordinate rings of a Cartesian affine-open chart are Tor independent.** If `X` and
`S'` are Tor independent over `S`, then for every chart the ring `A = 𝒪_X(U)` and the ring
`R' = 𝒪_{S'}(V')` are Tor independent over `R = 𝒪_S(V)`. -/
public theorem torIndependent (hTor : TorIndependent f g)
    (ch : BaseChangeChart f g f' g') :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    RingTheory.TorIndependence.TorIndependent ch.R ch.A ch.R' := by
  let _ := ch.isOpenImmersion_incU
  let _ := ch.isOpenImmersion_incV
  let _ := ch.isOpenImmersion_incV'
  let U := ch.incU ''ᵁ ⊤
  let V := ch.incV' ''ᵁ ⊤
  let W := ch.incV ''ᵁ ⊤
  let hu := chart_image_le f ch.incU ch.incV ch.a ch.wU
  let hv := chart_image_le g ch.incV' ch.incV ch.b ch.wV'
  let _ := (f.appLE W U hu).hom.toAlgebra
  let _ := (g.appLE W V hv).hom.toAlgebra
  let _ := ch.a.hom.toAlgebra
  let _ := ch.b.hom.toAlgebra
  exact (torIndependent_congr Γ(S, W) Γ(X, U) Γ(S', V) ch.R ch.A ch.R'
    ((ch.incV.appIso ⊤) ≪≫ Scheme.ΓSpecIso ch.R).commRingCatIsoToRingEquiv
    ((ch.incU.appIso ⊤) ≪≫ Scheme.ΓSpecIso ch.A).commRingCatIsoToRingEquiv
    ((ch.incV'.appIso ⊤) ≪≫ Scheme.ΓSpecIso ch.R').commRingCatIsoToRingEquiv
    (fun r => DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (chart_sections_square f ch.incU ch.incV ch.a ch.wU)) r)
    (fun r => DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (chart_sections_square g ch.incV' ch.incV ch.b ch.wV')) r)).mp
    (affineOpen_ringTorIndependent f g hTor U
      ((isAffineOpen_top _).image_of_isOpenImmersion ch.incU) V
      ((isAffineOpen_top _).image_of_isOpenImmersion ch.incV') W
      ((isAffineOpen_top _).image_of_isOpenImmersion ch.incV) hu hv)

/-- **Stacks 0661 on a Cartesian affine-open chart.** If `X` and `S'` are Tor independent over
`S`, then for every chart the canonical comparison

`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'`

of Stacks 065Z is an isomorphism on the whole unbounded derived category of `A`-modules, for
every choice of models of the two total derived extension-of-scalars functors.

The pushout hypothesis of Stacks 0661 is the chart's own square `A' = A ⊗_R R'`, and the Tor
independence hypothesis is `AlgebraicGeometry.BaseChangeChart.torIndependent`.

This is the Tor-independence input of Stacks 08IB, not its conclusion: it does not say that the
derived base-change map `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K` of Stacks 08HY is an isomorphism. Passing
from the chartwise comparison to that map is Stacks 0DJ9. -/
@[stacks 08IB "the Tor-independence input of the proof: on every Cartesian affine-open chart \
of the square the coordinate rings are Tor independent, so the ring-level derived base-change \
comparison of Stacks 065Z is invertible there. The global statement is \
isIso_derivedBaseChangeMap_of_torIndependent"]
public theorem isIso_derivedBaseChangeComparison (hTor : TorIndependent f g)
    (ch : BaseChangeChart f g f' g')
    (L_g : DerivedCategory (ModuleCat.{u} ch.R) ⥤ DerivedCategory (ModuleCat.{u} ch.R'))
    (L_h : DerivedCategory (ModuleCat.{u} ch.A) ⥤ DerivedCategory (ModuleCat.{u} ch.A'))
    (alpha_g : DerivedCategory.Q ⋙ L_g ⟶
      (ModuleCat.extendScalars.{u, u, u} ch.b.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (alpha_h : DerivedCategory.Q ⋙ L_h ⟶
      (ModuleCat.extendScalars.{u, u, u} ch.c.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [L_g.IsLeftDerivedFunctor alpha_g
      (HomologicalComplex.quasiIso (ModuleCat.{u} ch.R) (ComplexShape.up ℤ))]
    [L_h.IsLeftDerivedFunctor alpha_h
      (HomologicalComplex.quasiIso (ModuleCat.{u} ch.A) (ComplexShape.up ℤ))] :
    IsIso (RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, u}
      ch.a.hom ch.b.hom ch.c.hom ch.d.hom ch.isPushout_hom L_g L_h alpha_g alpha_h).2.1 := by
  let _ := ch.a.hom.toAlgebra
  let _ := ch.b.hom.toAlgebra
  let _ := ch.c.hom.toAlgebra
  let _ := ch.d.hom.toAlgebra
  let _ := (ch.c.hom.comp ch.a.hom).toAlgebra
  have _ : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ch.R ch.R' ch.A' :=
    IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
  have _ : Algebra.IsPushout ch.R ch.A ch.R' ch.A' :=
    CommRingCat.isPushout_iff_isPushout.mp ch.isPushout
  exact RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u,
    u, u} (ch.torIndependent hTor) L_g L_h alpha_g alpha_h

end BaseChangeChart

end AlgebraicGeometry

end

end
