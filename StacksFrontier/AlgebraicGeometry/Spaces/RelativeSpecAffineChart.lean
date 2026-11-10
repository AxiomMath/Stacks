module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecUniversalMap

/-!
# The relative spectrum over an affine étale chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `𝒜` a sheaf of commutative
`𝒪_X`-algebras whose sections over every étale chart are fewer than the cutoff of the site, and
`V` an affine étale chart of `X`.  Write `R = 𝒜(V)`, an algebra over `Γ(V)`.  This file builds the
spectrum `Spec R` as an object of the site over `V`, with the point of the functor of points
`P = AlgebraicGeometry.Space.relativeSpecPoints 𝒜` that it carries, and proves that the square

```
Spec R ⟶ P
  |       |
  v       v
  V  ⟶  X
```

is cartesian, given that the chart reading `AlgebraicGeometry.Space.chartEval` at `V` identifies
the morphisms of algebras `𝒜 ⟶ x_* 𝒪_T` with the `Γ(V)`-algebra maps `R ⟶ Γ(T)`.

## Main definitions

* `AlgebraicGeometry.Space.affineChartSpec`: `Spec 𝒜(V)` as an object of the big fppf site.
* `AlgebraicGeometry.Space.affineChartSpecHom`: its morphism to the chart `V`.

## Main results

* `AlgebraicGeometry.Space.isPullback_of_forall_isPullback_app`: a commutative square of presheaves
  of types is cartesian as soon as it is cartesian at every object.
* `AlgebraicGeometry.Space.Scheme.hom_ext_of_ΓSpecIso_inv`: a morphism into a spectrum is
  determined by the ring map it induces on global sections.
* `AlgebraicGeometry.Space.isPullback_affineChartSpec`: the square above is cartesian.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u v w

namespace AlgebraicGeometry.Space

/-! ### Two general facts -/

/-- **A square of presheaves of types is cartesian as soon as it is cartesian at every object.** -/
theorem isPullback_of_forall_isPullback_app {C : Type w} [Category.{v} C]
    {P Q R Z : Cᵒᵖ ⥤ Type v} (fst : P ⟶ Q) (snd : P ⟶ R) (f : Q ⟶ Z) (g : R ⟶ Z)
    (h : ∀ U : Cᵒᵖ, IsPullback (fst.app U) (snd.app U) (f.app U) (g.app U)) :
    IsPullback fst snd f g := by
  have w : fst ≫ f = snd ≫ g := NatTrans.ext (funext fun U => (h U).w)
  exact IsPullback.of_isLimit (evaluationJointlyReflectsLimits _ fun U =>
    (isLimitMapConePullbackConeEquiv ((evaluation Cᵒᵖ (Type v)).obj U) w).symm (h U).isLimit)

/-- **A morphism into a spectrum is determined by the ring map it induces on global sections**,
precomposed with the identification `R ≅ Γ(Spec R)`. -/
theorem Scheme.hom_ext_of_ΓSpecIso_inv {T : Scheme.{u}} {R : CommRingCat.{u}} {f g : T ⟶ Spec R}
    (h : (Scheme.ΓSpecIso R).inv ≫ f.appTop = (Scheme.ΓSpecIso R).inv ≫ g.appTop) : f = g :=
  ext_of_isAffine ((cancel_epi _).1 h)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The spectrum of the sections over an affine chart -/

section AffineChart

variable {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
  (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A) (V : SmallEtale B S hS X.1)
  [IsAffine (chartScheme V)]

/-- The structure map `Γ(V) ⟶ 𝒜(V)` of the algebra sheaf at a chart, as a morphism of rings. -/
def chartAlgebraMap : Γ(chartScheme V, ⊤) ⟶ A.right.obj.obj (op V) :=
  CommRingCat.ofHom (A.algebraMap (op V))

omit [IsAffine (chartScheme V)] in
include hA in
/-- The spectrum of `𝒜(V)` is an object of the site: it has fewer than `B.cutoff` points. -/
theorem contains_spec_chart : B.Contains (Spec (A.right.obj.obj (op V))) := by
  change (Spec (A.right.obj.obj (op V))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (hA V)

/-- The morphism of schemes `Spec 𝒜(V) ⟶ V` induced by the structure map `Γ(V) ⟶ 𝒜(V)`. -/
def specChartMap : Spec (A.right.obj.obj (op V)) ⟶ chartScheme V :=
  Spec.map (chartAlgebraMap B S hS A V) ≫ (chartScheme V).isoSpec.inv

/-- On global sections, `Spec 𝒜(V) ⟶ V` is the structure map `Γ(V) ⟶ 𝒜(V)` followed by the
identification `𝒜(V) ≅ Γ(Spec 𝒜(V))`. -/
theorem specChartMap_appTop :
    (specChartMap B S hS A V).appTop =
      chartAlgebraMap B S hS A V ≫ (Scheme.ΓSpecIso (A.right.obj.obj (op V))).inv := by
  have h : (chartScheme V).isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(chartScheme V, ⊤)).inv := by
    rw [← Iso.comp_hom_eq_id, ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop,
      Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]
  rw [specChartMap, Scheme.Hom.comp_appTop, h, Scheme.ΓSpecIso_inv_naturality]

/-- **`Spec 𝒜(V)` as an object of the big fppf site**, over `S` through `V`. -/
abbrev affineChartSpec : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := B.obj (contains_spec_chart B S hS A hA V)) (Y := B.obj hS)
    (specChartMap B S hS A V ≫ B.inclusion.map V.obj.left.hom))

/-- **The morphism `Spec 𝒜(V) ⟶ V`** of the big fppf site. -/
def affineChartSpecHom : affineChartSpec B S hS A hA V ⟶ V.obj.left :=
  Over.homMk (B.inclusion.preimage (X := B.obj (contains_spec_chart B S hS A hA V))
    (Y := V.obj.left.left) (specChartMap B S hS A V)) (by
      refine B.inclusion.map_injective ?_
      change B.inclusion.map (B.inclusion.preimage _ ≫ V.obj.left.hom) =
        B.inclusion.map (B.inclusion.preimage _)
      rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage])

/-- The underlying morphism of schemes of `affineChartSpecHom` is `specChartMap`. -/
theorem toScheme_map_affineChartSpecHom :
    (BigFppfOver.toScheme B S hS).map (affineChartSpecHom B S hS A hA V) =
      specChartMap B S hS A V :=
  Functor.map_preimage B.inclusion (X := B.obj (contains_spec_chart B S hS A hA V))
    (Y := V.obj.left.left) (specChartMap B S hS A V)

/-- The point of `X` with values in `Spec 𝒜(V)` through the chart `V`. -/
def affineChartSpecPt : X.1.obj (op (affineChartSpec B S hS A hA V)) :=
  yonedaEquiv (yoneda.map (affineChartSpecHom B S hS A hA V) ≫ V.obj.hom)

/-- The morphism of presheaves corresponding to `affineChartSpecPt` is the composite of
`Spec 𝒜(V) ⟶ V` with the chart `V ⟶ X`. -/
theorem yonedaEquiv_symm_affineChartSpecPt :
    yonedaEquiv.symm (affineChartSpecPt B S hS A hA V) =
      yoneda.map (affineChartSpecHom B S hS A hA V) ≫ V.obj.hom :=
  Equiv.symm_apply_apply _ _

/-- The structure map `Γ(V) ⟶ 𝒜(V)` followed by `𝒜(V) ≅ Γ(Spec 𝒜(V))` is the map on global
sections of `Spec 𝒜(V) ⟶ V`. -/
theorem chartAlgebraMap_comp_ΓSpecIso_inv :
    chartAlgebraMap B S hS A V ≫ (Scheme.ΓSpecIso (A.right.obj.obj (op V))).inv =
      ((BigFppfOver.toScheme B S hS).map (affineChartSpecHom B S hS A hA V)).appTop := by
  rw [toScheme_map_affineChartSpecHom, specChartMap_appTop]

omit [IsAffine (chartScheme V)] in
/-- A point of `X` with values in `T` through the chart, as computed by the chart's map to `X`. -/
theorem chart_hom_app_eq {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) :
    V.obj.hom.app (op T) v = yonedaEquiv (yoneda.map v ≫ V.obj.hom) := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- The pullback of `affineChartSpecPt` along `t : T ⟶ Spec 𝒜(V)` is the point of `X` given by
the chart along `t` followed by `Spec 𝒜(V) ⟶ V`. -/
theorem map_affineChartSpecPt {T : BigFppfOver B S hS} (t : T ⟶ affineChartSpec B S hS A hA V) :
    X.1.map t.op (affineChartSpecPt B S hS A hA V) =
      V.obj.hom.app (op T) (t ≫ affineChartSpecHom B S hS A hA V) := by
  rw [affineChartSpecPt, yonedaEquiv_naturality, chart_hom_app_eq, Functor.map_comp,
    Category.assoc]

/-- A morphism of schemes `T ⟶ Spec 𝒜(V)` over `V`, as a morphism of the big fppf site. -/
def affineChartSpecLift {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (t₀ : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (A.right.obj.obj (op V)))
    (h : t₀ ≫ specChartMap B S hS A V = (BigFppfOver.toScheme B S hS).map v) :
    T ⟶ affineChartSpec B S hS A hA V :=
  Over.homMk (B.inclusion.preimage (X := T.left)
    (Y := B.obj (contains_spec_chart B S hS A hA V)) t₀) (by
      refine B.inclusion.map_injective ?_
      change B.inclusion.map (B.inclusion.preimage (X := T.left)
          (Y := B.obj (contains_spec_chart B S hS A hA V)) t₀ ≫
        B.inclusion.preimage (X := B.obj (contains_spec_chart B S hS A hA V)) (Y := B.obj hS)
          (specChartMap B S hS A V ≫ B.inclusion.map V.obj.left.hom)) = B.inclusion.map T.hom
      rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage, ← Category.assoc, h]
      change B.inclusion.map v.left ≫ B.inclusion.map V.obj.left.hom = _
      rw [← Functor.map_comp, Over.w v])

/-- The underlying morphism of schemes of `affineChartSpecLift` is the given morphism `t₀`. -/
theorem toScheme_map_affineChartSpecLift {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (t₀ : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (A.right.obj.obj (op V)))
    (h : t₀ ≫ specChartMap B S hS A V = (BigFppfOver.toScheme B S hS).map v) :
    (BigFppfOver.toScheme B S hS).map (affineChartSpecLift B S hS A hA V v t₀ h) = t₀ :=
  Functor.map_preimage B.inclusion (X := T.left)
    (Y := B.obj (contains_spec_chart B S hS A hA V)) t₀

section Pullback

variable
  (hinj : ∀ {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom),
    Function.Injective (AlgebraicGeometry.Space.chartEval B S hS A V v x hxv))
  (hsurj : ∀ {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (β : A.right.obj.obj (op V) ⟶ Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)),
    chartAlgebraMap B S hS A V ≫ β = ((BigFppfOver.toScheme B S hS).map v).appTop →
      ∃ α, AlgebraicGeometry.Space.chartEval B S hS A V v x hxv α = β)

omit [IsAffine (chartScheme V)] in
include hinj in
/-- Two points of the relative spectrum with the same underlying point of `X` agree as soon as
their readings at the chart along a common morphism to the chart agree. -/
theorem RelativeSpecPoint.ext_of_chartEval {T : BigFppfOver B S hS}
    {p p' : RelativeSpecPoint B S hS A T} (hpt : p.pt = p'.pt) (v : T ⟶ V.obj.left)
    (h : yonedaEquiv.symm p.pt = yoneda.map v ≫ V.obj.hom)
    (h' : yonedaEquiv.symm p'.pt = yoneda.map v ≫ V.obj.hom)
    (he : p.chartEval B S hS V v h = p'.chartEval B S hS V v h') : p = p' := by
  obtain ⟨x, α⟩ := p
  obtain ⟨x', α'⟩ := p'
  obtain rfl : x = x' := hpt
  obtain rfl : α = α' := hinj v x h he
  rfl

/-- The morphism of algebras of the point of `P` carried by `Spec 𝒜(V)`: the one whose chart
reading is the canonical ring map `𝒜(V) ⟶ Γ(Spec 𝒜(V))`. -/
def affineChartSpecAlgHom :
    A ⟶ pushforwardAlgebra B S hS
      (specPointOver B S hS (affineChartSpec B S hS A hA V) (affineChartSpecPt B S hS A hA V)) :=
  Classical.choose (hsurj (affineChartSpecHom B S hS A hA V) (affineChartSpecPt B S hS A hA V)
    (yonedaEquiv_symm_affineChartSpecPt B S hS A hA V)
    (Scheme.ΓSpecIso (A.right.obj.obj (op V))).inv
    (chartAlgebraMap_comp_ΓSpecIso_inv B S hS A hA V))

/-- **The point of the relative spectrum carried by `Spec 𝒜(V)`.** -/
def affineChartSpecPoint : RelativeSpecPoint B S hS A (affineChartSpec B S hS A hA V) :=
  ⟨affineChartSpecPt B S hS A hA V, affineChartSpecAlgHom B S hS A hA V hsurj⟩

/-- The point of `X` underlying `affineChartSpecPoint` is `affineChartSpecPt`. -/
theorem affineChartSpecPoint_pt :
    (affineChartSpecPoint B S hS A hA V hsurj).pt = affineChartSpecPt B S hS A hA V :=
  rfl

/-- The reading of `affineChartSpecPoint` at the chart along `Spec 𝒜(V) ⟶ V` is the canonical
ring map `𝒜(V) ⟶ Γ(Spec 𝒜(V))`. -/
theorem affineChartSpecPoint_chartEval :
    (affineChartSpecPoint B S hS A hA V hsurj).chartEval B S hS V
        (affineChartSpecHom B S hS A hA V) (yonedaEquiv_symm_affineChartSpecPt B S hS A hA V) =
      (Scheme.ΓSpecIso (A.right.obj.obj (op V))).inv :=
  Classical.choose_spec (hsurj (affineChartSpecHom B S hS A hA V) (affineChartSpecPt B S hS A hA V)
    (yonedaEquiv_symm_affineChartSpecPt B S hS A hA V)
    (Scheme.ΓSpecIso (A.right.obj.obj (op V))).inv
    (chartAlgebraMap_comp_ΓSpecIso_inv B S hS A hA V))

/-- **The morphism `Spec 𝒜(V) ⟶ P`** to the functor of points of the relative spectrum. -/
def affineChartSpecToPoints :
    yoneda.obj (affineChartSpec B S hS A hA V) ⟶ relativeSpecPoints B S hS A :=
  yonedaEquiv.symm ((relativeSpecPointsEquiv B S hS A _).symm
    (affineChartSpecPoint B S hS A hA V hsurj))

/-- The image of `t : T ⟶ Spec 𝒜(V)` under `affineChartSpecToPoints` is the pullback of
`affineChartSpecPoint` along `t`. -/
theorem relativeSpecPointsEquiv_affineChartSpecToPoints_app {T : BigFppfOver B S hS}
    (t : T ⟶ affineChartSpec B S hS A hA V) :
    relativeSpecPointsEquiv B S hS A T
        ((affineChartSpecToPoints B S hS A hA V hsurj).app (op T) t) =
      (affineChartSpecPoint B S hS A hA V hsurj).map B S hS t := by
  change relativeSpecPointsEquiv B S hS A T ((relativeSpecPoints B S hS A).map t.op
    ((relativeSpecPointsEquiv B S hS A _).symm (affineChartSpecPoint B S hS A hA V hsurj))) = _
  rw [relativeSpecPointsEquiv_map, Equiv.apply_symm_apply]

/-- The reading of the pulled-back point along a morphism `t : T ⟶ Spec 𝒜(V)` is the ring map that
`t` induces, precomposed with `𝒜(V) ≅ Γ(Spec 𝒜(V))`. -/
theorem affineChartSpecPoint_map_chartEval {T : BigFppfOver B S hS}
    (t : T ⟶ affineChartSpec B S hS A hA V)
    (h : yonedaEquiv.symm ((affineChartSpecPoint B S hS A hA V hsurj).map B S hS t).pt =
      yoneda.map (t ≫ affineChartSpecHom B S hS A hA V) ≫ V.obj.hom) :
    ((affineChartSpecPoint B S hS A hA V hsurj).map B S hS t).chartEval B S hS V
        (t ≫ affineChartSpecHom B S hS A hA V) h =
      (Scheme.ΓSpecIso (A.right.obj.obj (op V))).inv ≫
        ((BigFppfOver.toScheme B S hS).map t).appTop := by
  rw [RelativeSpecPoint.chartEval_map B S hS V t _ _
    (yonedaEquiv_symm_affineChartSpecPt B S hS A hA V) h, affineChartSpecPoint_chartEval]

include hinj in
/-- **The fibre of the relative spectrum over an affine étale chart `V` is `Spec 𝒜(V)`**: the
square formed by `Spec 𝒜(V) ⟶ P`, `Spec 𝒜(V) ⟶ V`, the projection `π : P ⟶ X` and the chart
`V ⟶ X` is cartesian. -/
theorem isPullback_affineChartSpec :
    IsPullback (affineChartSpecToPoints B S hS A hA V hsurj)
      (yoneda.map (affineChartSpecHom B S hS A hA V)) (relativeSpecPointsπ B S hS A)
      V.obj.hom := by
  refine isPullback_of_forall_isPullback_app _ _ _ _ fun U => ?_
  obtain ⟨T⟩ := U
  have hpt0 : ∀ t : T ⟶ affineChartSpec B S hS A hA V,
      ((affineChartSpecPoint B S hS A hA V hsurj).map B S hS t).pt =
        V.obj.hom.app (op T) (t ≫ affineChartSpecHom B S hS A hA V) := by
    intro t
    rw [RelativeSpecPoint.map_pt, affineChartSpecPoint_pt]
    exact map_affineChartSpecPt B S hS A hA V t
  have hpt' : ∀ t : T ⟶ affineChartSpec B S hS A hA V,
      yonedaEquiv.symm ((affineChartSpecPoint B S hS A hA V hsurj).map B S hS t).pt =
        yoneda.map (t ≫ affineChartSpecHom B S hS A hA V) ≫ V.obj.hom := by
    intro t
    rw [hpt0, chart_hom_app_eq, Equiv.symm_apply_apply]
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext t
    exact (relativeSpecPointsπ_app ..).trans
      ((congrArg _ (relativeSpecPointsEquiv_affineChartSpecToPoints_app ..)).trans (hpt0 t))
  · rintro t t' ⟨h₁, h₂⟩
    have e₁ : (affineChartSpecPoint B S hS A hA V hsurj).map B S hS t =
        (affineChartSpecPoint B S hS A hA V hsurj).map B S hS t' := by
      rw [← relativeSpecPointsEquiv_affineChartSpecToPoints_app,
        ← relativeSpecPointsEquiv_affineChartSpecToPoints_app]
      exact congrArg _ h₁
    have e₂ : t ≫ affineChartSpecHom B S hS A hA V = t' ≫ affineChartSpecHom B S hS A hA V := h₂
    have e₃ := RelativeSpecPoint.chartEval_congr B S hS V e₂ e₁ (hpt' t) (hpt' t')
    rw [affineChartSpecPoint_map_chartEval, affineChartSpecPoint_map_chartEval] at e₃
    exact (BigFppfOver.toScheme B S hS).map_injective (Scheme.hom_ext_of_ΓSpecIso_inv e₃)
  · intro y v hy
    set p := relativeSpecPointsEquiv B S hS A T y with hp
    have hpv : p.pt = V.obj.hom.app (op T) v := (relativeSpecPointsπ_app ..).symm.trans hy
    have hxv : yonedaEquiv.symm p.pt = yoneda.map v ≫ V.obj.hom := by
      rw [hpv, chart_hom_app_eq, Equiv.symm_apply_apply]
    let β := p.chartEval B S hS V v hxv
    have hβ : chartAlgebraMap B S hS A V ≫ β = ((BigFppfOver.toScheme B S hS).map v).appTop := by
      ext r
      exact RelativeSpecPoint.chartEval_algebraMap B S hS V v p hxv r
    let t₀ : (BigFppfOver.toScheme B S hS).obj T ⟶ Spec (A.right.obj.obj (op V)) :=
      ΓSpec.adjunction.homEquiv _ (op (A.right.obj.obj (op V))) β.op
    have ht₀ : (Scheme.ΓSpecIso (A.right.obj.obj (op V))).inv ≫ t₀.appTop = β :=
      ΓSpecIso_inv_ΓSpec_adjunction_homEquiv β
    have ht₀q : t₀ ≫ specChartMap B S hS A V = (BigFppfOver.toScheme B S hS).map v := by
      refine ext_of_isAffine ?_
      rw [Scheme.Hom.comp_appTop, specChartMap_appTop, Category.assoc, ht₀, hβ]
    let t : T ⟶ affineChartSpec B S hS A hA V := affineChartSpecLift B S hS A hA V v t₀ ht₀q
    have ht : (BigFppfOver.toScheme B S hS).map t = t₀ :=
      toScheme_map_affineChartSpecLift B S hS A hA V v t₀ ht₀q
    have htq : t ≫ affineChartSpecHom B S hS A hA V = v := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, ht, toScheme_map_affineChartSpecHom, ht₀q]
    refine ⟨t, ?_, htq⟩
    apply (relativeSpecPointsEquiv B S hS A T).injective
    rw [relativeSpecPointsEquiv_affineChartSpecToPoints_app, ← hp]
    refine RelativeSpecPoint.ext_of_chartEval B S hS A V hinj ?_ v
      ((hpt' t).trans (by rw [htq])) hxv ?_
    · rw [hpv, ← htq]
      exact hpt0 t
    · have := affineChartSpecPoint_map_chartEval B S hS A hA V hsurj t (hpt' t)
      rw [ht, ht₀] at this
      exact (RelativeSpecPoint.chartEval_congr B S hS V htq.symm rfl _ _).trans this

end Pullback

end AffineChart

end AlgebraicGeometry.Space

end
