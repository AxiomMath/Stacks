module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecChartEval

/-!
# The universal morphism from an algebra sheaf to the direct image of its relative spectrum

Let `X` be an algebraic space over a scheme `S` of a big fppf site and `𝒜` a sheaf of commutative
`𝒪_X`-algebras.  Suppose the functor of points `P = AlgebraicGeometry.Space.relativeSpecPoints 𝒜`
of the relative spectrum is an algebraic space whose projection `π : P ⟶ X` is representable.
Then `𝒜` maps to `π_* 𝒪_P`: over an étale chart `V` of `X`, the fibre product `P ×_X V` is a scheme
`Z`, its projection to `P` is a point `(x, α)` of `P` with values in `Z` — the universal point —
and reading `α : 𝒜 ⟶ x_* 𝒪_Z` at `V` along `Z ⟶ V` gives a ring map `𝒜(V) ⟶ Γ(Z) = (π_* 𝒪_P)(V)`.

## Main definitions

* `AlgebraicGeometry.Space.relativeSpecOver`: `P` as an algebraic space over `X`.
* `AlgebraicGeometry.Space.relativeSpecUniversalPoint`: the universal point of `P` with values in
  `P ×_X V`.
* `AlgebraicGeometry.Space.relativeSpecUniversalMap`: the morphism of `𝒪_X`-algebras
  `𝒜 ⟶ π_* 𝒪_P`.

## Main results

* `AlgebraicGeometry.Space.relativeSpecUniversalMap_app`: its component at a chart `V` is the chart
  reading of the universal point, followed by the identification of `Γ(P ×_X V)` with
  `(π_* 𝒪_P)(V)`.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section PointEval

variable {X : AlgebraicSpaces B S hS} {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}

/-- The chart reading of a point of the relative spectrum, as a function of the point. -/
def RelativeSpecPoint.chartEval (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS}
    (v : T ⟶ V.obj.left) (p : RelativeSpecPoint B S hS A T)
    (h : yonedaEquiv.symm p.pt = yoneda.map v ≫ V.obj.hom) :
    A.right.obj.obj (op V) ⟶ Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  AlgebraicGeometry.Space.chartEval B S hS A V v p.pt h p.hom

/-- The chart reading of a point depends only on the point and the morphism to the chart, not on
the proof that they are compatible. -/
theorem RelativeSpecPoint.chartEval_congr (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS}
    {v v' : T ⟶ V.obj.left} (hv : v = v') {p q : RelativeSpecPoint B S hS A T} (hpq : p = q)
    (h : yonedaEquiv.symm p.pt = yoneda.map v ≫ V.obj.hom)
    (h' : yonedaEquiv.symm q.pt = yoneda.map v' ≫ V.obj.hom) :
    p.chartEval B S hS V v h = q.chartEval B S hS V v' h' := by
  subst hv hpq
  rfl

/-- **Naturality of the chart reading of points in the test object**, for the pullback of points
`AlgebraicGeometry.Space.RelativeSpecPoint.map`. -/
theorem RelativeSpecPoint.chartEval_map (V : SmallEtale B S hS X.1) {T T' : BigFppfOver B S hS}
    (g : T' ⟶ T) (v : T ⟶ V.obj.left) (p : RelativeSpecPoint B S hS A T)
    (h : yonedaEquiv.symm p.pt = yoneda.map v ≫ V.obj.hom)
    (h' : yonedaEquiv.symm (p.map B S hS g).pt = yoneda.map (g ≫ v) ≫ V.obj.hom) :
    (p.map B S hS g).chartEval B S hS V (g ≫ v) h' =
      p.chartEval B S hS V v h ≫ ((BigFppfOver.toScheme B S hS).map g).appTop := by
  obtain ⟨x, α⟩ := p
  exact chartEval_compPushforwardAlgebraMap B S hS V g v x h h' α

/-- **Naturality of the chart reading of points in the chart.** -/
theorem RelativeSpecPoint.map_comp_chartEval {V₁ V₂ : SmallEtale B S hS X.1} (k : V₁ ⟶ V₂)
    {T : BigFppfOver B S hS} (v₁ : T ⟶ V₁.obj.left) (p : RelativeSpecPoint B S hS A T)
    (h₁ : yonedaEquiv.symm p.pt = yoneda.map v₁ ≫ V₁.obj.hom)
    (h₂ : yonedaEquiv.symm p.pt = yoneda.map (v₁ ≫ k.hom.left) ≫ V₂.obj.hom) :
    A.right.obj.map k.op ≫ p.chartEval B S hS V₁ v₁ h₁ =
      p.chartEval B S hS V₂ (v₁ ≫ k.hom.left) h₂ :=
  AlgebraicGeometry.Space.map_comp_chartEval B S hS k v₁ p.pt h₁ h₂ p.hom

/-- The chart reading of a point is compatible with the structure maps: on the image of a section
`r` of `𝒪_X` it is the pullback of `r` along `T ⟶ V`. -/
theorem RelativeSpecPoint.chartEval_algebraMap (V : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (p : RelativeSpecPoint B S hS A T)
    (h : yonedaEquiv.symm p.pt = yoneda.map v ≫ V.obj.hom)
    (r : (structureSheaf B S hS X.1 X.2).obj.obj (op V)) :
    p.chartEval B S hS V v h (A.algebraMap (op V) r) =
      ((BigFppfOver.toScheme B S hS).map v).appTop r :=
  AlgebraicGeometry.Space.chartEval_algebraMap B S hS V v p.pt h p.hom r

end PointEval

section UniversalMap

variable {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
  (hP : IsAlgebraicSpace B S hS (relativeSpecPoints B S hS A))

/-- **The relative spectrum as an algebraic space over `X`**, when its functor of points is an
algebraic space. -/
abbrev relativeSpecOver : Over X :=
  Over.mk (ObjectProperty.homMk (relativeSpecPointsπ B S hS A) :
    (⟨relativeSpecPoints B S hS A, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)

variable (hπ : yoneda.relativelyRepresentable (relativeSpecPointsπ B S hS A))

/-- The sections of `π_* 𝒪_P` over a chart `V` are the regular functions on `P ×_X V`, with the
fibre product written as the representing object `hπ.pullback V`. -/
def relativeSpecSectionsIso (V : SmallEtale B S hS X.1) :
    (pushforwardAlgebra B S hS (relativeSpecOver B S hS A hP)).right.obj.obj (op V) ≅
      Γ((BigFppfOver.toScheme B S hS).obj (hπ.pullback V.obj.hom), ⊤) :=
  pushforwardAlgebraSectionsIso B S hS (relativeSpecOver B S hS A hP) hπ V

/-- **The universal point** of the relative spectrum with values in `P ×_X V`: the projection
`P ×_X V ⟶ P`, read as a point of `P`. -/
def relativeSpecUniversalPoint (V : SmallEtale B S hS X.1) :
    RelativeSpecPoint B S hS A (hπ.pullback V.obj.hom) :=
  relativeSpecPointsEquiv B S hS A _ (yonedaEquiv (hπ.fst V.obj.hom))

/-- The underlying point of `X` of the universal point at `V` is the projection `P ×_X V ⟶ V`
followed by the chart `V ⟶ X`. -/
theorem relativeSpecUniversalPoint_pt (V : SmallEtale B S hS X.1) :
    yonedaEquiv.symm (relativeSpecUniversalPoint B S hS A hπ V).pt =
      yoneda.map (hπ.snd V.obj.hom) ≫ V.obj.hom := by
  have h : (relativeSpecUniversalPoint B S hS A hπ V).pt =
      yonedaEquiv (hπ.fst V.obj.hom ≫ relativeSpecPointsπ B S hS A) := by
    rw [yonedaEquiv_comp]
    rfl
  rw [h, Equiv.symm_apply_apply]
  exact (hπ.isPullback V.obj.hom).w

/-- The universal point at `V`, pulled back along the base change `P ×_X V₁ ⟶ P ×_X V₂` of a
morphism of charts, is the universal point at `V₁`. -/
theorem relativeSpecUniversalPoint_map {V₁ V₂ : SmallEtale B S hS X.1}
    (a : hπ.pullback V₁.obj.hom ⟶ hπ.pullback V₂.obj.hom)
    (ha : yoneda.map a ≫ hπ.fst V₂.obj.hom = hπ.fst V₁.obj.hom) :
    (relativeSpecUniversalPoint B S hS A hπ V₂).map B S hS a =
      relativeSpecUniversalPoint B S hS A hπ V₁ := by
  unfold relativeSpecUniversalPoint
  rw [← relativeSpecPointsEquiv_map]
  congr 1
  rw [yonedaEquiv_naturality, ha]

/-- The component at a chart `V` of the universal morphism: the chart reading of the universal
point at `V`, followed by the identification of `Γ(P ×_X V)` with `(π_* 𝒪_P)(V)`. -/
def relativeSpecUniversalMapApp (V : SmallEtale B S hS X.1) :
    A.right.obj.obj (op V) ⟶
      (pushforwardAlgebra B S hS (relativeSpecOver B S hS A hP)).right.obj.obj (op V) :=
  (relativeSpecUniversalPoint B S hS A hπ V).chartEval B S hS V (hπ.snd V.obj.hom)
      (relativeSpecUniversalPoint_pt B S hS A hπ V) ≫
    (relativeSpecSectionsIso B S hS A hP hπ V).inv

/-- The components `relativeSpecUniversalMapApp` are natural in the chart `V`. -/
theorem relativeSpecUniversalMapApp_naturality {V₁ V₂ : SmallEtale B S hS X.1} (k : V₁ ⟶ V₂) :
    A.right.obj.map k.op ≫ relativeSpecUniversalMapApp B S hS A hP hπ V₁ =
      relativeSpecUniversalMapApp B S hS A hP hπ V₂ ≫
        (pushforwardAlgebra B S hS (relativeSpecOver B S hS A hP)).right.obj.map k.op := by
  have hk : yoneda.map (hπ.snd V₁.obj.hom) ≫ V₁.obj.hom =
      yoneda.map (hπ.snd V₁.obj.hom ≫ k.hom.left) ≫ V₂.obj.hom := by
    rw [Functor.map_comp, Category.assoc, CostructuredArrow.w k.hom]
  have hcond : hπ.fst V₁.obj.hom ≫ relativeSpecPointsπ B S hS A =
      yoneda.map (hπ.snd V₁.obj.hom ≫ k.hom.left) ≫ V₂.obj.hom :=
    (hπ.isPullback V₁.obj.hom).w.trans hk
  let a : hπ.pullback V₁.obj.hom ⟶ hπ.pullback V₂.obj.hom := hπ.lift _ _ hcond
  have ha₁ : yoneda.map a ≫ hπ.fst V₂.obj.hom = hπ.fst V₁.obj.hom :=
    Functor.relativelyRepresentable.lift_fst _ _ _ _
  have ha₂ : a ≫ hπ.snd V₂.obj.hom = hπ.snd V₁.obj.hom ≫ k.hom.left :=
    Functor.relativelyRepresentable.lift_snd _ _ _ _
  have nat' : (relativeSpecSectionsIso B S hS A hP hπ V₂).inv ≫
      (pushforwardAlgebra B S hS (relativeSpecOver B S hS A hP)).right.obj.map k.op =
        ((BigFppfOver.toScheme B S hS).map a).appTop ≫
          (relativeSpecSectionsIso B S hS A hP hπ V₁).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact pushforwardAlgebraSectionsIso_naturality B S hS (relativeSpecOver B S hS A hP) hπ k
      a ha₁ ha₂
  have h₂ : yonedaEquiv.symm (relativeSpecUniversalPoint B S hS A hπ V₁).pt =
      yoneda.map (hπ.snd V₁.obj.hom ≫ k.hom.left) ≫ V₂.obj.hom :=
    (relativeSpecUniversalPoint_pt B S hS A hπ V₁).trans hk
  have h' : yonedaEquiv.symm ((relativeSpecUniversalPoint B S hS A hπ V₂).map B S hS a).pt =
      yoneda.map (a ≫ hπ.snd V₂.obj.hom) ≫ V₂.obj.hom := by
    rwa [relativeSpecUniversalPoint_map B S hS A hπ a ha₁, ha₂]
  have key : A.right.obj.map k.op ≫
      (relativeSpecUniversalPoint B S hS A hπ V₁).chartEval B S hS V₁ (hπ.snd V₁.obj.hom)
        (relativeSpecUniversalPoint_pt B S hS A hπ V₁) =
      (relativeSpecUniversalPoint B S hS A hπ V₂).chartEval B S hS V₂ (hπ.snd V₂.obj.hom)
        (relativeSpecUniversalPoint_pt B S hS A hπ V₂) ≫
        ((BigFppfOver.toScheme B S hS).map a).appTop := by
    rw [RelativeSpecPoint.map_comp_chartEval B S hS k _ _ _ h₂,
      ← RelativeSpecPoint.chartEval_map B S hS V₂ a _ _ _ h']
    exact RelativeSpecPoint.chartEval_congr B S hS V₂ ha₂.symm
      (relativeSpecUniversalPoint_map B S hS A hπ a ha₁).symm _ _
  unfold relativeSpecUniversalMapApp
  rw [Category.assoc, nat', ← Category.assoc, ← Category.assoc, key]

/-- The component `relativeSpecUniversalMapApp` at `V` is compatible with the `𝒪_X(V)`-algebra
structures of `𝒜(V)` and `(π_* 𝒪_P)(V)`. -/
theorem relativeSpecUniversalMapApp_algebraMap (V : SmallEtale B S hS X.1)
    (r : (structureSheaf B S hS X.1 X.2).obj.obj (op V)) :
    relativeSpecUniversalMapApp B S hS A hP hπ V (A.algebraMap (op V) r) =
      (pushforwardAlgebra B S hS (relativeSpecOver B S hS A hP)).algebraMap (op V) r := by
  have hfs : (smallEtaleRingedToposHom B S hS (relativeSpecOver B S hS A hP).hom).fSharp.hom.app
      (op V) = ((BigFppfOver.toScheme B S hS).map (hπ.snd V.obj.hom)).appTop ≫
        (relativeSpecSectionsIso B S hS A hP hπ V).inv :=
    (Iso.eq_comp_inv _).2 <| fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS
      (relativeSpecOver B S hS A hP) hπ V
  unfold relativeSpecUniversalMapApp
  rw [ConcreteCategory.comp_apply, RelativeSpecPoint.chartEval_algebraMap]
  exact (ConcreteCategory.congr_hom hfs r).symm

/-- **The universal morphism `𝒜 ⟶ π_* 𝒪_P`** from an algebra sheaf to the direct image of the
structure sheaf of its relative spectrum `P`, when `P` is an algebraic space with representable
projection to `X`.  Its component at a chart `V` is the chart reading of the universal point of
`P` with values in `P ×_X V`. -/
def relativeSpecUniversalMap : A ⟶ pushforwardAlgebra B S hS (relativeSpecOver B S hS A hP) where
  right :=
    { hom :=
        { app := fun V => relativeSpecUniversalMapApp B S hS A hP hπ V.unop
          naturality := fun _ _ k =>
            relativeSpecUniversalMapApp_naturality B S hS A hP hπ k.unop } }
  comm U r := relativeSpecUniversalMapApp_algebraMap B S hS A hP hπ U.unop r

/-- The component of `relativeSpecUniversalMap` at a chart `V` is `relativeSpecUniversalMapApp`. -/
theorem relativeSpecUniversalMap_app (V : SmallEtale B S hS X.1) :
    (relativeSpecUniversalMap B S hS A hP hπ).right.hom.app (op V) =
      relativeSpecUniversalMapApp B S hS A hP hπ V :=
  rfl

end UniversalMap

end AlgebraicGeometry.Space

end
