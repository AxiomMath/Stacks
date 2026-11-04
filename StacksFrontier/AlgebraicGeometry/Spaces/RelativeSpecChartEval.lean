module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFull
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward

/-!
# Reading a morphism of algebras into a direct image at a chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `𝒜` a sheaf of commutative
`𝒪_X`-algebras, `T` an object of the site with a point `x ∈ X(T)`, and
`α : 𝒜 ⟶ x_* 𝒪_T` a morphism of `𝒪_X`-algebras.  If `x` factors through an étale chart `V` of `X`
by a morphism `v : T ⟶ V`, then `α` has a reading at `V`: a ring map `𝒜(V) ⟶ Γ(T, 𝒪_T)`.  It is
`α` at `V`, followed by the identification of the sections of `x_* 𝒪_T` over `V` with the regular
functions on `T ×_X V`, followed by pullback along the graph `T ⟶ T ×_X V` of `v`.

## Main definitions

* `AlgebraicGeometry.Space.chartEval`: the reading `𝒜(V) ⟶ Γ(T, 𝒪_T)` of `α` at `V` along `v`.
* `AlgebraicGeometry.Space.chartGraph`: the graph `T ⟶ T ×_X V` of `v`.

## Main results

* `AlgebraicGeometry.Space.chartEval_compPushforwardAlgebraMap`: **naturality in `T`.**  Reading
  the pullback of `α` along `g : T' ⟶ T` at `V` along `g ≫ v` is reading `α` and then pulling the
  functions back along `g`.
* `AlgebraicGeometry.Space.map_comp_chartEval`: **naturality in the chart.**  For a morphism of
  charts `k : V₁ ⟶ V₂`, restricting from `V₂` to `V₁` and reading along `v₁` is reading along
  `v₁ ≫ k`.
* `AlgebraicGeometry.Space.chartEval_algebraMap`: the reading is compatible with the structure
  maps: on the image of `𝒪_X(V) = Γ(V)` it is pullback of functions along `v`.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ChartEval

variable {X : AlgebraicSpaces B S hS}

/-- The structure morphism of `specPointOver T x` is representable, `X` being an algebraic
space. -/
theorem relativelyRepresentable_specPointOver (T : BigFppfOver B S hS) (x : X.1.obj (op T)) :
    yoneda.relativelyRepresentable (specPointOver B S hS T x).hom.hom :=
  (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X.1)).1
    X.2.diagonal_representable _

/-- **The graph of `v : T ⟶ V`** as a morphism `T ⟶ T ×_X V` into the fibre product of the point
`x` of `X` with the chart `V`, when `x` is the composite of `v` with the chart. -/
def chartGraph (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (x : X.1.obj (op T)) (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom) :
    T ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback V.obj.hom :=
  (relativelyRepresentable_specPointOver B S hS T x).lift (𝟙 _) v (by
    rw [Category.id_comp]
    exact hxv)

/-- The graph of `v` followed by the first projection `T ×_X V ⟶ T` is the identity. -/
@[reassoc (attr := simp)]
theorem chartGraph_fst (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (x : X.1.obj (op T)) (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom) :
    yoneda.map (chartGraph B S hS V v x hxv) ≫
        (relativelyRepresentable_specPointOver B S hS T x).fst V.obj.hom = 𝟙 _ :=
  Functor.relativelyRepresentable.lift_fst _ _ _ _

/-- The graph of `v` followed by the second projection `T ×_X V ⟶ V` is `v`. -/
@[reassoc (attr := simp)]
theorem chartGraph_snd (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (x : X.1.obj (op T)) (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom) :
    chartGraph B S hS V v x hxv ≫ (relativelyRepresentable_specPointOver B S hS T x).snd V.obj.hom =
      v :=
  Functor.relativelyRepresentable.lift_snd _ _ _ _

/-- Pullback of global functions along a composite of morphisms of the site, in the order the
chart readings produce it. -/
theorem appTop_map_comp_appTop_map {T₁ T₂ T₃ : BigFppfOver B S hS} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    ((BigFppfOver.toScheme B S hS).map g).appTop ≫ ((BigFppfOver.toScheme B S hS).map f).appTop =
      ((BigFppfOver.toScheme B S hS).map (f ≫ g)).appTop := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]

/-- The component of `compPushforwardAlgebraMap α f` at a chart is the component of `α` followed by
that of the map of direct images. -/
theorem compPushforwardAlgebraMap_right_app {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {P Q : Over X} (α : A ⟶ pushforwardAlgebra B S hS P) (f : Q ⟶ P)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (compPushforwardAlgebraMap B S hS α f).right.hom.app U =
      α.right.hom.app U ≫ (pushforwardRingMap B S hS f).hom.app U :=
  rfl

/-- **The sections of `x_* 𝒪_T` over a chart `V` are the regular functions on `T ×_X V`**, with
the fibre product written as the representing object `hx.pullback V` of the representable morphism
`x`. -/
def pointSectionsIso (T : BigFppfOver B S hS) (x : X.1.obj (op T)) (V : SmallEtale B S hS X.1) :
    (pushforwardAlgebra B S hS (specPointOver B S hS T x)).right.obj.obj (op V) ≅
      Γ((BigFppfOver.toScheme B S hS).obj
        ((relativelyRepresentable_specPointOver B S hS T x).pullback V.obj.hom), ⊤) :=
  pushforwardAlgebraSectionsIso B S hS (specPointOver B S hS T x)
    (relativelyRepresentable_specPointOver B S hS T x) V

/-- The map of direct images induced by `specPointOverMap g x`, read through `pointSectionsIso`, is
pullback of functions along the base-changed morphism `T' ×_X V ⟶ T ×_X V`. -/
theorem pointSectionsIso_inv_comp_pushforwardRingMap {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : X.1.obj (op T)) (V : SmallEtale B S hS X.1) :
    (pushforwardRingMap B S hS (specPointOverMap B S hS g x)).hom.app (op V) ≫
        (pointSectionsIso B S hS T' (X.1.map g.op x) V).hom =
      (pointSectionsIso B S hS T x V).hom ≫
        ((BigFppfOver.toScheme B S hS).map
          (smallBaseChangeOverMap B S hS (specPointOverMap B S hS g x)
            (relativelyRepresentable_specPointOver B S hS T' (X.1.map g.op x))
            (relativelyRepresentable_specPointOver B S hS T x) V)).appTop :=
  (Iso.inv_comp_eq _).1 (pushforwardRingMap_app_eq B S hS (specPointOverMap B S hS g x)
    (relativelyRepresentable_specPointOver B S hS T' (X.1.map g.op x))
    (relativelyRepresentable_specPointOver B S hS T x) V)

/-- `pointSectionsIso_inv_comp_pushforwardRingMap`, followed by a further morphism `h`. -/
theorem pointSectionsIso_inv_comp_pushforwardRingMap_assoc {T T' : BigFppfOver B S hS}
    (g : T' ⟶ T) (x : X.1.obj (op T)) (V : SmallEtale B S hS X.1) {Z : CommRingCat.{u}}
    (h : Γ((BigFppfOver.toScheme B S hS).obj
        ((relativelyRepresentable_specPointOver B S hS T' (X.1.map g.op x)).pullback V.obj.hom),
          ⊤) ⟶ Z) :
    (pushforwardRingMap B S hS (specPointOverMap B S hS g x)).hom.app (op V) ≫
        (pointSectionsIso B S hS T' (X.1.map g.op x) V).hom ≫ h =
      (pointSectionsIso B S hS T x V).hom ≫
        ((BigFppfOver.toScheme B S hS).map
          (smallBaseChangeOverMap B S hS (specPointOverMap B S hS g x)
            (relativelyRepresentable_specPointOver B S hS T' (X.1.map g.op x))
            (relativelyRepresentable_specPointOver B S hS T x) V)).appTop ≫ h := by
  rw [← Category.assoc, pointSectionsIso_inv_comp_pushforwardRingMap, Category.assoc]

/-- `pointSectionsIso` is natural in the chart: for `k : V₁ ⟶ V₂` the restriction of `x_* 𝒪_T` is
pullback along the base change of `k`. -/
theorem map_comp_pointSectionsIso {T : BigFppfOver B S hS} (x : X.1.obj (op T))
    {V₁ V₂ : SmallEtale B S hS X.1} (k : V₁ ⟶ V₂)
    (a : (relativelyRepresentable_specPointOver B S hS T x).pullback V₁.obj.hom ⟶
      (relativelyRepresentable_specPointOver B S hS T x).pullback V₂.obj.hom)
    (ha₁ : yoneda.map a ≫ (relativelyRepresentable_specPointOver B S hS T x).fst V₂.obj.hom =
      (relativelyRepresentable_specPointOver B S hS T x).fst V₁.obj.hom)
    (ha₂ : a ≫ (relativelyRepresentable_specPointOver B S hS T x).snd V₂.obj.hom =
      (relativelyRepresentable_specPointOver B S hS T x).snd V₁.obj.hom ≫ k.hom.left) :
    (pushforwardAlgebra B S hS (specPointOver B S hS T x)).right.obj.map k.op ≫
        (pointSectionsIso B S hS T x V₁).hom =
      (pointSectionsIso B S hS T x V₂).hom ≫ ((BigFppfOver.toScheme B S hS).map a).appTop :=
  pushforwardAlgebraSectionsIso_naturality B S hS (specPointOver B S hS T x)
    (relativelyRepresentable_specPointOver B S hS T x) k a ha₁ ha₂

/-- `map_comp_pointSectionsIso`, followed by a further morphism `h`. -/
theorem map_comp_pointSectionsIso_assoc {T : BigFppfOver B S hS} (x : X.1.obj (op T))
    {V₁ V₂ : SmallEtale B S hS X.1} (k : V₁ ⟶ V₂)
    (a : (relativelyRepresentable_specPointOver B S hS T x).pullback V₁.obj.hom ⟶
      (relativelyRepresentable_specPointOver B S hS T x).pullback V₂.obj.hom)
    (ha₁ : yoneda.map a ≫ (relativelyRepresentable_specPointOver B S hS T x).fst V₂.obj.hom =
      (relativelyRepresentable_specPointOver B S hS T x).fst V₁.obj.hom)
    (ha₂ : a ≫ (relativelyRepresentable_specPointOver B S hS T x).snd V₂.obj.hom =
      (relativelyRepresentable_specPointOver B S hS T x).snd V₁.obj.hom ≫ k.hom.left)
    {Z : CommRingCat.{u}}
    (h : Γ((BigFppfOver.toScheme B S hS).obj
        ((relativelyRepresentable_specPointOver B S hS T x).pullback V₁.obj.hom), ⊤) ⟶ Z) :
    (pushforwardAlgebra B S hS (specPointOver B S hS T x)).right.obj.map k.op ≫
        (pointSectionsIso B S hS T x V₁).hom ≫ h =
      (pointSectionsIso B S hS T x V₂).hom ≫ ((BigFppfOver.toScheme B S hS).map a).appTop ≫ h := by
  rw [← Category.assoc, map_comp_pointSectionsIso B S hS x k a ha₁ ha₂, Category.assoc]

/-- On the image of the structure sheaf, `pointSectionsIso` is pullback along the projection
`T ×_X V ⟶ V`. -/
theorem fSharp_app_comp_pointSectionsIso (T : BigFppfOver B S hS) (x : X.1.obj (op T))
    (V : SmallEtale B S hS X.1) :
    (smallEtaleRingedToposHom B S hS (specPointOver B S hS T x).hom).fSharp.hom.app (op V) ≫
        (pointSectionsIso B S hS T x V).hom =
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_specPointOver B S hS T x).snd V.obj.hom)).appTop :=
  fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS (specPointOver B S hS T x)
    (relativelyRepresentable_specPointOver B S hS T x) V

variable (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)

/-- **The reading of `α : 𝒜 ⟶ x_* 𝒪_T` at a chart `V` along `v : T ⟶ V`**: the ring map
`𝒜(V) ⟶ Γ(T, 𝒪_T)` obtained from `α` at `V`, the identification of the sections of `x_* 𝒪_T` over
`V` with the regular functions on `T ×_X V`, and pullback along the graph of `v`. -/
def chartEval (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (x : X.1.obj (op T)) (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) :
    A.right.obj.obj (op V) ⟶ Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  α.right.hom.app (op V) ≫ (pointSectionsIso B S hS T x V).hom ≫
    ((BigFppfOver.toScheme B S hS).map (chartGraph B S hS V v x hxv)).appTop

variable {A}

/-- **Naturality of the chart reading in the test object.**  Pulling `α` back along
`g : T' ⟶ T` and reading at `V` along `g ≫ v` is reading `α` along `v` and then pulling the
functions back along `g`. -/
theorem chartEval_compPushforwardAlgebraMap (V : SmallEtale B S hS X.1)
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (hxv' : yonedaEquiv.symm (X.1.map g.op x) = yoneda.map (g ≫ v) ≫ V.obj.hom)
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) :
    chartEval B S hS A V (g ≫ v) (X.1.map g.op x) hxv'
        (compPushforwardAlgebraMap B S hS α (specPointOverMap B S hS g x)) =
      chartEval B S hS A V v x hxv α ≫ ((BigFppfOver.toScheme B S hS).map g).appTop := by
  have hgr : chartGraph B S hS V (g ≫ v) (X.1.map g.op x) hxv' ≫
      smallBaseChangeOverMap B S hS (specPointOverMap B S hS g x)
        (relativelyRepresentable_specPointOver B S hS T' (X.1.map g.op x))
        (relativelyRepresentable_specPointOver B S hS T x) V =
        g ≫ chartGraph B S hS V v x hxv := by
    refine (relativelyRepresentable_specPointOver B S hS T x).hom_ext ?_ ?_
    · have hf : yoneda.map (smallBaseChangeOverMap B S hS (specPointOverMap B S hS g x)
          (relativelyRepresentable_specPointOver B S hS T' (X.1.map g.op x))
          (relativelyRepresentable_specPointOver B S hS T x) V) ≫
          (relativelyRepresentable_specPointOver B S hS T x).fst V.obj.hom =
            (relativelyRepresentable_specPointOver B S hS T' (X.1.map g.op x)).fst V.obj.hom ≫
              (specPointOverMap B S hS g x).left.hom :=
        Functor.relativelyRepresentable.lift_fst _ _ _ _
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, chartGraph_fst,
        Category.comp_id, hf, ← Category.assoc, chartGraph_fst, Category.id_comp]
      rfl
    · rw [Category.assoc, Category.assoc, chartGraph_snd, smallBaseChangeOverMap_snd,
        chartGraph_snd]
  unfold chartEval
  rw [compPushforwardAlgebraMap_right_app, Category.assoc, Category.assoc, Category.assoc,
    pointSectionsIso_inv_comp_pushforwardRingMap_assoc, appTop_map_comp_appTop_map,
    appTop_map_comp_appTop_map, hgr]

/-- **Naturality of the chart reading in the chart.**  For a morphism of charts `k : V₁ ⟶ V₂`,
restricting a section of `𝒜` from `V₂` to `V₁` and reading along `v₁` is reading along
`v₁ ≫ k`. -/
theorem map_comp_chartEval {V₁ V₂ : SmallEtale B S hS X.1} (k : V₁ ⟶ V₂)
    {T : BigFppfOver B S hS} (v₁ : T ⟶ V₁.obj.left) (x : X.1.obj (op T))
    (h₁ : yonedaEquiv.symm x = yoneda.map v₁ ≫ V₁.obj.hom)
    (h₂ : yonedaEquiv.symm x = yoneda.map (v₁ ≫ k.hom.left) ≫ V₂.obj.hom)
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) :
    A.right.obj.map k.op ≫ chartEval B S hS A V₁ v₁ x h₁ α =
      chartEval B S hS A V₂ (v₁ ≫ k.hom.left) x h₂ α := by
  have hcond : (relativelyRepresentable_specPointOver B S hS T x).fst V₁.obj.hom ≫
      (specPointOver B S hS T x).hom.hom =
      yoneda.map ((relativelyRepresentable_specPointOver B S hS T x).snd V₁.obj.hom ≫ k.hom.left) ≫
        V₂.obj.hom := by
    refine ((relativelyRepresentable_specPointOver B S hS T x).isPullback V₁.obj.hom).w.trans ?_
    rw [Functor.map_comp, Category.assoc, CostructuredArrow.w k.hom]
  have hgr : chartGraph B S hS V₁ v₁ x h₁ ≫
      (relativelyRepresentable_specPointOver B S hS T x).lift _ _ hcond =
        chartGraph B S hS V₂ (v₁ ≫ k.hom.left) x h₂ := by
    refine (relativelyRepresentable_specPointOver B S hS T x).hom_ext ?_ ?_
    · rw [Functor.map_comp, Category.assoc, Functor.relativelyRepresentable.lift_fst,
        chartGraph_fst, chartGraph_fst]
    · rw [Category.assoc, Functor.relativelyRepresentable.lift_snd, ← Category.assoc,
        chartGraph_snd, chartGraph_snd]
  unfold chartEval
  rw [← Category.assoc, α.right.hom.naturality k.op, Category.assoc,
    map_comp_pointSectionsIso_assoc B S hS x k
      ((relativelyRepresentable_specPointOver B S hS T x).lift _ _ hcond)
      (Functor.relativelyRepresentable.lift_fst _ _ _ _)
      (Functor.relativelyRepresentable.lift_snd _ _ _ _),
    appTop_map_comp_appTop_map, hgr]

/-- **The chart reading is compatible with the structure maps**: on a function `r ∈ Γ(V)`, read as
a section of `𝒪_X` over the chart `V` and mapped into `𝒜(V)`, the reading of `α` is the pullback of
`r` along `v`. -/
theorem chartEval_algebraMap (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS}
    (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x))
    (r : (structureSheaf B S hS X.1 X.2).obj.obj (op V)) :
    chartEval B S hS A V v x hxv α (A.algebraMap (op V) r) =
      ((BigFppfOver.toScheme B S hS).map v).appTop r := by
  have hα : α.right.hom.app (op V) (A.algebraMap (op V) r) =
      (smallEtaleRingedToposHom B S hS (specPointOver B S hS T x).hom).fSharp.hom.app (op V) r :=
    α.comm (op V) r
  have e : (smallEtaleRingedToposHom B S hS (specPointOver B S hS T x).hom).fSharp.hom.app (op V) ≫
      (pointSectionsIso B S hS T x V).hom ≫
      ((BigFppfOver.toScheme B S hS).map (chartGraph B S hS V v x hxv)).appTop =
        ((BigFppfOver.toScheme B S hS).map v).appTop := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => t ≫ ((BigFppfOver.toScheme B S hS).map
      (chartGraph B S hS V v x hxv)).appTop)
        (fSharp_app_comp_pointSectionsIso B S hS T x V)).trans ?_
    refine (appTop_map_comp_appTop_map B S hS _ _).trans ?_
    rw [chartGraph_snd]
  unfold chartEval
  rw [ConcreteCategory.comp_apply, hα]
  exact ConcreteCategory.congr_hom e r

end ChartEval

end AlgebraicGeometry.Space

end
