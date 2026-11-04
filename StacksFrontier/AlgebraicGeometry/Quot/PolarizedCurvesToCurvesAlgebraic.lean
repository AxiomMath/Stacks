module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSurjective
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# PolarizedCurves ⟶ Curves as a 1-morphism of algebraic stacks; surjectivity (Stacks 0DQ0)

Stacks 0DQ0 asserts that `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective as a 1-morphism of
algebraic stacks. The 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` asks for morphisms in
the universe `u` of the schemes. The categories `AlgebraicGeometry.curvesFiberedCategory` and
`AlgebraicGeometry.polarizedCurvesFiberedCategory` have morphisms in `Type (u + 1)`, so neither is
an object of it. Their hom sets are `u`-small, however, and shrinking them gives models with
`u`-small homs that are equivalent over the site. For the stack of curves that is
`AlgebraicGeometry.curvesSmall` (`StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel`). This file
builds the model `AlgebraicGeometry.polarizedCurvesSmall` of the stack of polarized curves, and
the projection `AlgebraicGeometry.polarizedCurvesSmallToCurvesSmall` between the two models.

Its main result is the surjectivity half of Stacks 0DQ0 in the form Stacks 04ZS asks for: the
map on points of the projection, read between the two algebraic stacks, is surjective. This
needs both stacks to be algebraic. That is Stacks 0D5A for `𝒞urves`, and for `PolarizedCurves`
it is Stacks 0D4X together with Stacks 0DPZ. Stacks 0DPZ is in this library
(`StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves`, registered given Stacks 0D3Z, which is the
parameter `h3Z` below); Stacks 0D4X and Stacks 0D5A are not, so both algebraicity statements are
explicit inputs, `hX` and `hY`, stated as algebraicity of the categories themselves.
The step from surjectivity on objects (Stacks 06D4) to surjectivity on points is
`AlgebraicGeometry.Stack.pointsMap_surjective_of_isSurjectiveOnObjects`. Surjectivity on
objects is `AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSquare_snd`, with its two
inputs discharged by the results of
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme` (Stacks 0ADD).

The second assertion of Stacks 0D3Z, `h3Z`, is the hypothesis of
`AlgebraicGeometry.polarizedCurvesSquare`. It is not proved in this library, so it stays a
parameter.

## The withheld registration

`isSurjective_polarizedCurvesToCurvesAlgebraic_of` carries no `stacks` attribute for tag 0DQ0, and
neither does anything else here. Two reasons.

First, the two algebraicity binders: `hX` is **Stacks 0D4X** (`PolarizedCurves` is an algebraic
stack), not yet proved here, and `hY` is **Stacks 0D5A** (`𝒞urves` is an
algebraic stack), not yet proved here. Neither exists in any form in this
library.

Second, Stacks 0DQ0 asserts that `PolarizedCurves ⟶ 𝒞urves` is smooth *and* surjective, and only
the surjectivity clause is proved here. The smooth clause is
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsSmoothLocallyPolarized`, which still rests on the
chain **Stacks 09DS** → **Stacks 0D04** → **Stacks 0DPJ** together with **Stacks 0D3D**, which
are not yet proved here. So the 0DQ0 registration is withheld for both reasons, and will go on a
covering set whose two pieces are the two clauses.

## Main definitions

* `AlgebraicGeometry.polarizedCurvesSmall`: the hom-shrunk model of `PolarizedCurves`.
* `AlgebraicGeometry.polarizedCurvesSmallToCurvesSmall`: the projection between the models.
* `AlgebraicGeometry.polarizedCurvesToCurvesAlgebraic`: given algebraicity of both stacks, the
  projection as a 1-morphism of `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Main results

* `AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSmallToCurvesSmall`: the projection
  between the models is surjective on objects (Stacks 06D4).
* `AlgebraicGeometry.isSurjective_polarizedCurvesToCurvesAlgebraic_of`: given that both stacks
  are algebraic, the projection is surjective (Stacks 04ZS).

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0DPZ](https://stacks.math.columbia.edu/tag/0DPZ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)

/-- **The projection `PolarizedCurves ⟶ 𝒞urves` is surjective on objects**, with no input beyond
the second assertion of Stacks 0D3Z. The two inputs of
`AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSquare_snd` are discharged by Stacks 0ADD:
the total space of a family of curves over a field is a scheme of dimension at most one. -/
theorem isSurjectiveOnObjects_polarizedCurvesSquare_snd_of_fiberedInGroupoids :
    Stack.IsSurjectiveOnObjects B integerBase hZ
      (polarizedCurvesFiberedCategory B hZ h3Z).val.p (curvesFiberedCategory B hZ).val.p
      (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd) :=
  isSurjectiveOnObjects_polarizedCurvesSquare_snd h3Z
    (fun K _ _ F hF => F.isRepresentable_total_of_base_eq (K := K)
      (congrArg (BigFppfOver.toScheme B integerBase hZ).obj hF))
    (fun _ _ hK F hF => CurveFamily.dimensionAtPoint_total_le_one_of_base_eq hK F hF)

/-- The morphisms between two polarized families form a `u`-small type: a morphism is determined
by its morphism of total spaces, its morphism of base schemes and its comparison of polarizations
(`AlgebraicGeometry.PolarizedFamily.Hom.ext`). -/
theorem small_polarizedFamily_hom (X Y : PolarizedFamily B) : Small.{u} (X ⟶ Y) := by
  let F : (X ⟶ Y) → Σ t : X.total ⟶ Y.total,
      (X.base ⟶ Y.base) × ((Scheme.Modules.pullback t).obj Y.lineBundle ≅ X.lineBundle) :=
    fun g => ⟨g.totalMap, g.baseMap, g.lineBundleIso⟩
  refine small_of_injective (f := F) fun g h e => ?_
  obtain ⟨gb, gt, gc, gi⟩ := g
  obtain ⟨hb, ht, hc, hi⟩ := h
  simp only [F, Sigma.mk.inj_iff] at e
  obtain ⟨rfl, e⟩ := e
  simp only [heq_eq_eq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rfl

/-- The hom sets of the stack of polarized curves are `u`-small. A morphism of the 2-fibre
product is determined by its three components: a morphism of the site, a morphism of polarized
families wrapped in `ULift`, and a morphism of families of curves. All three are `u`-small. -/
theorem locallySmall_polarizedCurves :
    LocallySmall.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj where
  hom_small P Q := by
    have : Small.{u} (P.y ⟶ Q.y) := (locallySmall_curveFamily B hZ).hom_small P.y Q.y
    let d : PolarizedFamilyUp B ⥤ PolarizedFamily B := ULiftHom.down
    have := small_polarizedFamily_hom B (d.obj P.x) (d.obj Q.x)
    have : Small.{u} (P.x ⟶ Q.x) :=
      inferInstanceAs (Small.{u} (ULift.{u + 1} (d.obj P.x ⟶ d.obj Q.x)))
    let F : (P ⟶ Q) → (P.base ⟶ Q.base) × (P.x ⟶ Q.x) × (P.y ⟶ Q.y) :=
      fun f => (f.hbase, f.a, f.b)
    exact small_of_injective (f := F) fun f g h => by
      simp only [F, Prod.mk.injEq] at h
      exact TwoFibreProductOver.Hom.ext h.1 h.2.1 h.2.2

attribute [local instance] locallySmall_polarizedCurves locallySmall_curveFamily

/-- The hom-shrunk model of the stack of polarized curves, as a category over the site. -/
def polarizedCurvesSmallBased : BasedCategory.{u, u + 1} (BigFppfOver B integerBase hZ) :=
  { obj := ShrinkHoms.{u + 1} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj
    p := ShrinkHoms.inverse (polarizedCurvesFiberedCategory B hZ h3Z).val.obj ⋙
      (polarizedCurvesFiberedCategory B hZ h3Z).val.p }

/-- The hom-shrunk model of the stack of polarized curves is equivalent over the site to the
stack of polarized curves. -/
def polarizedCurvesSmallEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (polarizedCurvesFiberedCategory B hZ h3Z).val.p
      (polarizedCurvesSmallBased B hZ h3Z).p :=
  StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u} _

/-- The hom-shrunk model of the stack of polarized curves is fibred in groupoids. -/
theorem isFiberedInGroupoids_polarizedCurvesSmall :
    (polarizedCurvesSmallBased B hZ h3Z).p.IsFiberedInGroupoids :=
  StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
    (polarizedCurvesSmallEquivalenceOver B hZ h3Z).symm
    (polarizedCurvesFiberedCategory B hZ h3Z).property

/-- **The hom-shrunk model of the stack of polarized curves**, as a category fibred in groupoids
at hom universe `u`. -/
def polarizedCurvesSmall :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  ⟨polarizedCurvesSmallBased B hZ h3Z, isFiberedInGroupoids_polarizedCurvesSmall B hZ h3Z⟩

/-- **The stack of polarized curves is algebraic exactly when its small model is.** -/
theorem isAlgebraicStack_polarizedCurvesSmall_iff :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (polarizedCurvesSmall B hZ h3Z).val ↔
      Stack.IsAlgebraicStack.{u, w} B integerBase hZ
        (polarizedCurvesFiberedCategory B hZ h3Z).val :=
  ⟨Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ
      (polarizedCurvesSmallEquivalenceOver B hZ h3Z).symm,
    Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ
      (polarizedCurvesSmallEquivalenceOver B hZ h3Z)⟩

/-- Given its algebraicity, the hom-shrunk model of the stack of polarized curves as an object of
`AlgebraicGeometry.Stack.AlgebraicStacks`. -/
def polarizedCurvesAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedCurvesFiberedCategory B hZ h3Z).val) :
    Stack.AlgebraicStacks.{u, w} B integerBase hZ :=
  ⟨polarizedCurvesSmall B hZ h3Z, (isAlgebraicStack_polarizedCurvesSmall_iff B hZ h3Z).2 h⟩

/-- The projection `PolarizedCurves ⟶ 𝒞urves` read between the two hom-shrunk models: undo the
shrinking, project, and shrink again. -/
def polarizedCurvesSmallToCurvesSmallFunctor :
    ShrinkHoms.{u + 1} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj ⥤
      ShrinkHoms.{u + 1} (CurveFamily B hZ) :=
  ShrinkHoms.inverse (polarizedCurvesFiberedCategory B hZ h3Z).val.obj ⋙
    CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd ⋙
      ShrinkHoms.functor (CurveFamily B hZ)

/-- Shrinking the hom sets of the category of families of curves and undoing it is the identity
functor. -/
theorem shrinkHoms_functor_comp_inverse_curveFamily :
    ShrinkHoms.functor (CurveFamily B hZ) ⋙ ShrinkHoms.inverse (CurveFamily B hZ) =
      𝟭 (CurveFamily B hZ) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
    simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map]
    change (equivShrink _).symm (equivShrink _ f) = _
    rw [Equiv.symm_apply_apply]
    exact (by simp : f = 𝟙 _ ≫ f ≫ 𝟙 _))

/-- The projection between the hom-shrunk models is a functor over the site. -/
theorem polarizedCurvesSmallToCurvesSmallFunctor_comp :
    polarizedCurvesSmallToCurvesSmallFunctor B hZ h3Z ⋙ (curvesSmallBased B hZ).p =
      (polarizedCurvesSmallBased B hZ h3Z).p := by
  have e : ShrinkHoms.functor (CurveFamily B hZ) ⋙ ShrinkHoms.inverse (CurveFamily B hZ) ⋙
      curvesProjectionOver B hZ = curvesProjectionOver B hZ := by
    rw [← CategoryTheory.Functor.assoc, shrinkHoms_functor_comp_inverse_curveFamily,
      CategoryTheory.Functor.id_comp]
  exact (congrArg (ShrinkHoms.inverse (polarizedCurvesFiberedCategory B hZ h3Z).val.obj ⋙
      CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd ⋙ ·) e).trans
    (congrArg (ShrinkHoms.inverse (polarizedCurvesFiberedCategory B hZ h3Z).val.obj ⋙ ·)
      (polarizedCurvesSquare B hZ h3Z).snd.hom.w)

/-- **The projection `PolarizedCurves ⟶ 𝒞urves`** between the hom-shrunk models, as a 1-morphism
of categories fibred in groupoids over the site. -/
def polarizedCurvesSmallToCurvesSmall : polarizedCurvesSmall B hZ h3Z ⟶ curvesSmall B hZ :=
  Bicategory.InducedBicategory.mkHom
    ({ toFunctor := polarizedCurvesSmallToCurvesSmallFunctor B hZ h3Z
       w := polarizedCurvesSmallToCurvesSmallFunctor_comp B hZ h3Z })

/-- **The projection between the hom-shrunk models is surjective on objects** (Stacks 06D4).
The shrinking leaves objects and the projections to the site unchanged, so this is
`AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSquare_snd_of_fiberedInGroupoids`. -/
theorem isSurjectiveOnObjects_polarizedCurvesSmallToCurvesSmall :
    Stack.IsSurjectiveOnObjects B integerBase hZ (polarizedCurvesSmallBased B hZ h3Z).p
      (curvesSmallBased B hZ).p (polarizedCurvesSmallToCurvesSmallFunctor B hZ h3Z) := by
  intro U hU y hy
  obtain ⟨V, hV, f, x, hx, α, hα⟩ :=
    isSurjectiveOnObjects_polarizedCurvesSquare_snd_of_fiberedInGroupoids B hZ h3Z U hU
      (ShrinkHoms.fromShrinkHoms y) hy
  let α₀ : ((CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd).obj x :
      CurveFamily B hZ) ⟶ ShrinkHoms.fromShrinkHoms y := α
  let α' : (polarizedCurvesSmallToCurvesSmallFunctor B hZ h3Z).obj
      (ShrinkHoms.toShrinkHoms x) ⟶ y := (ShrinkHoms.functor (CurveFamily B hZ)).map α₀
  refine ⟨V, hV, f, ShrinkHoms.toShrinkHoms x, hx, α', ?_⟩
  have hm : (curvesSmallBased B hZ).p.map α' = (curvesFiberedCategory B hZ).val.p.map α :=
    congrArg (curvesProjectionOver B hZ).map (Equiv.symm_apply_apply _ α₀)
  exact IsHomLift.of_fac' _ f α'
    (@IsHomLift.domain_eq _ _ _ _ (curvesFiberedCategory B hZ).val.p _ _ _ _ f α hα)
    (@IsHomLift.codomain_eq _ _ _ _ (curvesFiberedCategory B hZ).val.p _ _ _ _ f α hα)
    (hm.trans (@IsHomLift.fac' _ _ _ _ (curvesFiberedCategory B hZ).val.p _ _ _ _ f α hα))

/-- **The projection `PolarizedCurves ⟶ 𝒞urves` as a 1-morphism of algebraic stacks**, given
that both stacks are algebraic (Stacks 0D5A for `𝒞urves`, and Stacks 0D4X with Stacks 0DPZ for
`PolarizedCurves`). -/
def polarizedCurvesToCurvesAlgebraic
    (hX : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedCurvesFiberedCategory B hZ h3Z).val)
    (hY : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    polarizedCurvesAlgebraicStack B hZ h3Z hX ⟶ curvesAlgebraicStack B hZ hY :=
  Bicategory.InducedBicategory.mkHom (polarizedCurvesSmallToCurvesSmall B hZ h3Z)

/-- **The surjectivity half of Stacks 0DQ0, in the form of Stacks 04ZS.** Given that `𝒞urves` and
`PolarizedCurves` are algebraic stacks (`hY`, Stacks 0D5A; `hX`, Stacks 0D4X with Stacks 0DPZ),
the projection `PolarizedCurves ⟶ 𝒞urves` is surjective: its map on points is surjective. This
is surjectivity on objects
(`AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSmallToCurvesSmall`) followed by
`AlgebraicGeometry.Stack.pointsMap_surjective_of_isSurjectiveOnObjects`. -/
theorem isSurjective_polarizedCurvesToCurvesAlgebraic_of
    (hX : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedCurvesFiberedCategory B hZ h3Z).val)
    (hY : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    Stack.IsSurjective B integerBase hZ (polarizedCurvesToCurvesAlgebraic B hZ h3Z hX hY) :=
  Stack.pointsMap_surjective_of_isSurjectiveOnObjects B integerBase hZ _
    (isSurjectiveOnObjects_polarizedCurvesSmallToCurvesSmall B hZ h3Z)

end AlgebraicGeometry

end
