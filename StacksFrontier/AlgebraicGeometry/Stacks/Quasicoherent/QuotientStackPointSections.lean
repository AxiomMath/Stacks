module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointTransitionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PullbackTransportChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackChartExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines

/-!
# The module of sections along points on the pointwise quotient

Let `(𝒢, α)` be a quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic spaces
(Stacks 0441) and let `[U/_pR]` be its pointwise groupoid fibration: an object is a scheme `T` of
the site with a point `a ∈ U(T)`, and an arrow `(T', a') ⟶ (T, a)` is a morphism `h : T' ⟶ T`
with a point `r ∈ R(T')` from `a'` to `h^*a`. The proof of Stacks 06WT defines
`ℱ(T, a) = Γ(T, a^*𝒢)`, with restriction along `(h, r)` the pullback along `h` followed by `α`
read along `r`. This file constructs that presheaf of modules on the affine objects of `[U/_pR]`,
as a module on the chaotic affine ringed site of Stacks 0H0E.

## Main definitions

* `AlgebraicGeometry.Stack.pointSectionRestrict`: the restriction `Γ(T, a^*𝒢) ⟶ Γ(T', a'^*𝒢)`.
* `AlgebraicGeometry.Stack.pointPresheaf`: the presheaf of `𝒪`-modules `(T, a) ↦ Γ(T, a^*𝒢)` on
  the affine points.
* `AlgebraicGeometry.Stack.pointModuleSheaf`: the same as a module on the chaotic affine site.

## Main results

* `AlgebraicGeometry.Stack.pointSectionRestrict_comp`: the restriction maps compose, by the cocycle
  condition of Stacks 0441 (`AlgebraicGeometry.Space.pointTransition_comp`).
* `AlgebraicGeometry.Stack.pointSectionRestrict_id`: the restriction along an identity is the
  identity at an affine point.

## Implementation notes

The sections at `(T, a)` are the sections of `a^*𝒢` over the identity chart of `T`, where `a` is
read as a morphism of algebraic spaces from the represented space of `T`. All equations between
morphisms of modules are proved for abstract morphisms and instantiated, and every argument of
those instantiations is given explicitly.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Over a bijective algebra map `R → R'`, `m ↦ 1 ⊗ m` is injective on `R' ⊗_R M`. -/
theorem Stacks.injective_one_tmul_of_bijective {R R' M : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] (hφ : Function.Bijective (algebraMap R R')) :
    Function.Injective (fun m : M => (1 : R') ⊗ₜ[R] m) := by
  let e := RingEquiv.ofBijective (algebraMap R R') hφ
  have he : ∀ r : R, e.symm (algebraMap R R' r) = r := fun r => e.symm_apply_apply r
  let g : TensorProduct R R' M →ₗ[R] M := TensorProduct.lift
    { toFun := fun c => { toFun := fun m => e.symm c • m
                          map_add' := fun m m' => smul_add _ m m'
                          map_smul' := fun r m => by
                            simp only [RingHom.id_apply, smul_smul, mul_comm] }
      map_add' := fun c c' => by ext m; simp [add_smul]
      map_smul' := fun r c => by
        ext m
        show e.symm (r • c) • m = r • (e.symm c • m)
        rw [Algebra.smul_def, map_mul, he, smul_smul] }
  intro m m' h
  have hg := congrArg g h
  simpa [g] using hg

/-- A presheaf of modules from modules and semilinear restriction maps which are functorial on
elements. -/
def Stacks.PresheafOfModules.mkOfSemilinear {D : Type*} [Category D] {R : Dᵒᵖ ⥤ RingCat.{u}}
    (obj : ∀ X, ModuleCat.{u} (R.obj X))
    (map : ∀ {X Y : Dᵒᵖ} (f : X ⟶ Y), obj X →ₛₗ[(R.map f).hom] obj Y)
    (map_id : ∀ X (x : obj X), map (𝟙 X) x = x)
    (map_comp : ∀ {X Y Z : Dᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : obj X),
      map (f ≫ g) x = map g (map f x)) : PresheafOfModules.{u} R :=
  PresheafOfModules.mk (obj := obj)
    (map := fun f => ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _ (map f))
    (map_id := fun X => by
      ext x
      exact map_id X x)
    (map_comp := fun f g => by
      ext x
      exact map_comp f g x)

/-- The restriction maps of `Stacks.PresheafOfModules.mkOfSemilinear` are the given semilinear
maps. -/
theorem Stacks.PresheafOfModules.mkOfSemilinear_map_apply {D : Type*} [Category D]
    {R : Dᵒᵖ ⥤ RingCat.{u}} (obj : ∀ X, ModuleCat.{u} (R.obj X))
    (map : ∀ {X Y : Dᵒᵖ} (f : X ⟶ Y), obj X →ₛₗ[(R.map f).hom] obj Y)
    (map_id : ∀ X (x : obj X), map (𝟙 X) x = x)
    (map_comp : ∀ {X Y Z : Dᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : obj X),
      map (f ≫ g) x = map g (map f x)) {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : obj X) :
    (Stacks.PresheafOfModules.mkOfSemilinear obj map map_id map_comp).map f x = map f x :=
  rfl

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **Chart sections are injective over affine charts along a bijective change of rings.** -/
theorem injective_modulePullbackChartSection {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Modules.{u, u} C S hS Y.1 Y.2) (hN : N.IsQuasicoherentOnSite)
    (d : ChartDiagram C S hS X.1 Y.1 f.hom)
    (haU : IsAffine ((SmallEtale.toOver C S hS X.1 ⋙ BigFppfOver.toScheme C S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver C S hS Y.1 ⋙ BigFppfOver.toScheme C S hS).obj d.V))
    (hφ : Function.Bijective (chartDiagramRestrict C S hS f d)) :
    Function.Injective (modulePullbackChartSection C S hS f N d) := by
  let := chartDiagramAlgebra C S hS f d
  have hb := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite C S hS f N hN d
    haU haV
  have h1 := Stacks.injective_one_tmul_of_bijective (M := N.val.obj (op d.V)) hφ
  have key : ∀ m, modulePullbackChartBaseChange C S hS f N d (TensorProduct.tmul _ 1 m) =
      modulePullbackChartSection C S hS f N d m := fun m =>
    (modulePullbackChartBaseChange_tmul C S hS f N d 1 m).trans (one_smul _ _)
  intro m m' h
  exact h1 (hb.1 ((key m).trans (h.trans (key m').symm)))

/-- An isomorphism of modules is injective on sections. -/
theorem injective_val_app_of_isIso {Z : AlgebraicSpaces C S hS}
    {M₁ M₂ : Modules.{u, u} C S hS Z.1 Z.2} (φ : M₁ ⟶ M₂) (hφ : IsIso φ)
    (W : (SmallEtale C S hS Z.1)ᵒᵖ) : Function.Injective (φ.val.app W) := by
  intro x y h
  have hx : ∀ z : M₁.val.obj W, (inv φ).val.app W (φ.val.app W z) = z := fun z =>
    (comp_val_app_apply C S hS φ (inv φ) W z).symm.trans
      (congrArg (fun m : M₁ ⟶ M₁ => m.val.app W z) (IsIso.hom_inv_id φ))
  exact ((hx x).symm.trans (congrArg ((inv φ).val.app W) h)).trans (hx y)

/-- A composite `comp₃ x y z` of three isomorphisms is an isomorphism. -/
theorem _root_.CategoryTheory.isIso_comp₃ {D : Type*} [Category D] {X₁ X₂ X₃ X₄ : D}
    (x : X₁ ⟶ X₂) (y : X₂ ⟶ X₃) (z : X₃ ⟶ X₄) [IsIso x] [IsIso y] [IsIso z] :
    IsIso (comp₃ x y z) := by
  unfold comp₃
  infer_instance

/-- The reindexing `transitionReindex F α f` of an isomorphism `α` along `f` is an
isomorphism. -/
theorem isIso_transitionReindex {U V W : AlgebraicSpaces C S hS}
    (F : Modules.{u, u} C S hS U.1 U.2)
    {a b : V ⟶ U} (α : (modulePullback C S hS a).obj F ⟶ (modulePullback C S hS b).obj F)
    [IsIso α] (f : W ⟶ V) : IsIso (transitionReindex C S hS F α f) := by
  unfold transitionReindex
  infer_instance

/-- The twist `transitionTwist F α r hx hy` of an isomorphism `α` along `r` is an isomorphism. -/
theorem isIso_transitionTwist {U V W : AlgebraicSpaces C S hS} (F : Modules.{u, u} C S hS U.1 U.2)
    {a b : V ⟶ U} (α : (modulePullback C S hS a).obj F ⟶ (modulePullback C S hS b).obj F)
    [IsIso α] {x y : W ⟶ U} (r : W ⟶ V) (hx : r ≫ b = x) (hy : r ≫ a = y) :
    IsIso (transitionTwist F α r hx hy) := by
  have := isIso_transitionReindex F α r
  exact isIso_comp₃ (pullbackTransport F hy.symm) (transitionReindex C S hS F α r)
    (pullbackTransport F hx)

/-- The transition `pointTransition M f a r hs ht : f^*(a^*𝒢) ⟶ a'^*𝒢` of a quasi-coherent module
on a groupoid is an isomorphism. -/
theorem isIso_pointTransition {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
    (M : QuasicoherentModule C S hS G) {X X' : AlgebraicSpaces C S hS} (f : X' ⟶ X)
    (a : X ⟶ G.objects) {a' : X' ⟶ G.objects} (r : X' ⟶ G.arrows) (hs : r ≫ G.source = a')
    (ht : r ≫ G.target = f ≫ a) : IsIso (pointTransition M f a r hs ht) := by
  have := QuasicoherentModule.isIso_alpha M
  have := isIso_transitionTwist M.F.obj M.alpha r hs ht
  exact isIso_comp₃ ((modulePullbackCompIso C S hS f a).app M.F.obj).hom
    (transitionTwist M.F.obj M.alpha r hs ht) (𝟙 _)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- The morphism `T ⟶ U` of algebraic spaces classifying the point `a ∈ U(T)` of an object
`(T, a)` of the pointwise fibration. -/
def pointMap (X : PointwiseFibration G) :
    Space.yonedaSpace C S hS X.base ⟶ G.objects :=
  ObjectProperty.homMk (yonedaEquiv.symm X.fiber)

/-- The morphism `T' ⟶ R` of algebraic spaces classifying the point `r ∈ R(T')` of an arrow
`(h, r) : (T', a') ⟶ (T, a)` of the pointwise fibration. -/
def arrowMap {X Y : PointwiseFibration G} (m : X ⟶ Y) :
    Space.yonedaSpace C S hS X.base ⟶ G.arrows :=
  ObjectProperty.homMk (yonedaEquiv.symm (pointwiseArrow G m))

/-- The morphism of represented algebraic spaces induced by a morphism `h : T' ⟶ T` of the site. -/
def baseMap {T T' : BigFppfOver C S hS} (h : T' ⟶ T) :
    Space.yonedaSpace C S hS T' ⟶ Space.yonedaSpace C S hS T :=
  ObjectProperty.homMk (yoneda.map h)

/-- The source of the arrow `r` of `(h, r) : (T', a') ⟶ (T, a)` is `a'`. -/
theorem arrowMap_source {X Y : PointwiseFibration G} (m : X ⟶ Y) :
    arrowMap G m ≫ G.source = pointMap G X := by
  refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
  show yonedaEquiv (yonedaEquiv.symm (pointwiseArrow G m) ≫ G.source.hom) =
    yonedaEquiv (yonedaEquiv.symm X.fiber)
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (G.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _ m.fiber).2.1.trans
    (Equiv.apply_symm_apply yonedaEquiv _).symm

/-- The target of the arrow `r` of `(h, r) : (T', a') ⟶ (T, a)` is `h^*a`. -/
theorem arrowMap_target {X Y : PointwiseFibration G} (m : X ⟶ Y) :
    arrowMap G m ≫ G.target = baseMap m.base ≫ pointMap G Y := by
  refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
  show yonedaEquiv (yonedaEquiv.symm (pointwiseArrow G m) ≫ G.target.hom) =
    yonedaEquiv (yoneda.map m.base ≫ yonedaEquiv.symm Y.fiber)
  rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
  exact (G.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _ m.fiber).2.2

/-- `baseMap` preserves composition. -/
theorem baseMap_comp {T T' T'' : BigFppfOver C S hS} (h₁ : T'' ⟶ T') (h₂ : T' ⟶ T) :
    baseMap h₁ ≫ baseMap h₂ = baseMap (h₁ ≫ h₂) :=
  ObjectProperty.hom_ext _ (yoneda.map_comp h₁ h₂).symm

/-- The pair of arrows `(h₁^*r₂, r₁)` of a composite `m₁ ≫ m₂` of the pointwise fibration, as a
point of the space of composable pairs. -/
def pointwisePair {X Y Z : PointwiseFibration G} (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z) :
    (Deformation.composableArrows G.objects.obj G.arrows.obj G.source.hom G.target.hom).obj
      (op X.base) :=
  ⟨(G.arrows.obj.map m₁.base.op (pointwiseArrow G m₂), pointwiseArrow G m₁), by
    refine (NatTrans.naturality_apply G.source.hom m₁.base.op (pointwiseArrow G m₂)).trans ?_
    refine (congrArg (G.objects.obj.map m₁.base.op)
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op Y.base) _ _ m₂.fiber).2.1).trans ?_
    exact (G.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _ m₁.fiber).2.2.symm⟩

/-- The arrow of a composite `m₁ ≫ m₂` is the groupoid composition of the pair
`pointwisePair G m₁ m₂`. -/
theorem pointwiseArrow_comp {X Y Z : PointwiseFibration G} (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z) :
    pointwiseArrow G (m₁ ≫ m₂) = G.toGroupoidInFunctors.comp.app _ (pointwisePair G m₁ m₂) := by
  refine (pointwiseComp_arrow G.toGroupoidInFunctors m₁ m₂).trans ?_
  refine (Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp _ _ _ _).trans ?_
  exact congrArg (G.toGroupoidInFunctors.comp.app _) (Subtype.ext (Prod.ext
    (Deformation.evaluationMap_map_arrow G.toGroupoidInFunctors m₁.base.op m₂.fiber) rfl))

omit G in
/-- Composing the morphism from a representable classifying `x` with `φ` classifies `φ x`. -/
theorem yonedaEquiv_symm_comp' {T : BigFppfOver C S hS} {F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (x : F.obj (op T)) (φ : F ⟶ F') :
    yonedaEquiv.symm x ≫ φ = yonedaEquiv.symm (φ.app _ x) :=
  yonedaEquiv.injective (by rw [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

omit G in
/-- Precomposing the morphism classifying `x` with `yoneda.map h` classifies the restriction of
`x` along `h`. -/
theorem yoneda_map_comp_yonedaEquiv_symm {T T' : BigFppfOver C S hS}
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (h : T' ⟶ T) (x : F.obj (op T)) :
    yoneda.map h ≫ yonedaEquiv.symm x = yonedaEquiv.symm (F.map h.op x) :=
  yonedaEquiv.injective (by
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]; rfl)

/-- The map into the space of composable pairs classifying `(h₁^*r₂, r₁)`. -/
def pairMap {X Y Z : PointwiseFibration G} (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z) :
    Space.yonedaSpace C S hS X.base ⟶ AlgebraicSpaces.fiberProduct C S hS G.source G.target :=
  ObjectProperty.homMk (yonedaEquiv.symm
    ((composableToPullback G.source.hom G.target.hom).app _ (pointwisePair G m₁ m₂)))

/-- The first arrow of the pair classified by `pairMap G m₁ m₂` is `h₁^*r₂`. -/
theorem pairMap_firstArrow {X Y Z : PointwiseFibration G} (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z) :
    pairMap G m₁ m₂ ≫ GroupoidInAlgebraicSpaces.firstArrow G = baseMap m₁.base ≫ arrowMap G m₂ := by
  refine ObjectProperty.hom_ext _ ?_
  show yonedaEquiv.symm _ ≫ pullback.fst G.source.hom G.target.hom =
    yoneda.map m₁.base ≫ yonedaEquiv.symm (pointwiseArrow G m₂)
  rw [yonedaEquiv_symm_comp', yoneda_map_comp_yonedaEquiv_symm,
    pullbackFst_app_composableToPullback]
  rfl

/-- The second arrow of the pair classified by `pairMap G m₁ m₂` is `r₁`. -/
theorem pairMap_secondArrow {X Y Z : PointwiseFibration G} (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z) :
    pairMap G m₁ m₂ ≫ GroupoidInAlgebraicSpaces.secondArrow G = arrowMap G m₁ := by
  refine ObjectProperty.hom_ext _ ?_
  show yonedaEquiv.symm _ ≫ pullback.snd G.source.hom G.target.hom =
    yonedaEquiv.symm (pointwiseArrow G m₁)
  rw [yonedaEquiv_symm_comp', pullbackSnd_app_composableToPullback]
  rfl

/-- The groupoid composition of the pair classified by `pairMap G m₁ m₂` is the arrow of
`m₁ ≫ m₂`. -/
theorem pairMap_comp {X Y Z : PointwiseFibration G} (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z) :
    pairMap G m₁ m₂ ≫ G.comp = arrowMap G (m₁ ≫ m₂) := by
  refine ObjectProperty.hom_ext _ ?_
  show yonedaEquiv.symm _ ≫ G.comp.hom = yonedaEquiv.symm (pointwiseArrow G (m₁ ≫ m₂))
  exact (yonedaEquiv_symm_comp' _ _).trans
    (congrArg yonedaEquiv.symm (pointwiseArrow_comp G m₁ m₂).symm)

variable (M : Space.QuasicoherentModule C S hS G)

/-- A morphism `φ : f^*𝒩 ⟶ 𝒫` read on sections over a chart diagram `d` over `f`: a section
of `𝒩` over the chart of the target goes to its chart section, then through `φ`. -/
def chartRestrict {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Space.Modules.{u, u} C S hS Y.1 Y.2) (P : Space.Modules.{u, u} C S hS X.1 X.2)
    (φ : (Space.modulePullback C S hS f).obj N ⟶ P) (d : Space.ChartDiagram C S hS X.1 Y.1 f.hom)
    (s : N.val.obj (op d.V)) : P.val.obj (op d.U) :=
  φ.val.app (op d.U) (Space.modulePullbackChartSection C S hS f N d s)

/-- `chartRestrict` is additive. -/
theorem chartRestrict_add {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Space.Modules.{u, u} C S hS Y.1 Y.2) (P : Space.Modules.{u, u} C S hS X.1 X.2)
    (φ : (Space.modulePullback C S hS f).obj N ⟶ P) (d : Space.ChartDiagram C S hS X.1 Y.1 f.hom)
    (s t : N.val.obj (op d.V)) :
    chartRestrict f N P φ d (s + t) = chartRestrict f N P φ d s + chartRestrict f N P φ d t := by
  rw [chartRestrict, chartRestrict, chartRestrict, Space.modulePullbackChartSection_add]
  exact map_add _ _ _

/-- `chartRestrict` is semilinear along the restriction map of the chart diagram. -/
theorem chartRestrict_smul {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Space.Modules.{u, u} C S hS Y.1 Y.2) (P : Space.Modules.{u, u} C S hS X.1 X.2)
    (φ : (Space.modulePullback C S hS f).obj N ⟶ P) (d : Space.ChartDiagram C S hS X.1 Y.1 f.hom)
    (c : Space.chartRing C S hS Y.1 Y.2 d.V) (s : N.val.obj (op d.V)) :
    chartRestrict f N P φ d (c • s) =
      Space.chartDiagramRestrict C S hS f d c • chartRestrict f N P φ d s := by
  rw [chartRestrict, chartRestrict, Space.modulePullbackChartSection_smul]
  exact map_smul _ _ _

/-- **Restrictions along chart diagrams compose**, for any morphisms `φ₂ : f₂^*𝒩 ⟶ 𝒫'` and
`φ₁ : f₁^*𝒫' ⟶ 𝒫''` whose composite through the comparison of Stacks 03LU is `φ`. -/
theorem chartRestrict_comp {X X' X'' : AlgebraicSpaces C S hS} (f₁ : X'' ⟶ X') (f₂ : X' ⟶ X)
    (N : Space.Modules.{u, u} C S hS X.1 X.2) (P' : Space.Modules.{u, u} C S hS X'.1 X'.2)
    (P'' : Space.Modules.{u, u} C S hS X''.1 X''.2)
    (φ₂ : (Space.modulePullback C S hS f₂).obj N ⟶ P')
    (φ₁ : (Space.modulePullback C S hS f₁).obj P' ⟶ P'')
    (φ : (Space.modulePullback C S hS (f₁ ≫ f₂)).obj N ⟶ P'')
    (h : (Space.modulePullbackCompIso C S hS f₁ f₂).inv.app N ≫
      (Space.modulePullback C S hS f₁).map φ₂ ≫ φ₁ = φ)
    {U : Space.SmallEtale C S hS X''.1} {V : Space.SmallEtale C S hS X'.1}
    {W : Space.SmallEtale C S hS X.1}
    (a : (Space.SmallEtale.toOver C S hS X''.1).obj U ⟶ (Space.SmallEtale.toOver C S hS X'.1).obj V)
    (b : (Space.SmallEtale.toOver C S hS X'.1).obj V ⟶ (Space.SmallEtale.toOver C S hS X.1).obj W)
    (ha : U.1.hom ≫ f₁.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ f₂.hom = yoneda.map b ≫ W.1.hom) (s : N.val.obj (op W)) :
    chartRestrict f₁ P' P'' φ₁ ⟨U, V, a, ha⟩ (chartRestrict f₂ N P' φ₂ ⟨V, W, b, hb⟩ s) =
      chartRestrict (f₁ ≫ f₂) N P'' φ (Space.ChartDiagram.comp C S hS f₁ f₂ a b ha hb) s := by
  have e₁ := Space.modulePullbackChartSection_map C S hS f₁ ((Space.modulePullback C S hS f₂).obj N)
    φ₂ ⟨U, V, a, ha⟩ (Space.modulePullbackChartSection C S hS f₂ N ⟨V, W, b, hb⟩ s)
  have e₂ := Space.modulePullbackCompIso_inv_chartSection C S hS f₁ f₂ N a b ha hb s
  unfold chartRestrict
  rw [← h]
  exact (congrArg (φ₁.val.app (op U)) e₁.symm).trans
    (congrArg (fun x => φ₁.val.app (op U) (((Space.modulePullback C S hS f₁).map φ₂).val.app
      (op U) x)) e₂.symm)

/-- **Restriction along equal morphisms.** -/
theorem chartRestrict_transport {X Y : AlgebraicSpaces C S hS} {f f' : X ⟶ Y} (e : f = f')
    (N : Space.Modules.{u, u} C S hS Y.1 Y.2) (P : Space.Modules.{u, u} C S hS X.1 X.2)
    (φ : (Space.modulePullback C S hS f).obj N ⟶ P)
    (φ' : (Space.modulePullback C S hS f').obj N ⟶ P)
    (hφ : φ = Space.pullbackTransport N e ≫ φ') (d : Space.ChartDiagram C S hS X.1 Y.1 f.hom)
    (s : N.val.obj (op d.V)) :
    chartRestrict f N P φ d s = chartRestrict f' N P φ' (d.transport C S hS e) s := by
  subst e
  subst hφ
  simp only [Space.pullbackTransport, eqToIso.hom, eqToHom_refl, Category.id_comp]
  rfl

/-- A family of morphisms out of inverse images along varying morphisms, at two equal morphisms,
differs by the transport. -/
theorem family_eq_pullbackTransport_comp {X Y : AlgebraicSpaces C S hS}
    {N : Space.Modules.{u, u} C S hS Y.1 Y.2} {P : Space.Modules.{u, u} C S hS X.1 X.2}
    {p : (X ⟶ Y) → Prop} (Φ : ∀ f, p f → ((Space.modulePullback C S hS f).obj N ⟶ P))
    {f f' : X ⟶ Y} (e : f = f') (h : p f) (h' : p f') :
    Φ f h = Space.pullbackTransport N e ≫ Φ f' h' := by
  subst e
  simp [Space.pullbackTransport]

/-- Restriction along a chart diagram of affine charts, along a bijective change of rings and
through an isomorphism, is injective. -/
theorem injective_chartRestrict {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Space.Modules.{u, u} C S hS Y.1 Y.2) (P : Space.Modules.{u, u} C S hS X.1 X.2)
    (φ : (Space.modulePullback C S hS f).obj N ⟶ P) (hφ : IsIso φ)
    (d : Space.ChartDiagram C S hS X.1 Y.1 f.hom) (hN : N.IsQuasicoherentOnSite)
    (haU : IsAffine ((Space.SmallEtale.toOver C S hS X.1 ⋙ BigFppfOver.toScheme C S hS).obj d.U))
    (haV : IsAffine ((Space.SmallEtale.toOver C S hS Y.1 ⋙ BigFppfOver.toScheme C S hS).obj d.V))
    (hb : Function.Bijective (Space.chartDiagramRestrict C S hS f d)) :
    Function.Injective (chartRestrict f N P φ d) := fun _ _ h =>
  Space.injective_modulePullbackChartSection f N hN d haU haV hb
    (Space.injective_val_app_of_isIso φ hφ (op d.U) h)

/-- The sections `Γ(T, a^*𝒢)` at a point `(T, a)`. -/
abbrev pointSections (X : PointwiseFibration G) :=
  ((Space.modulePullback C S hS (pointMap G X)).obj M.F.obj).val.obj
    (op (Space.selfChart C S hS X.base))

/-- The transition `h^*(a^*𝒢) ⟶ a'^*𝒢` along an arrow `m : (T', a') ⟶ (T, a)`. -/
def pointwiseTransition {X Y : PointwiseFibration G} (m : X ⟶ Y) :
    (Space.modulePullback C S hS (baseMap m.base)).obj
        ((Space.modulePullback C S hS (pointMap G Y)).obj M.F.obj) ⟶
      (Space.modulePullback C S hS (pointMap G X)).obj M.F.obj :=
  Space.pointTransition M (baseMap m.base) (pointMap G Y) (arrowMap G m) (arrowMap_source G m)
    (arrowMap_target G m)

/-- The restriction map `Γ(T, a^*𝒢) ⟶ Γ(T', a'^*𝒢)` along an arrow `m : (T', a') ⟶ (T, a)`. -/
def pointSectionRestrict {X Y : PointwiseFibration G} (m : X ⟶ Y) :
    pointSections G M Y → pointSections G M X :=
  chartRestrict (baseMap m.base) ((Space.modulePullback C S hS (pointMap G Y)).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G X)).obj M.F.obj) (pointwiseTransition G M m)
    (Space.selfChartDiagram C S hS m.base)

/-- `pointSectionRestrict` is additive. -/
theorem pointSectionRestrict_add {X Y : PointwiseFibration G} (m : X ⟶ Y)
    (s t : pointSections G M Y) :
    pointSectionRestrict G M m (s + t) =
      pointSectionRestrict G M m s + pointSectionRestrict G M m t :=
  chartRestrict_add (baseMap m.base) ((Space.modulePullback C S hS (pointMap G Y)).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G X)).obj M.F.obj) (pointwiseTransition G M m)
    (Space.selfChartDiagram C S hS m.base) s t

/-- The module `Γ(T, a^*𝒢)` over `Γ(T, 𝒪_T)` at an affine object `(T, a)`. -/
def pointModule (x : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) :
    ModuleCat.{u} ((affineStructurePresheaf C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p).obj (op x)) :=
  ((Space.modulePullback C S hS (pointMap G x.obj)).obj M.F.obj).val.obj
    (op (Space.selfChart C S hS x.obj.base))

/-- The restriction map between the modules at two affine objects. -/
def affinePointRestrict {x y : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p} (m : x ⟶ y) :
    pointModule G M y → pointModule G M x :=
  pointSectionRestrict G M m.hom

/-- `affinePointRestrict` is semilinear along the restriction map of the structure presheaf. -/
theorem affinePointRestrict_smul {x y : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p} (m : x ⟶ y)
    (c : (affineStructurePresheaf C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p).obj (op y))
    (s : pointModule G M y) :
    affinePointRestrict G M m (c • s) =
      ((affineStructurePresheaf C S hS _).map m.op).hom c • affinePointRestrict G M m s :=
  chartRestrict_smul (baseMap m.hom.base)
    ((Space.modulePullback C S hS (pointMap G y.obj)).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G x.obj)).obj M.F.obj) (pointwiseTransition G M m.hom)
    (Space.selfChartDiagram C S hS m.hom.base) c s

/-- **Functoriality of the restriction maps.** -/
theorem pointSectionRestrict_comp {X Y Z : PointwiseFibration G} (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z)
    (s : pointSections G M Z) :
    pointSectionRestrict G M m₁ (pointSectionRestrict G M m₂ s) =
      pointSectionRestrict G M (m₁ ≫ m₂) s := by
  have ht : arrowMap G (m₁ ≫ m₂) ≫ G.target = (baseMap m₁.base ≫ baseMap m₂.base) ≫ pointMap G Z :=
    (arrowMap_target G (m₁ ≫ m₂)).trans
      (congrArg (· ≫ pointMap G Z) (baseMap_comp m₁.base m₂.base).symm)
  have hcomp := Space.pointTransition_comp M (baseMap m₁.base) (baseMap m₂.base) (pointMap G Z)
    (arrowMap G m₂) (arrowMap_source G m₂) (arrowMap_target G m₂)
    (arrowMap G m₁) (arrowMap_source G m₁) (arrowMap_target G m₁)
    (arrowMap G (m₁ ≫ m₂)) (arrowMap_source G (m₁ ≫ m₂)) ht (pairMap G m₁ m₂)
    (pairMap_firstArrow G m₁ m₂) (pairMap_secondArrow G m₁ m₂) (pairMap_comp G m₁ m₂)
  have h₁ := chartRestrict_comp (baseMap m₁.base) (baseMap m₂.base)
    ((Space.modulePullback C S hS (pointMap G Z)).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G Y)).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G X)).obj M.F.obj)
    (pointwiseTransition G M m₂) (pointwiseTransition G M m₁) _ hcomp
    (U := Space.selfChart C S hS X.base) (V := Space.selfChart C S hS Y.base)
    (W := Space.selfChart C S hS Z.base) m₁.base m₂.base
    (Space.selfChartDiagram C S hS m₁.base).comm (Space.selfChartDiagram C S hS m₂.base).comm s
  have hφ := family_eq_pullbackTransport_comp
    (p := fun f => arrowMap G (m₁ ≫ m₂) ≫ G.target = f ≫ pointMap G Z)
    (fun f h => Space.pointTransition M f (pointMap G Z) (arrowMap G (m₁ ≫ m₂))
      (arrowMap_source G (m₁ ≫ m₂)) h) (baseMap_comp m₁.base m₂.base) ht
    (arrowMap_target G (m₁ ≫ m₂))
  have h₂ := chartRestrict_transport (baseMap_comp m₁.base m₂.base)
    ((Space.modulePullback C S hS (pointMap G Z)).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G X)).obj M.F.obj) _ _ hφ
    (Space.ChartDiagram.comp C S hS (baseMap m₁.base) (baseMap m₂.base)
      (U := Space.selfChart C S hS X.base) (V := Space.selfChart C S hS Y.base)
      (W := Space.selfChart C S hS Z.base) m₁.base m₂.base
      (Space.selfChartDiagram C S hS m₁.base).comm (Space.selfChartDiagram C S hS m₂.base).comm) s
  exact h₁.trans h₂

omit G in
/-- The map on global sections induced by the identity of `T` is bijective. -/
theorem bijective_toScheme_map_id_appTop (T : BigFppfOver C S hS) :
    Function.Bijective ((BigFppfOver.toScheme C S hS).map (𝟙 T)).appTop.hom := by
  rw [CategoryTheory.Functor.map_id]
  simpa using Function.bijective_id

/-- The restriction map along an endomorphism equal to the identity is injective at an affine
point: the transition is an isomorphism and chart sections along an isomorphism of affine schemes
are injective. -/
theorem injective_pointSectionRestrict_of_eq_id {X : PointwiseFibration G} (m : X ⟶ X)
    (hm : m = 𝟙 X)
    (hX : IsAffine ((BigFppfOver.toScheme C S hS).obj X.base)) :
    Function.Injective (pointSectionRestrict G M m) := by
  have hiso : IsIso (pointwiseTransition G M m) :=
    Space.isIso_pointTransition M (baseMap m.base) (pointMap G X)
      (arrowMap G m) (arrowMap_source G m) (arrowMap_target G m)
  have hN := Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite C S hS
    (pointMap G X) M.F.obj M.F.property
  have ha : IsAffine ((Space.SmallEtale.toOver C S hS (Space.yonedaSpace C S hS X.base).1 ⋙
      BigFppfOver.toScheme C S hS).obj (Space.selfChart C S hS X.base)) := hX
  have hbase : m.base = 𝟙 X.base := by subst hm; rfl
  have hφ : Function.Bijective (Space.chartDiagramRestrict C S hS (baseMap m.base)
      (Space.selfChartDiagram C S hS m.base)) := by
    show Function.Bijective ((BigFppfOver.toScheme C S hS).map m.base).appTop.hom
    rw [hbase]
    exact bijective_toScheme_map_id_appTop _
  exact injective_chartRestrict _ _ _ _ hiso _ hN ha ha hφ

/-- **The restriction map along an identity is the identity**, at an affine point: it is
idempotent by functoriality and injective. -/
theorem pointSectionRestrict_id {X : PointwiseFibration G}
    (hX : IsAffine ((BigFppfOver.toScheme C S hS).obj X.base)) (s : pointSections G M X) :
    pointSectionRestrict G M (𝟙 X) s = s :=
  injective_pointSectionRestrict_of_eq_id G M (𝟙 X) rfl hX
    ((pointSectionRestrict_comp G M (𝟙 X) (𝟙 X) s).trans
      (congrArg (fun m => pointSectionRestrict G M m s) (Category.comp_id (𝟙 X))))

/-- The restriction map between affine points along an identity is the identity. -/
theorem affinePointRestrict_id (x : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) (s : pointModule G M x) :
    affinePointRestrict G M (𝟙 x) s = s :=
  pointSectionRestrict_id G M (X := x.obj) x.property s

/-- The restriction maps between affine points compose. -/
theorem affinePointRestrict_comp {x y z : (AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)ᵒᵖ} (f : x ⟶ y) (g : y ⟶ z)
    (s : pointModule G M x.unop) :
    affinePointRestrict G M (f ≫ g).unop s =
      affinePointRestrict G M g.unop (affinePointRestrict G M f.unop s) :=
  (pointSectionRestrict_comp G M g.unop.hom f.unop.hom s).symm

/-- The restriction map as a semilinear map. -/
def affinePointSemilinear {x y : (AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)ᵒᵖ} (f : x ⟶ y) :
    pointModule G M x.unop →ₛₗ[((affineStructurePresheaf C S hS _).map f).hom]
      pointModule G M y.unop where
  toFun := affinePointRestrict G M f.unop
  map_add' := pointSectionRestrict_add G M f.unop.hom
  map_smul' := affinePointRestrict_smul G M f.unop

/-- `affinePointSemilinear G M f` is `affinePointRestrict G M f.unop` on elements. -/
theorem affinePointSemilinear_apply {x y : (AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)ᵒᵖ} (f : x ⟶ y)
    (s : pointModule G M x.unop) :
    affinePointSemilinear G M f s = affinePointRestrict G M f.unop s :=
  rfl

/-- `affinePointSemilinear` along an identity is the identity. -/
theorem affinePointSemilinear_id (x : (AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)ᵒᵖ) (s : pointModule G M x.unop) :
    affinePointSemilinear G M (𝟙 x) s = s :=
  (affinePointSemilinear_apply G M (𝟙 x) s).trans (affinePointRestrict_id G M x.unop s)

/-- `affinePointSemilinear` preserves composition. -/
theorem affinePointSemilinear_comp {x y z : (AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)ᵒᵖ} (f : x ⟶ y) (g : y ⟶ z)
    (s : pointModule G M x.unop) :
    affinePointSemilinear G M (f ≫ g) s =
      affinePointSemilinear G M g (affinePointSemilinear G M f s) := by
  rw [affinePointSemilinear_apply G M (f ≫ g), affinePointSemilinear_apply G M g,
    affinePointSemilinear_apply G M f]
  exact affinePointRestrict_comp G M f g s

/-- **The presheaf of modules `(T, a) ↦ Γ(T, a^*𝒢)` on the affine points** of the pointwise
quotient `[U/_pR]`, with the restriction maps of the proof of Stacks 06WT. -/
def pointPresheaf : PresheafOfModules.{u} (affineStructurePresheaf C S hS (presheafOfGroupoids
    (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) :=
  Stacks.PresheafOfModules.mkOfSemilinear (fun x => pointModule G M x.unop)
    (fun f => affinePointSemilinear G M f) (affinePointSemilinear_id G M)
    (fun f g s => affinePointSemilinear_comp G M f g s)

/-- The presheaf of modules `(T, a) ↦ Γ(T, a^*𝒢)` as a module on the chaotic affine ringed site of
`[U/_pR]` of Stacks 0H0E: on the chaotic site every presheaf is a sheaf. -/
def pointModuleSheaf : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (AffineCategory.siteKindRingedSite C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).chaotic.O) :=
  ⟨pointPresheaf G M, Presheaf.isSheaf_bot _⟩

end AlgebraicGeometry.Stack

end
