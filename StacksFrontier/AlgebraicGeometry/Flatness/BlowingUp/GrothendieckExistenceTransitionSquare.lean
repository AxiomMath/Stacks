module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardSingle
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingleUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaAdjunctionUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaAlongAComposite

/-!
# The transition square of a pushed-forward system along closed immersions

Let `t : X' ⟶ X''`, `i' : X'' ⟶ X` and `i : X' ⟶ X` be closed immersions of schemes with
`t ≫ i' = i`, and let `φ : t^* F'' ≅ F'` be an isomorphism of modules. The map
`i'_* F'' ⟶ i_* F'` adjoint to `φ` (the transition of the pushed-forward system of
[Stacks, Tag 0CTD]) placed in degree zero is compared with the derived picture: under the
isomorphisms `(i_* F)[0] ≅ Ri_*(F[0])` it is `Ri'_*` of the derived unit at `F''[0]` followed by
`Rt_*` of the comparison `Lt^*(F''[0]) ⟶ (t^*F'')[0] ≅ F'[0]`, and the composition isomorphism
`Ri'_* Rt_* ≅ Ri_*`. Tensoring with `E` in `D(𝒪_X)` and applying the projection formula, this
gives the square through which the identification of the twisted pushed-forward system with the
level tower of [Stacks, Tag 0CTE] is compatible with the transitions.

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.derivedSingleTransitionOf`: the comparison
  `Lt^*(F''[0]) ⟶ F'[0]` induced by `φ`.
* `AlgebraicGeometry.GrothendieckExistence.derivedUnitSingle` and
  `AlgebraicGeometry.GrothendieckExistence.closedImmersionSingleMap`: the unit of `Lt^* ⊣ Rt_*` at
  `F''[0]` and the component of `(i_* F)[0] ≅ Ri_*(F[0])`, typed through the functors themselves.

## Main results

* `...derivedAdjunction_unit_app_single_comp_derivedSingleTransitionOf`: the derived unit at
  `F''[0]` followed by `Rt_*` of the comparison is the unit of `t^* ⊣ t_*` followed by `φ`, in
  degree zero, then `(t_* F')[0] ≅ Rt_*(F'[0])`.
* `...singleFunctor_map_pushforwardTransition_comp`: the transition square in degree zero.
* `...tensor_pushforwardTransition_comp_projectionFormula`: the same square tensored with `E`,
  through the projection formula.

## Implementation notes

The statements are in a generic context (arbitrary schemes and closed immersions); at the
situation of [Stacks, Tag 0CTC] the same unifications time out. Three spellings of `D(𝒪_X)` meet
here (the scheme spelling `X.Modules`, the ringed-space spelling of the derived pushforward and
pullback, and the ringed-site spelling of the derived tensor product). They are definitionally
equal, but unifying them under projections such as `NatTrans.app` and `Functor.obj`, or under a
composite or identity functor, unfolds the derived functors. Hence:
* the chases are carried out on atoms of one bare category (`chase_atoms`), fed with the library
  equations as they come, so that no hypothesis is retyped by a binder of the chase;
* the components of natural transformations that enter the chase are given typed names
  (`closedImmersionSingleMap`, `derivedUnitSingle`);
* the sheafification instance for enlarged coefficients is switched off, as in the files of the
  derived functors.

The declarations live at the standard model `HasDerivedCategory.standard`, the only model of the
derived pullback, pushforward and tensor product of ringed spaces, installed for each declaration
only.

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedProjectionFormula
  (unit_comp_derivedPushforward_map_derivedPullbackTensorIso)

-- Sheafification on the opens of a space is the instance of the small site here, as in the files
-- of the derived functors this is compared with; the instance for enlarged coefficients would make
-- the derived categories built from it differ by unfolding.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

universe u

namespace AlgebraicGeometry.GrothendieckExistence

/-- A reassociation, in a bare category. -/
private theorem comp_eq_of_comp_eq {𝒞 : Type*} [Category 𝒞] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ : 𝒞}
    (A : P₀ ⟶ P₁) (B : P₁ ⟶ P₂) (qa : P₂ ⟶ P₃) (qs : P₃ ⟶ P₅) (qas : P₂ ⟶ P₅) (iv : P₅ ⟶ P₆)
    (iv' : P₃ ⟶ P₄) (s : P₄ ⟶ P₆) (h₂ : qas = qa ≫ qs) (h₁ : qs ≫ iv = iv' ≫ s) :
    A ≫ B ≫ qas ≫ iv = (A ≫ B ≫ qa ≫ iv') ≫ s := by
  subst h₂
  simp [h₁]

variable {X' X'' X : Scheme.{u}} (t : X' ⟶ X'') {F'' : X''.Modules} {F' : X'.Modules}
  (φ : (Scheme.Modules.pullback t).obj F'' ≅ F')

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`Lt^*(F''[0]) ⟶ F'[0]` induced by `φ : t^* F'' ≅ F'`**: the comparison of the derived with
the ordinary pullback in degree zero, followed by `φ`. It is the body of the transition
`Ltₙ^* ℱₙ₊₁ ⟶ ℱₙ` of the level tower of [Stacks, Tag 0CTE]. -/
def derivedSingleTransitionOf :
    (derivedPullback t.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X''.Modules 0).obj F'') ⟶
      (DerivedCategory.singleFunctor X'.Modules 0).obj F' :=
  (derivedPullback t.toLRSHom.toShHom).map
      ((DerivedCategory.singleFunctorIsoCompQ X''.Modules 0).hom.app F'') ≫
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans t.toLRSHom.toShHom).app
      ((CochainComplex.singleFunctor X''.Modules 0).obj F'') ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (StacksDraft.KFlat.modulePullback t.toLRSHom.toShHom)
        (ComplexShape.up ℤ) 0).hom.app F'' ≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ.hom) ≫
    (DerivedCategory.singleFunctorIsoCompQ X'.Modules 0).inv.app F'

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `derivedSingleTransitionOf` is the comparison `Lt^*(F''[0]) ⟶ (t^*F'')[0]` followed by `φ` in
degree zero. -/
theorem derivedSingleTransitionOf_eq :
    derivedSingleTransitionOf t φ =
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackSingleComparison
          t.toLRSHom.toShHom F'' ≫
        (DerivedCategory.singleFunctor X'.Modules 0).map φ.hom := by
  unfold derivedSingleTransitionOf
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackSingleComparison
  exact comp_eq_of_comp_eq _ _ _ _ _ _ _ _ (Functor.map_comp _ _ _)
    ((DerivedCategory.singleFunctorIsoCompQ X'.Modules 0).inv.naturality φ.hom)

/-- The unit chase behind `derivedAdjunction_unit_app_single_comp_derivedSingleTransitionOf`, in
bare categories. -/
private theorem unit_chase {𝒜 𝒟 𝒟' : Type*} [Category 𝒜] [Category 𝒟] [Category 𝒟']
    (s : 𝒜 ⥤ 𝒟) (R : 𝒟' ⥤ 𝒟) {A B C : 𝒜} {L M N : 𝒟'}
    (u : s.obj A ⟶ R.obj L) (cmp : L ⟶ M) (sφ : M ⟶ N) (dst : L ⟶ N) (un : A ⟶ B) (pφ : B ⟶ C)
    (c' : s.obj B ⟶ R.obj M) (c : s.obj C ⟶ R.obj N) (he : dst = cmp ≫ sφ)
    (h₄ : u ≫ R.map cmp = s.map un ≫ c') (hn : s.map pφ ≫ c = c' ≫ R.map sφ) :
    u ≫ R.map dst = s.map (un ≫ pφ) ≫ c := by
  subst he
  rw [R.map_comp, reassoc_of% h₄, s.map_comp, Category.assoc, hn]

/-- The degree-zero transition chase behind `singleFunctor_map_pushforwardTransition_comp`, in bare
categories. -/
private theorem single_chase {𝒜 𝒟 𝒟' : Type*} [Category 𝒜] [Category 𝒟] [Category 𝒟']
    (s : 𝒜 ⥤ 𝒟) (R : 𝒟' ⥤ 𝒟) {M'' M M₁ N : 𝒜} {W V V' : 𝒟'} {T : 𝒟}
    (x : M'' ⟶ M) (y₁ : M ⟶ M₁) (y₂ : M₁ ⟶ N) (yinv : N ⟶ M) (hy : (y₁ ≫ y₂) ≫ yinv = 𝟙 M)
    (c : s.obj N ⟶ T) (c' : s.obj M ⟶ R.obj V) (c'' : s.obj M'' ⟶ R.obj W) (v : W ⟶ V)
    (w : V ⟶ V') (ud : W ⟶ V') (r : R.obj V' ⟶ T)
    (hcomp : c = s.map yinv ≫ c' ≫ R.map w ≫ r) (h₄ : ud = v ≫ w)
    (hnat : s.map x ≫ c' = c'' ≫ R.map v) :
    s.map (x ≫ y₁ ≫ y₂) ≫ c = c'' ≫ R.map ud ≫ r := by
  subst hcomp h₄
  have hy' : s.map (y₁ ≫ y₂) ≫ s.map yinv = 𝟙 _ := by rw [← s.map_comp, hy, s.map_id]
  rw [s.map_comp, Category.assoc, reassoc_of% hy', reassoc_of% hnat, R.map_comp, Category.assoc]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The unit `F''[0] ⟶ Rt_* Lt^*(F''[0])` of `Lt^* ⊣ Rt_*`, typed through `Rt_*` and `Lt^*` rather
than through the composite and identity functors. -/
def derivedUnitSingle (G : X''.Modules) :
    (DerivedCategory.singleFunctor X''.Modules 0).obj G ⟶
      (derivedPushforward t.toLRSHom.toShHom).obj
        ((derivedPullback t.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor X''.Modules 0).obj G)) :=
  (derivedAdjunction t.toLRSHom.toShHom).unit.app _

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The derived unit at `F''[0]` against `φ`, along a closed immersion.** For a closed immersion
`t` and `φ : t^* F'' ≅ F'`, the unit of `Lt^* ⊣ Rt_*` at `F''[0]` followed by `Rt_*` of
`derivedSingleTransitionOf t φ` is the unit of `t^* ⊣ t_*` at `F''` followed by `t_* φ`, placed in
degree zero, then `(t_* F')[0] ≅ Rt_*(F'[0])`. This is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_app_single_comp` and the
naturality of `closedImmersionDerivedPushforwardSingleIso`. -/
theorem derivedAdjunction_unit_app_single_comp_derivedSingleTransitionOf [IsClosedImmersion t] :
    derivedUnitSingle t F'' ≫
      (derivedPushforward t.toLRSHom.toShHom).map (derivedSingleTransitionOf t φ) =
    (DerivedCategory.singleFunctor X''.Modules 0).map
        ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F'' ≫
          (Scheme.Modules.pushforward t).map φ.hom) ≫
      (closedImmersionDerivedPushforwardSingleIso t).hom.app F' :=
  unit_chase (DerivedCategory.singleFunctor X''.Modules 0)
    (derivedPushforward t.toLRSHom.toShHom) _ _ _ _ _ _ _ _ (derivedSingleTransitionOf_eq t φ)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_app_single_comp
      t.toLRSHom.toShHom F'')
    ((closedImmersionDerivedPushforwardSingleIso t).hom.naturality φ.hom)

variable (i' : X'' ⟶ X) (i : X' ⟶ X) (h : t ≫ i' = i)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `(i_* F)[0] ⟶ Ri_*(F[0])`, the component of `closedImmersionDerivedPushforwardSingleIso` at
`F`, typed by `(i_* F)[0]` and `Ri_*(F[0])` rather than through the composite functors. -/
def closedImmersionSingleMap {Y' Y : Scheme.{u}} (j : Y' ⟶ Y) [IsClosedImmersion j]
    (G : Y'.Modules) :
    (DerivedCategory.singleFunctor Y.Modules 0).obj ((Scheme.Modules.pushforward j).obj G) ⟶
      (derivedPushforward j.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor Y'.Modules 0).obj G) :=
  (closedImmersionDerivedPushforwardSingleIso j).hom.app G

attribute [local instance 10000] HasDerivedCategory.standard in
/-- Naturality of `(i'_* -)[0] ≅ Ri'_*(-[0])` at the adjoint of `φ`. -/
private theorem single_naturality_adjoint [IsClosedImmersion i'] :
    (DerivedCategory.singleFunctor X.Modules 0).map
        ((Scheme.Modules.pushforward i').map
          ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F'' ≫
            (Scheme.Modules.pushforward t).map φ.hom)) ≫
      (closedImmersionDerivedPushforwardSingleIso i').hom.app
        ((Scheme.Modules.pushforward t).obj F') =
    (closedImmersionDerivedPushforwardSingleIso i').hom.app F'' ≫
      (derivedPushforward i'.toLRSHom.toShHom).map
        ((DerivedCategory.singleFunctor X''.Modules 0).map
          ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F'' ≫
            (Scheme.Modules.pushforward t).map φ.hom)) :=
  (closedImmersionDerivedPushforwardSingleIso i').hom.naturality _

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The transition of the pushed-forward system in degree zero, against
`(i_* F)[0] ≅ Ri_*(F[0])`.** For closed immersions `t ≫ i' = i` and `φ : t^* F'' ≅ F'`, the map
`(i'_* F'')[0] ⟶ (i_* F')[0]` adjoint to `φ`, followed by `(i_* F')[0] ≅ Ri_*(F'[0])`, is
`(i'_* F'')[0] ≅ Ri'_*(F''[0])` followed by `Ri'_*` of the derived unit at `F''[0]` and of
`Rt_*` of `derivedSingleTransitionOf t φ`, and the composition isomorphism
`Ri'_* Rt_* ≅ Ri_*`. -/
theorem singleFunctor_map_pushforwardTransition_comp [IsClosedImmersion t] [IsClosedImmersion i']
    [IsClosedImmersion i] :
    (DerivedCategory.singleFunctor X.Modules 0).map
        ((Scheme.Modules.pushforward i').map
            ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F'' ≫
              (Scheme.Modules.pushforward t).map φ.hom) ≫
          (Scheme.Modules.pushforwardComp t i').hom.app F' ≫
          (Scheme.Modules.pushforwardCongr h).hom.app F') ≫
      closedImmersionSingleMap i F' =
    closedImmersionSingleMap i' F'' ≫
      (derivedPushforward i'.toLRSHom.toShHom).map
        (derivedUnitSingle t F'' ≫
          (derivedPushforward t.toLRSHom.toShHom).map (derivedSingleTransitionOf t φ)) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          t.toLRSHom.toShHom i'.toLRSHom.toShHom ≪≫
        eqToIso (congrArg (fun h : X'.toLocallyRingedSpace.toSheafedSpace ⟶
            X.toLocallyRingedSpace.toSheafedSpace => derivedPushforward h)
          (show t.toLRSHom.toShHom ≫ i'.toLRSHom.toShHom = i.toLRSHom.toShHom from
            congrArg (fun m : X' ⟶ X => m.toLRSHom.toShHom) h))).hom.app
        ((DerivedCategory.singleFunctor X'.Modules 0).obj F') :=
  single_chase (DerivedCategory.singleFunctor X.Modules 0) (derivedPushforward i'.toLRSHom.toShHom)
    _ _ _ _ (by simp) _ _ _ _ _ _ _
    (closedImmersionDerivedPushforwardSingleIso_comp_hom_app t i' i h F')
    (derivedAdjunction_unit_app_single_comp_derivedSingleTransitionOf t φ)
    (single_naturality_adjoint t φ i')

/-- The chase behind `tensor_pushforwardTransition_comp_projectionFormula`, with every morphism an
atom of one bare category. -/
private theorem chase_atoms {𝒞 : Type*} [Category 𝒞]
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ C₁ C₂ C₃ C₄ : 𝒞}
    (Φtr : A₁ ⟶ A₂) (Φc₀ : A₂ ⟶ A₃) (π' : A₃ ⟶ A₄) (Φc₁ : A₁ ⟶ B₁) (π : B₁ ⟶ B₂)
    (M : B₂ ⟶ B₃) (r₁ : B₃ ⟶ B₄) (r₂ : B₄ ⟶ A₄) (A' : B₁ ⟶ C₁) (ΦρG : C₁ ⟶ A₃)
    (π₂ : C₁ ⟶ C₂) (Ri2π₁ : C₂ ⟶ C₃) (ρZ₂ : C₃ ⟶ C₄) (Ri1w : C₄ ⟶ A₄) (B : B₂ ⟶ C₂)
    (Ri2Rtw : C₃ ⟶ B₃) (ρZ' : B₃ ⟶ A₄)
    (S : Φtr ≫ Φc₀ = Φc₁ ≫ A' ≫ ΦρG) (E5 : π₂ ≫ Ri2π₁ ≫ ρZ₂ ≫ Ri1w = ΦρG ≫ π')
    (E3 : A' ≫ π₂ = π ≫ B) (E4 : Ri2Rtw ≫ ρZ' = ρZ₂ ≫ Ri1w)
    (hR : M = B ≫ Ri2π₁ ≫ Ri2Rtw) (hr : ρZ' = r₁ ≫ r₂) :
    Φtr ≫ (Φc₀ ≫ π') = (Φc₁ ≫ π) ≫ M ≫ r₁ ≫ r₂ := by
  subst hR hr
  simp only [Category.assoc, reassoc_of% S, ← E5, reassoc_of% E3, ← E4]

/-- The right-hand leg of the chase: the unit against the projection formula, then the projection
formula along `t` against the comparison, in bare categories. -/
private theorem chase_leg {𝒳 𝒴 𝒩 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒩]
    (Ri : 𝒴 ⥤ 𝒳) (Rt : 𝒩 ⥤ 𝒴) {A A₁ A₂ : 𝒴} {Z₀ Z₁ Z₂ Z' : 𝒩}
    (u : A ⟶ Rt.obj Z₀) (p : Z₀ ⟶ Z₁) (q : Z₁ ⟶ Z₂) (w w₅ : Z₂ ⟶ Z') (Ψu : A ⟶ A₁)
    (π₀ : A₁ ⟶ Rt.obj Z₁) (ΨRl : A₁ ⟶ A₂) (π₁ : A₂ ⟶ Rt.obj Z₂) (Ψc : A ⟶ A₂)
    (E₁ : u ≫ Rt.map p = Ψu ≫ π₀) (E₂ : ΨRl ≫ π₁ = π₀ ≫ Rt.map q) (hΨ : Ψc = Ψu ≫ ΨRl)
    (hw : w₅ = w) :
    Ri.map (u ≫ Rt.map (p ≫ q ≫ w)) = Ri.map Ψc ≫ Ri.map π₁ ≫ (Rt ⋙ Ri).map w₅ := by
  subst hw hΨ
  have : u ≫ Rt.map (p ≫ q ≫ w₅) = (Ψu ≫ ΨRl) ≫ π₁ ≫ Rt.map w₅ := by
    rw [Rt.map_comp, Rt.map_comp, reassoc_of% E₁, reassoc_of% E₂.symm, Category.assoc]
  rw [this, Functor.comp_map, Ri.map_comp, Ri.map_comp, Ri.map_comp]

/-- An isomorphism followed by `eqToIso`, read componentwise, in bare categories. -/
private theorem trans_eqToIso_hom_app {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {F G G' : 𝒞 ⥤ 𝒟}
    (α : F ≅ G) (P : G = G') (Z : 𝒞) :
    (α ≪≫ eqToIso P).hom.app Z = α.hom.app Z ≫ eqToHom (by rw [P]) := by
  subst P
  simp

/-- The component of an isomorphism followed by `eqToIso` is the component followed by `eqToIso`,
in bare categories. -/
private theorem trans_eqToIso_app {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {F G G' : 𝒞 ⥤ 𝒟}
    (α : F ≅ G) (P : G = G') (Z : 𝒞) (P' : G.obj Z = G'.obj Z) :
    (α ≪≫ eqToIso P).hom.app Z = (α.app Z ≪≫ eqToIso P').hom :=
  trans_eqToIso_hom_app α P Z

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `- ⊗^𝐋 E` preserves composition, for morphisms of `D(𝒪_X)` in the scheme spelling. -/
private theorem tensor_map_comp_app {P Q R : DerivedCategory X.Modules} (x : P ⟶ Q) (y : Q ⟶ R)
    (E : DerivedCategory X.Modules) :
    ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map (x ≫ y)).app E =
      ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map x).app E ≫
        ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map y).app E :=
  congrArg (fun f => NatTrans.app f E)
    ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map_comp x y)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The composition isomorphism `Rt_* ⋙ Ri'_* ≅ Ri_*` in the spelling of
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_comp_of_comp_eq` is the one in the
spelling of `closedImmersionDerivedPushforwardSingleIso_comp_hom_app`. -/
private theorem derivedPushforwardCompIso_eqToIso_spelling :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
        t.toLRSHom.toShHom i'.toLRSHom.toShHom ≪≫
      eqToIso (congrArg (fun h : @Quiver.Hom RingedSpace.{u, u} _
          X'.toLocallyRingedSpace.toSheafedSpace X.toLocallyRingedSpace.toSheafedSpace =>
            derivedPushforward h)
        (congrArg (fun m : X' ⟶ X => m.toLRSHom.toShHom) h))) =
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          t.toLRSHom.toShHom i'.toLRSHom.toShHom ≪≫
        eqToIso (congrArg (fun h : X'.toLocallyRingedSpace.toSheafedSpace ⟶
            X.toLocallyRingedSpace.toSheafedSpace => derivedPushforward h)
          (show t.toLRSHom.toShHom ≫ i'.toLRSHom.toShHom = i.toLRSHom.toShHom from
            congrArg (fun m : X' ⟶ X => m.toLRSHom.toShHom) h))) :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The transition square of the pushed-forward system tensored with `E`, through the projection
formula.** For closed immersions `t ≫ i' = i`, `φ : t^* F'' ≅ F'` and `E` in `D(𝒪_X)`: the map
`i'_* F'' ⊗^𝐋 E ⟶ i_* F' ⊗^𝐋 E` induced by the adjoint of `φ`, followed by
`i_* F' ⊗^𝐋 E ≅ Ri_*(F'[0]) ⊗^𝐋 E ⟶ Ri_*(F'[0] ⊗^𝐋 Li^* E)` (projection formula), is the same map
for `i'` followed by `Ri'_*` of the unit of `Lt^* ⊣ Rt_*` at `F''[0] ⊗^𝐋 Li'^* E` and of
`Rt_*` of the comparison
`Lt^*(F''[0] ⊗^𝐋 Li'^* E) ≅ Lt^*(F''[0]) ⊗^𝐋 Lt^* Li'^* E ⟶ F'[0] ⊗^𝐋 Li^* E`, and the composition
isomorphism `Ri'_* Rt_* ≅ Ri_*`.

It is `chase_sheaf` with the projection formula against the unit
(`unit_comp_derivedPushforward_map_derivedPullbackTensorIso`),
its naturality in the source and its compatibility with composition
(`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_comp_of_comp_eq`), from the
degree-zero square `singleFunctor_map_pushforwardTransition_comp`. -/
theorem tensor_pushforwardTransition_comp_projectionFormula [IsClosedImmersion t]
    [IsClosedImmersion i'] [IsClosedImmersion i] (E : DerivedCategory X.Modules)
    (σ : (derivedPullback t.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X''.Modules 0).obj F'') ⟶
      (DerivedCategory.singleFunctor X'.Modules 0).obj F')
    (hσ : σ = derivedSingleTransitionOf t φ) :
    ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map
          ((DerivedCategory.singleFunctor X.Modules 0).map
            ((Scheme.Modules.pushforward i').map
                ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F'' ≫
                  (Scheme.Modules.pushforward t).map φ.hom) ≫
              (Scheme.Modules.pushforwardComp t i').hom.app F' ≫
              (Scheme.Modules.pushforwardCongr h).hom.app F'))).app E ≫
        (((derivedTensorProductFunctor X.toRingedSpace.sheaf).map
            (closedImmersionSingleMap i F')).app E ≫
          Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap i.toLRSHom.toShHom
            ((DerivedCategory.singleFunctor X'.Modules 0).obj F') E) =
      (((derivedTensorProductFunctor X.toRingedSpace.sheaf).map
            (closedImmersionSingleMap i' F'')).app E ≫
          Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap i'.toLRSHom.toShHom
            ((DerivedCategory.singleFunctor X''.Modules 0).obj F'') E) ≫
        (derivedPushforward i'.toLRSHom.toShHom).map
          ((derivedAdjunction t.toLRSHom.toShHom).unit.app
              (((derivedTensorProductFunctor X''.toRingedSpace.sheaf).obj
                ((DerivedCategory.singleFunctor X''.Modules 0).obj F'')).obj
                  ((derivedPullback i'.toLRSHom.toShHom).obj E)) ≫
            (derivedPushforward t.toLRSHom.toShHom).map
              ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
                  t.toLRSHom.toShHom).hom.app
                  ((DerivedCategory.singleFunctor X''.Modules 0).obj F'',
                    (derivedPullback i'.toLRSHom.toShHom).obj E) ≫
                ((derivedTensorProductFunctor X'.toRingedSpace.sheaf).map σ).app
                    ((derivedPullback t.toLRSHom.toShHom).obj
                      ((derivedPullback i'.toLRSHom.toShHom).obj E)) ≫
                ((derivedTensorProductFunctor X'.toRingedSpace.sheaf).obj
                    ((DerivedCategory.singleFunctor X'.Modules 0).obj F')).map
                  ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
                      t.toLRSHom.toShHom i'.toLRSHom.toShHom).app E ≪≫
                    eqToIso (by rw [show t.toLRSHom.toShHom ≫ i'.toLRSHom.toShHom =
                        i.toLRSHom.toShHom from
                      congrArg (fun m : X' ⟶ X => m.toLRSHom.toShHom) h])).hom)) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
            t.toLRSHom.toShHom i'.toLRSHom.toShHom).hom.app
            (((derivedTensorProductFunctor X'.toRingedSpace.sheaf).obj
              ((DerivedCategory.singleFunctor X'.Modules 0).obj F')).obj
                ((derivedPullback i.toLRSHom.toShHom).obj E)) ≫
          eqToHom (by rw [show t.toLRSHom.toShHom ≫ i'.toLRSHom.toShHom = i.toLRSHom.toShHom from
            congrArg (fun m : X' ⟶ X => m.toLRSHom.toShHom) h]) := by
  subst hσ
  have hsh : t.toLRSHom.toShHom ≫ i'.toLRSHom.toShHom = i.toLRSHom.toShHom :=
    congrArg (fun m : X' ⟶ X => m.toLRSHom.toShHom) h
  have E₁ :=
    unit_comp_derivedPushforward_map_derivedPullbackTensorIso
      t.toLRSHom.toShHom ((DerivedCategory.singleFunctor X''.Modules 0).obj F'')
      ((derivedPullback i'.toLRSHom.toShHom).obj E)
  have E₂ := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left
    t.toLRSHom.toShHom (derivedSingleTransitionOf t φ) ((derivedPullback i'.toLRSHom.toShHom).obj E)
  have E₃ := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left
    i'.toLRSHom.toShHom
    (derivedUnitSingle t F'' ≫
      (derivedPushforward t.toLRSHom.toShHom).map (derivedSingleTransitionOf t φ)) E
  have E₅ := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_comp_of_comp_eq
    t.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom hsh
    ((DerivedCategory.singleFunctor X'.Modules 0).obj F') E
  have S₂ := (tensor_map_comp_app _ _ E).symm.trans
    ((congrArg (fun f => ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map f).app E)
      (singleFunctor_map_pushforwardTransition_comp t φ i' i h)).trans
      ((tensor_map_comp_app _ _ E).trans (congrArg (_ ≫ ·) (tensor_map_comp_app _ _ E))))
  have hρ := congrArg (fun ρ : derivedPushforward t.toLRSHom.toShHom ⋙
      derivedPushforward i'.toLRSHom.toShHom ≅ derivedPushforward i.toLRSHom.toShHom =>
        ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map
          (ρ.hom.app ((DerivedCategory.singleFunctor X'.Modules 0).obj F'))).app E)
    (derivedPushforwardCompIso_eqToIso_spelling t i' i h).symm
  have S₂R := S₂.trans (congrArg (_ ≫ _ ≫ ·) hρ)
  have hΨ := tensor_map_comp_app (X := X'') (derivedUnitSingle t F'')
    ((derivedPushforward t.toLRSHom.toShHom).map (derivedSingleTransitionOf t φ))
    ((derivedPullback i'.toLRSHom.toShHom).obj E)
  exact chase_atoms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S₂R E₅ E₃
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
        t.toLRSHom.toShHom i'.toLRSHom.toShHom ≪≫
      eqToIso (congrArg (fun h : @Quiver.Hom RingedSpace.{u, u} _
          X'.toLocallyRingedSpace.toSheafedSpace X.toLocallyRingedSpace.toSheafedSpace =>
            derivedPushforward h) hsh)).hom.naturality _)
    (chase_leg (derivedPushforward i'.toLRSHom.toShHom)
      (derivedPushforward t.toLRSHom.toShHom) _ _ _ _ _ _ _ _ _ _ E₁ E₂ hΨ
      (congrArg (CategoryTheory.Functor.map _) (trans_eqToIso_app _ _ _ _)))
    (trans_eqToIso_hom_app _ _ _)

end AlgebraicGeometry.GrothendieckExistence

end
