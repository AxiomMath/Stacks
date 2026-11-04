module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Comparison
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ComparisonReduction
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.DegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ExtComparisonInPositiveDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.StageDeltaFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.VertexFunctor
public import StacksFrontier.Topology.Sheaves.Limits.AbelianSystemInjective

/-!
# The comparison of Stacks 0A37 as a morphism of δ-functors on systems

Fix a cofiltered diagram `D` of spectral spaces `Xⱼ`, a cone `c₀` of spaces over it, a stage `i`
and an open `U ⊆ Xᵢ`. On the abelian category `D.AbelianSystem` of systems `(𝒜ⱼ, φₐ)` of abelian
sheaves over `D` this file builds the two sides of the comparison of Stacks 0A37 as cohomological
δ-functors and the comparison between them:

* the stage side `𝒜 ↦ colim_{B ∈ (Over i)ᵒᵖ} Hⁿ(f_B⁻¹ U, 𝒜_B)`, the colimit
  (`CategoryTheory.DeltaFunctor.colimitDelta`) of the diagram of δ-functors
  `SpectralDiagram.AbelianSystem.stageDiagram`;
* the limit side `𝒜 ↦ Hⁿ(pᵢ⁻¹ U, colimⱼ pⱼ⁻¹𝒜ⱼ)`,
  `SpectralDiagram.AbelianSystem.vertexExtDelta`;
* the comparison `SpectralDiagram.AbelianSystem.comparisonDelta`, whose components are the maps on
  cohomology induced by the legs of the cone `SpectralDiagram.AbelianSystem.vertexCone`.

All three are built on `Ext`-δ-functors: for a continuous map `f : X ⟶ Y`, opens `U ≤ f⁻¹ V` and
exact functors `ΨY`, `ΨX` from an abelian category to abelian sheaves on `Y` and on `X`, a natural
transformation `θ : f⁻¹ ∘ ΨY ⟶ ΨX` induces the morphism of δ-functors
`Stacks.Cohomology.SpectralLimit.pullbackDelta : Hⁿ(V, ΨY -) ⟶ Hⁿ(U, ΨX -)` (act by `f⁻¹` on
`Ext`, restrict to `U`, apply `θ`). Its components are the maps on cohomology prescribed by
injective resolutions
(`Stacks.Cohomology.SpectralLimit.extSpacePullbackMap_eq_spaceCohomologyMap`), which is what
makes the transition maps functorial and the legs compatible.

## Main results

* `SpectralDiagram.AbelianSystem.isLimitVertexCone`: for a limiting `c₀`, the cone over `𝒜` with
  vertex `c₀.pt` carrying `colimⱼ pⱼ⁻¹𝒜ⱼ` is a limiting cone of abelian sheafed spaces.
* `SpectralDiagram.AbelianSystem.isIso_comparisonDelta_iff`: in degree `n` at a system `𝒜`, the
  comparison is invertible exactly when the canonical presentation of the cohomology cocone of
  `𝒜` is a colimit cocone.
* `SpectralDiagram.AbelianSystem.isIso_comparisonDelta_app`: **for `c₀` limiting and `U`
  quasi-compact the comparison is invertible in every degree at every system.** Degree zero is
  abelian Stacks 0A33 on the vertex; the induction on the degree
  (`CategoryTheory.DeltaFunctor.isIso_app_of_isIso_app_zero`) uses that every system embeds into
  a stagewise injective system, on which both sides vanish in positive degree.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Cohomology.SpectralLimit

open Stacks.Cohomology.AbelianColimit Stacks.Cohomology.ExtComparison

/-- The `Ext`-side map attached to a morphism of abelian sheafed spaces satisfies
`IsCohomologyMap` for the canonical identifications with right-derived sections. -/
theorem isCohomologyMap_extSpacePullbackMap_space
    {W Z : SheafedSpace.{_, _, u} AddCommGrpCat.{u}} (g : W ⟶ Z)
    (V : Opens Z) (U : Opens W) (h : U ≤ (Opens.map g.hom.base).obj V) (p : ℕ) :
    IsCohomologyMap g.hom.base (sheafMap g) V U h p ((H'isoRightDerivedSections V p).app Z.sheaf)
        ((H'isoRightDerivedSections U p).app W.sheaf)
      (extSpacePullbackMap g.hom.base (sheafMap g) V U h p) :=
  isCohomologyMap_extSpacePullbackMap g.hom.base (sheafMap g) V U h p

/-- **The `Ext`-side map attached to a morphism of abelian sheafed spaces is the map on cohomology
prescribed by injective resolutions**, for the canonical identifications. -/
theorem extSpacePullbackMap_eq_spaceCohomologyMap
    {W Z : SheafedSpace.{_, _, u} AddCommGrpCat.{u}} (g : W ⟶ Z)
    (V : Opens Z) (U : Opens W) (h : U ≤ (Opens.map g.hom.base).obj V) (p : ℕ) :
    (extSpacePullbackMap g.hom.base (sheafMap g) V U h p :
        Sheaf.H'.{u, u, u} Z.sheaf p V ⟶ Sheaf.H'.{u, u, u} W.sheaf p U) =
      spaceCohomologyMap g V U h p ((H'isoRightDerivedSections V p).app Z.sheaf)
        ((H'isoRightDerivedSections U p).app W.sheaf) :=
  (isCohomologyMap_iff _ _ _ _ _ _ _ _ _).1 (isCohomologyMap_extSpacePullbackMap_space g V U h p)

section PullbackDelta

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {X Y : TopCat.{u}} (f : X ⟶ Y)
  (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V)
  (ΨY : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) [ΨY.Additive]
  [PreservesFiniteLimits ΨY] [PreservesFiniteColimits ΨY]
  (ΨX : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [ΨX.Additive]
  [PreservesFiniteLimits ΨX] [PreservesFiniteColimits ΨX]
  (θ : ΨY ⋙ sheafPullback f ⟶ ΨX)

/-- The morphism of δ-functors `Hⁿ(V, ΨY -) ⟶ Hⁿ(U, ΨX -)`: pull back along `f`, restrict to `U`,
and apply `θ : f⁻¹ ∘ ΨY ⟶ ΨX`. -/
def pullbackDelta :
    ModuleSheafCohomology.extDeltaFunctor ΨY (freeOfOpen V) ⟶
      ModuleSheafCohomology.extDeltaFunctor ΨX (freeOfOpen U) :=
  ModuleSheafCohomology.extMapExactHom ΨY (sheafPullback f) (freeOfOpen V) ≫
    ModuleSheafCohomology.extDeltaFunctorPrecomp (ΨY ⋙ sheafPullback f)
      (freeOfOpenPullbackMap f V U h) ≫
    ModuleSheafCohomology.extNatTransHom θ (freeOfOpen U)

/-- The components of `pullbackDelta` are the `Ext`-side maps of the adjoints of `θ`. -/
theorem pullbackDelta_app_app (n : ℕ) (A : 𝒜) :
    ((pullbackDelta f V U h ΨY ΨX θ).app n).app A =
      extSpacePullbackMap f (((Spaces.sheafAdjunction f).homEquiv _ _) (θ.app A)) V U h n := by
  rw [extSpacePullbackMap, Equiv.symm_apply_apply]
  rfl

end PullbackDelta

end Stacks.Cohomology.SpectralLimit

namespace SpectralDiagram.AbelianSystem

open Stacks.Cohomology.SpectralLimit Stacks.Cohomology.AbelianColimit
  Stacks.Cohomology.ExtComparison

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : SpectralDiagram.{u, u} J}

/-- A rearrangement of a unit followed by the image of a triple composite. -/
theorem unit_map_comp_comp {C E : Type*} [Category C] [Category E] (G : C ⥤ E) {X : E}
    {P Q Z W : C} (u : X ⟶ G.obj P) (h : P ⟶ Q) (i : Q ⟶ Z) (v : Z ⟶ W) (t : X ⟶ G.obj Q)
    (ht : u ≫ G.map h = t) : u ≫ G.map ((h ≫ i) ≫ v) = t ≫ G.map (i ≫ v) := by
  rw [← ht, Category.assoc, Functor.map_comp, Category.assoc]

section VertexCone

variable (c₀ : Cone D.F) (A : D.AbelianSystem)

/-- The space underlying the vertex of `c₀`, carrying the sheaf `colimⱼ pⱼ⁻¹𝒜ⱼ`. -/
abbrev vertexSpace : SheafedSpace.{_, _, u} AddCommGrpCat.{u} :=
  SheafedSpaceLimit.reseat (A.cone c₀) ((vertexFunctor c₀).obj A).presheaf
    ((vertexFunctor c₀).obj A).2

/-- The identification of `vertexSpace` with the vertex of the germ-model limiting cone: the
identity on spaces, and `vertexFunctorObjIsoConePtSheaf` on sheaves. -/
def vertexSpaceHom : A.vertexSpace c₀ ⟶ (A.cone c₀).pt :=
  SheafedSpaceLimit.over (A.cone c₀) ((vertexFunctor c₀).obj A).presheaf
    ((vertexFunctor c₀).obj A).2 (A.vertexFunctorObjIsoConePtSheaf c₀).inv.hom

/-- `vertexSpaceHom` is an isomorphism of abelian sheafed spaces. -/
instance : IsIso (A.vertexSpaceHom c₀) := by
  have : IsIso (A.vertexSpaceHom c₀).hom.base := show IsIso (𝟙 _) from inferInstance
  have : IsIso (A.vertexSpaceHom c₀).hom.c :=
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} c₀.pt).mapIso
      (A.vertexFunctorObjIsoConePtSheaf c₀)).isIso_inv
  have : IsIso (SheafedSpace.forgetToPresheafedSpace.map (A.vertexSpaceHom c₀)) :=
    PresheafedSpace.isIso_of_components (A.vertexSpaceHom c₀).hom
  exact SheafedSpace.fullyFaithfulForgetToPresheafedSpace.isIso_of_isIso_map _

/-- The `f`-map of the `k`-th leg of the vertex cone: the adjoint of the `k`-th colimit
inclusion `pₖ⁻¹𝒜ₖ ⟶ colimⱼ pⱼ⁻¹𝒜ⱼ`. -/
abbrev vertexLegMap (k : J) :
    A.sheaf k ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app k)).obj
      ((vertexFunctor c₀).obj A) :=
  ((Spaces.sheafAdjunction (c₀.π.app k)).homEquiv _ _) (colimit.ι (A.vertexSystem c₀) (op k))

/-- The `f`-maps of the legs of the germ-model cone, transported to `vertexSpace`, are the
adjoints of the colimit inclusions. -/
theorem pull_vertexSpaceHom (k : J) :
    SheafedSpaceLimit.pull (A.cone c₀) ((vertexFunctor c₀).obj A).presheaf
        (A.vertexFunctorObjIsoConePtSheaf c₀).inv.hom k = (A.vertexLegMap c₀ k).hom := by
  have e1 : colimit.ι (A.vertexSystem c₀) (op k) =
      ((A.vertexSystemObjIsoGermSystemObj c₀ k).hom ≫ colimit.ι (A.germSystem c₀) (op k)) ≫
        (A.vertexFunctorObjIsoConePtSheaf c₀).inv :=
    (Iso.eq_comp_inv _).2 (A.ι_comp_vertexFunctorObjIsoConePtSheaf_hom c₀ (op k))
  have e3 : A.vertexLegMap c₀ k =
      GermPullback.toPushforward (c₀.π.app k) (A.sheaf k) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app k)).map
          (colimit.ι (A.germSystem c₀) (op k) ≫ (A.vertexFunctorObjIsoConePtSheaf c₀).inv) :=
    ((Adjunction.homEquiv_unit _ _ _ _).trans (congrArg (fun z => _ ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app k)).map z) e1)).trans
      (unit_map_comp_comp _ _ _ _ _ _
        (GermPullback.unit_comp_map_abelianSheafPullbackComparison (c₀.π.app k) (A.sheaf k)))
  refine (congrArg InducedCategory.Hom.hom e3).symm ▸ ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm)

/-- The `k`-th leg of the vertex cone: the `k`-th leg of `c₀` on spaces, and `vertexLegMap` on
sheaves. -/
abbrev vertexLeg (k : J) : A.vertexSpace c₀ ⟶ A.E.obj k :=
  SheafedSpaceLimit.leg (A.cone c₀) ((vertexFunctor c₀).obj A).presheaf
    ((vertexFunctor c₀).obj A).2 k (A.vertexLegMap c₀ k).hom

/-- The legs of the vertex cone factor through the germ-model cone. -/
theorem vertexSpaceHom_comp_π (k : J) :
    A.vertexSpaceHom c₀ ≫ (A.cone c₀).π.app k = A.vertexLeg c₀ k :=
  (SheafedSpaceLimit.over_comp_π _ _ _ _ k).trans
    (congrArg (SheafedSpaceLimit.leg _ _ _ k) (A.pull_vertexSpaceHom c₀ k))

/-- **The cone over `A.E` with vertex `c₀.pt` carrying `colimⱼ pⱼ⁻¹𝒜ⱼ`**, whose legs are the
legs of `c₀` on spaces and the adjoints of the colimit inclusions on sheaves. -/
def vertexCone : Cone A.E where
  pt := A.vertexSpace c₀
  π :=
    { app := A.vertexLeg c₀
      naturality := fun j i a => (Category.id_comp _).trans
        ((A.vertexSpaceHom_comp_π c₀ i).symm.trans
          ((congrArg (A.vertexSpaceHom c₀ ≫ ·) ((A.cone c₀).w a).symm).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ A.E.map a) (A.vertexSpaceHom_comp_π c₀ j))))) }

/-- The vertex cone is a limit cone when `c₀` is. -/
def isLimitVertexCone (hc₀ : IsLimit c₀) : IsLimit (A.vertexCone c₀) :=
  IsLimit.ofIsoLimit (IsLimit.extendIso (A.vertexSpaceHom c₀) (A.isLimit c₀ hc₀))
    (Cone.ext (Iso.refl (A.vertexSpace c₀)) fun k => (A.vertexSpaceHom_comp_π c₀ k).trans
      (Category.id_comp _).symm)

end VertexCone

section StageDiagram

variable {i : J} (U : Opens (D.F.obj i))

/-- The open `f_B⁻¹ U` of the stage `B.left`, for `B : Over i`. -/
abbrev stageOpen (B : Over i) : Opens (D.F.obj B.left) := (Opens.map (D.F.map B.hom)).obj U

/-- `f_{B'}⁻¹ U ≤ f_b⁻¹ f_B⁻¹ U` for `b : B' ⟶ B` in `Over i`. -/
theorem stageOpen_le {B B' : Over i} (b : B' ⟶ B) :
    stageOpen U B' ≤ (Opens.map (D.F.map b.left)).obj (stageOpen U B) :=
  (congrArg (fun g => (Opens.map g).obj U)
    ((congrArg D.F.map (Over.w b)).symm.trans (D.F.map_comp _ _))).le

/-- The stage-side δ-functor at `B : Over i`: `𝒜 ↦ Hⁿ(f_B⁻¹ U, 𝒜_B)`. -/
abbrev stageExtDelta (B : Over i) :
    CategoryTheory.DeltaFunctor D.AbelianSystem AddCommGrpCat.{u} :=
  ModuleSheafCohomology.extDeltaFunctor (evSite D B.left) (freeOfOpen (stageOpen U B))

/-- The `f_a`-map of a system, at the site spelling of the categories of abelian sheaves. -/
abbrev pushSite (A : D.AbelianSystem) {j k : J} (a : j ⟶ k) :
    (evSite D k).obj A ⟶ (Spaces.sheafPushforward (D.F.map a)).obj ((evSite D j).obj A) :=
  A.pushSheaf a

/-- The adjoint `f_b⁻¹ 𝒜_B ⟶ 𝒜_{B'}` of the `f_b`-map of a system, natural in the system. -/
def stageTheta {B B' : Over i} (b : B' ⟶ B) :
    evSite D B.left ⋙ sheafPullback (D.F.map b.left) ⟶ evSite D B'.left where
  app A := ((Spaces.sheafAdjunction (D.F.map b.left)).homEquiv _ _).symm (A.pushSite b.left)
  naturality A A' α := by
    apply ((Spaces.sheafAdjunction (D.F.map b.left)).homEquiv _ _).injective
    rw [Functor.comp_map, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (α.push_app b.left).symm

/-- The components of `stageTheta` are the adjoints of the `f`-maps. -/
theorem stageTheta_app {B B' : Over i} (b : B' ⟶ B) (A : D.AbelianSystem) :
    (stageTheta b).app A =
      ((Spaces.sheafAdjunction (D.F.map b.left)).homEquiv _ _).symm (A.pushSite b.left) :=
  rfl

/-- The transition morphism of stage-side δ-functors along `b : B' ⟶ B` in `Over i`. -/
abbrev stageTrans {B B' : Over i} (b : B' ⟶ B) : stageExtDelta U B ⟶ stageExtDelta U B' :=
  pullbackDelta (D.F.map b.left) (stageOpen U B) (stageOpen U B') (stageOpen_le U b)
    (evSite D B.left) (evSite D B'.left) (stageTheta b)

/-- The components of the transition maps are the maps on cohomology induced by the transition
maps of the system. -/
theorem stageTrans_app_app {B B' : Over i} (b : B' ⟶ B) (n : ℕ) (A : D.AbelianSystem) :
    ((stageTrans U b).app n).app A =
      spaceCohomologyMap (A.E.map b.left) (stageOpen U B) (stageOpen U B') (stageOpen_le U b) n
        ((H'isoRightDerivedSections (stageOpen U B) n).app (A.E.obj B.left).sheaf)
        ((H'isoRightDerivedSections (stageOpen U B') n).app (A.E.obj B'.left).sheaf) := by
  refine (pullbackDelta_app_app _ _ _ _ _ _ _ n A).trans ?_
  rw [stageTheta_app, Equiv.apply_symm_apply]
  exact extSpacePullbackMap_eq_spaceCohomologyMap (A.E.map b.left) _ _ (stageOpen_le U b) n

/-- **The stage side of the comparison of Stacks 0A37, as a diagram of δ-functors on systems**:
`B ↦ (𝒜 ↦ Hⁿ(f_B⁻¹ U, 𝒜_B))` over `(Over i)ᵒᵖ`, the transition maps being the maps on
cohomology induced by the `f`-maps of the system. -/
def stageDiagram (i : J) (U : Opens (D.F.obj i)) :
    (Over i)ᵒᵖ ⥤ CategoryTheory.DeltaFunctor D.AbelianSystem AddCommGrpCat.{u} where
  obj B := stageExtDelta U B.unop
  map b := stageTrans U b.unop
  map_id B := DeltaFunctor.hom_ext fun n => NatTrans.ext (funext fun A =>
    (stageTrans_app_app U (𝟙 B.unop) n A).trans
      ((spaceCohomologyMap_congr (A.E.map_id B.unop.left) _ _ _ (le_refl _) n _ _).trans
        (spaceCohomologyMap_id _ (le_refl _) n _)))
  map_comp {X Y Z} f g := DeltaFunctor.hom_ext fun n => NatTrans.ext (funext fun A => by
    have h₃ : stageOpen U Z.unop ≤ (Opens.map (A.E.map g.unop.left ≫
        A.E.map f.unop.left).hom.base).obj (stageOpen U X.unop) := by
      rw [← A.E.map_comp]
      exact stageOpen_le U (g.unop ≫ f.unop)
    exact (stageTrans_app_app U (g.unop ≫ f.unop) n A).trans
      ((spaceCohomologyMap_congr (A.E.map_comp g.unop.left f.unop.left) _ _ _ h₃ n _ _).trans
        ((spaceCohomologyMap_comp (A.E.map g.unop.left) (A.E.map f.unop.left) _ _ _
          (stageOpen_le U f.unop) (stageOpen_le U g.unop) h₃ n _ _ _).trans
          (congrArg₂ (· ≫ ·) (stageTrans_app_app U f.unop n A).symm
            (stageTrans_app_app U g.unop n A).symm))))

end StageDiagram

section Comparison

variable (c₀ : Cone D.F) (hc₀ : IsLimit c₀) {i : J} (U : Opens (D.F.obj i))
  (hU : IsCompact (U : Set (D.F.obj i)))

/-- The vertex functor `𝒜 ↦ colimⱼ pⱼ⁻¹𝒜ⱼ`, at the site spelling of the category of abelian
sheaves on the vertex. -/
def vertexSite : D.AbelianSystem ⥤ Sheaf (Opens.grothendieckTopology c₀.pt) AddCommGrpCat.{u} :=
  vertexFunctor c₀

/-- The vertex functor is additive. -/
instance vertexSite_additive : (vertexSite c₀).Additive :=
  vertexFunctor_additive c₀

/-- The vertex functor is left exact. -/
instance vertexSite_preservesFiniteLimits : PreservesFiniteLimits (vertexSite c₀) :=
  vertexFunctor_preservesFiniteLimits c₀

/-- The vertex functor is right exact. -/
instance vertexSite_preservesFiniteColimits : PreservesFiniteColimits (vertexSite c₀) :=
  vertexFunctor_preservesFiniteColimits c₀

/-- The open `pᵢ⁻¹ U` of the vertex. -/
abbrev vertexOpen : Opens c₀.pt := (Opens.map (c₀.π.app i)).obj U

/-- `pᵢ⁻¹ U ≤ p_B⁻¹ f_B⁻¹ U` for `B : Over i`. -/
theorem vertexOpen_le (B : Over i) :
    vertexOpen c₀ U ≤ (Opens.map (c₀.π.app B.left)).obj (stageOpen U B) :=
  (congrArg (fun g => (Opens.map g).obj U) (c₀.w B.hom)).ge

/-- The limit side of the comparison of Stacks 0A37, as a δ-functor on systems:
`𝒜 ↦ Hⁿ(pᵢ⁻¹ U, colimⱼ pⱼ⁻¹𝒜ⱼ)`. -/
abbrev vertexExtDelta : CategoryTheory.DeltaFunctor D.AbelianSystem AddCommGrpCat.{u} :=
  ModuleSheafCohomology.extDeltaFunctor (vertexSite c₀) (freeOfOpen (vertexOpen c₀ U))

/-- The colimit inclusions `p_B⁻¹ 𝒜_B ⟶ colimⱼ pⱼ⁻¹𝒜ⱼ`, natural in the system. -/
def stageLegTheta (B : Over i) :
    evSite D B.left ⋙ sheafPullback (X := c₀.pt) (c₀.π.app B.left) ⟶ vertexSite c₀ where
  app A := colimit.ι (A.vertexSystem c₀) (op B.left)
  naturality _ _ α := (colimit.ι_map ((vertexSystemFunctor c₀).map α) (op B.left)).symm

/-- The components of `stageLegTheta` are the colimit inclusions. -/
theorem stageLegTheta_app (B : Over i) (A : D.AbelianSystem) :
    (stageLegTheta c₀ B).app A = colimit.ι (A.vertexSystem c₀) (op B.left) :=
  rfl

/-- The leg at `B : Over i` of the comparison: the map on cohomology induced by the `B`-th leg of
the vertex cone. -/
abbrev stageLeg (B : Over i) : stageExtDelta U B ⟶ vertexExtDelta c₀ U :=
  pullbackDelta (X := c₀.pt) (c₀.π.app B.left) (stageOpen U B) (vertexOpen c₀ U)
    (vertexOpen_le c₀ U B)
    (evSite D B.left) (vertexSite c₀) (stageLegTheta c₀ B)

/-- The components of the legs are the maps on cohomology induced by the legs of the vertex
cone. -/
theorem stageLeg_app_app (B : Over i) (n : ℕ) (A : D.AbelianSystem) :
    ((stageLeg c₀ U B).app n).app A =
      spaceCohomologyMap ((A.vertexCone c₀).π.app B.left) (stageOpen U B) (vertexOpen c₀ U)
        (vertexOpen_le c₀ U B) n
        ((H'isoRightDerivedSections (stageOpen U B) n).app (A.E.obj B.left).sheaf)
        ((H'isoRightDerivedSections (vertexOpen c₀ U) n).app (A.vertexCone c₀).pt.sheaf) := by
  refine (pullbackDelta_app_app _ _ _ _ _ _ _ n A).trans ?_
  rw [stageLegTheta_app]
  exact extSpacePullbackMap_eq_spaceCohomologyMap ((A.vertexCone c₀).π.app B.left) _ _
    (vertexOpen_le c₀ U B) n

/-- The legs are compatible with the transition maps. -/
theorem stageTrans_comp_stageLeg {B B' : Over i} (b : B' ⟶ B) :
    stageTrans U b ≫ stageLeg c₀ U B' = stageLeg c₀ U B :=
  DeltaFunctor.hom_ext fun n => NatTrans.ext (funext fun A => by
    have h₃ : vertexOpen c₀ U ≤ (Opens.map ((A.vertexCone c₀).π.app B'.left ≫
        A.E.map b.left).hom.base).obj (stageOpen U B) := by
      rw [(A.vertexCone c₀).w b.left]
      exact vertexOpen_le c₀ U B
    exact (congrArg₂ (· ≫ ·) (stageTrans_app_app U b n A) (stageLeg_app_app c₀ U B' n A)).trans
      ((spaceCohomologyMap_comp ((A.vertexCone c₀).π.app B'.left) (A.E.map b.left) _ _ _
        (stageOpen_le U b) (vertexOpen_le c₀ U B') h₃ n _ _ _).symm.trans
        ((spaceCohomologyMap_congr ((A.vertexCone c₀).w b.left) _ _ h₃ (vertexOpen_le c₀ U B)
          n _ _).trans (stageLeg_app_app c₀ U B n A).symm)))

/-- **The comparison of Stacks 0A37 as a morphism of δ-functors on systems**:
`colim_{B} Hⁿ(f_B⁻¹ U, 𝒜_B) ⟶ Hⁿ(pᵢ⁻¹ U, colimⱼ pⱼ⁻¹𝒜ⱼ)`. -/
def comparisonDelta :
    DeltaFunctor.colimitDelta (stageDiagram (D := D) i U) ⟶ vertexExtDelta c₀ U :=
  DeltaFunctor.colimitDeltaDesc (stageDiagram i U) (fun B => stageLeg c₀ U B.unop)
    fun g => stageTrans_comp_stageLeg c₀ U g.unop

/-- The canonical presentation of the cohomology cocone of a system over the vertex cone, with
the canonical identifications of cohomology with right-derived sections. -/
abbrev canonicalCocone (A : D.AbelianSystem) (n : ℕ) :
    CohomologyCocone (Over.forget i ⋙ A.E) ((A.vertexCone c₀).whisker (Over.forget i))
      (A.toSpectralAbelianSheafSystem.stageOpenCone (A.vertexCone c₀) i U) n :=
  cohomologyCocone _ _ _ n
    (fun B => (H'isoRightDerivedSections (stageOpen U B) n).app (A.E.obj B.left).sheaf)
    ((H'isoRightDerivedSections (vertexOpen c₀ U) n).app (A.vertexCone c₀).pt.sheaf)

/-- In degree `n` at a system `A`, the diagram of the stage δ-functors is the cohomology diagram
of the canonical presentation. -/
def degIso (A : D.AbelianSystem) (n : ℕ) :
    (DeltaFunctor.deg (stageDiagram (D := D) i U) n).obj A ≅
      (canonicalCocone c₀ U A n).diagram :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun b =>
    (Category.comp_id _).trans ((stageTrans_app_app U b.unop n A).trans (Category.id_comp _).symm)

/-- The cocone of the comparison of δ-functors in degree `n` at `A`, read on the canonical
presentation, is the comparison cocone of that presentation. -/
def descCoconeIso (A : D.AbelianSystem) (n : ℕ) :
    (Cocone.precompose (degIso c₀ U A n).hom).obj (canonicalCocone c₀ U A n).cocone ≅
      DeltaFunctor.descCocone (stageDiagram i U) (fun B => stageLeg c₀ U B.unop)
        (fun g => stageTrans_comp_stageLeg c₀ U g.unop) n A :=
  Cocone.ext (Iso.refl _) fun B =>
    (Category.id_comp _).trans ((Category.comp_id _).trans (stageLeg_app_app c₀ U B.unop n A).symm)

/-- In degree `n` at `A`, the comparison is invertible exactly when the canonical presentation of
the cohomology cocone of `A` is a colimit cocone. -/
theorem isIso_comparisonDelta_iff (A : D.AbelianSystem) (n : ℕ) :
    IsIso (((comparisonDelta c₀ U).app n).app A) ↔
      Nonempty (IsColimit (canonicalCocone c₀ U A n).cocone) := by
  constructor
  · intro h
    have := IsColimit.ofPointIso (colimit.isColimit ((DeltaFunctor.deg (stageDiagram i U) n).obj A))
      (t := DeltaFunctor.descCocone (stageDiagram i U) (fun B => stageLeg c₀ U B.unop)
        (fun g => stageTrans_comp_stageLeg c₀ U g.unop) n A) (i := h)
    exact ⟨(IsColimit.precomposeHomEquiv (degIso c₀ U A n) _)
      (this.ofIsoColimit (descCoconeIso c₀ U A n).symm)⟩
  · rintro ⟨hD⟩
    have hs := ((IsColimit.precomposeHomEquiv (degIso c₀ U A n) _).symm hD).ofIsoColimit
      (descCoconeIso c₀ U A n)
    have := IsColimit.hom_isIso (colimit.isColimit _) hs
      ((colimit.isColimit _).descCoconeMorphism _)
    exact (Cocone.forget _).map_isIso ((colimit.isColimit _).descCoconeMorphism _)

include hc₀ hU in
/-- **The comparison of Stacks 0A37 in every degree, for every system over `D`**, read on the
canonical presentation: the degree-zero case is abelian Stacks 0A33 on the vertex, and the
induction on the degree runs on the δ-functor structure of both sides, every system embedding into
a stagewise injective one, on which both sides vanish in positive degree. -/
theorem isIso_comparisonDelta_app (n : ℕ) (A : D.AbelianSystem) :
    IsIso (((comparisonDelta c₀ U).app n).app A) := by
  refine DeltaFunctor.isIso_app_of_isIso_app_zero (comparisonDelta c₀ U) (fun A => ?_)
    (fun A => ?_) n A
  · exact (isIso_comparisonDelta_iff c₀ U A 0).2
      (A.toSpectralAbelianSheafSystem.nonempty_isColimit_cohomologyCocone_zero (A.vertexCone c₀)
        (A.isLimitVertexCone c₀ hc₀) i U hU _)
  · obtain ⟨G, α, hα, hinj⟩ := A.exists_mono_stageInjective
    refine ⟨G, α, hα, fun m => ?_, fun m => ?_⟩
    · exact DeltaFunctor.isZero_colimitDelta_obj _ (m + 1) G fun B =>
        Stacks.Cohomology.AbelianBasis.isZero_H'_succ_of_injective (G.sheaf B.unop.left)
          (hinj _) _ m
    · exact G.toSpectralAbelianSheafSystem.isZero_H'_succ_conePoint_of_injective'
        (G.vertexCone c₀) (G.isLimitVertexCone c₀ hc₀) hinj i U hU m

end Comparison

end SpectralDiagram.AbelianSystem
