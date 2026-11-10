module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceChartConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PresentationOfSectionsHom
public import StacksFrontier.AlgebraicGeometry.Stacks.CartesianAffinePresentation

/-!
# The internal hom `hom(ℱ, 𝒢) = Q(𝓗om(ℱ, 𝒢))` and the restriction to an algebraic space

Let `𝒳` be an algebraic stack. Stacks 0GQN defines the quasi-coherent internal hom
`hom(ℱ, 𝒢) = Q(𝓗om_{𝒪_𝒳}(ℱ, 𝒢))`, the image under the coherator `Q` of the internal Hom of
Stacks 03EM. Here `Q` is `AlgebraicGeometry.Stack.FlatFppf.lowerShriekInverseImageCoherator`, the
functor `g_!g^{-1}` of
Stacks 0779 and 0GQK, and `𝓗om` is computed on the fppf site of `𝒳` at the universe of the
schemes (`AlgebraicGeometry.RingedSite.internalHomSheafSmall`).

For a flat 1-morphism `f : 𝒰 ⟶ 𝒳` from the algebraic stack of an algebraic space `U`, Stacks
0GQS considers `d : ℱ ↦ f^*ℱ|_{U_étale}`. This file proves the two inputs of Stacks 0GQT that
concern the objects of `𝒳`:

* every object of `𝒳` attached to an étale chart of `U` is a flat object
  (`AlgebraicGeometry.Stack.FlatFppf.flatObject_map_chartObject`), so `d` carries the counit
  `Q(K) ⟶ K` to an isomorphism for every `𝒪_𝒳`-module `K`
  (`AlgebraicGeometry.Stack.FlatFppf.isIso_spaceChartRestrictionFunctor_map_coheratorCounit`):
  this is item (7) of Stacks 0GQS, `c = d ∘ Q`, which holds here on all modules;
* the generation and relation statements over a slice at an object over an affine scheme, for a
  module cartesian between affine objects, that the comparison of internal Homs uses.

## References

* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 0GQT](https://stacks.math.columbia.edu/tag/0GQT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

section CartesianHom

universe u v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v'} [Category.{w'} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [EssentiallySmall.{u} 𝒳]

/-- Locally on a slice object `V`, every arrow of a covering sieve factors through an affine
object over `V`. -/
private theorem exists_sieve_over_factor_affine {𝒴 : Type v'} [Category.{w'} 𝒴]
    [EssentiallySmall.{u} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) {z : 𝒴}
    (V : Over z) :
    ∃ T : Sieve V, T ∈ (associatedTopology B S hS q B.topology).over z V ∧
      ∀ ⦃W : Over z⦄ (g : W ⟶ V), T.arrows g →
        ∃ (y : 𝒴) (φ : y ⟶ V.left) (e : W.left ⟶ y),
          IsAffineOver B S hS (q.obj y) ∧ g.left = e ≫ φ := by
  obtain ⟨ι, y, φ, hyaff, hcov, -⟩ := FibredSite.exists_affine_fppf_ofArrows B S hS q hq V.left
  refine ⟨(Sieve.overEquiv V).symm (Sieve.ofArrows y φ),
    GrothendieckTopology.overEquiv_symm_mem_over _ V _ hcov, fun W g hg ↦ ?_⟩
  obtain ⟨j, e, he⟩ := (Sieve.mem_ofArrows_iff y φ g.left).1 (by simpa using hg)
  exact ⟨y j, φ j, e, hyaff j, he⟩

/-- Restricting a finite combination of the restrictions of sections along `h` along `f` restricts
the coefficients along `f` and the sections along `f ≫ h`. -/
private theorem map_sum_smul_restrict {𝒴 : Type v'} [Category.{w'} 𝒴] [EssentiallySmall.{u} 𝒴]
    (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    {a b z : 𝒴} (f : a ⟶ b) (h : b ⟶ z) (k : a ⟶ z) (hk : f ≫ h = k)
    (c : M.val.obj (op z) →₀ fibredSectionRing B S hS q b) :
    letI := fibredSectionsModule hq M a
    letI := fibredSectionsModule hq M b
    M.val.map f.op (c.sum fun i r ↦ r • (show M.val.obj (op b) from M.val.map h.op i)) =
      (c.mapRange (fibredSectionRestrict f) (map_zero _)).sum fun i r ↦
        r • (show M.val.obj (op a) from M.val.map k.op i) := by
  subst hk
  exact (Stacks.SheafOfModules.FreeSheafification.map_finsupp_sum_smul M.val f.op c _).trans
    (Finset.sum_congr rfl fun i _ ↦ congrArg (_ • ·) (M.val.map_comp_apply h.op f.op i).symm)

/-- **The sections over an object over an affine scheme generate a module cartesian between
affine objects, locally on the slice.** -/
theorem hgen_over_of_isCartesianBetweenAffines
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hM : IsCartesianBetweenAffines hp M) {z : 𝒳}
    (hz : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (V : Over z) (x : (M.over z).val.obj (op V)) :
    ∃ T : Sieve V, T ∈ (associatedTopology B S hS p B.topology).over z V ∧
      ∀ ⦃W : Over z⦄ (g : W ⟶ V), T.arrows g →
        ∃ c : M.val.obj (op z) →₀
            (((ringStructureSheafCore B S hS p hp B.topology le_rfl).over z).obj.obj (op W)),
          (c.sum fun i r ↦ r • (show (M.over z).val.obj (op W) from
            (M.over z).val.map ((Over.isTerminalMkId z).from W).op i)) =
            (M.over z).val.map g.op x := by
  classical
  let := fibredSectionsModule hp M z
  obtain ⟨T, hT, hfac⟩ := exists_sieve_over_factor_affine B S hS p hp V
  refine ⟨T, hT, fun W g hg ↦ ?_⟩
  obtain ⟨y, φ, e, hyaff, he⟩ := hfac g hg
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (φ ≫ V.hom)
  let := fibredSectionsModule hp M y
  let := fibredSectionsModuleOver hp M (φ ≫ V.hom)
  have : IsScalarTower (fibredSectionRing B S hS p z) (fibredSectionRing B S hS p y)
      (M.val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨c, hc⟩ := Module.BaseChange.exists_finsupp_of_surjective_liftBaseChange
    (fibredSectionsRestrict hp M (φ ≫ V.hom)) (hM _ hz hyaff).2 (M.val.map φ.op x)
  let := fibredSectionsModule hp M W.left
  change ∃ c' : M.val.obj (op z) →₀ fibredSectionRing B S hS p W.left,
    (c'.sum fun i r ↦ r • (show M.val.obj (op W.left) from M.val.map W.hom.op i)) =
      M.val.map g.left.op x
  have hx : M.val.map g.left.op x = M.val.map e.op (M.val.map φ.op x) :=
    (M.val.congr_map_apply (congrArg Quiver.Hom.op he) x).trans
      (M.val.map_comp_apply φ.op e.op x)
  refine ⟨c.mapRange (fibredSectionRestrict e) (map_zero _),
    Eq.trans ?_ ((congrArg (fun m ↦ M.val.map e.op m) hc).trans hx.symm)⟩
  exact (map_sum_smul_restrict B S hS p hp M e (φ ≫ V.hom) W.hom
    (by rw [← Category.assoc, ← he, Over.w g]) c).symm

/-- **The relations among the sections over an object over an affine scheme generate all
relations, locally on the slice**, for a module cartesian between affine objects. -/
theorem hrel_over_of_isCartesianBetweenAffines
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hM : IsCartesianBetweenAffines hp M) {z : 𝒳}
    (hz : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (V : Over z)
    (c : M.val.obj (op z) →₀
      (((ringStructureSheafCore B S hS p hp B.topology le_rfl).over z).obj.obj (op V)))
    (hc0 : (c.sum fun i r ↦ r • (show (M.over z).val.obj (op V) from
      (M.over z).val.map ((Over.isTerminalMkId z).from V).op i)) = 0) :
    letI := fibredSectionsModule hp M z
    ∃ T : Sieve V, T ∈ (associatedTopology B S hS p B.topology).over z V ∧
      ∀ ⦃W : Over z⦄ (g : W ⟶ V), T.arrows g →
        ∃ d : Module.BaseChange.Relations (fibredSectionRing B S hS p z) (M.val.obj (op z)) →₀
            (((ringStructureSheafCore B S hS p hp B.topology le_rfl).over z).obj.obj (op W)),
          c.mapRange (((ringStructureSheafCore B S hS p hp B.topology le_rfl).over z).obj.map
            g.op).hom (map_zero _) =
          d.sum fun k r ↦ r • k.1.mapRange
            (((ringStructureSheafCore B S hS p hp B.topology le_rfl).over z).obj.map
              ((Over.isTerminalMkId z).from W).op).hom (map_zero _) := by
  classical
  let := fibredSectionsModule hp M z
  let := fibredSectionsModule hp M V.left
  change (c.sum fun i r ↦ (show fibredSectionRing B S hS p V.left from r) •
    (show M.val.obj (op V.left) from M.val.map V.hom.op i)) = 0 at hc0
  obtain ⟨T, hT, hfac⟩ := exists_sieve_over_factor_affine B S hS p hp V
  refine ⟨T, hT, fun W g hg ↦ ?_⟩
  obtain ⟨y, φ, e, hyaff, he⟩ := hfac g hg
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (φ ≫ V.hom)
  let := fibredSectionsModule hp M y
  let := fibredSectionsModuleOver hp M (φ ≫ V.hom)
  have : IsScalarTower (fibredSectionRing B S hS p z) (fibredSectionRing B S hS p y)
      (M.val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let cj : M.val.obj (op z) →₀ fibredSectionRing B S hS p (y) :=
    c.mapRange (fibredSectionRestrict φ) (map_zero _)
  have hcj : (cj.sum fun i r ↦ r • fibredSectionsRestrict hp M (φ ≫ V.hom) i) = 0 := by
    exact (map_sum_smul_restrict B S hS p hp M φ V.hom (φ ≫ V.hom) rfl c).symm.trans
      ((congrArg (fun m ↦ M.val.map φ.op m) hc0).trans (map_zero _))
  obtain ⟨d, hd⟩ := Module.BaseChange.exists_finsupp_relations_of_bijective_liftBaseChange
    (fibredSectionsRestrict hp M (φ ≫ V.hom)) (hM _ hz hyaff) cj hcj
  change ∃ d' : Module.BaseChange.Relations (fibredSectionRing B S hS p z) (M.val.obj (op z)) →₀
      fibredSectionRing B S hS p W.left,
    c.mapRange (fibredSectionRestrict g.left) (map_zero _) =
      d'.sum fun k r ↦ r • k.1.mapRange (fibredSectionRestrict W.hom) (map_zero _)
  refine ⟨d.mapRange (fibredSectionRestrict e) (map_zero _), ?_⟩
  have hcomp : c.mapRange (fibredSectionRestrict g.left) (map_zero _) =
      cj.mapRange (fibredSectionRestrict e) (map_zero _) := by
    ext i
    simp only [cj, Finsupp.mapRange_apply, he]
    exact fibredSectionRestrict_comp φ e (c i)
  rw [hcomp, hd, Finsupp.mapRange_sum_smul (fibredSectionRestrict e)]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg (_ • ·) ?_
  ext i
  simp only [Finsupp.mapRange_apply]
  change fibredSectionRestrict e (fibredSectionRestrict (φ ≫ V.hom) (k.1 i)) =
    fibredSectionRestrict W.hom (k.1 i)
  rw [← fibredSectionRestrict_comp, ← Category.assoc, ← he, Over.w g]

end CartesianHom

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w v₀ w₀

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- The internal Hom `𝓗om_{𝒪_𝒳}(ℱ, 𝒢)` of Stacks 03EM on the fppf site of `𝒳`, at the universe
of the schemes. -/
abbrev sheafHom (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :
    _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) :=
  @RingedSite.internalHomSheafSmall.{u, u, u + 1, u}
    (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)
    (essentiallySmall_obj_algebraicStack B S hS 𝒳) F G

/-- **The internal hom `hom(ℱ, 𝒢) = Q(𝓗om_{𝒪_𝒳}(ℱ, 𝒢))` of Stacks 0GQN**: the coherator of
Stacks 0778 applied to the internal Hom of Stacks 03EM. -/
def coheratorInternalHom (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :
    _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) :=
  (lowerShriekInverseImageCoherator B S hS 𝒳).obj (sheafHom B S hS 𝒳 F G)

variable (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- The object of the algebraic stack of `U` attached to an étale chart `V` of `U`. -/
abbrev chartObject (V : Space.SmallEtale B S hS U) :
    (algebraicSpaceStack.{u, w} B S hS U hU).val.val.obj :=
  (Space.restrictionFunctor B S hS U (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p
    (StacksRepresentableCFG.EquivalenceOver.refl _)).obj V

/-- The morphism of representing presheaves of the 1-morphism named by the object attached to an
étale chart `V ⟶ U` is that chart. -/
theorem representingMap_objectMorphism_chartObject (V : Space.SmallEtale B S hS U) :
    representingMap B S hS (schemeFibredCategory B S hS V.obj.left)
      (algebraicSpaceStack.{u, w} B S hS U hU).val
      (yoneda.obj V.obj.left) U (PresheafOfCategories.sliceElementsEquivalenceOver V.obj.left)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (objectMorphism B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val
        (Functor.Fiber.mk (a := chartObject.{u, w} B S hS U hU V) rfl)) = V.obj.hom := by
  apply yonedaEquiv.injective
  have : (schemeFibredCategory B S hS V.obj.left).val.p.IsFibered :=
    (schemeFibredCategory B S hS V.obj.left).2.isFibered
  have : (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p.IsFibered :=
    (algebraicSpaceStack.{u, w} B S hS U hU).val.2.isFibered
  exact (congrArg (PresheafOfCategories.discreteFiberEquiv U V.obj.left)
    ((PresheafOfCategories.isDiscrete_fiber_discreteProjection U V.obj.left).eq_of_hom
      ((Functor.TwoYoneda.liftBasedEvaluationIso
        (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p
        (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids V.obj.left
        (Functor.Fiber.mk (a := chartObject.{u, w} B S hS U hU V) rfl)).symm ≪≫
        (Functor.exists_iso_of_isoClassMk_eq
          ((Functor.isoClassMap_app_isoClassMk _ _).symm.trans
            (morphismSpaceEquiv_map.{u, u + 1} B S hS (schemeFibredCategory B S hS V.obj.left)
              (algebraicSpaceStack.{u, w} B S hS U hU).val (yoneda.obj V.obj.left) U
              (PresheafOfCategories.sliceElementsEquivalenceOver V.obj.left)
              (StacksRepresentableCFG.EquivalenceOver.refl _)
              ⟨CatFiberedInGroupoids.homFunctor (objectMorphism B S hS
                  (algebraicSpaceStack.{u, w} B S hS U hU).val
                  (Functor.Fiber.mk (a := chartObject.{u, w} B S hS U hU V) rfl)),
                CatFiberedInGroupoids.homFunctor_comp_p _⟩ V.obj.left (𝟙 _)))).some).hom)).symm

/-- The object of the algebraic stack of `U` attached to an étale chart of `U` is flat. -/
theorem flatObject_chartObject (V : Space.SmallEtale B S hS U) :
    flatObject B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val
      (chartObject.{u, w} B S hS U hU V) := by
  refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ h => Space.IsFlat B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
    (schemeStack.{u, w} B S hS V.obj.left).property
    (algebraicSpaceStack.{u, w} B S hS U hU).property
    (yoneda.obj V.obj.left) U
    (isAlgebraicSpace_yoneda B S hS V.obj.left) hU
    (PresheafOfCategories.sliceElementsEquivalenceOver V.obj.left)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _).2 ?_
  exact cast (congrArg (fun φ => Space.IsFlat B S hS φ)
    (representingMap_objectMorphism_chartObject.{u, w} B S hS U hU V).symm)
    (Space.isFlat_of_presheafEtale B S hS V.property)

/-- The image under a flat 1-morphism `f` of the object attached to an étale chart is flat. -/
theorem flatObject_map_chartObject (hf : AlgebraicStacks.IsFlat B S hS f)
    (V : Space.SmallEtale B S hS U) :
    flatObject B S hS 𝒳.val
      ((CatFiberedInGroupoids.homFunctor f.hom).obj (chartObject.{u, w} B S hS U hU V)) :=
  flatObject_map B S hS f hf ⟨_, flatObject_chartObject.{u, w} B S hS U hU V⟩

/-- The functor `d : ℱ ↦ f^*ℱ|_{U_étale}` of Stacks 0GQS on modules on the big fppf site of `𝒳`:
read a module on the étale site of `𝒳`, then restrict along `U_étale ⥤ 𝒳`. On objects it is
`AlgebraicGeometry.Stack.spaceChartRestriction`. -/
def spaceChartRestrictionFunctor :
    _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) ⥤
      Space.Modules.{u, u} B S hS U hU where
  obj M := spaceChartRestriction B S hS 𝒳 U hU f M
  map {M N} φ :=
    (Space.etaleRestrictedModuleInverseImageFunctor (U := ⟨U, hU⟩) B S hS
      (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
      (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (CatFiberedInGroupoids.homFunctor f.hom)
      (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)).map
      (⟨φ.val⟩ : FibredSite.restrictSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .etale M ⟶ FibredSite.restrictSiteModules B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .etale N)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- On sections over an étale chart `V`, the restriction `d(φ)` is `φ` on sections over the
object of `𝒳` attached to `V`. -/
theorem spaceChartRestrictionFunctor_map_val_app {M N : _root_.SheafOfModules.{u}
    (ambientRingStructureSheaf B S hS 𝒳)} (φ : M ⟶ N) (V : Space.SmallEtale B S hS U)
    (x : (spaceChartRestriction B S hS 𝒳 U hU f M).val.obj (op V)) :
    ((spaceChartRestrictionFunctor B S hS 𝒳 U hU f).map φ).val.app (op V) x =
      φ.val.app (op ((CatFiberedInGroupoids.homFunctor f.hom).obj
        (chartObject.{u, w} B S hS U hU V))) x :=
  rfl

/-- A morphism of presheaves of modules which is an isomorphism on every group of sections is an
isomorphism. -/
theorem _root_.PresheafOfModules.isIso_of_isIso_app {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{v₀}} {P Q : PresheafOfModules.{w₀} R} (φ : P ⟶ Q)
    (h : ∀ X, IsIso (φ.app X)) : IsIso φ := by
  have : φ = (PresheafOfModules.isoMk (fun X ↦ asIso (φ.app X))
      (fun _ _ g ↦ φ.naturality g)).hom := rfl
  rw [this]
  infer_instance

/-- **The restriction to `U_étale` along a flat `f` does not see the coherator.** For every
`𝒪_𝒳`-module `K`, `d` carries the counit `Q(K) ⟶ K` to an isomorphism: every object of `𝒳`
attached to an étale chart of `U` is flat, and the counit is bijective at flat objects. -/
theorem isIso_spaceChartRestrictionFunctor_map_coheratorCounit
    (hf : AlgebraicStacks.IsFlat B S hS f)
    (K : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :
    IsIso ((spaceChartRestrictionFunctor B S hS 𝒳 U hU f).map
      ((coheratorCounit B S hS 𝒳).app K)) := by
  have h : ∀ V : (Space.SmallEtale B S hS U)ᵒᵖ, IsIso
      (((spaceChartRestrictionFunctor B S hS 𝒳 U hU f).map
        ((coheratorCounit B S hS 𝒳).app K)).val.app V) := by
    intro V
    have hx := flatObject_map_chartObject B S hS 𝒳 U hU f hf V.unop
    have := Functor.map_isIso (_root_.SheafOfModules.evaluation _ (op (⟨_, hx⟩ :
      FlatFppf B S hS 𝒳))) ((moduleInverseImageU B S hS 𝒳).map
        ((coheratorCounit B S hS 𝒳).app K))
    exact (ConcreteCategory.isIso_iff_bijective _).2 (ConcreteCategory.bijective_of_isIso
      ((_root_.SheafOfModules.evaluation _ (op (⟨_, hx⟩ : FlatFppf B S hS 𝒳))).map
        ((moduleInverseImageU B S hS 𝒳).map ((coheratorCounit B S hS 𝒳).app K))))
  have : IsIso ((_root_.SheafOfModules.forget _).map
      ((spaceChartRestrictionFunctor B S hS 𝒳 U hU f).map
        ((coheratorCounit B S hS 𝒳).app K))) := PresheafOfModules.isIso_of_isIso_app _ h
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.forget _)

/-- The functor `U_étale ⥤ 𝒳` along which `d` restricts. -/
abbrev chartFunctor : Space.SmallEtale B S hS U ⥤ 𝒳.val.val.obj :=
  Space.etaleChartToFibred (U := ⟨U, hU⟩) B S hS
    (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p
    (StacksRepresentableCFG.EquivalenceOver.refl _) (CatFiberedInGroupoids.homFunctor f.hom)

/-- The structure map `𝒪_U ⟶ u^*𝒪_𝒳` of the restriction `d`, on underlying presheaves of rings. -/
def chartRingHom :
    _root_.Oforget (Space.smallEtaleRingedSite B S hS U hU).O.obj ⟶
      (chartFunctor B S hS 𝒳 U hU f).op ⋙ _root_.Oforget
        (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).O.obj :=
  (Space.etaleChartStructureHom (U := ⟨U, hU⟩) B S hS
      (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
      (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (CatFiberedInGroupoids.homFunctor f.hom)
      (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)).hom

/-- The ringed fppf site of `𝒳`. -/
abbrev fppfRingedSite : RingedSite.{u + 1, u, u} :=
  FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf

end AlgebraicGeometry.Stack.FlatFppf
