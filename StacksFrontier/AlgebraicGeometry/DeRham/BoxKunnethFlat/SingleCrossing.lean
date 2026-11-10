module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.BoxComparisonTranspose
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.Devissage
public import StacksFrontier.Topology.Sheaves.Cohomology.KunnethOnSections.CrossingNaive
public import StacksFrontier.Homology.TensorComplex.ConcentratedBifunctor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.PullbackStalkTensorComplex

/-!
# The naive crossing map against the box comparison, at single complexes

Let `a : X ⟶ S`, `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y`, `f = p ∘ a`, and
`τ_X : X ⟶ (X, a^{-1}𝒪_S)`, `τ_Y`, `τ_W` the identity-on-spaces morphisms of ringed spaces.  For
finite-order differential operator modules `𝓕`, `𝓖` placed in degrees `i` and `j`, the map
`Tot(p'^*τ_{X,*}𝓕[-i] ⊗ q'^*τ_{Y,*}𝓖[-j]) ⟶ Tot(𝓕[-i] ⊠ 𝓖[-j])` of step (5) of
[Stacks, Tag 0FLR] is the naive crossing map followed by an isomorphism.

## Main results

* `Stacks.Cohomology.KunnethNaive.naiveCrossingLeg_f`: the degreewise crossing leg in one degree.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.DeRhamDirectImage
open scoped CategoryTheory.Prod

universe u

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf

namespace Stacks.Cohomology.KunnethNaive

section Generic

variable {X X' Y Y' W W' : RingedSpace.{u, u}} (τX : X ⟶ X') (τW : W ⟶ W') (p : W ⟶ X)
    (p' : W' ⟶ X')
  (hpsq : τW ≫ p' = p ≫ τX)
  (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)

/-- **The degreewise crossing leg in one degree**: the composition isomorphism for `(τ_W, p')`,
the transport along `τ_W ≫ p' = p ≫ τ_X`, the inverse composition isomorphism for `(p, τ_X)`
and `p^*` of the counit of `τ_X^* ⊣ τ_{X,*}`. -/
theorem naiveCrossingLeg_f (n : ℤ) :
    (naiveCrossingLeg τX τW p p' hpsq K).f n =
      (Stacks.DerivedPullback.Composition.modulePullbackComp τW p').hom.app
          ((StacksDraft.KFlat.modulePushforward τX).obj (K.X n)) ≫
        eqToHom (congrArg (fun g => (StacksDraft.KFlat.modulePullback g).obj
          ((StacksDraft.KFlat.modulePushforward τX).obj (K.X n))) hpsq) ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp p τX).inv.app
          ((StacksDraft.KFlat.modulePushforward τX).obj (K.X n)) ≫
        (StacksDraft.KFlat.modulePullback p).map
          ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction τX).counit.app
            (K.X n)) := by
  exact congrArg (fun t => _ ≫ t ≫ _) (HomologicalComplex.eqToHom_f _ n)

/-- The chase behind `ι_naiveCrossing_f`, every object and morphism a variable. -/
private theorem chase_ι {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {x x' : C} {w₁ w₂ w₃ y : D} (ι₀ : x ⟶ x') (pt : L.obj x' ⟶ w₂)
    (tt : w₂ ⟶ y) (cm : L.obj x ⟶ w₁) (ι₁ : w₁ ⟶ w₂) (lg : w₁ ⟶ w₃) (ι₂ : w₃ ⟶ y)
    (h1 : L.map ι₀ ≫ pt = cm ≫ ι₁) (h2 : ι₁ ≫ tt = lg ≫ ι₂) :
    ι₀ ≫ adj.homEquiv _ _ (pt ≫ tt) = adj.homEquiv _ _ (cm ≫ lg) ≫ R.map ι₂ := by
  rw [← adj.homEquiv_naturality_left, reassoc_of% h1, h2, ← Category.assoc,
    adj.homEquiv_naturality_right]

variable (τY : Y ⟶ Y') (q : W ⟶ Y) (q' : W' ⟶ Y') (hqsq : τW ≫ q' = q ≫ τY)
  (M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The naive crossing map on a summand**: on the summand `(i, j)` of degree `n`, the naive
crossing map is the transpose of the comparison of Stacks 01CD at the two terms followed by the
two crossing legs in degrees `i` and `j`, followed by `τ_{W,*}` of the inclusion of the summand. -/
theorem ι_naiveCrossing_f (i j n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) = n) :
    HomologicalComplex.ιMapBifunctor ((pullbackComplex p').obj ((pushforwardComplex τX).obj K))
        ((pullbackComplex q').obj ((pushforwardComplex τY).obj M))
            (Stacks.SheafOfModules.Tensor.sheafTensor W'.sheaf)
        (ComplexShape.up ℤ) i j n h ≫
      (naiveCrossing τX τY τW p q p' q' hpsq hqsq K M).f n =
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction τW).homEquiv _ _
        ((comparisonAppIso τW (((pullbackComplex p').obj ((pushforwardComplex τX).obj K)).X i)
            (((pullbackComplex q').obj ((pushforwardComplex τY).obj M)).X j)).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).map
              ((naiveCrossingLeg τX τW p p' hpsq K).f i)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).obj _).map
              ((naiveCrossingLeg τY τW q q' hqsq M).f j)) ≫
      (StacksDraft.KFlat.modulePushforward τW).map
        (HomologicalComplex.ιMapBifunctor ((pullbackComplex p).obj K) ((pullbackComplex q).obj M)
          (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf) (ComplexShape.up ℤ) i j n h) := by
  have h1 := Stacks.ModuleSkyscraper.ι_pullbackTensorComplexNatIso_hom τW
    ((pullbackComplex p').obj ((pushforwardComplex τX).obj K))
    ((pullbackComplex q').obj ((pushforwardComplex τY).obj M)) i j n h
  have h2 : HomologicalComplex.ιMapBifunctor
        ((pullbackComplex τW).obj ((pullbackComplex p').obj ((pushforwardComplex τX).obj K)))
        ((pullbackComplex τW).obj ((pullbackComplex q').obj ((pushforwardComplex τY).obj M)))
        (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf) (ComplexShape.up ℤ) i j n h ≫
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf)).map
        (naiveCrossingLeg τX τW p p' hpsq K ×ₘ naiveCrossingLeg τY τW q q' hqsq M)).f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).map
          ((naiveCrossingLeg τX τW p p' hpsq K).f i)).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).obj _).map
            ((naiveCrossingLeg τY τW q q' hqsq M).f j) ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplex p).obj K) ((pullbackComplex q).obj M)
          (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf) (ComplexShape.up ℤ) i j n h := by
    rw [totalComplexPair_map]
    exact HomologicalComplex.ι_mapBifunctorMap _ _ _ _ _ _ _ _
  exact chase_ι (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction τW) _ _ _ _ _ _ _
    h1 h2

end Generic

end Stacks.Cohomology.KunnethNaive

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

section Factors

variable {W X' S' : Scheme.{u}} (p : W ⟶ X') (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g)

/-- **The degreewise crossing leg** `τ^*p'^*τ_{X,*}𝓤 ⟶ p^*𝓤` for `g` presented as the
factorization `p ∘ c`: the composition isomorphism for `(τ, p')`, the transport along
`τ ≫ p' = p ≫ τ_X`, the inverse composition isomorphism for `(p, τ_X)` and `p^*` of the counit
of `τ_X^* ⊣ τ_{X,*}`. -/
def crossingLegOfFactors (U : Modules X'.toRingedSpace) :
    (RingedSpaceModuleAdjunction.modulePullback (toInverseImageBase g)).obj
        ((RingedSpaceModuleAdjunction.modulePullback
          (relativeInverseImageProjectionOfFactors p c g hg)).obj
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase c)).obj U)) ⟶
      (StacksDraft.KFlat.modulePullback p.toLRSHom.toShHom).obj U :=
  (Stacks.DerivedPullback.Composition.modulePullbackComp (toInverseImageBase g)
        (relativeInverseImageProjectionOfFactors p c g hg)).hom.app
        ((StacksDraft.KFlat.modulePushforward (toInverseImageBase c)).obj U) ≫
      eqToHom (congrArg (fun z => (StacksDraft.KFlat.modulePullback z).obj
        ((StacksDraft.KFlat.modulePushforward (toInverseImageBase c)).obj U))
        (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors p c g hg)) ≫
      (Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
          (toInverseImageBase c)).inv.app
        ((StacksDraft.KFlat.modulePushforward (toInverseImageBase c)).obj U) ≫
      (StacksDraft.KFlat.modulePullback p.toLRSHom.toShHom).map
        ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase c)).counit.app U)

/-- **A crossing leg of the box comparison is the degreewise crossing leg**: `τ^*` of the
comparison `p^{-1}𝓕 ⟶ p^*𝓕` followed by the counit of `τ^* ⊣ τ_*`. -/
theorem crossingLeg_ofFactors (U : Modules X'.toRingedSpace) :
    (Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
        (relativeInverseImageToPullbackOfFactors p c g hg U) ≫
      (Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase g)).counit.app
        ((_root_.pullback p.toLRSHom.toShHom).obj U) =
    crossingLegOfFactors p c g hg U :=
  pullback_relativeInverseImageToPullbackOfFactors_counit p c g hg U

end Factors

section Transpose

variable {W X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y) (g : W ⟶ S)
  (hp : p ≫ a = g) (hq : q ≫ b = g)

/-- **The tensor product of the two comparisons followed by the lax comparison is the transpose
of the comparison of Stacks 01CD followed by the two crossing legs**, the crossing legs in their
composite form. -/
theorem tensorMap_relativeInverseImageToPullbackOfFactors_eq_homEquiv
    (U : Modules X.toRingedSpace) (V : Modules Y.toRingedSpace) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(inverseImageBase g).presheaf, (inverseImageBase g).IsSheaf⟩)).map
        (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
        ((pushforward (toInverseImageBase a)).obj U)),
        ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
        ((pushforward (toInverseImageBase b)).obj V))))
        (Y := (((pushforward (toInverseImageBase g)).obj
        ((_root_.pullback p.toLRSHom.toShHom).obj U)),
        ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj V))))
        ((relativeInverseImageToPullbackOfFactors p a g hp U),
        (relativeInverseImageToPullbackOfFactors q b g hq V)) ≫ inverseImageTensorLax g
        ((_root_.pullback p.toLRSHom.toShHom).obj U) ((_root_.pullback q.toLRSHom.toShHom).obj V) =
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase g)).homEquiv _ _
        (Stacks.RingedSpace.comparison (toInverseImageBase g)
            ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
            ((pushforward (toInverseImageBase a)).obj U)) ((_root_.pullback
            (relativeInverseImageProjectionOfFactors q b g hq)).obj
            ((pushforward (toInverseImageBase b)).obj V)) ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
              (((Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
              (relativeInverseImageToPullbackOfFactors p a g hp U) ≫
              (Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase g)).counit.app
              ((_root_.pullback p.toLRSHom.toShHom).obj U)) ×ₘ
            ((Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
                (relativeInverseImageToPullbackOfFactors q b g hq V) ≫
                (Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase g)).counit.app
                ((_root_.pullback q.toLRSHom.toShHom).obj V)))) :=
  (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      (toInverseImageBase g)).homEquiv _ _).apply_symm_apply _).symm.trans
    (congrArg ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        (toInverseImageBase g)).homEquiv _ _)
      ((Adjunction.homEquiv_counit _ _ _ _).trans
        (pullback_tensorMap_relativeInverseImageToPullbackOfFactors_counit a b p q g hp hq U V)))

/-- The box comparison as the transpose of the comparison followed by the degreewise crossing
legs. -/
theorem tensorMap_relativeInverseImageToPullbackOfFactors_eq_homEquiv_crossingLegs
    (U : Modules X.toRingedSpace) (V : Modules Y.toRingedSpace) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(inverseImageBase g).presheaf, (inverseImageBase g).IsSheaf⟩)).map
        (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
        ((pushforward (toInverseImageBase a)).obj U)),
        ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
        ((pushforward (toInverseImageBase b)).obj V))))
        (Y := (((pushforward (toInverseImageBase g)).obj
        ((_root_.pullback p.toLRSHom.toShHom).obj U)),
        ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj V))))
        ((relativeInverseImageToPullbackOfFactors p a g hp U),
        (relativeInverseImageToPullbackOfFactors q b g hq V)) ≫
        inverseImageTensorLax g ((_root_.pullback p.toLRSHom.toShHom).obj U)
            ((_root_.pullback q.toLRSHom.toShHom).obj V)) =
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toInverseImageBase g)).homEquiv _ _
        (Stacks.RingedSpace.comparison (toInverseImageBase g)
            ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
            ((pushforward (toInverseImageBase a)).obj U)) ((_root_.pullback
            (relativeInverseImageProjectionOfFactors q b g hq)).obj
            ((pushforward (toInverseImageBase b)).obj V)) ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
              (((crossingLegOfFactors p a g hp U) : (Stacks.RingedSpace.pullbackFunctor
              (toInverseImageBase g)).obj ((_root_.pullback (relativeInverseImageProjectionOfFactors
              p a g hp)).obj ((pushforward (toInverseImageBase a)).obj U)) ⟶
              ((_root_.pullback p.toLRSHom.toShHom).obj U)) ×ₘ
            ((crossingLegOfFactors q b g hq V) : (Stacks.RingedSpace.pullbackFunctor
                (toInverseImageBase g)).obj
                ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
                ((pushforward (toInverseImageBase b)).obj V)) ⟶
                ((_root_.pullback q.toLRSHom.toShHom).obj V)))) := by
  rw [tensorMap_relativeInverseImageToPullbackOfFactors_eq_homEquiv a b p q g hp hq U V,
    crossingLeg_ofFactors p a g hp U, crossingLeg_ofFactors q b g hq V]
  rfl

/-- The comparison followed by the degreewise crossing legs, in the spelling of the naive crossing
map. -/
theorem comparison_crossingLegs_eq (U : Modules X.toRingedSpace) (V : Modules Y.toRingedSpace) :
    Stacks.RingedSpace.comparison (toInverseImageBase g)
        ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
        ((pushforward (toInverseImageBase a)).obj U)) ((_root_.pullback
        (relativeInverseImageProjectionOfFactors q b g hq)).obj
        ((pushforward (toInverseImageBase b)).obj V)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (((crossingLegOfFactors p a g hp U) : (Stacks.RingedSpace.pullbackFunctor
            (toInverseImageBase g)).obj ((_root_.pullback (relativeInverseImageProjectionOfFactors p
            a g hp)).obj ((pushforward (toInverseImageBase a)).obj U)) ⟶
            ((_root_.pullback p.toLRSHom.toShHom).obj U)) ×ₘ
          ((crossingLegOfFactors q b g hq V) : (Stacks.RingedSpace.pullbackFunctor
              (toInverseImageBase g)).obj ((_root_.pullback (relativeInverseImageProjectionOfFactors
              q b g hq)).obj ((pushforward (toInverseImageBase b)).obj V)) ⟶
              ((_root_.pullback q.toLRSHom.toShHom).obj V))) =
      (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso (toInverseImageBase g)
          ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).obj U))
          ((StacksDraft.KFlat.modulePullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
          ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).obj V))).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor W.toRingedSpace.sheaf).map
            (crossingLegOfFactors p a g hp U)).app _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
            W.toRingedSpace.sheaf).obj _).map (crossingLegOfFactors q b g hq V) :=
  rfl

end Transpose

section Single

variable {X S : Scheme.{u}} (a : X ⟶ S) (F : FiniteOrderDifferentialOperatorCategory a) (i : ℤ)

/-- In its degree, the single complex on the underlying module of `𝓕` and the underlying module of
the single complex on `𝓕` are the same module. -/
theorem single_module_eq :
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i =
      (((HomologicalComplex.single (FiniteOrderDifferentialOperatorCategory a)
        (ComplexShape.up ℤ) i).obj F).X i).module :=
  (HomologicalComplex.single_obj_X_self _ _ _).trans
    (congrArg FiniteOrderDifferentialOperatorCategory.module
      (HomologicalComplex.single_obj_X_self _ _ _)).symm

/-- **`τ_{X,*}𝓕[-i]` is the complex `𝓕[-i]` read over `a^{-1}𝒪_S`**: both are concentrated in
degree `i`, where they are the same module. -/
def pushforwardSingleIso :
    (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex (toInverseImageBase a)).obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module) ≅
      ((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F) :=
  Stacks.ConcentratedComplex.isoOfConcentrated _ _ i
    (fun k hk => (StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ k hk))
    (fun k hk => (toInverseImageModules a).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ k hk))
    ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).mapIso
      (eqToIso (single_module_eq a F i)))

/-- In degree `i` the isomorphism is the identity of the module, transported. -/
theorem pushforwardSingleIso_hom_f :
    (pushforwardSingleIso a F i).hom.f i =
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map
        (eqToHom (single_module_eq a F i)) :=
  Stacks.ConcentratedComplex.isoOfConcentrated_hom_f _ _ _ _ _ _

end Single

section SingleBox

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (F : FiniteOrderDifferentialOperatorCategory a)
  (G : FiniteOrderDifferentialOperatorCategory b) (i j : ℤ)

/-- The pullback `p^*𝓕[-i]` is concentrated in degree `i`. -/
theorem isZero_pullbackComplex_single_X {Z W : RingedSpace.{u, u}} (f : W ⟶ Z)
    (M : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) (k : ℤ) (hk : k ≠ i) :
    IsZero (((pullbackComplex f).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj M)).X k) :=
  (StacksDraft.KFlat.modulePullback f).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ k hk)

/-- The summand inclusion of `Tot(p^*𝓕[-i] ⊗ q^*𝓖[-j])` in degree `i + j` is an
isomorphism. -/
theorem isIso_ι_pullbackSingle : IsIso (HomologicalComplex.ιMapBifunctor
    ((pullbackComplex (pullback.fst a b).toLRSHom.toShHom).obj
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module))
    ((pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
    ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module))
    (Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf)
    (ComplexShape.up ℤ) i j (i + j) rfl) :=
  Stacks.ConcentratedComplex.isIso_ιMapBifunctor _ _ _ i j
    (isZero_pullbackComplex_single_X i (pullback.fst a b).toLRSHom.toShHom F.module)
    (isZero_pullbackComplex_single_X j (pullback.snd a b).toLRSHom.toShHom G.module)

/-- The summand inclusion of `Tot(𝓕[-i] ⊠ 𝓖[-j])` in degree `i + j` is an isomorphism. -/
theorem isIso_ι_boxSingle : IsIso (HomologicalComplex.ιMapBifunctor
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
    (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j (i + j)
    rfl) := by
  have := Stacks.Cohomology.BoxKunnethFlat.boxProductRelativeCurried_additive a b
  have := Stacks.Cohomology.BoxKunnethFlat.boxProductRelativeCurried_obj_additive a b
  exact HomologicalComplex.isIso_ιMapBifunctor_single_single _ F G i j

/-- The two terms in degree `(i, j)`: `τ_{W,*}(p^*𝓕 ⊗ q^*𝓖)` is `𝓕 ⊠ 𝓖` read over `f^{-1}𝒪_S`. -/
theorem pushforward_tensor_single_eq :
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).obj
            (((pullbackComplex (pullback.fst a b).toLRSHom.toShHom).obj
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module)).X i)).obj
            (((pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
            ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)).X j)) =
      ((Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b).obj
        (((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F).X i)).obj
        (((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G).X j) := by
  change (StacksDraft.KFlat.modulePushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).obj
          ((StacksDraft.KFlat.modulePullback (pullback.fst a b).toLRSHom.toShHom).obj
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module).X i))).obj
        ((StacksDraft.KFlat.modulePullback (pullback.snd a b).toLRSHom.toShHom).obj
          (((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module).X j))) = _
  rw [single_module_eq a F i, single_module_eq b G j]
  rfl

/-- **`τ_{W,*}Tot(p^*𝓕[-i] ⊗ q^*𝓖[-j]) ≅ Tot(𝓕[-i] ⊠ 𝓖[-j])`**: both are concentrated in degree
`i + j`, where they are the same module. -/
def pushforwardTotalSingleIso : (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
    (toInverseImageBase (pullback.fst a b ≫ a))).obj
    ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor
    (pullback a b).toRingedSpace.sheaf)).obj (((pullbackComplex
    (pullback.fst a b).toLRSHom.toShHom).obj ((HomologicalComplex.single X.Modules
    (ComplexShape.up ℤ) i).obj F.module)), ((pullbackComplex
    (pullback.snd a b).toLRSHom.toShHom).obj ((HomologicalComplex.single Y.Modules
    (ComplexShape.up ℤ) j).obj G.module)))) ≅ HomologicalComplex.mapBifunctor
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
    (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) :=
  haveI := isIso_ι_pullbackSingle a b F G i j
  haveI := isIso_ι_boxSingle a b F G i j
  haveI := Stacks.Cohomology.BoxKunnethFlat.boxProductRelativeCurried_additive a b
  haveI := Stacks.Cohomology.BoxKunnethFlat.boxProductRelativeCurried_obj_additive a b
  Stacks.ConcentratedComplex.isoOfConcentrated _ _ (i + j)
    (fun k hk => (StacksDraft.KFlat.modulePushforward
        (toInverseImageBase (pullback.fst a b ≫ a))).map_isZero
      (Stacks.ConcentratedComplex.isZero_mapBifunctor_X _ _ _ i j
        (isZero_pullbackComplex_single_X i (pullback.fst a b).toLRSHom.toShHom F.module)
        (isZero_pullbackComplex_single_X j (pullback.snd a b).toLRSHom.toShHom G.module) k hk))
    (fun k hk => HomologicalComplex.isZero_mapBifunctor_single_single_X _ F G i j k hk)
    ((StacksDraft.KFlat.modulePushforward (toInverseImageBase (pullback.fst a b ≫ a))).mapIso
        (asIso (HomologicalComplex.ιMapBifunctor ((pullbackComplex
        (pullback.fst a b).toLRSHom.toShHom).obj ((HomologicalComplex.single X.Modules
        (ComplexShape.up ℤ) i).obj F.module)) ((pullbackComplex
        (pullback.snd a b).toLRSHom.toShHom).obj ((HomologicalComplex.single Y.Modules
        (ComplexShape.up ℤ) j).obj G.module)) (Stacks.SheafOfModules.Tensor.sheafTensor
        (pullback a b).toRingedSpace.sheaf) (ComplexShape.up ℤ) i j (i + j) rfl)).symm ≪≫
      eqToIso (pushforward_tensor_single_eq a b F G i j) ≪≫
      asIso (HomologicalComplex.ιMapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ)
          i).obj F) ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl))

/-- On the summand `(i, j)`, the isomorphism is the identification of the two terms. -/
theorem pushforward_ι_pushforwardTotalSingleIso_hom_f :
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase (pullback.fst a b ≫ a))).map
        (HomologicalComplex.ιMapBifunctor ((pullbackComplex (pullback.fst a b).toLRSHom.toShHom).obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module))
        ((pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
        ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module))
        (Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf)
        (ComplexShape.up ℤ) i j (i + j) rfl) ≫
        (pushforwardTotalSingleIso a b F G i j).hom.f (i + j) =
      eqToHom (pushforward_tensor_single_eq a b F G i j) ≫ HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b) (ComplexShape.up ℤ) i j
          (i + j) rfl := by
  have := isIso_ι_pullbackSingle a b F G i j
  have := isIso_ι_boxSingle a b F G i j
  rw [pushforwardTotalSingleIso, Stacks.ConcentratedComplex.isoOfConcentrated_hom_f]
  exact Iso.hom_inv_id_assoc ((StacksDraft.KFlat.modulePushforward
    (toInverseImageBase (pullback.fst a b ≫ a))).mapIso
        (asIso (HomologicalComplex.ιMapBifunctor ((pullbackComplex
        (pullback.fst a b).toLRSHom.toShHom).obj ((HomologicalComplex.single X.Modules
        (ComplexShape.up ℤ) i).obj F.module)) ((pullbackComplex
        (pullback.snd a b).toLRSHom.toShHom).obj ((HomologicalComplex.single Y.Modules
        (ComplexShape.up ℤ) j).obj G.module)) (Stacks.SheafOfModules.Tensor.sheafTensor
        (pullback a b).toRingedSpace.sheaf) (ComplexShape.up ℤ) i j (i + j) rfl))) _

end SingleBox

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
