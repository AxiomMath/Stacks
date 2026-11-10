module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoKoszul
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoCompatibility
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.Statement
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullbackNatural
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductRightOperator

/-!
# The rows of Tag 01XX under an isomorphism of modules

Let `e : E ≅ E'` be an isomorphism of finite locally free `𝒪_S`-modules of constant rank `n + 1`
and `f : 𝐏(E') ⟶ 𝐏(E)` the induced isomorphism of projective bundles over `S`. The higher direct
images of the twists of `𝐏(E)` map to those of `𝐏(E')`: through `R^q π_* ≅ R^q π'_* ∘ f^*` and
`f^* 𝒪(d) ≅ 𝒪'(d)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImageIsoMap`: the map
  `R^q π_* 𝒪_{𝐏(E)}(d) ⟶ R^q π'_* 𝒪_{𝐏(E')}(d)` induced by `e`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.psi_pullback`: the homogeneous-section maps
  `Sym^k(E) ⟶ π_* 𝒪(k)` correspond under `e`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Rows

variable {S : Scheme.{u}} {E E' : S.Modules} {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (e : E ≅ E')
  (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree'))

/-- `p_* ≅ p'_* ∘ f^*` is the restriction of sections followed by the comparison of restriction
with pullback. -/
public theorem pushforwardPullbackIso_bundleMap
    (M : (relativeProj (bundleAlgebra E hfree)).scheme.Modules) :
    (pushforwardPullbackIso (bundleMap hfree hfree' e) _ _
        (bundleMap_comp_toBase hfree hfree' e)).hom.app M =
      bundleRestrictPushforward hfree hfree' e M ≫
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).map
          ((Scheme.Modules.restrictFunctorIsoPullback (bundleMap hfree hfree' e)).hom.app M) := by
  have h := Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback
    (bundleMap hfree hfree' e) M
  have n1 := (Scheme.Modules.pushforwardComp (bundleMap hfree hfree' e)
    (relativeProj (bundleAlgebra E hfree)).toBase).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback (bundleMap hfree hfree' e)).hom.app M)
  have n2 := (Scheme.Modules.pushforwardCongr (bundleMap_comp_toBase hfree hfree' e)).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback (bundleMap hfree hfree' e)).hom.app M)
  change (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (bundleMap hfree hfree' e)).unit.app M) ≫
      𝟙 _ ≫ ((Scheme.Modules.pushforwardComp (bundleMap hfree hfree' e)
        (relativeProj (bundleAlgebra E hfree)).toBase).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr (bundleMap_comp_toBase hfree hfree' e)).hom.app _) = _
  refine (Category.id_comp _ |> congrArg (_ ≫ ·)).trans ?_
  refine (congrArg (fun φ => (Scheme.Modules.pushforward
    (relativeProj (bundleAlgebra E hfree)).toBase).map φ ≫ _) h.symm).trans ?_
  refine ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase).map_comp _ _
    =≫ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) n1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) n2

/-- **The map `R^q π_* 𝒪_{𝐏(E)}(d) ⟶ R^q π'_* 𝒪_{𝐏(E')}(d)` induced by `e : E ≅ E'`**, for all
integers `q` and `d`: the comparison `R^q π_* ≅ R^q π'_* ∘ f^*` along the induced isomorphism
`f : 𝐏(E') ⟶ 𝐏(E)` over `S`, followed by the identification `f^* 𝒪(d) ≅ 𝒪'(d)` of the twists. -/
public def higherDirectImageIsoMap (q d : ℤ) :
    ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus
        q).obj (D.algebra.piece d) ⟶
      ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).rightDerivedPlus
        q).obj (D'.algebra.piece d) :=
  higherDirectImagePullback (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e) q
      (twistPiece D d) ≫
    ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).rightDerivedPlus
      q).map (twistPullbackIso hfree hfree' e D D' d).hom

/-- In degree zero the induced map is the restriction of sections followed by the identification
of the twists. -/
public theorem higherDirectImageIsoMap_zero (d : ℕ) :
    higherDirectImageIsoMap hfree hfree' e D D' 0 d =
      higherDirectImageZeroMap hfree hfree' e D D' d := by
  have hA := pushforwardPullbackIso_bundleMap hfree hfree' e (twistPiece D d)
  have hc := directImageComparisonApp_zero _ _ (Scheme.Modules.pullback (bundleMap hfree hfree' e))
    (pushforwardPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e))
    (twistPiece D d)
  have hn := (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (Scheme.Modules.pushforward
    (relativeProj (bundleAlgebra E' hfree')).toBase)).inv.naturality
    (twistPullbackIso hfree hfree' e D D' d).hom
  change (((Stacks.DerivedIndexing.rightDerivedIso _ 0).app _).inv ≫
      (directImageComparisonApp _ _ (Scheme.Modules.pullback (bundleMap hfree hfree' e))
        (pushforwardPullbackIso (bundleMap hfree hfree' e) _ _
          (bundleMap_comp_toBase hfree hfree' e)) 0 (twistPiece D d)).hom ≫
      ((Stacks.DerivedIndexing.rightDerivedIso _ 0).app _).hom) ≫ _ = _
  rw [hc]
  simp only [rightDerivedZeroIsoPlus, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Category.assoc, Iso.app_inv, Iso.app_hom, Iso.inv_hom_id_app_assoc]
  have hθ : (Scheme.Modules.restrictFunctorIsoPullback (bundleMap hfree hfree' e)).hom.app
        (twistPiece D d) ≫ (twistPullbackIso hfree hfree' e D D' d).hom =
      (bundleTwistIso hfree hfree' e D D').hom.app (d : ℤ) :=
    Iso.hom_inv_id_app_assoc _ _ _
  rw [hA, ← hn, Category.assoc, ← Functor.map_comp_assoc, hθ]
  rfl

end Rows

section Exterior

variable {X X' T : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ T) (p' : X' ⟶ T) (hbase : f ≫ p = p')
  {M M' : T.Modules} (e : M ≅ M')

/-- **The comparison of Tag 01CI for a composite, against an isomorphism of modules.** For
`p' = f ≫ p` and `e : M ≅ M'`, the comparison `p'^*(⋀ᵐ M') ≅ ⋀ᵐ(p'^* M')` precomposed with
`p'^*(⋀ᵐ e)` is the comparison `p^*(⋀ᵐ M) ≅ ⋀ᵐ(p^* M)` pulled back along `f`, followed by the
comparison along `f` with `f^* p^* M ≅ p'^* M ≅ p'^* M'`. -/
public theorem exteriorPowerPullbackIso_pullback (m : ℤ) :
    (Scheme.Modules.pullback p').map (Scheme.Modules.exteriorPowerMap e.hom m) ≫
        (Scheme.Modules.exteriorPowerPullbackIso p' M' m).hom =
      (pullbackPullbackIso f p p' hbase (Scheme.Modules.exteriorPower M m)).inv ≫
        (Scheme.Modules.pullback f).map (Scheme.Modules.exteriorPowerPullbackIso p M m).hom ≫
        (extPullbackIso f.toLRSHom.toShHom
          (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X) (Osharp := X.sheaf)
            ((Scheme.Modules.pullback p).obj M))
          (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X') (Osharp := X'.sheaf)
            ((Scheme.Modules.pullback p').obj M'))
          (pullbackPullbackIso f p p' hbase M ≪≫ (Scheme.Modules.pullback p').mapIso e) m).hom := by
  subst hbase
  rw [Scheme.Modules.exteriorPowerPullbackIso_natural]
  have hA := Scheme.Modules.isExteriorAlgebra_exteriorAlgebra M
  have hD := Scheme.Modules.isExteriorAlgebra_exteriorAlgebra ((Scheme.Modules.pullback p).obj M)
  have hB := Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
    ((Scheme.Modules.pullback (f ≫ p)).obj M)
  have hB' := Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
    ((Scheme.Modules.pullback (f ≫ p)).obj M')
  have hL := SheafOfModules.GradedAlgebra.pullbackComparison_comp_unitalHom
    (f ≫ p).toLRSHom.toShHom hA hB.1
    (hB.map hB' ((Scheme.Modules.pullback (f ≫ p)).map e.hom)) m
  have hμ := hB'.1.comp (pullbackPullbackIso f p (f ≫ p) rfl M ≪≫
    (Scheme.Modules.pullback (f ≫ p)).mapIso e).hom
  have hε : ∀ (N : T.Modules) (U : (Opens T.carrier)ᵒᵖ) (x : N.val.obj U),
      ((Scheme.Modules.pullbackComp f p ≪≫ Scheme.Modules.pullbackCongr rfl).inv.app N).val.app
          ((opensMap (f.toLRSHom.toShHom ≫ p.toLRSHom.toShHom)).op.obj U)
          (pullbackUnit (f.toLRSHom.toShHom ≫ p.toLRSHom.toShHom) N U x) =
        pullbackUnit f.toLRSHom.toShHom ((Scheme.Modules.pullback p).obj N)
          ((opensMap p.toLRSHom.toShHom).op.obj U) (pullbackUnit p.toLRSHom.toShHom N U x) :=
    fun N U x => ((congrArg (((pullbackPullbackIso f p (f ≫ p) rfl N).inv).val.app _)
      (pullbackPullbackIso_rfl_pbUnit f p N U.unop x).symm).trans
      (Stacks.SheafOfModules.inv_val_app_hom_val_app (pullbackPullbackIso f p (f ≫ p) rfl N) _ _))
  have hR := SheafOfModules.GradedAlgebra.pullbackComparison_comp p.toLRSHom.toShHom
    f.toLRSHom.toShHom hA hD (c := 𝟙 _) hμ
    (Scheme.Modules.pullbackComp f p ≪≫ Scheme.Modules.pullbackCongr rfl).inv hε m
  have hκ : ((Scheme.Modules.pullback (f ≫ p)).obj M).exteriorGenerator ≫
        (hB.map hB' ((Scheme.Modules.pullback (f ≫ p)).map e.hom)).app 1 =
      ((Scheme.Modules.pullbackComp f p ≪≫ Scheme.Modules.pullbackCongr rfl).inv.app M ≫
        (modulePullback f.toLRSHom.toShHom).map (𝟙 _)) ≫
        (pullbackPullbackIso f p (f ≫ p) rfl M ≪≫
          (Scheme.Modules.pullback (f ≫ p)).mapIso e).hom ≫
        ((Scheme.Modules.pullback (f ≫ p)).obj M').exteriorGenerator := by
    have h1 : ((Scheme.Modules.pullbackComp f p ≪≫ Scheme.Modules.pullbackCongr rfl).inv.app M ≫
        (modulePullback f.toLRSHom.toShHom).map (𝟙 _)) ≫
        (pullbackPullbackIso f p (f ≫ p) rfl M ≪≫
          (Scheme.Modules.pullback (f ≫ p)).mapIso e).hom =
        (Scheme.Modules.pullback (f ≫ p)).map e.hom :=
      (congrArg (· ≫ _) ((congrArg (_ ≫ ·)
        ((modulePullback f.toLRSHom.toShHom).map_id _)).trans (Category.comp_id _))).trans
        (Iso.inv_hom_id_app_assoc
          (Scheme.Modules.pullbackComp f p ≪≫ Scheme.Modules.pullbackCongr rfl) M _)
    exact (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_app_one hB hB' _).trans
      ((congrArg (· ≫ ((Scheme.Modules.pullback (f ≫ p)).obj M').exteriorGenerator)
        h1.symm).trans (Category.assoc _ _ _))
  have hc := SheafOfModules.GradedAlgebra.pullbackComparison_congr p.toLRSHom.toShHom hA
    (Category.id_comp ((Scheme.Modules.pullback p).obj M).exteriorGenerator) (hD.1.comp (𝟙 _))
    hD.1 m
  refine hL.trans ?_
  refine (SheafOfModules.GradedAlgebra.pullbackComparison_congr _ hA hκ _
    (hμ.comp ((Scheme.Modules.pullbackComp f p ≪≫ Scheme.Modules.pullbackCongr rfl).inv.app M ≫
        (modulePullback f.toLRSHom.toShHom).map (𝟙 _))) m).trans ?_
  refine hR.trans ?_
  exact congrArg (fun φ => (Scheme.Modules.pullbackComp f p ≪≫
    Scheme.Modules.pullbackCongr rfl).inv.app (M.exteriorAlgebra.piece m) ≫
      (modulePullback f.toLRSHom.toShHom).map φ ≫
      SheafOfModules.GradedAlgebra.pullbackComparison f.toLRSHom.toShHom hD hμ m) hc

end Exterior

section Swap

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {M L : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {N L' : _root_.SheafOfModules.{u} (structureRingSheaf X)}

/-- **`tensorPullbackIso` commutes with the swap of the two factors.** -/
public theorem tensorPullbackIso_swap (a : (pullbackFunctor f).obj M ≅ N)
    (l : (pullbackFunctor f).obj L ≅ L') :
    (pullbackFunctor f).map (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap Y M L).hom ≫
        (tensorPullbackIso f l a).hom =
      (tensorPullbackIso f a l).hom ≫
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X N L').hom := by
  refine pullback_tensorSheaf_hom_ext f fun U x y => ?_
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine (congrArg ((tensorPullbackIso f l a).hom.val.app _)
    ((pullbackUnit_naturality f _ U _).trans (congrArg (pullbackUnit f _ U)
      (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_app_toTensorSheafSection Y M L
        U.unop x y)))).trans ?_
  refine (tensorPullbackIso_unit f l a U y x).trans ?_
  refine Eq.trans ?_ (congrArg
    ((Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X N L').hom.val.app _)
    (tensorPullbackIso_unit f a l U x y)).symm
  exact (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_app_toTensorSheafSection X N L'
    _ _ _).symm

end Swap

section ProjectionNaturality

variable {X Y : Scheme.{u}} (p : X ⟶ Y) (G : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]

/-- The projection formula `R^q p_*(ℱ ⊗ p^* G) ≅ R^q p_* ℱ ⊗ G` is natural in `ℱ`. -/
public theorem projectionFormulaDeltaApp_naturality (q : ℕ) {F F' : X.Modules} (φ : F ⟶ F') :
    ((Scheme.Modules.pushforward p).rightDerived q).map
        ((Stacks.ProjectionFormula.tensorRightInvertible X
          ((Scheme.Modules.pullback p).obj G)).map φ) ≫
        (projectionFormulaDeltaApp p G F' q).hom =
      (projectionFormulaDeltaApp p G F q).hom ≫
        (Stacks.ProjectionFormula.tensorRightInvertible Y G).map
          (((Scheme.Modules.pushforward p).rightDerived q).map φ) :=
  ((projectionFormulaDelta p G).hom.app q).naturality φ

end ProjectionNaturality

section ProjectionPullback

variable {X X' T : Scheme.{u}} (f : X' ⟶ X) [IsIso f] (p : X ⟶ T) (p' : X' ⟶ T)
  (hbase : f ≫ p = p') {G G' : T.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G'] (g : G ≅ G')

omit [IsIso f] in
/-- `tensorPullbackIso` with the identity in the first factor, followed by a morphism there. -/
public theorem tensorPullbackIso_refl_comp {F : X.Modules} {F' : X'.Modules}
    (θ : (Scheme.Modules.pullback f).obj F ≅ F') {L : T.Modules} {L' : X'.Modules}
    (l : (pullbackFunctor f.toLRSHom.toShHom).obj ((Scheme.Modules.pullback p).obj L) ≅ L') :
    (tensorPullbackIso f.toLRSHom.toShHom
        (Iso.refl ((pullbackFunctor f.toLRSHom.toShHom).obj F)) l).hom ≫
      tensorMap θ.hom (𝟙 L') = (tensorPullbackIso f.toLRSHom.toShHom θ l).hom := by
  have hn := tensorPullbackIso_naturality₂ f.toLRSHom.toShHom
    (Iso.refl ((pullbackFunctor f.toLRSHom.toShHom).obj F)) θ l l (𝟙 _) θ.hom (𝟙 _) (𝟙 _)
    (((congrArg (· ≫ _) ((pullbackFunctor f.toLRSHom.toShHom).map_id _)).trans
      (Category.id_comp _)).trans (Category.id_comp _).symm)
    (((congrArg (· ≫ _) ((pullbackFunctor f.toLRSHom.toShHom).map_id _)).trans
      (Category.id_comp _)).trans (Category.comp_id _).symm)
  exact hn.symm.trans ((congrArg (· ≫ _) ((congrArg (pullbackFunctor f.toLRSHom.toShHom).map
    (tensorMap_id _ _)).trans ((pullbackFunctor f.toLRSHom.toShHom).map_id _))).trans
    (Category.id_comp _))

omit [IsIso f] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G'] in
/-- `f^*(F ⊗ p^* G) ≅ f^* F ⊗ p'^* G'` followed by `f^* F ≅ F'` is `tensorPullbackIso`. -/
public theorem tensorPullbackNatIso_app_comp {F : X.Modules} {F' : X'.Modules}
    (θ : (Scheme.Modules.pullback f).obj F ≅ F') :
    (tensorPullbackNatIso f p p' hbase g).hom.app F ≫
        (Stacks.ProjectionFormula.tensorRightInvertible X'
          ((Scheme.Modules.pullback p').obj G')).map θ.hom =
      (tensorPullbackIso f.toLRSHom.toShHom θ (pullbackPullbackIso' f p p' hbase g)).hom :=
  tensorPullbackIso_refl_comp f p θ (pullbackPullbackIso' f p p' hbase g)

/-- **The projection formulas of `p` and `p'` correspond**, along `f^* F ≅ F'` and `G ≅ G'`. -/
public theorem projectionFormulaDeltaApp_pullback_iso (q : ℕ) {F : X.Modules} {F' : X'.Modules}
    (θ : (Scheme.Modules.pullback f).obj F ≅ F') :
    (projectionFormulaDeltaApp p G F q).hom ≫
        tensorMap ((directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q F).hom ≫
          ((Scheme.Modules.pushforward p').rightDerived q).map θ.hom) g.hom =
      (directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q _).hom ≫
        ((Scheme.Modules.pushforward p').rightDerived q).map
          (tensorPullbackIso f.toLRSHom.toShHom θ (pullbackPullbackIso' f p p' hbase g)).hom ≫
        (projectionFormulaDeltaApp p' G' F' q).hom := by
  have hC := projectionFormulaDeltaApp_pullback f p p' hbase g q F
  have hD := projectionFormulaDeltaApp_naturality p' G' q θ.hom
  have hT := tensorPullbackNatIso_app_comp f p p' hbase g θ
  refine (congrArg (_ ≫ ·) ((congrArg₂ (fun a b => tensorMap (Z := T.toRingedSpace) a b) rfl
    (Category.comp_id g.hom).symm).trans
      (tensorMap_comp (Z := T.toRingedSpace) _ _ _ _).symm)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hC).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hD.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)
  exact (((Scheme.Modules.pushforward p').rightDerived q).map_comp _ _).symm.trans
    (congrArg ((Scheme.Modules.pushforward p').rightDerived q).map hT)

end ProjectionPullback

/-- `koszulMiddleIso` is the swap followed by the tensor of the identity with the Tag 01CI
comparison. -/
private theorem koszulMiddleIso_hom_eq {S : Scheme.{u}} {E : S.Modules}
    {hqc : Stacks.SymGraded.IsQuasicoherentPieces E}
    (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) (p k : ℕ) :
    (koszulMiddleIso E hqc D p k).hom = (koszulMiddleSwap E hqc D p k).hom ≫
      tensorMap (Z := (bundle E hqc).toRingedSpace) (𝟙 (negTwist E hqc D k))
        (Scheme.Modules.exteriorPowerPullbackIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E p).inv :=
  (rfl : (koszulMiddleIso E hqc D p k).hom = (koszulMiddleSwap E hqc D p k).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩).obj
          (negTwist E hqc D k)).map (Scheme.Modules.exteriorPowerPullbackIso
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E p).inv).trans
    (congrArg ((koszulMiddleSwap E hqc D p k).hom ≫ ·)
      (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩)
        (negTwist E hqc D k) _).symm)

section KoszulGeneral

variable {S S' : Scheme.{u}} {E : S.Modules} {E' : S'.Modules} [E.IsQuasicoherent]
  [E'.IsQuasicoherent]
  {hqc : Stacks.SymGraded.IsQuasicoherentPieces E}
  {hqc' : Stacks.SymGraded.IsQuasicoherentPieces E'}
  {D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)}
  {D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')}
  (f : bundle E' hqc' ⟶ bundle E hqc)
  (θ : ∀ d : ℤ, (Scheme.Modules.pullback f).obj (D.algebra.piece d) ≅ D'.algebra.piece d)
  (lV : (Scheme.Modules.pullback f).obj (bundlePullback E hqc) ≅ bundlePullback E' hqc')

omit [E.IsQuasicoherent] [E'.IsQuasicoherent] in
/-- **The middle term of the twisted Koszul filtration under pullback**, for a morphism of
projective bundles over two bases: `⋀ᵖ π^* E ⊗ 𝒪(-k) ≅ 𝒪(-k) ⊗ π^*(⋀ᵖ E)` corresponds to the same
isomorphism for `E'`, along `f^* π^* ⋀ᵖ E ≅ π'^* ⋀ᵖ E'` compatible with `⋀ᵖ` of
`f^* π^* E ≅ π'^* E'`. -/
public theorem koszulMiddleIso_pullback_of (p k : ℕ)
    (lD : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
        (Scheme.Modules.exteriorPower E p)) ≅
      (Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
        (Scheme.Modules.exteriorPower E' p))
    (hk : (Scheme.Modules.pullback f).map
        (Scheme.Modules.exteriorPowerPullbackIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E p).inv ≫
        lD.hom =
      (pbExtIso f lV (p : ℤ)).hom ≫
        (Scheme.Modules.exteriorPowerPullbackIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase E' p).inv) :
    (Scheme.Modules.pullback f).map (koszulMiddleIso E hqc D p k).hom ≫
        (tensorPullbackIso f.toLRSHom.toShHom (θ (-(k : ℤ))) lD).hom =
      (tensorPullbackIso f.toLRSHom.toShHom (pbExtIso f lV (p : ℤ)) (θ (-(k : ℤ)))).hom ≫
        (koszulMiddleIso E' hqc' D' p k).hom := by
  have h2 := tensorPullbackIso_naturality₂ f.toLRSHom.toShHom (θ (-(k : ℤ))) (θ (-(k : ℤ)))
    (pbExtIso f lV (p : ℤ)) lD (𝟙 _) (𝟙 _) _ _
    (((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)).trans
      (Category.comp_id _).symm) hk
  have h1 := tensorPullbackIso_swap f.toLRSHom.toShHom (pbExtIso f lV (p : ℤ)) (θ (-(k : ℤ)))
  rw [koszulMiddleIso_hom_eq D, koszulMiddleIso_hom_eq D']
  refine ((Scheme.Modules.pullback f).map_comp (koszulMiddleSwap E hqc D p k).hom
    (tensorMap (𝟙 _) (Scheme.Modules.exteriorPowerPullbackIso
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E p).inv) =≫
        _).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans (Category.assoc _ _ _))))

variable
  (hu : (Scheme.Modules.pullback f).map (tautologicalMap E hqc D) ≫ (θ ((1 : ℕ) : ℤ)).hom =
    lV.hom ≫ tautologicalMap E' hqc' D')
  (hmul : ∀ i j : ℤ, (Scheme.Modules.pullback f).map (twistMul D i j) ≫ (θ (i + j)).hom =
    (tensorPullbackIso f.toLRSHom.toShHom (θ i) (θ j)).hom ≫ twistMul D' i j)
  (κ : (Scheme.Modules.pullback f).obj (tautologicalKernel E hqc D) ≅
    tautologicalKernel E' hqc' D')
  (hκ : (Scheme.Modules.pullback f).map (kernel.ι (tautologicalMap E hqc D)) ≫ lV.hom =
    κ.hom ≫ kernel.ι (tautologicalMap E' hqc' D'))
  {n : ℕ} (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1))

include hu hmul hκ hfree hfree' in
/-- **The last step of the Koszul filtration under pullback**, for a morphism of projective
bundles over two bases: `⋀ⁿ K ⊗ 𝒪(-n) ≅ 𝒪(-n-1) ⊗ π^*(⋀ⁿ⁺¹ E)` corresponds to the same
isomorphism for `E'`. -/
public theorem koszulTopStep_pullback_of
    (lD : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))) ≅
      (Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
        (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ)))
    (hk : (Scheme.Modules.pullback f).map
        (Scheme.Modules.exteriorPowerPullbackIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E
            ((n + 1 : ℕ) : ℤ)).inv ≫
        lD.hom =
      (pbExtIso f lV ((n + 1 : ℕ) : ℤ)).hom ≫
        (Scheme.Modules.exteriorPowerPullbackIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase E'
            ((n + 1 : ℕ) : ℤ)).inv) :
    (Scheme.Modules.pullback f).map ((koszulTwistIso E hqc D n).inv ≫
        (@asIso _ _ _ _ (koszulTwistSequence E hqc D n).g
          (isIso_koszulTwistSequence_g E hqc D hfree)).inv ≫
        (koszulMiddleIso E hqc D (n + 1) (n + 1)).hom) ≫
        (tensorPullbackIso f.toLRSHom.toShHom (θ (-((n + 1 : ℕ) : ℤ))) lD).hom =
      (koszulTermIsoOf f θ κ n).hom ≫
        ((koszulTwistIso E' hqc' D' n).inv ≫ (@asIso _ _ _ _ (koszulTwistSequence E' hqc' D' n).g
          (isIso_koszulTwistSequence_g E' hqc' D' hfree')).inv ≫
          (koszulMiddleIso E' hqc' D' (n + 1) (n + 1)).hom) := by
  have h1 := iso_square_inv ((Scheme.Modules.pullback f).mapIso (koszulTwistIso E hqc D n))
    (koszulTwistIso E' hqc' D' n) _ _ (koszulTwistIso_pullback_of f θ hmul κ n)
  have h2 := iso_square_inv ((Scheme.Modules.pullback f).mapIso
      (@asIso _ _ _ _ (koszulTwistSequence E hqc D n).g
        (isIso_koszulTwistSequence_g E hqc D hfree)))
      (@asIso _ _ _ _ (koszulTwistSequence E' hqc' D' n).g
        (isIso_koszulTwistSequence_g E' hqc' D' hfree')) _ _
    (koszulTwistSequencePullbackIsoOf f θ lV hu κ hκ n).hom.comm₂₃.symm
  have h3 := koszulMiddleIso_pullback_of f θ lV (n + 1) (n + 1) lD hk
  refine (congrArg (· ≫ _) (((Scheme.Modules.pullback f).map_comp _ _).trans
    (congrArg (_ ≫ ·) ((Scheme.Modules.pullback f).map_comp _ _)))).trans ?_
  exact (paste_three _ _ _ _ _ _ _ _ _ _ h1.symm h2.symm h3.symm).symm

end KoszulGeneral

section Koszul

variable {S : Scheme.{u}} {E E' : S.Modules} [E.IsQuasicoherent] [E'.IsQuasicoherent]
  {hqc : Stacks.SymGraded.IsQuasicoherentPieces E}
  {hqc' : Stacks.SymGraded.IsQuasicoherentPieces E'}
  {D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)}
  {D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')}
  (f : bundle E' hqc' ⟶ bundle E hqc) [IsIso f]
  (θ : ∀ d : ℤ, (Scheme.Modules.pullback f).obj (D.algebra.piece d) ≅ D'.algebra.piece d)
  (hbase : f ≫ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase =
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase)
  (e : E ≅ E')

/-- `f^*(π^* ⋀ᵖ E) ≅ π'^* ⋀ᵖ E'`. -/
public abbrev detPullbackIso (p : ℤ) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
        (Scheme.Modules.exteriorPower E p)) ≅
      (Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
        (Scheme.Modules.exteriorPower E' p) :=
  pullbackPullbackIso f _ _ hbase (Scheme.Modules.exteriorPower E p) ≪≫
    (Scheme.Modules.pullback _).mapIso (asIso (Scheme.Modules.exteriorPowerMap e.hom p))

omit [E.IsQuasicoherent] [E'.IsQuasicoherent] [IsIso f] in
/-- `f^* π^* ⋀ᵖ E ≅ π'^* ⋀ᵖ E'` is `⋀ᵖ` of `f^* π^* E ≅ π'^* E'` under the comparisons of
Tag 01CI. -/
public theorem detPullbackIso_compat (p : ℕ) :
    (Scheme.Modules.pullback f).map
        (Scheme.Modules.exteriorPowerPullbackIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E p).inv ≫
        (detPullbackIso f hbase e p).hom =
      (pbExtIso f (pullbackPullbackIso f _ _ hbase E ≪≫ (Scheme.Modules.pullback _).mapIso e)
        (p : ℤ)).hom ≫
        (Scheme.Modules.exteriorPowerPullbackIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase E' p).inv := by
  have hext := exteriorPowerPullbackIso_pullback f _ _ hbase e (p : ℤ)
  refine (Iso.eq_comp_inv _).mpr ?_
  refine (Category.assoc _ _ _).trans ?_
  change _ ≫ ((pullbackPullbackIso f _ _ hbase (Scheme.Modules.exteriorPower E p)).hom ≫
    (Scheme.Modules.pullback _).map (Scheme.Modules.exteriorPowerMap e.hom p)) ≫ _ = _
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hext).trans
    (Iso.hom_inv_id_assoc _ _)))).trans
    (((Scheme.Modules.pullback f).mapIso (Scheme.Modules.exteriorPowerPullbackIso
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E p)).inv_hom_id_assoc
        _)

omit [E.IsQuasicoherent] [E'.IsQuasicoherent] [IsIso f] in
/-- **The middle term of the twisted Koszul filtration under pullback**:
`⋀ᵖ π^* E ⊗ 𝒪(-k) ≅ 𝒪(-k) ⊗ π^*(⋀ᵖ E)` corresponds to the same isomorphism for `E'`. -/
public theorem koszulMiddleIso_pullback (p k : ℕ) :
    (Scheme.Modules.pullback f).map (koszulMiddleIso E hqc D p k).hom ≫
        (tensorPullbackIso f.toLRSHom.toShHom (θ (-(k : ℤ))) (detPullbackIso f hbase e p)).hom =
      (tensorPullbackIso f.toLRSHom.toShHom
          (pbExtIso f (pullbackPullbackIso f _ _ hbase E ≪≫ (Scheme.Modules.pullback _).mapIso e)
            (p : ℤ)) (θ (-(k : ℤ)))).hom ≫
        (koszulMiddleIso E' hqc' D' p k).hom :=
  koszulMiddleIso_pullback_of f θ _ p k (detPullbackIso f hbase e p)
    (detPullbackIso_compat f hbase e p)

/-- `f^*(π^* E) ≅ π'^* E'`. -/
public abbrev bundlePullbackIso :
    (Scheme.Modules.pullback f).obj (bundlePullback E hqc) ≅ bundlePullback E' hqc' :=
  pullbackPullbackIso f _ _ hbase E ≪≫ (Scheme.Modules.pullback _).mapIso e

variable
  (hu : (Scheme.Modules.pullback f).map (tautologicalMap E hqc D) ≫ (θ ((1 : ℕ) : ℤ)).hom =
    (bundlePullbackIso f hbase e).hom ≫ tautologicalMap E' hqc' D')
  (hmul : ∀ i j : ℤ, (Scheme.Modules.pullback f).map (twistMul D i j) ≫ (θ (i + j)).hom =
    (tensorPullbackIso f.toLRSHom.toShHom (θ i) (θ j)).hom ≫ twistMul D' i j)
  {n : ℕ} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1))

include hmul hfree hfree' in
/-- **The last step of the Koszul filtration under pullback**:
`⋀ⁿ K ⊗ 𝒪(-n) ≅ 𝒪(-n-1) ⊗ π^*(⋀ⁿ⁺¹ E)` corresponds to the same isomorphism for `E'`. -/
public theorem koszulTopStep_pullback :
    (Scheme.Modules.pullback f).map ((koszulTwistIso E hqc D n).inv ≫
        (@asIso _ _ _ _ (koszulTwistSequence E hqc D n).g
          (isIso_koszulTwistSequence_g E hqc D hfree)).inv ≫
        (koszulMiddleIso E hqc D (n + 1) (n + 1)).hom) ≫
        (tensorPullbackIso f.toLRSHom.toShHom (θ (-((n + 1 : ℕ) : ℤ)))
          (detPullbackIso f hbase e ((n + 1 : ℕ) : ℤ))).hom =
      (koszulTermIso f θ (bundlePullbackIso f hbase e) hu n).hom ≫
        ((koszulTwistIso E' hqc' D' n).inv ≫ (@asIso _ _ _ _ (koszulTwistSequence E' hqc' D' n).g
          (isIso_koszulTwistSequence_g E' hqc' D' hfree')).inv ≫
          (koszulMiddleIso E' hqc' D' (n + 1) (n + 1)).hom) :=
  koszulTopStep_pullback_of f θ (bundlePullbackIso f hbase e) hu hmul _
    (tautKernelIso_ι f θ (bundlePullbackIso f hbase e) hu) hfree hfree'
    (detPullbackIso f hbase e ((n + 1 : ℕ) : ℤ)) (detPullbackIso_compat f hbase e (n + 1))

/-- The diagram chase behind `koszulTopIso_pullback`. -/
private theorem top_chase {C : Type*} [Category C] {A₀ A₁ B₀ B₁ B₂ Q₁ Q₂ Q₃ Z : C}
    {c : A₀ ⟶ A₁} {cn : A₁ ⟶ Q₁} {x : Q₁ ⟶ Q₂} {y : Q₂ ⟶ Q₃} {p' : Q₃ ⟶ Z} {c₀ : A₀ ⟶ B₀}
    {r₀ : B₀ ⟶ B₁} {c' : B₁ ⟶ B₂} {r : Q₁ ⟶ B₂} {x' : B₂ ⟶ Q₃}
    (hM : x ≫ y = r ≫ x') (hA : c ≫ cn ≫ r = c₀ ≫ r₀ ≫ c') :
    c ≫ (cn ≫ x) ≫ y ≫ p' = c₀ ≫ r₀ ≫ c' ≫ x' ≫ p' := by
  rw [Category.assoc, reassoc_of% hM]
  simp only [← Category.assoc] at hA ⊢
  rw [hA]

/-- `koszulTopIso` as a composite. -/
public theorem koszulTopIso_hom
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))] :
    (koszulTopIso E hqc D hn hfree).hom = (koszulChainIso E hqc D hn hfree n le_rfl).hom ≫
      ((bundlePushforward E hqc).rightDerived n).map ((koszulTwistIso E hqc D n).inv ≫
        (@asIso _ _ _ _ (koszulTwistSequence E hqc D n).g
          (isIso_koszulTwistSequence_g E hqc D hfree)).inv ≫
        (koszulMiddleIso E hqc D (n + 1) (n + 1)).hom) ≫
      (projectionFormulaDeltaApp _ _ _ n).hom := rfl

include hmul in
/-- The chase behind `koszulTopIso_pullback`, after the projection formula. -/
public theorem koszulTopIso_pullback_aux
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))] :
    (koszulChainIso E hqc D hn hfree n le_rfl).hom ≫
      ((bundleComparison f hbase n (koszulTerm E hqc D n)).hom ≫
        ((bundlePushforward E' hqc').rightDerived n).map ((Scheme.Modules.pullback f).map
          ((koszulTwistIso E hqc D n).inv ≫ (@asIso _ _ _ _ (koszulTwistSequence E hqc D n).g
            (isIso_koszulTwistSequence_g E hqc D hfree)).inv ≫
            (koszulMiddleIso E hqc D (n + 1) (n + 1)).hom))) ≫
      ((bundlePushforward E' hqc').rightDerived n).map
        (tensorPullbackIso f.toLRSHom.toShHom (θ (-((n + 1 : ℕ) : ℤ)))
          (detPullbackIso f hbase e ((n + 1 : ℕ) : ℤ))).hom ≫
      (projectionFormulaDeltaApp _ (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))
        (negTwist E' hqc' D' (n + 1)) n).hom =
    (bundleComparison f hbase 0 (koszulTerm E hqc D 0)).hom ≫
      ((bundlePushforward E' hqc').rightDerived 0).map
        (koszulTermIso f θ (bundlePullbackIso f hbase e) hu 0).hom ≫
      (koszulChainIso E' hqc' D' hn hfree' n le_rfl).hom ≫
      ((bundlePushforward E' hqc').rightDerived n).map ((koszulTwistIso E' hqc' D' n).inv ≫
        (@asIso _ _ _ _ (koszulTwistSequence E' hqc' D' n).g
          (isIso_koszulTwistSequence_g E' hqc' D' hfree')).inv ≫
        (koszulMiddleIso E' hqc' D' (n + 1) (n + 1)).hom) ≫
      (projectionFormulaDeltaApp _ _ _ n).hom :=
  top_chase ((((bundlePushforward E' hqc').rightDerived n).map_comp _ _).symm.trans
    ((congrArg ((bundlePushforward E' hqc').rightDerived n).map
      (koszulTopStep_pullback f θ hbase e hu hmul hfree hfree')).trans
      (((bundlePushforward E' hqc').rightDerived n).map_comp _ _)))
    (koszulChainIso_pullback f θ (bundlePullbackIso f hbase e) hu hmul hbase hn hfree hfree' n
      le_rfl)

include hmul in
/-- **The trace isomorphism of the Koszul filtration under an isomorphism of modules**:
`π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ Rⁿ π_* 𝒪(-n-1) ⊗ ⋀ⁿ⁺¹ E` corresponds to the same isomorphism for `E'`
under `f` and `⋀ⁿ⁺¹ e`. -/
public theorem koszulTopIso_pullback :
    (koszulTopIso E hqc D hn hfree).hom ≫
        tensorMap ((bundleComparison f hbase n (negTwist E hqc D (n + 1))).hom ≫
          ((bundlePushforward E' hqc').rightDerived n).map (θ (-((n + 1 : ℕ) : ℤ))).hom)
          (Scheme.Modules.exteriorPowerMap e.hom ((n + 1 : ℕ) : ℤ)) =
      (bundleComparison f hbase 0 _).hom ≫
        ((bundlePushforward E' hqc').rightDerived 0).map
          (koszulTermIso f θ (bundlePullbackIso f hbase e) hu 0).hom ≫
        (koszulTopIso E' hqc' D' hn hfree').hom := by
  have := isFiniteLocallyFree_of_rank E hfree
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E (n + 1)
  have := isFiniteLocallyFree_of_rank E' hfree'
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E' (n + 1)
  have hB := directImageComparisonApp_naturality _ _ (Scheme.Modules.pullback f)
    (pushforwardPullbackIso f _ _ hbase) n ((koszulTwistIso E hqc D n).inv ≫
        (@asIso _ _ _ _ (koszulTwistSequence E hqc D n).g
          (isIso_koszulTwistSequence_g E hqc D hfree)).inv ≫
        (koszulMiddleIso E hqc D (n + 1) (n + 1)).hom)
  have hC := projectionFormulaDeltaApp_pullback_iso f _ _ hbase
    (asIso (Scheme.Modules.exteriorPowerMap e.hom ((n + 1 : ℕ) : ℤ))) n (θ (-((n + 1 : ℕ) : ℤ)))
  rw [koszulTopIso_hom, koszulTopIso_hom]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hC).trans
    (Category.assoc _ _ _).symm))).trans ?_
  refine (congrArg (fun φ => _ ≫ φ ≫ _ ≫ _) hB).trans ?_
  exact koszulTopIso_pullback_aux f θ hbase e hu hmul hn hfree hfree'

end Koszul

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
