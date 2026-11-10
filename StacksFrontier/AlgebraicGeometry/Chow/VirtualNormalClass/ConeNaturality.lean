module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ConormalNaturality
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.PairComposition
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeZeroSectionAffineCriterion

/-!
# The normal cone inside the normal bundle, over an arbitrary base change

Let `f ≫ i' = i ≫ g` be a commutative square of closed immersions. The closed immersion
`C_ZX ⟶ N_ZX = 𝐕(𝒞_{Z/X})` of the normal cone into the normal bundle is natural: followed by the
morphism `N_ZX ⟶ N_{Z'}X'` it is the canonical morphism of normal cones `C_ZX ⟶ C_{Z'}X'` followed
by the closed immersion for `i'`. Both sides are read on sections over an arbitrary open, through
the sections of the morphism attached to a relative-spectrum pair over every open of the base
(`Stacks.RelativeSpec.pairToHom_appLE_of_opens`); no affineness of the square is needed.

## Main results

* `Stacks.Conormal.normalConeToNormalBundle_appLE_of_opens` — the closed immersion
  `C_ZX ⟶ N_ZX` on sections over any open.
* `Stacks.Conormal.normalConeMapOfSquare_comp_normalConeToNormalBundle` — its naturality.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.Blowup Stacks.Conormal
  Stacks.SymAlgSheaf

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A composite of morphisms of modules on sections, elementwise. -/
theorem comp_val_app_apply {A B C : X.Modules} (φ : A ⟶ B) (ψ : B ⟶ C) (U : X.Opensᵒᵖ)
    (x : A.val.obj U) :
    ((φ ≫ ψ).val.app U).hom x = (ψ.val.app U).hom ((φ.val.app U).hom x) :=
  rfl

/-- The comparison `f_* g_* ≅ (f ≫ g)_*` is the identity on sections. -/
theorem comp_pushforwardComp_hom_val_app_apply {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) {A : Z.Modules}
    (φ : A ⟶ (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj M))
    (U : Z.Opensᵒᵖ) (x : A.val.obj U) :
    ((φ ≫ ((Scheme.Modules.pushforwardComp f g).app M).hom).val.app U).hom x =
      (φ.val.app U).hom x :=
  rfl

/-- The pushforward of a morphism of modules, on sections. -/
theorem pushforward_map_val_app_apply {Y : Scheme.{u}} (f : X ⟶ Y) {M N : X.Modules}
    (ψ : M ⟶ N) (U : Y.Opens) (x : M.val.obj (op (f ⁻¹ᵁ U))) :
    (((Scheme.Modules.pushforward f).map ψ).val.app (op U)).hom x =
      (ψ.val.app (op (f ⁻¹ᵁ U))).hom x :=
  rfl

/-- **The point of `𝐕(ℱ)` of a base-changed point**: composing a point `u : W ⟶ 𝐕(g^*ℱ)` over
`T` with the base-change morphism `𝐕(g^*ℱ) ⟶ 𝐕(ℱ)` gives the point whose module morphism is the
transpose of that of `u`. -/
theorem vectorBundleHomEquiv_map_comp_vectorBundleBaseChangeOver {T : Scheme.{u}} (g : T ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] [((Scheme.Modules.pullback g).obj F).IsQuasicoherent]
    {W : Over T} (v : W ⟶ vectorBundleOver T (F := (Scheme.Modules.pullback g).obj F)) :
    vectorBundleHomEquiv F ((Over.map g).obj W)
        ((Over.map g).map v ≫ vectorBundleBaseChangeOver g F) =
      transposeEquiv g F W (vectorBundleHomEquiv _ W v) :=
  (vectorBundleHomEquiv_comp F ((Over.map g).map v) (vectorBundleBaseChangeOver g F)).trans
    ((congrArg (· ≫ _) ((vectorBundleHomEquiv F _).apply_symm_apply _)).trans
      ((transposeEquiv_comp g F v _).symm.trans
        (congrArg (transposeEquiv g F W) ((vectorBundleHomEquiv_comp _ v (𝟙 _)).symm.trans
          (congrArg _ (Category.comp_id v))))))

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.RelativeSpec.AlgebraSheaf

/-- The module morphism underlying a morphism of algebra sheaves, on sections, is the morphism
of rings. -/
theorem underlyingModuleMap_val_app_apply {X : Scheme.{u}} {A B : AlgebraSheaf X} (φ : A ⟶ B)
    (U : X.Opensᵒᵖ) (x : (underlyingModule A).val.obj U) :
    ((underlyingModuleMap φ).val.app U).hom x = (φ.right.hom.app U).hom x :=
  rfl

end Stacks.RelativeSpec.AlgebraSheaf

namespace Stacks.Conormal

section Bundle

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The canonical morphism `C_ZX ⟶ N_ZX`, read on sections over any open `U` of `Z`**: the
universal algebra map of `Sym(𝒞_{Z/X})` followed by the sections of the morphism is the sections
of the canonical map of algebra sheaves followed by the universal algebra map of `𝒞_{Z/X,*}`. Over
an affine open this is `Stacks.Conormal.normalConeToNormalBundle_appLE`. -/
theorem normalConeToNormalBundle_appLE_of_opens (U : Z.Opens)
    (h : normalConeToBase i ⁻¹ᵁ U ≤
      normalConeToNormalBundle i ⁻¹ᵁ
        (Scheme.Modules.vectorBundleToBase Z (conormalSheafDegreeOne i) ⁻¹ᵁ U)) :
    (Stacks.RelativeSpec.universalAlgebraMap (normalBundleSituation i)).right.app (op U) ≫
        (normalConeToNormalBundle i).appLE
          (Scheme.Modules.vectorBundleToBase Z (conormalSheafDegreeOne i) ⁻¹ᵁ U)
          (normalConeToBase i ⁻¹ᵁ U) h =
      (conormalSymmetricAlgebraSheafHom i).right.hom.app (op U) ≫
        (Stacks.RelativeSpec.universalAlgebraMap
          ((normalBundleSituation i).withAlgebra (conormalAlgebraSheaf i)
              (isQuasicoherent_conormalAlgebraSheaf i))).right.app
            (op U) :=
  Stacks.RelativeSpec.pairToHom_appLE_of_opens (s := normalBundleSituation i)
    (Stacks.RelativeSpec.algebraHomPair (normalBundleSituation i) (conormalAlgebraSheaf i)
      (isQuasicoherent_conormalAlgebraSheaf i) (conormalSymmetricAlgebraSheafHom i)) U h

/-- The normal cone `C_ZX` as a scheme over `Z`. -/
abbrev normalConeOver : Over Z := Over.mk (normalConeToBase i)

/-- The canonical morphism `C_ZX ⟶ N_ZX` as a morphism of schemes over `Z`. -/
def normalConeToNormalBundleOver :
    normalConeOver i ⟶ Scheme.Modules.vectorBundleOver Z (F := conormalSheafDegreeOne i) :=
  Over.homMk (normalConeToNormalBundle i) (normalConeToNormalBundle_toBase i)

/-- **The module morphism `𝒞_{Z/X} ⟶ π_* 𝒪_{C_ZX}` of the canonical morphism `C_ZX ⟶ N_ZX`** is
the inclusion of the degree-one part of the conormal algebra: on a local section `y` of
`𝒞_{Z/X}` over any open `V` it is the image `coneIncl i 1 V y` of `y` in `Γ(C_ZX, π⁻¹V)`. -/
theorem vectorBundleHomEquiv_normalConeToNormalBundleOver_app (V : Z.Opens)
    (y : (conormalSheafDegreeOne i).val.obj (op V)) :
    ((Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i) (normalConeOver i)
        (normalConeToNormalBundleOver i)).val.app (op V)) y =
      Stacks.Deformation.coneIncl i 1 V y := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver Z (F := conormalSheafDegreeOne i)
  refine (congrArg (fun φ : conormalSheafDegreeOne i ⟶
      Scheme.Modules.structurePushforward (normalConeOver i).hom => (φ.val.app (op V)) y)
    (Scheme.Modules.vectorBundleHomEquiv_apply (conormalSheafDegreeOne i) (normalConeOver i)
      (normalConeToNormalBundleOver i))).trans ?_
  refine (Stacks.RelativeSpec.ungradedAlgebraSheafModuleHomEquiv_apply_val_app _ _ _ _ _ _ V
    y).trans ?_
  have hle : (normalConeOver i).hom ⁻¹ᵁ V ≤ (normalConeToNormalBundleOver i).left ⁻¹ᵁ
      ((Scheme.Modules.vectorBundleOver Z (F := conormalSheafDegreeOne i)).hom ⁻¹ᵁ V) :=
    preimage_le_preimage_preimage _ _
  have hpA := pushforwardAlgebraMap_app (normalConeToNormalBundleOver i) V hle
  have hN := normalConeToNormalBundle_appLE_of_opens i V hle
  have hB := Stacks.RelativeSpec.ungradedToGradedRight_ungradedAlgebraSheafIncl Z
    (Scheme.Modules.symmetricAlgebra Z (conormalSheafDegreeOne i))
    (Scheme.Modules.symmetricAlgebra_mul_comm Z (conormalSheafDegreeOne i)) 1 V
    ((Scheme.Modules.symmetricAlgebraGen Z (conormalSheafDegreeOne i)).val.app (op V) y)
  have hS := SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap (conormalSymmetricHom i)
    (X := op V) 1 ((Scheme.Modules.symmetricAlgebraGen Z (conormalSheafDegreeOne i)).val.app
      (op V) y)
  have hgen : ((conormalSymmetricHom i).app 1).val.app (op V)
      ((Scheme.Modules.symmetricAlgebraGen Z (conormalSheafDegreeOne i)).val.app (op V) y) = y :=
    congrArg (fun φ : conormalSheafDegreeOne i ⟶ conormalSheafDegreeOne i => φ.val.app (op V) y)
      (conormalSymmetricHom_gen i)
  have e1 : ((Scheme.Modules.symmetricAlgebraSheafComparison (conormalSheafDegreeOne i)).hom ≫
      (Scheme.Modules.vectorBundlePushforwardIso Z (F := conormalSheafDegreeOne i)).inv ≫
        pushforwardAlgebraMap (normalConeToNormalBundleOver i)).right.hom.app (op V) =
      (Scheme.Modules.symmetricAlgebraSheafComparison (conormalSheafDegreeOne i)).hom.right.hom.app
        (op V) ≫
      (Scheme.Modules.vectorBundlePushforwardIso Z
        (F := conormalSheafDegreeOne i)).inv.right.hom.app
        (op V) ≫ (pushforwardAlgebraMap (normalConeToNormalBundleOver i)).right.hom.app (op V) :=
    rfl
  have hB' : ((Scheme.Modules.symmetricAlgebraSheafComparison
      (conormalSheafDegreeOne i)).hom.right.hom.app (op V)).hom
      (Stacks.RelativeSpec.ungradedAlgebraSheafIncl Z
        (Scheme.Modules.symmetricAlgebra Z (conormalSheafDegreeOne i))
        (Scheme.Modules.symmetricAlgebra_mul_comm Z (conormalSheafDegreeOne i)) 1 V
        ((Scheme.Modules.symmetricAlgebraGen Z (conormalSheafDegreeOne i)).val.app (op V) y)) =
      (Scheme.Modules.symmetricAlgebra Z (conormalSheafDegreeOne i)).ungradedIncl 1
        ((Scheme.Modules.symmetricAlgebraGen Z (conormalSheafDegreeOne i)).val.app (op V) y) := hB
  have key : ((Scheme.Modules.symmetricAlgebraSheafComparison (conormalSheafDegreeOne i)).hom ≫
      (Scheme.Modules.vectorBundlePushforwardIso Z (F := conormalSheafDegreeOne i)).inv ≫
        pushforwardAlgebraMap (normalConeToNormalBundleOver i)).right.hom.app (op V) =
      (Scheme.Modules.symmetricAlgebraSheafComparison (conormalSheafDegreeOne i)).hom.right.hom.app
        (op V) ≫ (conormalSymmetricAlgebraSheafHom i).right.hom.app (op V) ≫
        (Stacks.RelativeSpec.universalAlgebraMap
          ((normalBundleSituation i).withAlgebra (conormalAlgebraSheaf i)
              (isQuasicoherent_conormalAlgebraSheaf i))).right.app (op V) := by
    refine e1.trans (congrArg (fun k => (Scheme.Modules.symmetricAlgebraSheafComparison
      (conormalSheafDegreeOne i)).hom.right.hom.app (op V) ≫ k) ?_)
    refine (congrArg (fun k => (Scheme.Modules.vectorBundlePushforwardIso Z
      (F := conormalSheafDegreeOne i)).inv.right.hom.app (op V) ≫ k) hpA).trans ?_
    exact hN
  refine (ConcreteCategory.congr_hom key _).trans ?_
  refine (congrArg (fun z => ((Stacks.RelativeSpec.universalAlgebraMap
          ((normalBundleSituation i).withAlgebra (conormalAlgebraSheaf i)
              (isQuasicoherent_conormalAlgebraSheaf i))).right.app (op V)).hom
      (((conormalSymmetricAlgebraSheafHom i).right.hom.app (op V)).hom z)) hB').trans ?_
  refine (congrArg (fun z => ((Stacks.RelativeSpec.universalAlgebraMap
          ((normalBundleSituation i).withAlgebra (conormalAlgebraSheaf i)
              (isQuasicoherent_conormalAlgebraSheaf i))).right.app (op V)).hom z) hS).trans ?_
  rw [hgen]
  exact (congrArg _ (Stacks.RelativeSpec.ungradedToGradedRight_ungradedAlgebraSheafIncl Z
    (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int 1 V y)).symm

end Bundle

section Square

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i]
  [IsClosedImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X') (comm : f ≫ i' = i ≫ g)

/-- The canonical morphism of normal cones over a commutative square, as a morphism of schemes
over `Z'`. -/
def normalConeMapOfSquareOver : (Over.map f).obj (normalConeOver i) ⟶ normalConeOver i' :=
  Over.homMk (normalConeMapOfSquare i i' f g comm) (normalConeMapOfSquare_toBase i i' f g comm)

/-- The canonical map `f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of Stacks 0634 in degree one, with source and
target spelled as degree-one pieces of the conormal algebras. -/
abbrev canonicalPullbackHomOne :
    (Scheme.Modules.pullback f).obj (conormalSheafDegreeOne i') ⟶ conormalSheafDegreeOne i :=
  (AlgebraicGeometry.canonicalPullbackHom i i' f g comm).hom 1

/-- The canonical morphism of Stacks 0634 into the pushforward, on sections. -/
theorem canonicalPushforwardHom_val_app_apply (n : ℤ) (W : Z'.Opens)
    (a : (conormalPiece i' n).val.obj (op W)) :
    ((AlgebraicGeometry.canonicalPushforwardHom i i' f g comm n).val.app (op W)).hom a =
      (conormalAlgebraHom i i' f g comm).hom.map n (f ⁻¹ᵁ W) W le_rfl a :=
  rfl

/-- **The degree-one inclusions of the conormal algebras are natural**: for a commutative square
of closed immersions, the inclusion `𝒞_{Z'/X'} ⟶ π'_* 𝒪_{C_{Z'}X'}` followed by the canonical
morphism of normal cones is the transpose of the canonical map `f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of
Stacks 0634 followed by the inclusion `𝒞_{Z/X} ⟶ π_* 𝒪_{C_ZX}`. -/
theorem transposeEquiv_canonicalPullbackHom_comp :
    Scheme.Modules.transposeEquiv f (conormalSheafDegreeOne i') (normalConeOver i)
        ((AlgebraicGeometry.canonicalPullbackHom i i' f g comm).hom 1 ≫
          Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i) (normalConeOver i)
            (normalConeToNormalBundleOver i)) =
      Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i') (normalConeOver i')
          (normalConeToNormalBundleOver i') ≫
        AlgebraSheaf.underlyingModuleMap
          (pushforwardAlgebraMap (normalConeMapOfSquareOver i i' f g comm)) := by
  have h1 : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((AlgebraicGeometry.canonicalPullbackHom i i' f g comm).hom 1 ≫
        Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i) (normalConeOver i)
          (normalConeToNormalBundleOver i)) =
      AlgebraicGeometry.canonicalPushforwardHom i i' f g comm 1 ≫
        (Scheme.Modules.pushforward f).map
          (Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i) (normalConeOver i)
            (normalConeToNormalBundleOver i)) :=
    (Adjunction.homEquiv_naturality_right _ _ _).trans
      (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _))
  refine ((Scheme.Modules.transposeEquiv_apply f (conormalSheafDegreeOne i') (normalConeOver i)
    _).trans (congrArg (· ≫ _) h1)).trans ?_
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ (fun V : Z'.affineOpens => V.1)
    (by rw [Subtype.range_coe]; exact Z'.isBasis_affineOpens) _ _ fun V => ?_
  beta_reduce
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  have hle : ((Over.map f).obj (normalConeOver i)).hom ⁻¹ᵁ V.1 ≤
      (normalConeMapOfSquareOver i i' f g comm).left ⁻¹ᵁ ((normalConeOver i').hom ⁻¹ᵁ V.1) :=
    preimage_le_preimage_preimage _ _
  have hpA := pushforwardAlgebraMap_app (normalConeMapOfSquareOver i i' f g comm) V.1 hle
  have hL := vectorBundleHomEquiv_normalConeToNormalBundleOver_app i (f ⁻¹ᵁ V.1)
    ((conormalAlgebraHom i i' f g comm).hom.map 1 (f ⁻¹ᵁ V.1) V.1 le_rfl a)
  have hR := vectorBundleHomEquiv_normalConeToNormalBundleOver_app i' V.1 a
  have hsq := Stacks.Deformation.normalConeMapOfSquare_appLE_coneIncl i i' f g comm V 1 a hle
  refine (Scheme.Modules.comp_pushforwardComp_hom_val_app_apply (normalConeOver i).hom f
    (SheafOfModules.unit _)
    (AlgebraicGeometry.canonicalPushforwardHom i i' f g comm 1 ≫
        (Scheme.Modules.pushforward f).map
          (Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i) (normalConeOver i)
            (normalConeToNormalBundleOver i))) _ a).trans ?_
  refine (Scheme.Modules.comp_val_app_apply
    (AlgebraicGeometry.canonicalPushforwardHom i i' f g comm 1)
    ((Scheme.Modules.pushforward f).map
          (Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i) (normalConeOver i)
            (normalConeToNormalBundleOver i))) _ a).trans ?_
  refine (Scheme.Modules.pushforward_map_val_app_apply f _ V.1 _).trans ?_
  refine (congrArg _ (canonicalPushforwardHom_val_app_apply i i' f g comm 1 V.1 a)).trans ?_
  refine (hL.trans hsq.symm).trans ?_
  refine Eq.trans ?_ (Scheme.Modules.comp_val_app_apply
    (Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i') (normalConeOver i')
      (normalConeToNormalBundleOver i'))
    (AlgebraSheaf.underlyingModuleMap
      (pushforwardAlgebraMap (normalConeMapOfSquareOver i i' f g comm))) _ a).symm
  refine Eq.trans ?_ (AlgebraSheaf.underlyingModuleMap_val_app_apply
    (pushforwardAlgebraMap (normalConeMapOfSquareOver i i' f g comm)) (op V.1)
    (((Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i') (normalConeOver i')
      (normalConeToNormalBundleOver i')).val.app (op V.1)).hom a)).symm
  refine Eq.trans ?_ (ConcreteCategory.congr_hom hpA.symm _)
  exact congrArg _ hR.symm

/-- **The canonical morphism `C_ZX ⟶ N_ZX` is natural under a commutative square of closed
immersions**: followed by the morphism of normal cones, it is `C_ZX ⟶ N_ZX` followed by the
morphism `N_ZX = 𝐕(𝒞_{Z/X}) ⟶ 𝐕(f^*𝒞_{Z'/X'}) = N_{Z'}X' ×_{Z'} Z ⟶ N_{Z'}X'` induced by the
canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of Stacks 0634. -/
theorem normalConeMapOfSquare_comp_normalConeToNormalBundle :
    haveI := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback f
      (conormalSheafDegreeOne i')
    normalConeMapOfSquare i i' f g comm ≫ normalConeToNormalBundle i' =
      normalConeToNormalBundle i ≫
        (Scheme.Modules.vectorBundleMap Z
          (canonicalPullbackHomOne i i' f g comm)).left ≫
          Scheme.Modules.vectorBundleBaseChangeMap f (conormalSheafDegreeOne i') := by
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback f
    (conormalSheafDegreeOne i')
  have key : normalConeMapOfSquareOver i i' f g comm ≫ normalConeToNormalBundleOver i' =
      (Over.map f).map (normalConeToNormalBundleOver i ≫ Scheme.Modules.vectorBundleMap Z
          (canonicalPullbackHomOne i i' f g comm)) ≫
        Scheme.Modules.vectorBundleBaseChangeOver f (conormalSheafDegreeOne i') := by
    apply (Scheme.Modules.vectorBundleHomEquiv (conormalSheafDegreeOne i')
      ((Over.map f).obj (normalConeOver i))).injective
    refine (Scheme.Modules.vectorBundleHomEquiv_comp (conormalSheafDegreeOne i')
      (normalConeMapOfSquareOver i i' f g comm) (normalConeToNormalBundleOver i')).trans ?_
    refine (transposeEquiv_canonicalPullbackHom_comp i i' f g comm).symm.trans ?_
    refine Eq.trans ?_ (Scheme.Modules.vectorBundleHomEquiv_map_comp_vectorBundleBaseChangeOver f
      (conormalSheafDegreeOne i') _).symm
    exact congrArg (Scheme.Modules.transposeEquiv f (conormalSheafDegreeOne i')
      (normalConeOver i)) (Scheme.Modules.vectorBundleHomEquiv_comp_vectorBundleMap
        (canonicalPullbackHomOne i i' f g comm) (normalConeOver i)
        (normalConeToNormalBundleOver i)).symm
  have hl := congrArg (fun φ => φ.left) key
  refine hl.trans ?_
  change (normalConeToNormalBundle i ≫ (Scheme.Modules.vectorBundleMap Z
          (canonicalPullbackHomOne i i' f g comm)).left) ≫
      (Scheme.Modules.vectorBundleBaseChangeOver f (conormalSheafDegreeOne i')).left = _
  exact (Category.assoc _ _ _).trans (congrArg (normalConeToNormalBundle i ≫ ·)
    (congrArg (_ ≫ ·) (Scheme.Modules.vectorBundleBaseChangeMap_eq f _).symm))

end Square

end Stacks.Conormal

end
