module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChangeOverBase

/-!
# Morphisms into a vector bundle

Morphisms `T ⟶ V(ℰ) = Spec(Sym ℰ)` over a scheme are classified by module maps out of `ℰ`
(the classifying map of a morphism into a vector bundle), and this classification is compatible
with base change. The maps of pushforward algebras induced by the relative-Spec identifications
are those of `StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChangeOverBase`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec.AlgebraSheaf

section Classifying

variable {X : Scheme.{u}} (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent]

/-- `underlyingModuleMap` preserves composition. -/
private theorem underlyingModuleMap_comp' {A B C : Stacks.RelativeSpec.AlgebraSheaf X}
    (f : A ⟶ B) (g : B ⟶ C) :
    underlyingModuleMap (f ≫ g) = underlyingModuleMap f ≫ underlyingModuleMap g :=
  (underlyingModuleFunctor X).map_comp f g

/-- **The classifying module map of a morphism into a vector bundle.** A morphism
`m : Y ⟶ 𝐕(ℱ)` of schemes over `X` corresponds to the morphism of `𝒪_X`-algebras
`Sym(ℱ) ⟶ (Y ⟶ X)_* 𝒪_Y`, and hence to its restriction `ℱ ⟶ (Y ⟶ X)_* 𝒪_Y` to the generator. -/
def vectorBundleClassifyingMap {Y : Over X} (m : Y ⟶ vectorBundleOver X (F := F)) :
    F ⟶ underlyingModule (pushforwardAlgebra Y.hom) :=
  symmetricAlgebraSheafι F ≫
    underlyingModuleMap ((vectorBundlePushforwardIso X (F := F)).inv ≫ pushforwardAlgebraMap m)

/-- **Morphisms into a vector bundle are determined by their classifying module maps.** -/
theorem vectorBundle_hom_ext {Y : Over X} {m₁ m₂ : Y ⟶ vectorBundleOver X (F := F)}
    (h : vectorBundleClassifyingMap F m₁ = vectorBundleClassifyingMap F m₂) : m₁ = m₂ := by
  have := isAffineHom_vectorBundleOver X (F := F)
  refine eq_of_pushforwardAlgebraMap_eq ?_
  simpa using congrArg ((vectorBundlePushforwardIso X (F := F)).hom ≫ ·)
    (algebraHom_ext (pushforwardAlgebra Y.hom) F h)

/-- The classifying module map of a composite. -/
theorem vectorBundleClassifyingMap_comp {Y Y' : Over X} (k : Y' ⟶ Y)
    (m : Y ⟶ vectorBundleOver X (F := F)) :
    vectorBundleClassifyingMap F (k ≫ m) =
      vectorBundleClassifyingMap F m ≫ underlyingModuleMap (pushforwardAlgebraMap k) := by
  simp only [vectorBundleClassifyingMap, pushforwardAlgebraMap_comp, underlyingModuleMap_comp']
  exact (Category.assoc _ _ _).symm

omit [F.IsQuasicoherent] in
/-- The generator of `Sym(ℱ)` is natural in `ℱ`. -/
theorem symmetricAlgebraSheafι_comp_symmetricAlgebraSheafMap {G : SheafOfModules.{u} X.ringCatSheaf}
    (f : F ⟶ G) :
    symmetricAlgebraSheafι F ≫ underlyingModuleMap (symmetricAlgebraSheafMap X f) =
      f ≫ symmetricAlgebraSheafι G := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show ((symmetricAlgebraSheafMap X f).right.hom.app W).hom
      ((symmetricAlgebra X F).ungradedIncl 1 ((symmetricAlgebraGen X F).val.app W x)) =
    (symmetricAlgebra X G).ungradedIncl 1 ((symmetricAlgebraGen X G).val.app W (f.val.app W x))
  rw [symmetricAlgebraSheafMap_ungradedIncl]
  congr 1
  exact congrArg (fun φ : F ⟶ (symmetricAlgebra X G).piece 1 => φ.val.app W x)
    (symmetricAlgebraGen_comp_symmetricAlgebraUnitalHom X f)

/-- The classifying module map of the morphism of vector bundles induced by `f : ℱ ⟶ 𝒢` is `f`
followed by the generator of `Sym(𝒢)`. -/
theorem vectorBundleClassifyingMap_vectorBundleMap {G : SheafOfModules.{u} X.ringCatSheaf}
    [G.IsQuasicoherent] (f : F ⟶ G) :
    vectorBundleClassifyingMap F (vectorBundleMap X f) =
      f ≫ symmetricAlgebraSheafι G ≫
        underlyingModuleMap (vectorBundlePushforwardIso X (F := G)).inv := by
  rw [vectorBundleClassifyingMap, pushforwardAlgebraMap_vectorBundleMap, Iso.inv_hom_id_assoc,
    underlyingModuleMap_comp']
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (symmetricAlgebraSheafι_comp_symmetricAlgebraSheafMap F f)).trans (Category.assoc _ _ _))

/-- The classifying module map of the morphism of relative spectra induced by a morphism of
algebras `ψ : Sym(ℱ) ⟶ 𝓑`. -/
theorem vectorBundleClassifyingMap_relativeSpecMapOfAlgebraHom
    (B : Stacks.RelativeSpec.AlgebraSheaf X) [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent B]
    (ψ : symmetricAlgebraSheaf X F ⟶ B) :
    vectorBundleClassifyingMap F (relativeSpecMapOfAlgebraHom (symmetricAlgebraSheaf X F) B ψ) =
      symmetricAlgebraSheafι F ≫ underlyingModuleMap (ψ ≫ (pushforwardAlgebraIso B).inv) :=
  congrArg (fun k => symmetricAlgebraSheafι F ≫ underlyingModuleMap k)
    ((congrArg ((vectorBundlePushforwardIso X (F := F)).inv ≫ ·)
      (pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom _ _ ψ)).trans
      (Iso.inv_hom_id_assoc (pushforwardAlgebraIso (symmetricAlgebraSheaf X F)) _))

/-- The classifying module map of a morphism followed by a morphism of vector bundles. -/
theorem vectorBundleClassifyingMap_comp_vectorBundleMap {G : SheafOfModules.{u} X.ringCatSheaf}
    [G.IsQuasicoherent] (f : F ⟶ G) {Y : Over X} (k : Y ⟶ vectorBundleOver X (F := G)) :
    vectorBundleClassifyingMap F (k ≫ vectorBundleMap X f) =
      f ≫ vectorBundleClassifyingMap G k := by
  rw [vectorBundleClassifyingMap_comp, vectorBundleClassifyingMap_vectorBundleMap]
  refine (Category.assoc _ _ _).trans (congrArg (f ≫ ·) ((Category.assoc _ _ _).trans ?_))
  exact congrArg (symmetricAlgebraSheafι G ≫ ·) (underlyingModuleMap_comp' _ _).symm

end Classifying

section BaseChange

variable {T S : Scheme.{u}} (g : T ⟶ S) (M : S.Modules) [_root_.SheafOfModules.IsQuasicoherent M]

/-- **The morphism `𝐕(g^* M) ⟶ 𝐕(M)` over `S`**, the projection of `𝐕(M) ×_S T` read through
`𝐕(M) ×_S T ≅ 𝐕(g^* M)`. -/
def vectorBundlePullbackProjection :
    (Over.map g).obj (vectorBundleOver T (F := (pullback g).obj M)) ⟶
      vectorBundleOver S (F := M) :=
  (Over.map g).map (vectorBundlePullbackOverIso g M).inv ≫
    baseChangeProjection g (vectorBundleOver S (F := M))

/-- The underlying morphism of schemes of `vectorBundlePullbackProjection g M` is the inverse of
`𝐕(M) ×_S T ≅ 𝐕(g^* M)` followed by the first projection of the fibre product. -/
theorem vectorBundlePullbackProjection_left :
    (vectorBundlePullbackProjection g M).left =
      (vectorBundlePullbackIso g M).inv ≫ Limits.pullback.fst (vectorBundleToBase S M) g :=
  rfl

/-- The map of pushforward algebras induced by `vectorBundlePullbackProjection g M`. -/
private theorem pushforwardAlgebraMap_vectorBundlePullbackProjection :
    pushforwardAlgebraMap (vectorBundlePullbackProjection g M) =
      (pushforwardAlgebraIso (symmetricAlgebraSheaf S M)).hom ≫
        algebraLift ((algebraPushforward g).obj
            (symmetricAlgebraSheaf T ((pullback g).obj M))) M
          ((pullbackPushforwardAdjunction g).unit.app M ≫
            (pushforward g).map (symmetricAlgebraSheafι ((pullback g).obj M))) ≫
        (algebraPushforward g).map
          (pushforwardAlgebraIso (symmetricAlgebraSheaf T ((pullback g).obj M))).inv := by
  have : Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      ((algebraPullback g).obj (symmetricAlgebraSheaf S M)) :=
    Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent g _ inferInstance
  have h1 : pushforwardAlgebraMap (vectorBundlePullbackOverIso g M).inv =
      (pullbackAlgebraIso g (symmetricAlgebraSheaf S M)).hom ≫
        (symmetricAlgebraSheafPullbackIso g M).hom ≫
          (pushforwardAlgebraIso (symmetricAlgebraSheaf T ((pullback g).obj M))).inv :=
    have := isAffineHom_vectorBundleOver S (F := M)
    have : IsAffineHom (Limits.pullback.snd (vectorBundleOver S (F := M)).hom g) :=
      isAffineHom_overPullback_hom g _
    (pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso _ _ _).trans (Category.assoc _ _ _)
  have h2 : baseChangeAlgebraHom g (vectorBundleOver S (F := M)) ≫
      pushforwardAlgebraMap (vectorBundlePullbackOverIso g M).inv =
      (algebraPullback g).map (pushforwardAlgebraIso (symmetricAlgebraSheaf S M)).hom ≫
        (symmetricAlgebraSheafPullbackIso g M).hom ≫
          (pushforwardAlgebraIso (symmetricAlgebraSheaf T ((pullback g).obj M))).inv :=
    (congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (baseChangeAlgebraHom_comp_pullbackAlgebraIso_hom g _)))
  refine (homEquiv_baseChangeAlgebraHom_comp g (vectorBundleOver S (F := M))
    (vectorBundlePullbackOverIso g M).inv).symm.trans ((congrArg _ h2).trans ?_)
  exact (Adjunction.homEquiv_naturality_left _ _ _).trans (congrArg (_ ≫ ·)
    ((Adjunction.homEquiv_naturality_right _ _ _).trans
      (congrArg (· ≫ _) (homEquiv_symmetricAlgebraPullbackHom g M))))

/-- **The classifying module map of `𝐕(g^* M) ⟶ 𝐕(M)`** is the unit `M ⟶ g_* g^* M` followed by
the direct image of the generator of `Sym(g^* M)`. -/
theorem vectorBundleClassifyingMap_vectorBundlePullbackProjection :
    vectorBundleClassifyingMap M (vectorBundlePullbackProjection g M) =
      ((pullbackPushforwardAdjunction g).unit.app M :
        M ⟶ (pushforward g).obj ((pullback g).obj M)) ≫
        (pushforward g).map (symmetricAlgebraSheafι ((pullback g).obj M) ≫
          underlyingModuleMap (vectorBundlePushforwardIso T (F := (pullback g).obj M)).inv) := by
  have h4 : (vectorBundlePushforwardIso S (F := M)).inv ≫
      pushforwardAlgebraMap (vectorBundlePullbackProjection g M) =
      algebraLift ((algebraPushforward g).obj
            (symmetricAlgebraSheaf T ((pullback g).obj M))) M
          ((pullbackPushforwardAdjunction g).unit.app M ≫
            (pushforward g).map (symmetricAlgebraSheafι ((pullback g).obj M))) ≫
        (algebraPushforward g).map
          (pushforwardAlgebraIso (symmetricAlgebraSheaf T ((pullback g).obj M))).inv :=
    (congrArg (_ ≫ ·) (pushforwardAlgebraMap_vectorBundlePullbackProjection g M)).trans
      (Iso.inv_hom_id_assoc _ _)
  refine (congrArg (fun k => symmetricAlgebraSheafι M ≫ underlyingModuleMap k) h4).trans ?_
  have h5 := symmetricAlgebraSheafι_comp_algebraLift ((algebraPushforward g).obj
      (symmetricAlgebraSheaf T ((pullback g).obj M))) M
    ((pullbackPushforwardAdjunction g).unit.app M ≫
      (pushforward g).map (symmetricAlgebraSheafι ((pullback g).obj M)))
  have h6 := underlyingModuleMap_comp' (algebraLift ((algebraPushforward g).obj
            (symmetricAlgebraSheaf T ((pullback g).obj M))) M
          ((pullbackPushforwardAdjunction g).unit.app M ≫
            (pushforward g).map (symmetricAlgebraSheafι ((pullback g).obj M))))
        ((algebraPushforward g).map
          (pushforwardAlgebraIso (symmetricAlgebraSheaf T ((pullback g).obj M))).inv)
  have h7 := underlyingModuleMap_algebraPushforward_map g
    (pushforwardAlgebraIso (symmetricAlgebraSheaf T ((pullback g).obj M))).inv
  have h8 := (pushforward g).map_comp (symmetricAlgebraSheafι ((pullback g).obj M))
    (underlyingModuleMap (pushforwardAlgebraIso (symmetricAlgebraSheaf T ((pullback g).obj M))).inv)
  refine (congrArg (symmetricAlgebraSheafι M ≫ ·) h6).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h5).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (_ ≫ ·) ?_
  exact (congrArg (_ ≫ ·) h7).trans h8.symm

/-- **Classifying maps under base change.** For a morphism `m : Y ⟶ 𝐕(g^* M)` of schemes over `T`,
the classifying map of `Y ⟶ 𝐕(g^* M) ⟶ 𝐕(M)` over `S` is the transpose, under `g^* ⊣ g_*`, of the
classifying map of `m`: the unit followed by its direct image. -/
theorem vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection {Y : Over T}
    (m : Y ⟶ vectorBundleOver T (F := (pullback g).obj M)) :
    vectorBundleClassifyingMap M ((Over.map g).map m ≫ vectorBundlePullbackProjection g M) =
      (pullbackPushforwardAdjunction g).unit.app M ≫
        (pushforward g).map (vectorBundleClassifyingMap ((pullback g).obj M) m) := by
  refine (vectorBundleClassifyingMap_comp M _ _).trans ?_
  rw [← algebraPushforward_map_pushforwardAlgebraMap_overMap g m]
  refine (congrArg (· ≫ _)
    (vectorBundleClassifyingMap_vectorBundlePullbackProjection g M)).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (congrArg (_ ≫ ·)
    (underlyingModuleMap_algebraPushforward_map g (pushforwardAlgebraMap m))).trans ?_
  refine ((pushforward g).map_comp _ _).symm.trans (congrArg (pushforward g).map ?_)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact (underlyingModuleMap_comp' _ _).symm

end BaseChange

end AlgebraicGeometry.Scheme.Modules

end
