module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernelOfFunctor
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.GluedKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAffineBase
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaSections
public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Equivalence
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward

/-!
# Base change and projection formula at the morphisms of a triple fibre product

Let `R` be a ring and `X`, `Y`, `Z` schemes over `R`.  The composition formula of Tag 0GPC
compares `F_L ∘ F_K` with the integral transform of the convolution of the kernels through three
comparison morphisms on the triple fibre product `X ×_R Y ×_R Z`: base change (Tag 02KG) along the
square relating `pr_{12}` and `pr_{23}`, and the projection formula (Tag 0FZE) at `pr_{23}` and at
`pr_{13}`.  None of the morphisms involved is affine unless `X` and `Y` are, and none of the
comparisons is invertible on all quasi-coherent modules.  This file proves that they are
invertible on the modules that occur.

## Main definitions

* `AlgebraicGeometry.pr23ComparisonNatTrans`: the composite of the base change along the square
  relating `pr_{12}` and `pr_{23}` and of the projection formula at `pr_{23}`.
* `AlgebraicGeometry.pullbackTargetFunctor`: `M ↦ q_* h_*(G ⊗ h^* p^* M)`, the target of the
  projection-formula morphism of `h : T ⟶ X ×_R Z` at `p^*M`, pushed forward to `Z`.

## Main results

* `AlgebraicGeometry.isIso_of_isIso_pushforward_map`: direct image along an affine morphism
  reflects isomorphisms of quasi-coherent modules.
* `AlgebraicGeometry.isIso_baseChangeNatTrans_app_pushforward_ι` and
  `AlgebraicGeometry.isIso_projectionFormulaMap_pushforward_ι`: base change and the projection
  formula hold at a direct image from an open whose inclusion and whose composite with the
  morphism are affine.
* `AlgebraicGeometry.isIso_pr23ComparisonNatTrans_app`: the comparison at `pr_{23}` is invertible
  when `X` is quasi-compact with affine diagonal and the integral transform of `L` is left exact.
* `AlgebraicGeometry.isIso_projectionFormulaMap_pullback`: the projection formula at a
  quasi-compact quasi-separated `h : T ⟶ X ×_R Z` holds at `p^*M` for every quasi-coherent `M`,
  when `X` has affine diagonal and `pullbackTargetFunctor h G` is right exact on direct images
  from the affine opens of `X`.

## References

* [Stacks Project, Tag 0GPC](https://stacks.math.columbia.edu/tag/0GPC)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)
open Stacks.AlgebraicGeometry.ProjectionFormula (projectionFormulaMap)

universe u

namespace AlgebraicGeometry

section Generic

/-- Direct image along an affine morphism reflects isomorphisms of quasi-coherent modules. -/
theorem isIso_of_isIso_pushforward_map {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    {M N : X.Modules} (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) (φ : M ⟶ N)
    (h : IsIso ((Scheme.Modules.pushforward f).map φ)) : IsIso φ := by
  let F := Stacks.AlgebraicGeometry.AffineQcohEquivalence.affineQuasicoherentPushforward f
  have : F.IsEquivalence :=
    Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward f
  let φ' : (⟨M, hM⟩ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
      ⟨N, hN⟩ := ObjectProperty.homMk φ
  have h1 : IsIso ((SheafOfModules.toSheaf _).map (F.map φ').hom) :=
    ((SheafOfModules.toSheaf S.ringCatSheaf).mapIso
      (@asIso (SheafOfModules S.ringCatSheaf) _ _ _ ((Scheme.Modules.pushforward f).map φ)
        h)).isIso_hom
  have h2 : IsIso (F.map φ').hom := isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  have h3 : IsIso (F.map φ') := by
    have : IsIso ((ObjectProperty.ι _).map (F.map φ')) := h2
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  have h4 : IsIso φ' := isIso_of_reflects_iso φ' F
  exact Functor.map_isIso (ObjectProperty.ι _) φ'

/-- Direct image along an affine morphism reflects the colimit of a parallel pair of
quasi-coherent modules with quasi-coherent cocone point. -/
def isColimitOfIsColimitMapCoconePushforward {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    {D : WalkingParallelPair ⥤ X.Modules} (h₀ : (D.obj .zero).IsQuasicoherent)
    (h₁ : (D.obj .one).IsQuasicoherent) {c : Cocone D} (hc : c.pt.IsQuasicoherent)
    (hfc : IsColimit ((Scheme.Modules.pushforward f).mapCocone c)) : IsColimit c := by
  have hκ := colimit.isColimit D
  have : PreservesColimit D (Scheme.Modules.pushforward f) :=
    Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_walkingParallelPair f D h₀ h₁
  have hfκ := isColimitOfPreserves (Scheme.Modules.pushforward f) hκ
  have hκq : (colimit.cocone D).pt.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
      (fun j => match j with
        | .zero => h₀
        | .one => h₁) hκ
  have e : (Scheme.Modules.pushforward f).map (hκ.desc c) =
      (IsColimit.coconePointUniqueUpToIso hfκ hfc).hom := by
    refine hfκ.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    change (Scheme.Modules.pushforward f).map _ ≫ (Scheme.Modules.pushforward f).map _ = _
    rw [← Functor.map_comp, hκ.fac]
    rfl
  have : IsIso ((Scheme.Modules.pushforward f).map (hκ.desc c)) := by rw [e]; infer_instance
  have : IsIso (hκ.desc c) := isIso_of_isIso_pushforward_map f hκq hc _ this
  exact IsColimit.ofPointIso hκ

/-- A morphism sandwiched between isomorphisms, followed by a further isomorphism, is invertible
as soon as the whole composite is. -/
theorem isIso_of_isIso_comp_sandwich {C : Type*} [Category C] {A B B' D E : C} (a : A ⟶ B)
    (x : B ⟶ B') (b : B' ⟶ D) (c : D ⟶ E) (ha : IsIso a) (hb : IsIso b) (hc : IsIso c)
    (h : IsIso (a ≫ (x ≫ b) ≫ c)) : IsIso x := by
  have h1 : IsIso ((x ≫ b) ≫ c) := IsIso.of_isIso_comp_left a _
  have h2 : IsIso (x ≫ b) := IsIso.of_isIso_comp_right _ c
  exact IsIso.of_isIso_comp_right x b

/-- For a cartesian square `g' : X' ⟶ X`, `f' : X' ⟶ S'` over `f : X ⟶ S`, `g : S' ⟶ S` and an
open `W ⊆ X` whose inclusion and whose composite with `f` are affine, the base-change morphism of
Tag 02KG is invertible at `(W ↪ X)_* N` for every quasi-coherent `N` on `W`, although `f` itself
need not be affine. -/
theorem isIso_baseChangeNatTrans_app_pushforward_ι {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g) (W : X.Opens)
    [IsAffineHom W.ι] [IsAffineHom (W.ι ≫ f)] (N : W.toScheme.Modules)
    (hN : N.IsQuasicoherent) :
    IsIso ((baseChangeNatTrans sq.w).app ((Scheme.Modules.pushforward W.ι).obj N)) := by
  have hsq₂ : IsPullback (g' ∣_ W) (g' ⁻¹ᵁ W).ι W.ι g' := isPullback_morphismRestrict g' W
  have hsq : IsPullback (g' ∣_ W) ((g' ⁻¹ᵁ W).ι ≫ f') (W.ι ≫ f) g := hsq₂.paste_vert sq
  have := hN
  have e := congrArg (fun τ => τ.app N) (baseChangeNatTrans_vpaste' sq.w hsq₂.w hsq.w rfl)
  have h1 : IsIso ((baseChangeNatTrans hsq.w).app N) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsq N
  have h2 : IsIso ((baseChangeNatTrans hsq₂.w).app N) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsq₂ N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at e
  rw [e] at h1
  have h3 : IsIso ((Scheme.Modules.pushforward f').map ((baseChangeNatTrans hsq₂.w).app N)) :=
    Functor.map_isIso _ _
  exact isIso_of_isIso_comp_sandwich _ _ _ _ inferInstance h3 inferInstance h1

/-- A morphism between two isomorphisms is invertible as soon as the composite is. -/
theorem isIso_of_isIso_comp_comp {C : Type*} [Category C] {A B B' D : C} (a : A ⟶ B)
    (x : B ⟶ B') (c : B' ⟶ D) (ha : IsIso a) (hc : IsIso c) (h : IsIso (a ≫ x ≫ c)) :
    IsIso x := by
  have h1 : IsIso (x ≫ c) := IsIso.of_isIso_comp_left a _
  exact IsIso.of_isIso_comp_right x c

/-- A morphism `x` with `a ≫ x ≫ y = z` for isomorphisms `a`, `y`, `z` is invertible. -/
theorem isIso_of_comp_eq {C : Type*} [Category C] {A B B' D : C} (a : A ⟶ B) (x : B ⟶ B')
    (y : B' ⟶ D) (z : A ⟶ D) (ha : IsIso a) (hy : IsIso y) (hz : IsIso z)
    (h : a ≫ x ≫ y = z) : IsIso x := by
  rw [← h] at hz
  exact isIso_of_isIso_comp_comp a x y ha hy hz

/-- For a morphism `k : T ⟶ S` and an open `W ⊆ T` whose inclusion and whose composite with `k`
are affine, the projection-formula morphism of Tag 0FZE for `k` is invertible at `(W ↪ T)_* G`
for quasi-coherent `G` on `W` and `H` on `S`, although `k` itself need not be affine. -/
theorem isIso_projectionFormulaMap_pushforward_ι {T S : Scheme.{u}} (k : T ⟶ S) (W : T.Opens)
    [IsAffineHom W.ι] [IsAffineHom (W.ι ≫ k)] (G : W.toScheme.Modules) (hG : G.IsQuasicoherent)
    (H : S.Modules) (hH : H.IsQuasicoherent) :
    IsIso (projectionFormulaMap k ((Scheme.Modules.pushforward W.ι).obj G) H) := by
  have e := NatTrans.congr_app (projectionFormulaSourceNatTrans_comp_whisker W.ι k H) G
  have e' : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.obj (H))).map
        ((Scheme.Modules.pushforwardComp W.ι k).inv.app G) ≫
      (projectionFormulaSourceNatTrans k H).app ((Scheme.Modules.pushforward W.ι).obj G) ≫
        ((Scheme.Modules.pushforward k).map
            ((projectionFormulaSourceNatTrans W.ι ((Scheme.Modules.pullback k).obj H)).app G) ≫
          (Scheme.Modules.pushforward k).map ((Scheme.Modules.pushforward W.ι).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                (W.toScheme.toRingedSpace).sheaf).flip.map
              ((Scheme.Modules.pullbackComp W.ι k).hom.app H)).app G))) =
      (projectionFormulaSourceNatTrans (W.ι ≫ k) H).app G ≫
        (Scheme.Modules.pushforwardComp W.ι k).inv.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (W.toScheme.toRingedSpace).sheaf).flip.obj
                (((Scheme.Modules.pullback (W.ι ≫ k)).obj H)))).obj G) := e
  have hk : IsIso ((projectionFormulaSourceNatTrans (W.ι ≫ k) H).app G) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap (W.ι ≫ k) G H hG hH
  have hι : IsIso ((projectionFormulaSourceNatTrans W.ι ((Scheme.Modules.pullback k).obj H)).app
      G) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap W.ι G _ hG
      (Stacks.Modules.isQuasicoherent_pullback k H hH)
  have hψ := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    W.toScheme.toRingedSpace.sheaf).obj G).mapIso
      ((Scheme.Modules.pullbackComp W.ι k).app H)).isIso_hom
  suffices key : IsIso (C := S.Modules)
      ((projectionFormulaSourceNatTrans k H).app ((Scheme.Modules.pushforward W.ι).obj G)) from
    key
  refine isIso_of_comp_eq _ _ _ _ ?_ ?_ ?_ e'
  · exact ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (S.toRingedSpace).sheaf).flip.obj (H))).mapIso
      ((Scheme.Modules.pushforwardComp W.ι k).app G).symm).isIso_hom
  · have hy1 := @Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pushforward k) _ hι
    have hy2 := @Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pushforward W.ι) _ hψ
    have hy3 := @Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pushforward k) _ hy2
    exact IsIso.comp_isIso' hy1 hy3
  · exact IsIso.comp_isIso' hk ((Scheme.Modules.pushforwardComp W.ι k).app _).symm.isIso_hom

/-! ### The projection formula in the target variable -/

/-- The projection-formula morphism of Tag 0FZE, as a natural transformation in the module on
the target of `h`. -/
def projectionFormulaTargetNatTrans {T S : Scheme.{u}} (h : T ⟶ S) (G : T.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} (S).toRingedSpace.sheaf).obj
        (((Scheme.Modules.pushforward h).obj G))) ⟶
      Scheme.Modules.pullback h ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} (T).toRingedSpace.sheaf).obj
          (G)) ⋙
          Scheme.Modules.pushforward h where
  app H := Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap h G H
  naturality _ _ k := projectionFormulaMap_naturality_target h G k

end Generic

/-! ### The base change and the projection formula at `pr_{23}`, at direct images from opens -/

/-- The inclusion of the preimage of an open is affine when that of the open is, being a base
change of it. -/
theorem isAffineHom_preimage_ι {A B : Scheme.{u}} (f : A ⟶ B) (W : B.Opens) [IsAffineHom W.ι] :
    IsAffineHom (f ⁻¹ᵁ W).ι :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_morphismRestrict f W)
    inferInstance

/-- In a cartesian square, the restriction of the left leg over an open `W` whose composite with
the bottom leg is affine again has affine composite with the right leg. -/
private theorem isAffineHom_preimage_ι_comp {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g) (W : X.Opens)
    [IsAffineHom (W.ι ≫ f)] : IsAffineHom ((g' ⁻¹ᵁ W).ι ≫ f') :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((isPullback_morphismRestrict g' W).paste_vert sq) inferInstance

section Triple

variable (R : Type u) [CommRing R] (X Y Z : Over (Spec (.of R)))

/-- The open `pr_1^{-1}(U)` of `X ×_R Y` over an open `U ⊆ X`. -/
abbrev fstOpen (U : X.left.Opens) : (pullback X.hom Y.hom).Opens :=
  pullback.fst X.hom Y.hom ⁻¹ᵁ U

variable {R X Y Z}

/-- The inclusion of `pr_1^{-1}(U)` is affine when that of `U` is, being a base change of it. -/
theorem isAffineHom_fstOpen_ι (U : X.left.Opens) [IsAffineHom U.ι] :
    IsAffineHom (fstOpen R X Y U).ι :=
  isAffineHom_preimage_ι _ U

/-- The square `pr_1^{-1}(U) ⟶ U`, `pr_1^{-1}(U) ⟶ Y` over `U ⟶ Spec R`, `Y ⟶ Spec R` is
cartesian. -/
theorem isPullback_fstOpen (U : X.left.Opens) :
    IsPullback (pullback.fst X.hom Y.hom ∣_ U) ((fstOpen R X Y U).ι ≫ pullback.snd X.hom Y.hom)
      (U.ι ≫ X.hom) Y.hom :=
  (isPullback_morphismRestrict (pullback.fst X.hom Y.hom) U).paste_vert
    (IsPullback.of_hasPullback X.hom Y.hom)

/-- `pr_1^{-1}(U) ⟶ Y` is affine for an affine open `U ⊆ X`, being a base change of
`U ⟶ Spec R`. -/
theorem isAffineHom_fstOpen_ι_snd (U : X.left.Opens) (hU : IsAffineOpen U) :
    IsAffineHom ((fstOpen R X Y U).ι ≫ pullback.snd X.hom Y.hom) :=
  have : IsAffine U.toScheme := hU
  isAffineHom_preimage_ι_comp (IsPullback.of_hasPullback X.hom Y.hom) U

/-- The comparison at `pr_{23}`: for a module `L` on `Y ×_R Z` and a module `N` on
`X ×_R Y`, the composite of the base-change morphism of Tag 02KG along the cartesian square
relating `pr_{12}` and `pr_{23}` and of the projection-formula morphism of Tag 0FZE at `pr_{23}`,

`t_*(s^* b_* N ⊗ L) ⟶ t_*(pr_{23,*} pr_{12}^* N ⊗ L) ⟶ t_* pr_{23,*}(pr_{12}^* N ⊗ pr_{23}^* L)`,

where `b : X ×_R Y ⟶ Y`, `s : Y ×_R Z ⟶ Y` and `t : Y ×_R Z ⟶ Z` are the projections. -/
def pr23ComparisonNatTrans (L : (pullback Y.hom Z.hom).Modules) :
    Scheme.Modules.pushforward (pullback.snd X.hom Y.hom) ⋙
        Scheme.Modules.pullback (pullback.fst Y.hom Z.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          (pullback Y.hom Z.hom).toRingedSpace.sheaf).obj (L)) ⋙
        Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom) ⟶
      Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).sheaf).flip.obj
            (((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L))) ⋙
        Scheme.Modules.pushforward (fourierMukaiPr23 X.hom Y.hom Z.hom) ⋙
        Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom) :=
  Functor.whiskerRight (baseChangeNatTrans (isPullback_fourierMukaiPr12_pr23 X.hom Y.hom Z.hom).w)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          (pullback Y.hom Z.hom).toRingedSpace.sheaf).obj (L)) ⋙
        Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom)) ≫
    Functor.whiskerLeft (Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom) ⋙
        Scheme.Modules.pushforward (fourierMukaiPr23 X.hom Y.hom Z.hom))
      (Functor.whiskerRight ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
          ((pullback Y.hom Z.hom)).presheaf ((pullback Y.hom Z.hom)).ringCatSheaf.2 (L))).hom
        (Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom))) ≫
    Functor.whiskerLeft (Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom))
      (Functor.whiskerRight (projectionFormulaSourceNatTrans (fourierMukaiPr23 X.hom Y.hom Z.hom) L)
        (Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom)))

/-- The comparison at `pr_{23}` is invertible at direct images from suitable opens: for an open
`W ⊆ X ×_R Y` whose inclusion and whose composite with `X ×_R Y ⟶ Y` are affine — for instance
`pr_1^{-1}(U)` for an affine open `U` of a scheme `X` with affine diagonal — it is invertible at
`(W ↪ X ×_R Y)_* N` for every quasi-coherent `N` on `W`, although neither `X ×_R Y ⟶ Y` nor
`pr_{23}` need be affine. -/
theorem isIso_pr23ComparisonNatTrans_app_pushforward (L : (pullback Y.hom Z.hom).Modules)
    (hL : L.IsQuasicoherent) (W : (pullback X.hom Y.hom).Opens) [IsAffineHom W.ι]
    [IsAffineHom (W.ι ≫ pullback.snd X.hom Y.hom)] (N : W.toScheme.Modules)
    (hN : N.IsQuasicoherent) :
    IsIso ((pr23ComparisonNatTrans L).app ((Scheme.Modules.pushforward W.ι).obj N)) := by
  let sq := isPullback_fourierMukaiPr12_pr23 X.hom Y.hom Z.hom
  let W' := fourierMukaiPr12 X.hom Y.hom Z.hom ⁻¹ᵁ W
  have hsq₂ := isPullback_morphismRestrict (fourierMukaiPr12 X.hom Y.hom Z.hom) W
  have : IsAffineHom W'.ι := isAffineHom_preimage_ι _ W
  have : IsAffineHom (W'.ι ≫ fourierMukaiPr23 X.hom Y.hom Z.hom) :=
    isAffineHom_preimage_ι_comp sq W
  have hbc : IsIso ((baseChangeNatTrans sq.w).app ((Scheme.Modules.pushforward W.ι).obj N)) :=
    isIso_baseChangeNatTrans_app_pushforward_ι sq W N hN
  have := hN
  have hbc₂ : IsIso ((baseChangeNatTrans hsq₂.w).app N) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsq₂ N
  have hG : ((Scheme.Modules.pullback
      (fourierMukaiPr12 X.hom Y.hom Z.hom ∣_ W)).obj N).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback _ N hN
  have hpf₀ := isIso_projectionFormulaMap_pushforward_ι (fourierMukaiPr23 X.hom Y.hom Z.hom) W'
    _ hG L hL
  have hpf : IsIso ((projectionFormulaSourceNatTrans (fourierMukaiPr23 X.hom Y.hom Z.hom) L).app
      ((Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom)).obj
        ((Scheme.Modules.pushforward W.ι).obj N))) :=
    isIso_app_of_iso_of_isIso_app _ (@asIso _ _ _ _ _ hbc₂) hpf₀
  have hsw : IsIso (((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
      ((pullback Y.hom Z.hom)).presheaf ((pullback Y.hom Z.hom)).ringCatSheaf.2 (L))).hom.app
      ((Scheme.Modules.pushforward (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj
        ((Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom)).obj
          ((Scheme.Modules.pushforward W.ι).obj N)))) :=
    (((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
      ((pullback Y.hom Z.hom)).presheaf ((pullback Y.hom Z.hom)).ringCatSheaf.2 (L))).app
        _).isIso_hom
  have h1 := @Functor.map_isIso _ _ _ _ _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (pullback Y.hom Z.hom).toRingedSpace.sheaf).obj (L)) ⋙
    Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom)) _ hbc
  have h2 := @Functor.map_isIso _ _ _ _ _ _
    (Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom)) _ hsw
  have h3 := @Functor.map_isIso _ _ _ _ _ _
    (Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom)) _ hpf
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3)

/-- `X ×_R Y`, regarded as a scheme over `R` through `X ×_R Y ⟶ Y ⟶ Spec R`. -/
abbrev productOver (X Y : Over (Spec (.of R))) : Over (Spec (.of R)) :=
  Over.mk (pullback.snd X.hom Y.hom ≫ Y.hom)

/-- The kernel `pr_{23}^*L` on `(X ×_R Y) ×_R Z`. -/
def pr23Kernel (L : Scheme.QuasicoherentModules (pullback Y.hom Z.hom)) :
    Scheme.QuasicoherentModules (pullback (productOver X Y).hom Z.hom) :=
  ⟨(Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L.obj,
    Stacks.Modules.isQuasicoherent_pullback _ L.obj L.property⟩

/-- The target of `AlgebraicGeometry.pr23ComparisonNatTrans`, on quasi-coherent modules, is the
pullback--tensor--pushforward formula of the kernel `pr_{23}^*L` on `(X ×_R Y) ×_R Z`. -/
def pr23ComparisonTargetIso (L : Scheme.QuasicoherentModules (pullback Y.hom Z.hom)) :
    (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).sheaf).flip.obj
            (((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L.obj))) ⋙
        Scheme.Modules.pushforward (fourierMukaiPr23 X.hom Y.hom Z.hom) ⋙
        Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom) ≅
      integralTransformFormula R (productOver X Y) Z (pr23Kernel L).obj :=
  Functor.isoWhiskerLeft ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
      Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom))
    (Functor.isoWhiskerRight ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
          ((fourierMukaiTripleProduct X.hom Y.hom Z.hom)).presheaf
          ((fourierMukaiTripleProduct X.hom Y.hom Z.hom)).ringCatSheaf.2 ((pr23Kernel L).obj))).symm
        (Scheme.Modules.pushforward (fourierMukaiPr23 X.hom Y.hom Z.hom) ⋙
          Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom)) ≪≫
      Functor.isoWhiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          (fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace.sheaf).obj
            ((pr23Kernel L).obj)))
        (Scheme.Modules.pushforwardComp (fourierMukaiPr23 X.hom Y.hom Z.hom)
            (pullback.snd Y.hom Z.hom) ≪≫
          Scheme.Modules.pushforwardCongr (fourierMukaiPr23_snd X.hom Y.hom Z.hom)))

variable [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]

/-- Let `X` be quasi-compact with affine diagonal and `Y` quasi-compact and quasi-separated over
`R`. If the integral transform `F_L` of a quasi-coherent module `L` on `Y ×_R Z` is left exact,
then the comparison at `pr_{23}` is invertible at every quasi-coherent module `N` on `X ×_R Y`. -/
theorem isIso_pr23ComparisonNatTrans_app
    (L : Scheme.QuasicoherentModules (pullback Y.hom Z.hom))
    (hL : PreservesFiniteLimits (quasicoherentIntegralTransform R Y Z L))
    (N : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    IsIso ((pr23ComparisonNatTrans L.obj).app N.obj) := by
  classical
  have : QuasiCompact X.hom := quasiCompact_of_compactSpace X.hom
  have : QuasiSeparated X.hom := QuasiSeparated.of_quasiSeparatedSpace X.hom
  have : QuasiCompact Y.hom := quasiCompact_of_compactSpace Y.hom
  have : QuasiSeparated Y.hom := QuasiSeparated.of_quasiSeparatedSpace Y.hom
  have : QuasiSeparated (pullback.fst X.hom Y.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X.hom Y.hom).flip inferInstance
  have : CompactSpace (productOver X Y).left :=
    (inferInstance : CompactSpace (Limits.pullback X.hom Y.hom).carrier)
  have : QuasiSeparatedSpace (productOver X Y).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst X.hom Y.hom)
  let ιZ := (SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).ι
  let ιP := (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι
  let A := quasicoherentPushforward (pullback.snd X.hom Y.hom) ⋙
    quasicoherentIntegralTransform R Y Z L
  let B := quasicoherentIntegralTransform R (productOver X Y) Z (pr23Kernel L)
  let eA : A ⋙ ιZ ≅ ιP ⋙ Scheme.Modules.pushforward (pullback.snd X.hom Y.hom) ⋙
      Scheme.Modules.pullback (pullback.fst Y.hom Z.hom) ⋙
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (pullback Y.hom Z.hom).toRingedSpace.sheaf).obj (L.obj)) ⋙
      Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom) :=
    Functor.isoWhiskerLeft (quasicoherentPushforward (pullback.snd X.hom Y.hom))
      (quasicoherentIntegralTransformData R Y Z L).comparison
  let eB : B ⋙ ιZ ≅ ιP ⋙ Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom) ⋙
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).sheaf).flip.obj
          (((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L.obj))) ⋙
      Scheme.Modules.pushforward (fourierMukaiPr23 X.hom Y.hom Z.hom) ⋙
      Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom) :=
    (quasicoherentIntegralTransformData R (productOver X Y) Z (pr23Kernel L)).comparison ≪≫
      (pr23ComparisonTargetIso L).symm
  let τ : A ⟶ B :=
    ((SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      _).preimage (eA.hom ≫ Functor.whiskerLeft ιP (pr23ComparisonNatTrans L.obj) ≫ eB.inv)
  have hτ : ∀ M, ιZ.map (τ.app M) =
      eA.hom.app M ≫ (pr23ComparisonNatTrans L.obj).app M.obj ≫ eB.inv.app M := fun M =>
    NatTrans.congr_app (((SheafOfModules.isQuasicoherent
      Z.left.ringCatSheaf).fullyFaithfulι.whiskeringRight _).map_preimage
        (eA.hom ≫ Functor.whiskerLeft ιP (pr23ComparisonNatTrans L.obj) ≫ eB.inv)) M
  have hiff : ∀ M, IsIso (τ.app M) → IsIso ((pr23ComparisonNatTrans L.obj).app M.obj) := by
    intro M hM
    have h1 : IsIso (ιZ.map (τ.app M)) := Functor.map_isIso _ _
    rw [hτ M] at h1
    exact isIso_of_isIso_comp_comp (C := SheafOfModules Z.left.ringCatSheaf) (eA.hom.app M)
      ((pr23ComparisonNatTrans L.obj).app M.obj) (eB.inv.app M) (eA.app M).isIso_hom
      (eB.app M).symm.isIso_hom h1
  have hleg : ∀ (W : (pullback X.hom Y.hom).Opens) [IsAffineHom W.ι]
      [IsAffineHom (W.ι ≫ pullback.snd X.hom Y.hom)], IsIso (τ.app ((cechObj W).obj N)) := by
    intro W _ _
    have h := isIso_pr23ComparisonNatTrans_app_pushforward L.obj L.property W
      ((qcohRestrict W.ι).obj N).obj ((qcohRestrict W.ι).obj N).property
    have h1 : IsIso (ιZ.map (τ.app ((cechObj W).obj N))) := by
      rw [hτ]
      exact IsIso.comp_isIso' (eA.app _).isIso_hom (IsIso.comp_isIso' h (eB.app _).symm.isIso_hom)
    exact isIso_of_reflects_iso _ ιZ
  apply hiff
  obtain ⟨s, hs⟩ := isOpenCover_finset_affineOpens R X
  let U : s → X.left.Opens := fun i => ((i : X.left.affineOpens) : X.left.Opens)
  let V : s → (pullback X.hom Y.hom).Opens := fun i => fstOpen R X Y (U i)
  have hUa : ∀ i, IsAffineHom (U i).ι := fun i => isAffineHom_ι_affineOpens (i : X.left.affineOpens)
  have hUb : ∀ i j, IsAffineHom (U i ⊓ U j).ι := fun i j =>
    isAffineHom_ι_affineOpens_inf (i : X.left.affineOpens) (j : X.left.affineOpens)
  have hVinf : ∀ i j, V i ⊓ V j = fstOpen R X Y (U i ⊓ U j) := fun i j =>
    (Scheme.Hom.preimage_inf _).symm
  have hVa : ∀ i, IsAffineHom (V i).ι := fun i => have := hUa i; isAffineHom_fstOpen_ι (U i)
  have hVb : ∀ i j, IsAffineHom (V i ⊓ V j).ι := fun i j => by
    rw [hVinf]; have := hUb i j; exact isAffineHom_fstOpen_ι _
  have hVa' : ∀ i, IsAffineHom ((V i).ι ≫ pullback.snd X.hom Y.hom) := fun i =>
    isAffineHom_fstOpen_ι_snd (U i) (i : X.left.affineOpens).2
  have hVb' : ∀ i j, IsAffineHom ((V i ⊓ V j).ι ≫ pullback.snd X.hom Y.hom) := fun i j => by
    rw [hVinf]
    exact isAffineHom_fstOpen_ι_snd _
      (IsAffineOpen.inf (i : X.left.affineOpens).2 (j : X.left.affineOpens).2)
  have : ∀ i, QuasiCompact (V i).ι := fun i => by have := hVa i; infer_instance
  have : ∀ i, QuasiSeparated (V i).ι := fun i => by have := hVa i; infer_instance
  have : ∀ i j, QuasiCompact (V i ⊓ V j).ι := fun i j => by have := hVb i j; infer_instance
  have : ∀ i j, QuasiSeparated (V i ⊓ V j).ι := fun i j => by have := hVb i j; infer_instance
  have hV : TopologicalSpace.IsOpenCover V := by
    simpa [TopologicalSpace.IsOpenCover, V, fstOpen, Scheme.Hom.preimage_iSup] using
      congrArg (fun W : X.left.Opens => pullback.fst X.hom Y.hom ⁻¹ᵁ W) hs
  have : Fintype (MulticospanShape.prod s).L := inferInstanceAs (Fintype s)
  have : Fintype (MulticospanShape.prod s).R := inferInstanceAs (Fintype (s × s))
  have : DecidableEq (MulticospanShape.prod s).L := inferInstanceAs (DecidableEq s)
  have : DecidableEq (MulticospanShape.prod s).R := inferInstanceAs (DecidableEq (s × s))
  have : PreservesFiniteLimits A := comp_preservesFiniteLimits _ _
  have hP := isLimitOfPreserves A (isLimitCechMultifork R (productOver X Y) V hV N)
  have hQ := isLimitIntegralTransformCechMultifork R (productOver X Y) Z (pr23Kernel L) V hV N
  refine isIso_app_pt_of_isLimit τ (cechMultifork V N) hP hQ ?_
  rintro (i | p)
  · have := hVa i; have := hVa' i
    exact hleg (V i)
  · have := hVb p.1 p.2; have := hVb' p.1 p.2
    exact hleg (V p.1 ⊓ V p.2)

end Triple

/-! ### The projection formula at modules pulled back from a scheme with affine diagonal -/

section PullbackTarget

variable {R : Type u} [CommRing R] {X Z : Over (Spec (.of R))} {T : Scheme.{u}}
  (h : T ⟶ pullback X.hom Z.hom) [QuasiCompact h] [QuasiSeparated h] (G : T.Modules)

/-- The target `M ↦ q_* h_*(G ⊗ h^* p^* M)` of the projection-formula morphism of `h` at `p^*M`,
pushed forward to `Z`, where `p` and `q` are the two projections of `X ×_R Z`. -/
abbrev pullbackTargetFunctor : X.left.Modules ⥤ Z.left.Modules :=
  Scheme.Modules.pullback (pullback.fst X.hom Z.hom) ⋙ Scheme.Modules.pullback h ⋙
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} (T).toRingedSpace.sheaf).obj (G)) ⋙
    Scheme.Modules.pushforward h ⋙ Scheme.Modules.pushforward (pullback.snd X.hom Z.hom)

/-- `pullbackTargetFunctor` on direct images from an open `U` is computed over `p^{-1}(U)`:
affine base change (Tag 02KG) along `U ↪ X` and along `p^{-1}(U) ↪ X ×_R Z`, and the projection
formula (Tag 0FZE) along `h^{-1}(p^{-1}(U)) ↪ T`, identify it with the same construction for the
restriction of `h` over `p^{-1}(U)`. -/
def pullbackTargetFunctorRestrictIso (U : X.left.Opens) [IsAffineHom U.ι]
    (hG : G.IsQuasicoherent) :
    letI : IsAffineHom (pullback.fst X.hom Z.hom ⁻¹ᵁ U).ι := isAffineHom_preimage_ι _ U
    quasicoherentPushforward U.ι ⋙ (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
        pullbackTargetFunctor h G ≅
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X.hom Z.hom ∣_ U) ⋙
        Scheme.Modules.pullback (h ∣_ (pullback.fst X.hom Z.hom ⁻¹ᵁ U)) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ((h ⁻¹ᵁ (pullback.fst X.hom Z.hom ⁻¹ᵁ U)).toScheme).toRingedSpace.sheaf).obj
            (((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ (pullback.fst X.hom Z.hom ⁻¹ᵁ U)).ι).obj G))) ⋙
        Scheme.Modules.pushforward (h ∣_ (pullback.fst X.hom Z.hom ⁻¹ᵁ U)) ⋙
        Scheme.Modules.pushforward
          ((pullback.fst X.hom Z.hom ⁻¹ᵁ U).ι ≫ pullback.snd X.hom Z.hom) := by
  let V := pullback.fst X.hom Z.hom ⁻¹ᵁ U
  let W := h ⁻¹ᵁ V
  have : IsAffineHom V.ι := isAffineHom_preimage_ι _ U
  have : IsAffineHom W.ι := isAffineHom_preimage_ι _ V
  let ιU := (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι
  let F₂ := ιU ⋙ Scheme.Modules.pullback (pullback.fst X.hom Z.hom ∣_ U)
  let F₃ := F₂ ⋙ Scheme.Modules.pullback (h ∣_ V)
  have hF₂ : ∀ A, (F₂.obj A).IsQuasicoherent := fun A =>
    Stacks.Modules.isQuasicoherent_pullback _ A.obj A.property
  have hF₃ : ∀ A, (F₃.obj A).IsQuasicoherent := fun A =>
    Stacks.Modules.isQuasicoherent_pullback _ _ (hF₂ A)
  exact Functor.isoWhiskerRight
      (baseChangeIsoOfFunctor (isPullback_morphismRestrict (pullback.fst X.hom Z.hom) U) ιU
        (fun A => A.property))
      (Scheme.Modules.pullback h ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} (T).toRingedSpace.sheaf).obj
          (G)) ⋙
        Scheme.Modules.pushforward h ⋙ Scheme.Modules.pushforward (pullback.snd X.hom Z.hom)) ≪≫
    Functor.isoWhiskerRight (baseChangeIsoOfFunctor (isPullback_morphismRestrict h V) F₂ hF₂)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} (T).toRingedSpace.sheaf).obj
          (G)) ⋙
        Scheme.Modules.pushforward h ⋙ Scheme.Modules.pushforward (pullback.snd X.hom Z.hom)) ≪≫
    Functor.isoWhiskerLeft (F₃ ⋙ Scheme.Modules.pushforward W.ι)
      (Functor.isoWhiskerRight ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
          (T).presheaf (T).ringCatSheaf.2 (G)))
        (Scheme.Modules.pushforward h ⋙ Scheme.Modules.pushforward (pullback.snd X.hom Z.hom))) ≪≫
    Functor.isoWhiskerRight (projectionFormulaSourceIsoOfFunctor W.ι G hG F₃ hF₃)
      (Scheme.Modules.pushforward h ⋙ Scheme.Modules.pushforward (pullback.snd X.hom Z.hom)) ≪≫
    Functor.isoWhiskerLeft F₃ (Functor.isoWhiskerRight
      (((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight W.toScheme.presheaf
        W.toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback W.ι).obj G))).symm ≪≫
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          W.toScheme.toRingedSpace.sheaf).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app G).symm)
      (Scheme.Modules.pushforward W.ι ⋙ Scheme.Modules.pushforward h ⋙
        Scheme.Modules.pushforward (pullback.snd X.hom Z.hom))) ≪≫
    Functor.isoWhiskerLeft (F₃ ⋙ ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (W.toScheme).toRingedSpace.sheaf).obj (((Scheme.Modules.restrictFunctor W.ι).obj G))))
      (Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp W.ι h ≪≫
          Scheme.Modules.pushforwardCongr (morphismRestrict_ι h V).symm ≪≫
          (Scheme.Modules.pushforwardComp (h ∣_ V) V.ι).symm)
        (Scheme.Modules.pushforward (pullback.snd X.hom Z.hom)) ≪≫
      Functor.isoWhiskerLeft (Scheme.Modules.pushforward (h ∣_ V))
        (Scheme.Modules.pushforwardComp V.ι (pullback.snd X.hom Z.hom)))

/-- Let `U ⊆ X` be an affine open with affine inclusion, and suppose `pullbackTargetFunctor h G`
composed with the direct image along `U ↪ X` is right exact. Then the projection-formula morphism
of the restriction of `h` over `V = p^{-1}(U)` is invertible at `(p|_U)^*` of a cokernel of a
morphism of free modules. -/
theorem isIso_projectionFormulaMap_restrict_pullback_cokernel (U : X.left.Opens)
    (hU : IsAffineOpen U) [IsAffineHom U.ι] (hG : G.IsQuasicoherent)
    (hR : PreservesColimitsOfShape WalkingParallelPair (quasicoherentPushforward U.ι ⋙
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙ pullbackTargetFunctor h G))
    {I₁ I₂ : Type u} (f : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I₁ ⟶
      SheafOfModules.free I₂) (c : Cocone (parallelPair f 0)) (hc : IsColimit c) :
    IsIso ((projectionFormulaTargetNatTrans (h ∣_ (pullback.fst X.hom Z.hom ⁻¹ᵁ U))
      ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ (pullback.fst X.hom Z.hom ⁻¹ᵁ U)).ι).obj G)).app
      ((Scheme.Modules.pullback (pullback.fst X.hom Z.hom ∣_ U)).obj c.pt)) := by
  let V := pullback.fst X.hom Z.hom ⁻¹ᵁ U
  let W := h ⁻¹ᵁ V
  let p' := pullback.fst X.hom Z.hom ∣_ U
  let h' := h ∣_ V
  let G' := (Scheme.Modules.restrictFunctor W.ι).obj G
  let q' := V.ι ≫ pullback.snd X.hom Z.hom
  have : IsAffineHom V.ι := isAffineHom_preimage_ι _ U
  have hq' : IsAffineHom q' := isAffineHom_fstOpen_ι_snd (Y := Z) U hU
  have hG' : G'.IsQuasicoherent :=
    have := hG
    Scheme.Modules.isQuasicoherent_restrictFunctor W.ι G
  have hunit : (SheafOfModules.unit U.toScheme.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  have hfree : ∀ I : Type u,
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I).IsQuasicoherent := fun I =>
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
      (fun _ => hunit) (SheafOfModules.isColimitFreeCofan I)
  have hD : ∀ j, ((parallelPair f 0).obj j).IsQuasicoherent := fun j => match j with
    | .zero => hfree I₁
    | .one => hfree I₂
  have hpt : c.pt.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit hD hc
  let Pq := SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf
  let Dq : WalkingParallelPair ⥤ Pq.FullSubcategory := Pq.lift (parallelPair f 0) hD
  let cq : Cocone Dq :=
    { pt := ⟨c.pt, hpt⟩
      ι := { app := fun j => ObjectProperty.homMk (c.ι.app j)
             naturality := fun _ _ g => Pq.ι.map_injective (c.ι.naturality g) } }
  have hcq : IsColimit cq := isColimitOfReflects Pq.ι hc
  have h1 := isColimitOfPreserves (quasicoherentPushforward U.ι ⋙
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙ pullbackTargetFunctor h G) hcq
  have h2 := (IsColimit.mapCoconeEquiv (pullbackTargetFunctorRestrictIso h G U hG)) h1
  let c₁ := (Scheme.Modules.pullback p').mapCocone (Pq.ι.mapCocone cq)
  have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback p') :=
    (Scheme.Modules.pullbackPushforwardAdjunction p').leftAdjoint_preservesColimits
  have hc₁ : IsColimit c₁ :=
    ((this.preservesColimitsOfShape (J := WalkingParallelPair)).preservesColimit.preserves
      (isColimitOfPreserves Pq.ι hcq)).some
  let Θ := Scheme.Modules.pullback h' ⋙
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (W.toScheme).toRingedSpace.sheaf).obj (G')) ⋙
    Scheme.Modules.pushforward h'
  have h3 : IsColimit ((Scheme.Modules.pushforward q').mapCocone (Θ.mapCocone c₁)) := h2
  have hΘ : ∀ A : V.toScheme.Modules, A.IsQuasicoherent → (Θ.obj A).IsQuasicoherent :=
    fun A hA => @pushforward_isQuasicoherent _ _ h' inferInstance inferInstance _
      (Stacks.AlgebraicGeometry.ProjectionFormula.isQuasicoherent_pullbackTensor h' hG' hA)
  have hp' : ∀ A : U.toScheme.Modules, A.IsQuasicoherent →
      ((Scheme.Modules.pullback p').obj A).IsQuasicoherent := fun A hA =>
    Stacks.Modules.isQuasicoherent_pullback _ A hA
  have h4 : IsColimit (Θ.mapCocone c₁) :=
    isColimitOfIsColimitMapCoconePushforward q' (hΘ _ (hp' _ (hD _))) (hΘ _ (hp' _ (hD _)))
      (hΘ _ (hp' _ hpt)) h3
  have h5 : IsColimit ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (V.toScheme).toRingedSpace.sheaf).obj
        (((Scheme.Modules.pushforward h').obj G')))).mapCocone c₁) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isColimitMapCoconeTensorPushforwardFunctorFinite
      h' G' hc₁
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback p') :=
    (Scheme.Modules.pullbackPushforwardAdjunction p').leftAdjoint_preservesColimits
  have hunitV : IsIso ((projectionFormulaTargetNatTrans h' G').app
      ((Scheme.Modules.pullback p').obj (SheafOfModules.unit U.toScheme.ringCatSheaf))) :=
    NatTrans.isIso_app_of_iso (projectionFormulaTargetNatTrans h' G')
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso p'.toLRSHom.toShHom).symm
      (Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_unit h' G')
  have hfr : ∀ I : Type u, IsIso ((projectionFormulaTargetNatTrans h' G').app
      ((Scheme.Modules.pullback p').obj (SheafOfModules.free I))) := fun I => by
    have hpres : PreservesColimit (Discrete.functor fun _ : I =>
        SheafOfModules.unit U.toScheme.ringCatSheaf) (Scheme.Modules.pullback p') :=
      (this.preservesColimitsOfShape (J := Discrete I)).preservesColimit
    exact Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isColimit_cofan
      h' G' (Cofan.mk ((Scheme.Modules.pullback p').obj (SheafOfModules.free I))
        fun i => (Scheme.Modules.pullback p').map (SheafOfModules.ιFree i))
      (isColimitCofanMkObjOfIsColimit (G := Scheme.Modules.pullback p')
        (f := fun _ : I => SheafOfModules.unit U.toScheme.ringCatSheaf)
        (fun i => SheafOfModules.ιFree i) (SheafOfModules.isColimitFreeCofan I))
      (fun _ => hunitV)
  have hpts : ∀ j, IsIso ((projectionFormulaTargetNatTrans h' G').app
      (((Dq ⋙ Pq.ι) ⋙ Scheme.Modules.pullback p').obj j)) := fun j => match j with
    | .zero => hfr I₁
    | .one => hfr I₂
  exact NatTrans.isIso_app_of_isColimit_mapCocone (projectionFormulaTargetNatTrans h' G') c₁ h5 h4
    hpts

attribute [local instance] isAffineHom_ι_affineOpens in
/-- Let `X` and `Z` be schemes over `R` with `X` having affine diagonal, let `h : T ⟶ X ×_R Z` be
quasi-compact and quasi-separated and `G` a quasi-coherent module on `T`, and suppose that for
every affine open `U ⊆ X` the functor `pullbackTargetFunctor h G` composed with the direct image
along `U ↪ X` is right exact.  Then the projection-formula morphism of Tag 0FZE,
`h_*G ⊗ p^*M ⟶ h_*(G ⊗ h^* p^* M)`, is invertible at every quasi-coherent `M` on `X`, although
`h` need not be affine. -/
theorem isIso_projectionFormulaMap_pullback [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (hG : G.IsQuasicoherent)
    (hR : ∀ U : X.left.affineOpens, PreservesColimitsOfShape WalkingParallelPair
      (quasicoherentPushforward (U : X.left.Opens).ι ⋙
        (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙ pullbackTargetFunctor h G))
    (M : X.left.Modules) (hM : M.IsQuasicoherent) :
    IsIso ((projectionFormulaTargetNatTrans h G).app
      ((Scheme.Modules.pullback (pullback.fst X.hom Z.hom)).obj M)) := by
  let H := (Scheme.Modules.pullback (pullback.fst X.hom Z.hom)).obj M
  suffices key : IsIso (projectionFormulaMap h G H) from key
  refine Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isOpenCover h G H
    (fun U : X.left.affineOpens => pullback.fst X.hom Z.hom ⁻¹ᵁ (U : X.left.Opens)) ?_ ?_
  · simpa [TopologicalSpace.IsOpenCover, Scheme.Hom.preimage_iSup] using
      congrArg (fun W : X.left.Opens => pullback.fst X.hom Z.hom ⁻¹ᵁ W)
        (iSup_affineOpens_eq_top X.left)
  · intro U
    let V := pullback.fst X.hom Z.hom ⁻¹ᵁ (U : X.left.Opens)
    have : IsAffine (U : X.left.Opens).toScheme := U.2
    have hMU : ((Scheme.Modules.restrictFunctor (U : X.left.Opens).ι).obj M).IsQuasicoherent :=
      have := hM
      Scheme.Modules.isQuasicoherent_restrictFunctor _ M
    obtain ⟨P⟩ := Stacks.AlgebraicGeometry.ProjectionFormula.nonempty_presentation_of_isAffine
      (S := (U : X.left.Opens).toScheme) hMU
    have hloc := isIso_projectionFormulaMap_restrict_pullback_cokernel h G (U : X.left.Opens) U.2 hG
      (hR U) _ _ P.isColimit
    have hloc' : IsIso ((projectionFormulaTargetNatTrans (h ∣_ V)
        ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G)).app
        ((Scheme.Modules.restrictFunctor V.ι).obj H)) :=
      NatTrans.isIso_app_of_iso _
        ((Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso
          (pullback.fst X.hom Z.hom) (U : X.left.Opens)).app M).symm hloc
    have hsq : IsIso ((Stacks.AlgebraicGeometry.ProjectionFormula.restrictSourceIso h V G H).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H) ≫
          (Stacks.AlgebraicGeometry.ProjectionFormula.restrictTargetIso h V G H).hom) := by
      rw [Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_restrict h V G H]
      exact hloc'
    exact Stacks.AlgebraicGeometry.ProjectionFormula.isIso_of_isIso_conj _ _ _ hsq

end PullbackTarget

end AlgebraicGeometry
