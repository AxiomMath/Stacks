module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DirectImageStructureSheafBaseChange

/-!
# The affine computation of Tag 0E7K (b)

Let `p : X ⟶ Spec R` be flat with `X` quasi-compact and quasi-separated, and suppose `H¹(X, -)`
vanishes on globally generated quasi-coherent modules (clause (4) of [Stacks, Tag 0E7H]). The
proof of [Stacks, Tag 0E7K] computes

> `H⁰(X ×_S S', 𝒪) = H⁰(X, 𝒪_X ⊗_A A') = H⁰(X, 𝒪_X) ⊗_A A'`.

This file proves that chain and turns it into the invertibility of the canonical base-change
comparison over an affine base.

* The second equality is the Eilenberg-Watts computation
  `structureSheafZeroTensorGlobalSectionsIso` of `StructureSheafEilenbergWatts.lean`, read through
  `structureSheafZeroFunctorIso` at the functor `pullbackSectionsFunctor`, `M ↦ Γ(X, p^* M~)`. Any
  natural transformation out of `N ⊗ -` is determined by its value at `R`
  (`tensorLeft_natTrans_app_tmul`), which pins the resulting isomorphism down on pure tensors:
  `exists_addEquiv_tensor_pullbackGlobalSections` says `Γ(X, 𝒪_X) ⊗_R Γ(N) ≅ Γ(X, p^* N)` by
  `a ⊗ n ↦ a · p^* n`, for every quasi-coherent `N`.
* The first equality, at `N = h_* 𝒪_{T'}` for a morphism `h : T' ⟶ T` of affine schemes, is
  [Stacks, Tag 02KG] (`AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`) together
  with the normalisation of the base-change map on global sections.
  `exists_addEquiv_tensor_globalSections_of_isPullback` is the result:
  `Γ(X, 𝒪_X) ⊗_{Γ(T)} Γ(T') ≅ Γ(X', 𝒪_{X'})` by `a ⊗ b ↦ g'^* a · p'^* b`.
* `isIso_baseChangeNatTrans_structureSheaf_of_affine`: for two stacked cartesian squares
  `X' ⟶ X` over `Y' ⟶ Y` over `S' ⟶ S` with `Y, Y', S, S'` affine and `X ⟶ S` flat, the
  comparison `g^* f_* 𝒪_X ⟶ f'_* (g')^* 𝒪_X` is an isomorphism. Both of its sides are base
  changes of `Γ(X, 𝒪_X)` along `Γ(S) ⟶ Γ(S')` — the source by
  `affinePullbackSectionsBaseChangeIso` and the pushout square of rings of the lower square, the
  target by the previous item — and the comparison is compatible with the two structure maps.

## References

* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

noncomputable section

variable (R : Type u) [CommRing R] (W : Over (Spec (CommRingCat.of R)))

/-- `M ↦ Γ(X, p^* M~)`, as an endofunctor of `R`-modules. -/
abbrev pullbackSectionsFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  tildeFactor R ⋙ pullbackFactor R W ⋙ moduleGlobalSections W.left ⋙
    ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))

/-- The functor `M ↦ H⁰(X, 𝒪_X ⊗ p^* M~)` of the Eilenberg-Watts computation is
`M ↦ Γ(X, p^* M~)`: degree-zero cohomology is global sections and `𝒪_X ⊗ -` is the identity. -/
def structureSheafZeroFunctorIso :
    structureSheafZeroFunctor R W ≅ pullbackSectionsFunctor R W :=
  Functor.isoWhiskerRight (geometricFactorCompιIso R W (structureSheafQcoh W.left))
      ((moduleGlobalSections W.left).rightDerived 0 ⋙
        ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))) ≪≫
    Functor.isoWhiskerLeft (tildeFactor R ⋙ pullbackFactor R W)
      (Functor.isoWhiskerRight (tensorFactorStructureSheafIso R W)
        ((moduleGlobalSections W.left).rightDerived 0 ⋙
          ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))) ≪≫
        Functor.isoWhiskerRight (moduleGlobalSections W.left).rightDerivedZeroIsoSelf
          (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))))


omit [CommRing R] in
/-- A natural transformation out of `N ⊗ -` is determined by its value at `R`, on pure tensors. -/
theorem tensorLeft_natTrans_app_tmul {R : Type u} [CommRing R] {N : ModuleCat.{u} R}
    {F : ModuleCat.{u} R ⥤ ModuleCat.{u} R}
    (θ : MonoidalCategory.tensorLeft N ⟶ F) (M : ModuleCat.{u} R) (n : N) (m : M) :
    (θ.app M).hom (n ⊗ₜ[R] m) =
      (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom
        ((θ.app (ModuleCat.of R R)).hom (n ⊗ₜ[R] (1 : R))) := by
  have h := congrArg (fun φ => φ.hom (n ⊗ₜ[R] (1 : R)))
    (θ.naturality (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [← h]
  congr 1
  show n ⊗ₜ[R] m = n ⊗ₜ[R] (LinearMap.toSpanSingleton R M m 1)
  simp

/-- The pullback of a global section is natural in the module. -/
theorem pullbackGlobalSections_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) {F G : Y.Modules}
    (ψ : F ⟶ G) (s : Γ(F, ⊤)) :
    pullbackGlobalSections f G (ψ.app ⊤ s) =
      ((Scheme.Modules.pullback f).map ψ).app ⊤ (pullbackGlobalSections f F s) := by
  rw [SectionsEqualizer.pullbackGlobalSections_unit, SectionsEqualizer.pullbackGlobalSections_unit]
  have h := congrArg (fun φ => φ.app ⊤ s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality ψ)
  simp only [Scheme.Modules.Hom.comp_app, Functor.id_map] at h
  exact h.trans (SectionsEqualizer.moduleHom_app_preimage_top f _ _)


section Sections

variable [Flat W.hom] [CompactSpace (W.left : Type u)] [QuasiSeparatedSpace (W.left : Type u)]

/-- `Γ(X, 𝒪_X) ⊗_R M ≅ Γ(X, p^* M~)`. -/
def pullbackSectionsTensorIso
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus 1).obj G)) :
    MonoidalCategory.tensorLeft
        ((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
          (ModuleCat.of Γ(W.left, ⊤) Γ(W.left, ⊤))) ≅
      pullbackSectionsFunctor R W :=
  structureSheafZeroTensorGlobalSectionsIso R W hvan ≪≫ structureSheafZeroFunctorIso R W

/-- The pullback of the section `1` of `R~`. -/
def pullbackSectionsOne : (pullbackSectionsFunctor R W).obj (ModuleCat.of R R) :=
  pullbackGlobalSections W.hom ((tildeFactor R).obj (ModuleCat.of R R))
    ((tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R R) ⊤).hom 1 :)

/-- The section of `R~` given by `1 ∈ R` is the unit section of `𝒪_{Spec R}`. -/
theorem toOpen_one : ((tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R R) ⊤).hom 1 :
    Γ(Spec (CommRingCat.of R), ⊤)) = (1 : Γ(Spec (CommRingCat.of R), ⊤)) :=
  StructureSheaf.const_one ⊤

/-- `Γ(X, p^* R~) ≅ Γ(X, 𝒪_X)`, through `p^* 𝒪 ≅ 𝒪`. -/
def pullbackSectionsSelfIso :
    (pullbackSectionsFunctor R W).obj (ModuleCat.of R R) ≅
      (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
        (ModuleCat.of Γ(W.left, ⊤) Γ(W.left, ⊤)) :=
  (moduleGlobalSections W.left ⋙ ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).mapIso
    (Scheme.Modules.pullbackUnitIso W.hom)

/-- The pullback of the global section `1` of `𝒪_{Spec R}`. -/
abbrev pullbackOne : Γ((Scheme.Modules.pullback W.hom).obj
    (Scheme.unitModule (Spec (CommRingCat.of R))), ⊤) :=
  pullbackGlobalSections W.hom _ (1 : Γ(Spec (CommRingCat.of R), ⊤))

omit [Flat W.hom] [CompactSpace (W.left : Type u)] [QuasiSeparatedSpace (W.left : Type u)] in
/-- `p^* 𝒪 ≅ 𝒪` sends `a · p^* 1` to `a`. -/
theorem pullbackUnitIso_smul_pullbackOne (a : Γ(W.left, ⊤)) :
    (Scheme.Modules.pullbackUnitIso W.hom).hom.app ⊤ (a • pullbackOne R W) = a := by
  refine (Scheme.Modules.Hom.app_smul _ a _).trans ?_
  refine (congrArg (fun z => a • z) (SectionsEqualizer.pullbackUnitIso_unit W.hom 1)).trans ?_
  rw [map_one]
  exact mul_one a

/-- The map `R~ ⟶ M~` given by `n ∈ M` sends the section `1` to `n`, after `fromTildeΓ`. -/
private theorem fromTildeΓ_app_tilde_map_toSpanSingleton (N : (Spec (CommRingCat.of R)).Modules)
    (n : (moduleSpecΓFunctor (R := CommRingCat.of R)).obj N) :
    (Scheme.Modules.fromTildeΓ N).app ⊤ ((tilde.map (ConcreteCategory.ofHom (C := ModuleCat R)
      (X := ModuleCat.of R R) (Y := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj N)
      (LinearMap.toSpanSingleton R _ n))).app ⊤
        ((tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R R) ⊤).hom 1)) = n := by
  let ñ : ModuleCat.of R R ⟶ (moduleSpecΓFunctor (R := CommRingCat.of R)).obj N :=
    ConcreteCategory.ofHom (C := ModuleCat R) (LinearMap.toSpanSingleton R _ n)
  have a1 := ConcreteCategory.congr_hom (tilde.toOpen_map_app (R := CommRingCat.of R) ñ ⊤) (1 : R)
  have a2 := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app N ⊤) n
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at a1 a2
  rw [show ñ.hom (1 : R) = n by simp [ñ]] at a1
  rw [show (homOfLE (le_top (a := (⊤ : (Spec (CommRingCat.of R)).Opens)))).op = 𝟙 _ from
    Subsingleton.elim _ _, CategoryTheory.Functor.map_id] at a2
  exact (congrArg (fun z => (Scheme.Modules.fromTildeΓ N).app ⊤ z) a1).trans a2

/-- **The sections of the pullback of a quasi-coherent module on `Spec R`.** For `p : X ⟶ Spec R`
flat with `X` quasi-compact and quasi-separated and `H¹(X, -)` vanishing on globally generated
quasi-coherent modules, `Γ(X, 𝒪_X) ⊗_R Γ(N) ≅ Γ(X, p^* N)`, `a ⊗ n ↦ a · p^* n`. -/
theorem exists_addEquiv_tensor_pullbackGlobalSections
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus 1).obj G))
    (N : (Spec (CommRingCat.of R)).Modules) [N.IsQuasicoherent] :
    ∃ e : (Γ(W.left, ⊤) : Type u) ⊗[R]
        ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj N : Type u) ≃+
        Γ((Scheme.Modules.pullback W.hom).obj N, ⊤),
      ∀ (a : Γ(W.left, ⊤)) (n : (moduleSpecΓFunctor (R := CommRingCat.of R)).obj N),
        e (a ⊗ₜ[R] n) = a • pullbackGlobalSections W.hom N n := by
  let P := (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
    (ModuleCat.of Γ(W.left, ⊤) Γ(W.left, ⊤))
  let θ := pullbackSectionsTensorIso R W hvan
  let M : ModuleCat.{u} R := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj N
  let k : P ≃ₗ[R] (pullbackSectionsFunctor R W).obj (ModuleCat.of R R) :=
    (TensorProduct.rid R P).symm.trans (θ.app (ModuleCat.of R R)).toLinearEquiv
  let J : (pullbackSectionsFunctor R W).obj (ModuleCat.of R R) ≃ₗ[R] P :=
    (pullbackSectionsSelfIso R W).toLinearEquiv
  let L : P ≃ₗ[R] P := J.symm.trans k.symm
  let E1 : P ⊗[R] M ≃ₗ[R] (pullbackSectionsFunctor R W).obj M :=
    (TensorProduct.congr L (LinearEquiv.refl R M)).trans (θ.app M).toLinearEquiv
  have hφ : IsIso (Scheme.Modules.fromTildeΓ N) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ N).mp inferInstance
  let E2 := ((moduleGlobalSections W.left).mapIso
    ((Scheme.Modules.pullback W.hom).mapIso (asIso (Scheme.Modules.fromTildeΓ N)))).toLinearEquiv
  refine ⟨E1.toAddEquiv.trans E2.toAddEquiv, fun a n => ?_⟩
  let ñ : ModuleCat.of R R ⟶ M :=
    ConcreteCategory.ofHom (C := ModuleCat R) (X := ModuleCat.of R R) (Y := M)
      (LinearMap.toSpanSingleton R M n)
  let s1 : Γ((Scheme.Modules.pullback W.hom).obj ((tildeFactor R).obj (ModuleCat.of R R)), ⊤) :=
    pullbackSectionsOne R W
  have hone : (pullbackSectionsOne R W : Γ((Scheme.Modules.pullback W.hom).obj
      (Scheme.unitModule (Spec (CommRingCat.of R))), ⊤)) = pullbackOne R W :=
    congrArg (pullbackGlobalSections W.hom (Scheme.unitModule (Spec (CommRingCat.of R))))
      (toOpen_one R)
  have h4 : @Eq Γ((Scheme.Modules.pullback W.hom).obj ((tildeFactor R).obj (ModuleCat.of R R)), ⊤)
      (J.symm a) (a • s1) := by
    apply J.injective
    refine (J.apply_symm_apply _).trans ?_
    show _ = (Scheme.Modules.pullbackUnitIso W.hom).hom.app ⊤ (a • s1)
    refine Eq.trans ?_ (congrArg (fun z => (Scheme.Modules.pullbackUnitIso W.hom).hom.app ⊤
      (a • z)) hone.symm)
    exact (pullbackUnitIso_smul_pullbackOne R W a).symm
  have h3 : @Eq Γ((Scheme.Modules.pullback W.hom).obj ((tildeFactor R).obj (ModuleCat.of R R)), ⊤)
      ((θ.hom.app (ModuleCat.of R R)).hom (L a ⊗ₜ[R] (1 : R))) (a • s1) :=
    (k.apply_symm_apply (J.symm a)).trans h4
  have h1 : E1 (a ⊗ₜ[R] n) =
      ((pullbackSectionsFunctor R W).map ñ).hom (a • s1) :=
    (tensorLeft_natTrans_app_tmul θ.hom M (L a) n).trans
      (congrArg (fun z => ((pullbackSectionsFunctor R W).map ñ).hom z) h3)
  refine (congrArg (fun x => E2 x) h1).trans ?_
  show ((Scheme.Modules.pullback W.hom).map (Scheme.Modules.fromTildeΓ N)).app ⊤
    (((Scheme.Modules.pullback W.hom).map (tilde.map ñ)).app ⊤
      (a • s1)) = _
  refine (congrArg (fun z => ((Scheme.Modules.pullback W.hom).map
    (Scheme.Modules.fromTildeΓ N)).app ⊤ z) (Scheme.Modules.Hom.app_smul _ a _)).trans ?_
  refine (Scheme.Modules.Hom.app_smul _ a _).trans ?_
  refine congrArg (fun z => a • z) ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullback W.hom).map
    (Scheme.Modules.fromTildeΓ N)).app ⊤ z)
      (pullbackGlobalSections_naturality W.hom (tilde.map ñ) _).symm).trans ?_
  refine (pullbackGlobalSections_naturality W.hom (Scheme.Modules.fromTildeΓ N) _).symm.trans ?_
  exact congrArg (pullbackGlobalSections W.hom N) (fromTildeΓ_app_tilde_map_toSpanSingleton R N n)

end Sections
/-! ### The affine computation -/

/-- Transport of a tensor-product description along equalities of the two module structures. -/
theorem exists_addEquiv_tensor_congr {A M N Q : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup Q] {iM jM : Module A M} {iN jN : Module A N}
    (hM : iM = jM) (hN : iN = jN) (φ : M → N → Q)
    (h : letI := iM; letI := iN; ∃ e : M ⊗[A] N ≃+ Q, ∀ a b, e (a ⊗ₜ[A] b) = φ a b) :
    letI := jM; letI := jN; ∃ e : M ⊗[A] N ≃+ Q, ∀ a b, e (a ⊗ₜ[A] b) = φ a b := by
  subst hM hN
  exact h

/-- Sections over `⊤` of an isomorphism of modules, as an additive equivalence. -/
def moduleIsoAppTopAddEquiv {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    Γ(F, ⊤) ≃+ Γ(G, ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  left_inv y := (ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) (Iso.hom_inv_id e)) y).trans
      (CategoryTheory.id_apply y)
  right_inv y := (ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) (Iso.inv_hom_id e)) y).trans
      (CategoryTheory.id_apply y)
  map_add' := map_add _

/-- `p^* 𝒪 ≅ 𝒪` sends the adjunction unit applied to a function `s` to `p^# s`. -/
private theorem pullbackUnitIso_hom_app_unit_app {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    (Scheme.Modules.pullbackUnitIso f).hom.app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Scheme.unitModule Y)).app ⊤
        s) = f.appTop s :=
  (congrArg _ (SectionsEqualizer.pullbackGlobalSections_unit f (Scheme.unitModule Y) s).symm).trans
    (SectionsEqualizer.pullbackUnitIso_unit f s)

/-- Composing with `T ≅ Spec Γ(T, ⊤)` does not change the map on global sections. -/
private theorem comp_isoSpec_hom_appTop_ΓSpecIso_inv {Z T : Scheme.{u}} [IsAffine T] (q : Z ⟶ T)
    (r : Γ(T, ⊤)) :
    (q ≫ T.isoSpec.hom).appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(T, ⊤))).inv r) =
      q.appTop r := by
  rw [Scheme.Hom.comp_appTop]
  show (q.appTop) ((T.toSpecΓ.appTop) ((Scheme.ΓSpecIso Γ(T, ⊤)).inv r)) = _
  rw [Scheme.toSpecΓ_appTop]
  simp

/-- **The affine computation of [Stacks, Tag 0E7K] (b).** Let
```
X' --g'--> X
|p'        |p
T' --h---> T
```
be cartesian with `T` and `T'` affine, `p` flat, quasi-compact and quasi-separated, and suppose
`H¹(X, -)` vanishes on globally generated quasi-coherent modules. Then
`Γ(X, 𝒪_X) ⊗_{Γ(T)} Γ(T') ≅ Γ(X', 𝒪_{X'})` by `a ⊗ b ↦ g'^* a · p'^* b`. -/
theorem exists_addEquiv_tensor_globalSections_of_isPullback {X X' T T' : Scheme.{u}}
    {g' : X' ⟶ X} {p' : X' ⟶ T'} {p : X ⟶ T} {h : T' ⟶ T} (hq : IsPullback g' p' p h)
    [IsAffine T] [IsAffine T'] [Flat p] [QuasiCompact p] [QuasiSeparated p]
    (hvan : ∀ G : X.Modules, G.IsQuasicoherent → SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj G)) :
    letI := p.appTop.hom.toAlgebra
    letI := h.appTop.hom.toAlgebra
    ∃ e : (Γ(X, ⊤) : Type u) ⊗[Γ(T, ⊤)] (Γ(T', ⊤) : Type u) ≃+ Γ(X', ⊤),
      ∀ a b, e (a ⊗ₜ[Γ(T, ⊤)] b) = g'.appTop a * p'.appTop b := by
  let R : Type u := Γ(T, ⊤)
  let ps : X ⟶ Spec (CommRingCat.of R) := p ≫ T.isoSpec.hom
  let hs : T' ⟶ Spec (CommRingCat.of R) := h ≫ T.isoSpec.hom
  let W : Over (Spec (CommRingCat.of R)) := Over.mk ps
  have hqs : IsPullback g' p' ps hs := by
    simpa using hq.paste_vert (IsPullback.of_vert_isIso (fst := h) (snd := 𝟙 T')
      (f := T.isoSpec.hom) (g := hs) ⟨by simp [hs]⟩)
  have : Flat W.hom := by
    dsimp only [W, Over.mk_hom, ps]
    infer_instance
  have : CompactSpace (W.left : Type u) := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace (W.left : Type u) := quasiSeparatedSpace_of_quasiSeparated p
  let N : (Spec (CommRingCat.of R)).Modules :=
    (Scheme.Modules.pushforward hs).obj (Scheme.unitModule T')
  have : N.IsQuasicoherent := inferInstance
  obtain ⟨e1, he1⟩ := exists_addEquiv_tensor_pullbackGlobalSections R W hvan N
  have hβ : IsIso ((AffinePushforward.baseChangeNatTrans hqs.flip.w).app
      (Scheme.unitModule T')) :=
    AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hqs.flip _
  let κ : (Scheme.Modules.pullback ps).obj N ≅
      (Scheme.Modules.pushforward g').obj (Scheme.unitModule X') :=
    asIso ((AffinePushforward.baseChangeNatTrans hqs.flip.w).app (Scheme.unitModule T')) ≪≫
      (Scheme.Modules.pushforward g').mapIso (Scheme.Modules.pullbackUnitIso p')
  let e2 : Γ((Scheme.Modules.pullback ps).obj N, ⊤) ≃+ Γ(X', ⊤) := moduleIsoAppTopAddEquiv κ
  have he2 : ∀ (a : Γ(X, ⊤)) (n : Γ(N, ⊤)),
      e2 (a • pullbackGlobalSections ps N n) =
        g'.appTop a * p'.appTop (show Γ(T', ⊤) from n) := by
    intro a n
    have k1 : e2 (a • pullbackGlobalSections ps N n) =
        g'.appTop a * e2 (pullbackGlobalSections ps N n) :=
      Scheme.Modules.Hom.app_smul κ.hom a _
    rw [k1]
    congr 1
    have k2 := ConcreteCategory.congr_hom
      (AffineBaseChangeIso.baseChangeNatTrans_app_app_top hqs.flip.w (Scheme.unitModule T')) n
    show (Scheme.Modules.pullbackUnitIso p').hom.app ⊤
      (((AffinePushforward.baseChangeNatTrans hqs.flip.w).app (Scheme.unitModule T')).app ⊤
        (pullbackGlobalSections ps N n)) = _
    rw [SectionsEqualizer.pullbackGlobalSections_unit]
    refine (congrArg (fun z => (Scheme.Modules.pullbackUnitIso p').hom.app ⊤ z) k2).trans ?_
    exact pullbackUnitIso_hom_app_unit_app p' n
  let iN : Module R Γ(T', ⊤) :=
    show Module R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj N) from inferInstance
  refine exists_addEquiv_tensor_congr (iM := (baseSectionsAlgebra R W).toModule) (iN := iN)
    ?_ ?_ _ ⟨e1.trans e2, fun a b => ?_⟩
  · refine Module.ext' _ _ fun r m => ?_
    show (algebraMap R Γ(W.left, ⊤) r) * m =
      @HMul.hMul Γ(W.left, ⊤) Γ(W.left, ⊤) Γ(W.left, ⊤) _ (p.appTop r) m
    rw [algebraMap_baseSectionsAlgebra_apply]
    exact congrArg (· * m) (comp_isoSpec_hom_appTop_ΓSpecIso_inv p r)
  · refine Module.ext' _ _ fun r m => ?_
    show hs.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) * m = h.appTop r * m
    exact congrArg (· * m) (comp_isoSpec_hom_appTop_ΓSpecIso_inv h r)
  · exact (congrArg e2 (he1 a b)).trans (he2 a b)

/-- `exists_addEquiv_tensor_globalSections_of_isPullback` for arbitrary module structures given
by the same scalar multiplications. -/
theorem exists_addEquiv_tensor_globalSections_of_isPullback' {X X' T T' : Scheme.{u}}
    {g' : X' ⟶ X} {p' : X' ⟶ T'} {p : X ⟶ T} {h : T' ⟶ T} (hq : IsPullback g' p' p h)
    [IsAffine T] [IsAffine T'] [Flat p] [QuasiCompact p] [QuasiSeparated p]
    (hvan : ∀ G : X.Modules, G.IsQuasicoherent → SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj G))
    (iM : Module Γ(T, ⊤) Γ(X, ⊤)) (hiM : ∀ (r : Γ(T, ⊤)) (m : Γ(X, ⊤)), r • m = p.appTop r * m)
    (iN : Module Γ(T, ⊤) Γ(T', ⊤))
    (hiN : ∀ (r : Γ(T, ⊤)) (b : Γ(T', ⊤)), r • b = h.appTop r * b) :
    ∃ e : (Γ(X, ⊤) : Type u) ⊗[Γ(T, ⊤)] (Γ(T', ⊤) : Type u) ≃+ Γ(X', ⊤),
      ∀ a b, e (a ⊗ₜ[Γ(T, ⊤)] b) = g'.appTop a * p'.appTop b :=
  exists_addEquiv_tensor_congr (iM := p.appTop.hom.toAlgebra.toModule)
    (iN := h.appTop.hom.toAlgebra.toModule)
    (Module.ext' _ _ fun r m => (hiM r m).symm) (Module.ext' _ _ fun r b => (hiN r b).symm) _
    (exists_addEquiv_tensor_globalSections_of_isPullback hq hvan)

/-! ### The base-change comparison over an affine base -/

open AffineBaseChangeIso in
/-- `AffineBaseChangeIso.isIso_of_isPushout` with the map running from the extension of scalars
along `B ⟶ B'` to the one along `A ⟶ A'`. -/
theorem isIso_of_isPushout_of_isIso_transposeExtend {A B A' B' : CommRingCat.{u}}
    {pb : A ⟶ B} {qa : A ⟶ A'} {qb : B ⟶ B'} {pb' : A' ⟶ B'}
    (hsq : IsPushout pb qa qb pb')
    {M : ModuleCat.{u} B} {P : ModuleCat.{u} A'} {N' : ModuleCat.{u} B'}
    {u : (ModuleCat.restrictScalars pb.hom).obj M ⟶ (ModuleCat.restrictScalars qa.hom).obj P}
    (hu : IsIso (transposeExtend qa u))
    {v : M ⟶ (ModuleCat.restrictScalars qb.hom).obj N'} (hv : IsIso (transposeExtend qb v))
    (σ : (ModuleCat.restrictScalars pb'.hom).obj N' ⟶ P)
    (htri : ∀ x : M, σ (v x) = u x) : IsIso σ := by
  algebraize [pb.hom, qa.hom, qb.hom, pb'.hom, qb.hom.comp pb.hom]
  have hsc : IsScalarTower (A : Type u) (A' : Type u) (B' : Type u) :=
    .of_algebraMap_eq' <| congr($(hsq.1.1).hom)
  have hpo : Algebra.IsPushout (A : Type u) (B : Type u) (A' : Type u) (B' : Type u) :=
    CommRingCat.isPushout_iff_isPushout.mp hsq
  let iAM : Module (A : Type u) (M : Type u) := Module.compHom _ pb.hom
  let iAP : Module (A : Type u) (P : Type u) := Module.compHom _ qa.hom
  let iBN : Module (B : Type u) (N' : Type u) := Module.compHom _ qb.hom
  let iA'N : Module (A' : Type u) (N' : Type u) := Module.compHom _ pb'.hom
  let iAN : Module (A : Type u) (N' : Type u) := Module.compHom _ (qb.hom.comp pb.hom)
  have t1 : IsScalarTower (A : Type u) (B : Type u) (M : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t2 : IsScalarTower (A : Type u) (A' : Type u) (P : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t3 : IsScalarTower (A : Type u) (B : Type u) (N' : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t4 : IsScalarTower (B : Type u) (B' : Type u) (N' : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t5 : IsScalarTower (A' : Type u) (B' : Type u) (N' : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t6 : IsScalarTower (A : Type u) (A' : Type u) (N' : Type u) :=
    .of_algebraMap_smul fun r x => congrArg (· • x) (congr($(hsq.1.1).hom r)).symm
  let u' : (M : Type u) →ₗ[(A : Type u)] (P : Type u) := u.hom
  let v' : (M : Type u) →ₗ[(B : Type u)] (N' : Type u) := v.hom
  let σ' : (N' : Type u) →ₗ[(A' : Type u)] (P : Type u) := σ.hom
  have hbu : IsBaseChange (A' : Type u) u' :=
    IsBaseChange.of_equiv (asIso (transposeExtend qa u)).toLinearEquiv fun m =>
      transposeExtend_one_tmul qa u m
  have hbv : IsBaseChange (B' : Type u) v' :=
    IsBaseChange.of_equiv (asIso (transposeExtend qb v)).toLinearEquiv fun m =>
      transposeExtend_one_tmul qb v m
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_of_isBaseChange (isBaseChange_restrictScalars hbv) hbu σ' htri

/-- The pullback of global sections of a quasi-coherent module along a morphism of affine
schemes, as a map whose transpose under extension of scalars is invertible. -/
theorem exists_pullbackSection_isIso_transposeExtend {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsAffine Y] [IsAffine Y'] (F : Y.Modules) [F.IsQuasicoherent]
    (hle : (⊤ : Y'.Opens) ≤ g ⁻¹ᵁ ⊤) :
    ∃ v : ModuleCat.of Γ(Y, ⊤) Γ(F, ⊤) ⟶ (ModuleCat.restrictScalars (g.appLE ⊤ ⊤ hle).hom).obj
        (ModuleCat.of Γ(Y', ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤)),
      IsIso (AffineBaseChangeIso.transposeExtend (g.appLE ⊤ ⊤ hle) v) ∧
        ∀ x, v x = Scheme.Modules.pullbackSection g F ⊤ ⊤ hle x := by
  let isoV := affinePullbackSectionsBaseChangeIso g F (isAffineOpen_top Y) (isAffineOpen_top Y') hle
  let v := ((ModuleCat.extendRestrictScalarsAdj (g.appLE ⊤ ⊤ hle).hom).homEquiv _ _) isoV.hom
  have hvt : AffineBaseChangeIso.transposeExtend (g.appLE ⊤ ⊤ hle) v = isoV.hom :=
    ((ModuleCat.extendRestrictScalarsAdj (g.appLE ⊤ ⊤ hle).hom).homEquiv _ _).symm_apply_apply _
  refine ⟨v, by rw [hvt]; infer_instance, fun x => ?_⟩
  have e1 := AffineBaseChangeIso.transposeExtend_one_tmul _ v x
  rw [hvt] at e1
  exact e1.symm.trans (affinePullbackSectionsBaseChangeIso_one_tmul g F _ _ hle x)

/-- **The comparison at `𝒪_X` over an affine base, for a base change coming from an affine base
of the base.** Let
```
X' --g'--> X
|f'        |f
Y' --g---> Y
|q'        |q
S' --h---> S
```
be two cartesian squares with `Y`, `Y'`, `S`, `S'` affine, `f` quasi-compact and
quasi-separated, `X ⟶ S` flat, and `H¹(X, -)` vanishing on globally generated quasi-coherent
modules. Then `g^* f_* 𝒪_X ⟶ f'_* (g')^* 𝒪_X` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_structureSheaf_of_affine {X X' Y Y' S S' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (hw : IsPullback g' f' f g)
    {q' : Y' ⟶ S'} {q : Y ⟶ S} {h : S' ⟶ S} (hY : IsPullback g q' q h)
    [IsAffine Y] [IsAffine Y'] [IsAffine S] [IsAffine S'] [QuasiCompact f] [QuasiSeparated f]
    [Flat (f ≫ q)]
    (hvan : ∀ G : X.Modules, G.IsQuasicoherent → SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj G)) :
    IsIso ((AffinePushforward.baseChangeNatTrans hw.w).app (Scheme.unitModule X)) := by
  have hout : IsPullback g' (f' ≫ q') (f ≫ q) h := hw.paste_vert hY
  let F : Y.Modules := (Scheme.Modules.pushforward f).obj (Scheme.unitModule X)
  let β := (AffinePushforward.baseChangeNatTrans hw.w).app (Scheme.unitModule X)
  have hFq : F.IsQuasicoherent :=
    FlatBaseChange.isQuasicoherent_pushforward_of_qcqs f (Scheme.unitModule X)
  refine isIso_baseChangeNatTrans_structureSheaf_of_isIso_appTop hw ?_
  have hle : (⊤ : Y'.Opens) ≤ g ⁻¹ᵁ ⊤ := le_top
  have hgle : g.appLE ⊤ ⊤ hle = g.appTop := g.appLE_eq_app (U := ⊤)
  have hsq : IsPushout q.appTop h.appTop (g.appLE ⊤ ⊤ hle) q'.appTop := by
    rw [hgle]
    exact isPushout_appTop_of_isPullback hY
  let M : ModuleCat.{u} Γ(Y, ⊤) := ModuleCat.of Γ(Y, ⊤) Γ(F, ⊤)
  let N' : ModuleCat.{u} Γ(Y', ⊤) := ModuleCat.of Γ(Y', ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤)
  let P : ModuleCat.{u} Γ(S', ⊤) := (ModuleCat.restrictScalars q'.appTop.hom).obj
    (ModuleCat.of Γ(Y', ⊤) Γ((Scheme.Modules.pushforward f').obj
      ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)), ⊤))
  obtain ⟨v, hv, hvx⟩ := exists_pullbackSection_isIso_transposeExtend g F hle
  let ρ₂ : Γ(F, ⊤) ⟶ Γ((Scheme.Modules.pushforward f').obj
      ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)), ⊤) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app (Scheme.unitModule X)).app
      (f ⁻¹ᵁ ⊤)
  let u : (ModuleCat.restrictScalars q.appTop.hom).obj (ModuleCat.of Γ(Y, ⊤) Γ(F, ⊤)) ⟶
      (ModuleCat.restrictScalars h.appTop.hom).obj P :=
    ConcreteCategory.ofHom (C := ModuleCat Γ(S, ⊤))
      { toFun := ρ₂
        map_add' := map_add _
        map_smul' := fun r x => by
          have hr : g'.appTop (f.appTop (q.appTop r)) = f'.appTop (q'.appTop (h.appTop r)) := by
            simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using
              congrArg (fun φ : X' ⟶ S => φ.appTop.hom r) hout.w
          have k1 := Scheme.Modules.Hom.app_smul (U := f ⁻¹ᵁ ⊤)
            ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app (Scheme.unitModule X))
            (f.appTop (q.appTop r)) x
          show ρ₂ (@HSMul.hSMul Γ(X, ⊤) Γ(Scheme.unitModule X, ⊤) _ _
            (f.appTop (q.appTop r)) x) = _
          refine k1.trans ?_
          show @HSMul.hSMul Γ(X', ⊤) Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤)
              _ _ (g'.appTop (f.appTop (q.appTop r))) (ρ₂ x) =
            @HSMul.hSMul Γ(X', ⊤) Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤)
              _ _ (f'.appTop (q'.appTop (h.appTop r))) (ρ₂ x)
          rw [hr] }
  let σ : (ModuleCat.restrictScalars q'.appTop.hom).obj
      (ModuleCat.of Γ(Y', ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤)) ⟶ P :=
    ConcreteCategory.ofHom (C := ModuleCat Γ(S', ⊤))
      { toFun := β.app ⊤
        map_add' := map_add _
        map_smul' := fun c y => Scheme.Modules.Hom.app_smul β (q'.appTop c) y }
  have htri : ∀ x, σ (v x) = u x := by
    intro x
    show β.app ⊤ (v x) = ρ₂ x
    rw [hvx]
    have k := ConcreteCategory.congr_hom
      (AffineBaseChangeIso.baseChangeNatTrans_app_app_top hw.w (Scheme.unitModule X)) x
    refine Eq.trans ?_ k
    have hps : Scheme.Modules.pullbackSection g F ⊤ ⊤ hle x = pullbackGlobalSections g F x := by
      unfold Scheme.Modules.pullbackSection pullbackGlobalSections
      congr 1
    rw [hps, SectionsEqualizer.pullbackGlobalSections_unit]
    rfl
  have hu : IsIso (AffineBaseChangeIso.transposeExtend h.appTop u) := by
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f ≫ q).appTop.hom.toAlgebra
    let : Algebra Γ(S, ⊤) Γ(S', ⊤) := h.appTop.hom.toAlgebra
    obtain ⟨eA, heA⟩ := exists_addEquiv_tensor_globalSections_of_isPullback hout hvan
    let idM : (ModuleCat.restrictScalars q.appTop.hom).obj M ≃ₗ[Γ(S, ⊤)] Γ(X, ⊤) :=
      LinearEquiv.refl _ _
    let idS : (ModuleCat.restrictScalars h.appTop.hom).obj (ModuleCat.of Γ(S', ⊤) Γ(S', ⊤))
        ≃ₗ[Γ(S, ⊤)]
        Γ(S', ⊤) :=
      LinearEquiv.refl _ _
    let e' := ((TensorProduct.comm _ _ _).trans (TensorProduct.congr idM idS)).toAddEquiv.trans eA
    let ε : Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤) ≃+ Γ(X', ⊤) :=
      moduleIsoAppTopAddEquiv (Scheme.Modules.pullbackUnitIso g')
    have hερ : ∀ x : Γ(F, ⊤), ε (ρ₂ x) = g'.appTop x := pullbackUnitIso_hom_app_unit_app g'
    have hval : ∀ z, ε (AffineBaseChangeIso.transposeExtend h.appTop u z) =
        e' z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero =>
        refine (congrArg ε (map_zero (AffineBaseChangeIso.transposeExtend h.appTop u).hom)).trans ?_
        exact (map_zero ε).trans (map_zero e').symm
      | add z w hz hw =>
        refine (congrArg ε
          (map_add (AffineBaseChangeIso.transposeExtend h.appTop u).hom z w)).trans ?_
        refine (map_add ε _ _).trans ?_
        exact (congrArg₂ (· + ·) hz hw).trans (map_add e' z w).symm
      | tmul b x =>
        let b' : Γ(S', ⊤) := b
        let y : P := u x
        have k0 : (b ⊗ₜ[Γ(S, ⊤), h.appTop.hom] x :
            (ModuleCat.extendScalars h.appTop.hom).obj
              ((ModuleCat.restrictScalars q.appTop.hom).obj M)) =
            b' • ((1 : Γ(S', ⊤)) ⊗ₜ[Γ(S, ⊤), h.appTop.hom] x) :=
          ((ModuleCat.ExtendScalars.smul_tmul h.appTop.hom b' 1 x).trans
            (by rw [mul_one]; rfl)).symm
        have e1 : (AffineBaseChangeIso.transposeExtend h.appTop u).hom (b ⊗ₜ x) = b' • y := by
          refine (congrArg (AffineBaseChangeIso.transposeExtend h.appTop u).hom k0).trans ?_
          refine ((AffineBaseChangeIso.transposeExtend h.appTop u).hom.map_smul b' _).trans ?_
          exact congrArg (b' • ·) (AffineBaseChangeIso.transposeExtend_one_tmul _ u x)
        have e2 : ε (b' • y) = f'.appTop (q'.appTop b') * ε y :=
          Scheme.Modules.Hom.app_smul (Scheme.Modules.pullbackUnitIso g').hom
            (f'.appTop (q'.appTop b')) y
        have e3 : e' (b ⊗ₜ x) = g'.appTop x * (f' ≫ q').appTop b' := heA x b
        refine (congrArg ε e1).trans (e2.trans ?_)
        refine Eq.trans ?_ e3.symm
        rw [show ε y = g'.appTop x from hερ x, Scheme.Hom.comp_appTop, mul_comm]
        rfl
    rw [ConcreteCategory.isIso_iff_bijective]
    refine Function.bijective_iff_has_inverse.mpr ⟨fun w => e'.symm (ε w), fun z => ?_, fun w => ?_⟩
    · exact (congrArg e'.symm (hval z)).trans (e'.symm_apply_apply z)
    · exact ε.injective ((hval _).trans (e'.apply_symm_apply _))
  have hσ := isIso_of_isPushout_of_isIso_transposeExtend hsq hu hv σ htri
  rw [ConcreteCategory.isIso_iff_bijective] at hσ ⊢
  exact hσ

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
