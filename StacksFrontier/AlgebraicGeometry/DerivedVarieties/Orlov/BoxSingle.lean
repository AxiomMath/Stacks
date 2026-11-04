module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.ExternalTensorBox
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxPairings
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.SingleKernel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatHomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShiftedDegreeZero
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FppfDescent

/-!
# The derived external product of two finite locally free modules

Let `X` and `Y` be schemes over `S` whose two projections from `X ×_S Y` are flat, and let `ℰ`,
`𝒢` be modules on `X` and `Y`, with `𝒢` finite locally free. Then the derived external product
of `ℰ[0]` and `𝒢[0]` is the external tensor product placed in degree zero:

`L pr_1^*(ℰ[0]) ⊗^𝐋 L pr_2^*(𝒢[0]) ≅ (pr_1^*ℰ ⊗ pr_2^*𝒢)[0] = (ℰ ⊠ 𝒢)[0]`,

naturally in `ℰ` and `𝒢`. The derived pullbacks along the flat projections are the underived
ones, and the derived tensor product with the flat module `pr_2^*𝒢` is the underived one: its
cohomology is `Hⁱ(pr_1^*ℰ[0]) ⊗ pr_2^*𝒢`, which vanishes away from degree `0`, and in degree `0`
the canonical comparison is an isomorphism ([Stacks, Tag 06YU]).

This identifies the terms `ℰᵢ ⊠ 𝒢ᵢ` of a resolution of the diagonal, placed in degree zero,
with the derived external products through which the integral transforms of
[Stacks, Section 0G07] are computed.

## Main definitions

* `AlgebraicGeometry.tensorSingleHom`: the canonical map `A[0] ⊗^𝐋 N[0] ⟶ (A ⊗ N)[0]`.
* `AlgebraicGeometry.boxSingleHom`: the canonical map `ℰ[0] ⊠ 𝒢[0] ⟶ (ℰ ⊠ 𝒢)[0]`.

## Main results

* `AlgebraicGeometry.isIso_boxSingleHom`: it is an isomorphism for `𝒢` finite locally free
  (the isomorphism itself is `AlgebraicGeometry.derivedBoxSingleIso`; the point here is the
  naturality).
* `AlgebraicGeometry.boxSingleHom_naturality`: naturality in both factors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Functor.flip_obj_additive
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-! ### The derived tensor product with a flat module in degree zero -/

section Tensor

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- The canonical map `A[0] ⊗^𝐋 N[0] ⟶ (A ⊗ N)[0]` is natural in `A`. -/
theorem tensorSingleToSingle_naturality_left {A A' : Modules R} (a : A ⟶ A') (N : Modules R) :
    ((derivedTensorProductFunctor R).map
        (DerivedCategory.Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
          a))).app (DerivedCategory.Q.obj (sg R N)) ≫ tensorSingleToSingle R A' N =
    tensorSingleToSingle R A N ≫
      DerivedCategory.Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).app N)) := by
  have h1 := (canonicalDerivedTensorProduct R).toTensor_naturality
    ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map a) (𝟙 (sg R N))
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h1
  have h2 := Stacks.DegreeZeroTensor.map_sq (DerivedCategory.Q (C := Modules R)) _ _ _ _
    (totSingleIsoSingle_hom_naturality R N a)
  exact Stacks.DegreeZeroTensor.two_sq _ _ _ _ _ _ _ h1 h2

/-- The canonical map `A[0] ⊗^𝐋 N[0] ⟶ (A ⊗ N)[0]` is natural in `N`. -/
theorem tensorSingleToSingle_naturality_right (A : Modules R) {N N' : Modules R} (b : N ⟶ N') :
    ((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).map
        (DerivedCategory.Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
          b)) ≫ tensorSingleToSingle R A N' =
    tensorSingleToSingle R A N ≫
      DerivedCategory.Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).map b)) := by
  have h1 := (canonicalDerivedTensorProduct R).toTensor_naturality
    (𝟙 (sg R A)) ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map b)
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h1
  have h2 := Stacks.DegreeZeroTensor.map_sq (DerivedCategory.Q (C := Modules R)) _ _ _ _
    (totSingleIsoSingle_hom_naturality_second R A b)
  exact Stacks.DegreeZeroTensor.two_sq _ _ _ _ _ _ _ h1 h2

/-- Tensoring with a flat module in degree zero kills the degrees in which the complex has no
cohomology. -/
theorem isZero_homology_tensor_single_of_isFlat (L : CochainComplex (Modules R) ℤ)
    (N : Modules R) (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)
    (i : ℤ) (hL : IsZero (L.homology i)) :
    IsZero ((DerivedCategory.homologyFunctor (Modules R) i).obj
      (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj L)).obj
        (DerivedCategory.Q.obj (sg R N)))) :=
  IsZero.of_iso (Functor.map_isZero ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj N) hL)
    (homologyTensorFlatIso R N hN L i)

/-- **For a flat `N`, the canonical map `A[0] ⊗^𝐋 N[0] ⟶ (A ⊗ N)[0]` is an isomorphism.** -/
theorem isIso_tensorSingleToSingle (A N : Modules R)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N) :
    IsIso (tensorSingleToSingle R A N) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  by_cases hi : i = 0
  · subst hi
    have := isIso_degreeZeroTensorMap R N A
    have h' : (DerivedCategory.homologyFunctor (Modules R) 0).map (tensorSingleToSingle R A N) =
        degreeZeroTensorMap R N A ≫
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R) 0).app
            (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj N)).inv := by
      rw [← homologyMap_tensorSingleToSingle R A N, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [h']
    infer_instance
  · have hs : IsZero ((DerivedCategory.homologyFunctor (Modules R) i).obj
        (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).obj
          (DerivedCategory.Q.obj (sg R N)))) :=
      isZero_homology_tensor_single_of_isFlat R (sg R A) N hN i
        (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi)
    have ht : IsZero ((DerivedCategory.homologyFunctor (Modules R) i).obj
        (DerivedCategory.Q.obj (sg R
          (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj N)))) :=
      (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi).of_iso
        ((DerivedCategory.homologyFunctorFactors (Modules R) i).app _)
    exact ⟨⟨0, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩

/-- Pasting four commuting squares. -/
theorem four_sq {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : D}
    (t : X₀ ⟶ X₁) (r : X₁ ⟶ X₂) (e : X₂ ⟶ X₃) (k : X₃ ⟶ X₄)
    (t' : Y₀ ⟶ Y₁) (r' : Y₁ ⟶ Y₂) (e' : Y₂ ⟶ Y₃) (k' : Y₃ ⟶ Y₄)
    (p : X₀ ⟶ Y₀) (q : X₁ ⟶ Y₁) (s : X₂ ⟶ Y₂) (g : X₃ ⟶ Y₃) (h : X₄ ⟶ Y₄)
    (h₁ : p ≫ t' = t ≫ q) (h₂ : q ≫ r' = r ≫ s) (h₃ : s ≫ e' = e ≫ g) (h₄ : g ≫ k' = k ≫ h) :
    p ≫ t' ≫ r' ≫ e' ≫ k' = (t ≫ r ≫ e ≫ k) ≫ h := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

/-- The canonical map `A[0] ⊗^𝐋 N[0] ⟶ (A ⊗ N)[0]` in the spelling of `singleFunctor`. -/
def tensorSingleHom (A N : Modules R) :
    ((derivedTensorProductFunctor R).obj
        ((DerivedCategory.singleFunctor (Modules R) 0).obj A)).obj
        ((DerivedCategory.singleFunctor (Modules R) 0).obj N) ⟶
      (DerivedCategory.singleFunctor (Modules R) 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj A).obj N) :=
  ((derivedTensorProductFunctor R).map
      ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).hom.app A)).app _ ≫
    ((derivedTensorProductFunctor R).obj _).map
      ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).hom.app N) ≫
    tensorSingleToSingle R A N ≫
    (DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).inv.app _

/-- For a flat `N`, the canonical map `A[0] ⊗^𝐋 N[0] ⟶ (A ⊗ N)[0]` is an isomorphism. -/
theorem isIso_tensorSingleHom (A N : Modules R)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N) :
    IsIso (tensorSingleHom R A N) := by
  have := isIso_tensorSingleToSingle R A N hN
  unfold tensorSingleHom
  infer_instance

/-- The map `tensorSingleHom R A N : A[0] ⊗^𝐋 N[0] ⟶ (A ⊗ N)[0]` is natural in `A`. -/
theorem tensorSingleHom_naturality_left {A A' : Modules R} (a : A ⟶ A') (N : Modules R) :
    ((derivedTensorProductFunctor R).map
        ((DerivedCategory.singleFunctor (Modules R) 0).map a)).app _ ≫ tensorSingleHom R A' N =
    tensorSingleHom R A N ≫ (DerivedCategory.singleFunctor (Modules R) 0).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).map a).app N) :=
  four_sq _ _ _ _ _ _ _ _ _ _ _ _ _
    (Stacks.DegreeZeroTensor.map_sq (derivedTensorProductFunctor R ⋙
      (evaluation _ _).obj ((DerivedCategory.singleFunctor (Modules R) 0).obj N)) _ _ _ _
      ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).hom.naturality a))
    ((((derivedTensorProductFunctor R).map (DerivedCategory.Q.map
      ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map a))).naturality
      ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).hom.app N)).symm)
    (tensorSingleToSingle_naturality_left R a N)
    ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).inv.naturality
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).map a).app N))

/-- The map `tensorSingleHom R A N : A[0] ⊗^𝐋 N[0] ⟶ (A ⊗ N)[0]` is natural in `N`. -/
theorem tensorSingleHom_naturality_right (A : Modules R) {N N' : Modules R} (b : N ⟶ N') :
    ((derivedTensorProductFunctor R).obj _).map
        ((DerivedCategory.singleFunctor (Modules R) 0).map b) ≫ tensorSingleHom R A N' =
    tensorSingleHom R A N ≫ (DerivedCategory.singleFunctor (Modules R) 0).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj A).map b) :=
  four_sq _ _ _ _ _ _ _ _ _ _ _ _ _
    (((derivedTensorProductFunctor R).map
      ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).hom.app A)).naturality
      ((DerivedCategory.singleFunctor (Modules R) 0).map b))
    (Stacks.DegreeZeroTensor.map_sq ((derivedTensorProductFunctor R).obj _) _ _ _ _
      ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).hom.naturality b))
    (tensorSingleToSingle_naturality_right R A b)
    ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).inv.naturality
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj A).map b))

end Tensor

/-! ### The derived external product -/

section Box

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Flat (pullback.fst f g)]
  [Flat (pullback.snd f g)]

omit [Flat (pullback.fst f g)] [Flat (pullback.snd f g)] in
/-- The pullback of a finite locally free module along the second projection is flat. -/
theorem isFlat_pullback_snd (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (pullback f g).toRingedSpace.sheaf)
      ((Scheme.Modules.pullback (pullback.snd f g)).obj G) :=
  AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ G hG)

/-- The comparison `ℰ[0] ⊠ 𝒢[0] ⟶ (ℰ ⊠ 𝒢)[0]`. -/
def boxSingleHom (E : X.Modules) (G : Y.Modules) :
    derivedBox f g ((DerivedCategory.singleFunctor X.Modules 0).obj E)
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (externalTensorProduct f g E G) :=
  ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).map
      ((dpullSingleIsoOfIsFlat (pullback.fst f g)
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)).hom.app E)).app _ ≫
    ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj _).map
      ((dpullSingleIsoOfIsFlat (pullback.snd f g)
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)).hom.app G) ≫
    tensorSingleHom (pullback f g).toRingedSpace.sheaf
      ((Scheme.Modules.pullback (pullback.fst f g)).obj E)
      ((Scheme.Modules.pullback (pullback.snd f g)).obj G)

/-- **`ℰ[0] ⊠ 𝒢[0] ≅ (ℰ ⊠ 𝒢)[0]`**, with forward map `boxSingleHom`, for `𝒢` finite locally
free. -/
def boxSingleIso (E : X.Modules) (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G) :
    derivedBox f g ((DerivedCategory.singleFunctor X.Modules 0).obj E)
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≅
      (DerivedCategory.singleFunctor _ 0).obj (externalTensorProduct f g E G) :=
  ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).mapIso
      ((dpullSingleIsoOfIsFlat (pullback.fst f g)
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)).app E)).app _ ≪≫
    ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj _).mapIso
      ((dpullSingleIsoOfIsFlat (pullback.snd f g)
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)).app G) ≪≫
    @asIso _ _ _ _ (tensorSingleHom (pullback f g).toRingedSpace.sheaf
      ((Scheme.Modules.pullback (pullback.fst f g)).obj E)
      ((Scheme.Modules.pullback (pullback.snd f g)).obj G))
      (isIso_tensorSingleHom (pullback f g).toRingedSpace.sheaf
        ((Scheme.Modules.pullback (pullback.fst f g)).obj E)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj G) (isFlat_pullback_snd f g G hG))

/-- The forward map of `boxSingleIso` is `boxSingleHom`. -/
theorem boxSingleIso_hom (E : X.Modules) (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G) :
    (boxSingleIso f g E G hG).hom = boxSingleHom f g E G :=
  rfl

/-- **`ℰ[0] ⊠ 𝒢[0] ⟶ (ℰ ⊠ 𝒢)[0]` is an isomorphism** for `𝒢` finite locally free. -/
theorem isIso_boxSingleHom (E : X.Modules) (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G) :
    IsIso (boxSingleHom f g E G) := by
  rw [← boxSingleIso_hom f g E G hG]
  infer_instance

/-- The map `boxSingleHom f g ℰ 𝒢 : ℰ[0] ⊠ 𝒢[0] ⟶ (ℰ ⊠ 𝒢)[0]` is natural in `ℰ`. -/
theorem boxSingleHom_naturality_left {E E' : X.Modules} (a : E ⟶ E') (G : Y.Modules) :
    derivedBoxMapLeft f g ((DerivedCategory.singleFunctor X.Modules 0).map a) _ ≫
      boxSingleHom f g E' G =
    boxSingleHom f g E G ≫ (DerivedCategory.singleFunctor _ 0).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
        (pullback f g).toRingedSpace.sheaf).map
        ((Scheme.Modules.pullback (pullback.fst f g)).map a)).app
        ((Scheme.Modules.pullback (pullback.snd f g)).obj G)) :=
  Stacks.DegreeZeroTensor.three_sq _ _ _ _ _ _ _ _ _ _
    (Stacks.DegreeZeroTensor.map_sq (derivedTensorProductFunctor _ ⋙
      (evaluation _ _).obj ((dpull (pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G))) _ _ _ _
      ((dpullSingleIsoOfIsFlat (pullback.fst f g)
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)).hom.naturality a))
    ((((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).map
      ((DerivedCategory.singleFunctor _ 0).map
        ((Scheme.Modules.pullback (pullback.fst f g)).map a))).naturality
      ((dpullSingleIsoOfIsFlat (pullback.snd f g)
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)).hom.app G)).symm)
    (tensorSingleHom_naturality_left (pullback f g).toRingedSpace.sheaf
      ((Scheme.Modules.pullback (pullback.fst f g)).map a)
      ((Scheme.Modules.pullback (pullback.snd f g)).obj G))

/-- The map `boxSingleHom f g ℰ 𝒢 : ℰ[0] ⊠ 𝒢[0] ⟶ (ℰ ⊠ 𝒢)[0]` is natural in `𝒢`. -/
theorem boxSingleHom_naturality_right (E : X.Modules) {G G' : Y.Modules} (b : G ⟶ G') :
    derivedBoxMapRight f g _ ((DerivedCategory.singleFunctor Y.Modules 0).map b) ≫
      boxSingleHom f g E G' =
    boxSingleHom f g E G ≫ (DerivedCategory.singleFunctor _ 0).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
        (pullback f g).toRingedSpace.sheaf).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj E)).map
        ((Scheme.Modules.pullback (pullback.snd f g)).map b)) :=
  Stacks.DegreeZeroTensor.three_sq _ _ _ _ _ _ _ _ _ _
    (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).map
      ((dpullSingleIsoOfIsFlat (pullback.fst f g)
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)).hom.app E)).naturality
      ((dpull (pullback.snd f g)).map ((DerivedCategory.singleFunctor Y.Modules 0).map b)))
    (Stacks.DegreeZeroTensor.map_sq ((derivedTensorProductFunctor _).obj _) _ _ _ _
      ((dpullSingleIsoOfIsFlat (pullback.snd f g)
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)).hom.naturality b))
    (tensorSingleHom_naturality_right (pullback f g).toRingedSpace.sheaf
      ((Scheme.Modules.pullback (pullback.fst f g)).obj E)
      ((Scheme.Modules.pullback (pullback.snd f g)).map b))

/-- **Naturality of `ℰ[0] ⊠ 𝒢[0] ⟶ (ℰ ⊠ 𝒢)[0]` in both factors.** -/
theorem boxSingleHom_naturality {E E' : X.Modules} {G G' : Y.Modules} (a : E ⟶ E')
    (b : G ⟶ G') :
    derivedBoxMap f g ((DerivedCategory.singleFunctor X.Modules 0).map a)
        ((DerivedCategory.singleFunctor Y.Modules 0).map b) ≫ boxSingleHom f g E' G' =
      boxSingleHom f g E G ≫
        (DerivedCategory.singleFunctor _ 0).map (externalTensorProductMap f g a b) :=
  (Category.assoc _ _ _).trans
    ((congrArg (derivedBoxMapLeft f g ((DerivedCategory.singleFunctor X.Modules 0).map a) _ ≫ ·)
      (boxSingleHom_naturality_right f g E' b)).trans
    ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (boxSingleHom_naturality_left f g a G)).trans
    ((Category.assoc _ _ _).trans
    (congrArg (boxSingleHom f g E G ≫ ·)
      ((DerivedCategory.singleFunctor _ 0).map_comp _ _).symm)))))

end Box

end AlgebraicGeometry
