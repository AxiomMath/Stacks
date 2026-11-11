module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.CategoryTheory.Functor.Bifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact

/-!
# The derived tensor product of a derived pullback with a module flat over the base

Let `f : X ⟶ Y` be a morphism of schemes, `F` an `𝒪_Y`-module and `G` an `𝒪_X`-module flat
over `Y`. Then `Lf^*(F[-n]) ⊗ᴸ_{𝒪_X} G[0] ≅ (f^*F ⊗_{𝒪_X} G)[-n]` for every `n`.

Choose a K-flat resolution `Q ⟶ F[-n]`. Then `Lf^*(F[-n])` is represented by the K-flat complex
`f^*Q`, so the derived tensor product is `Tot(f^*Q ⊗ G[0])`, which is `f^*Q ⊗ G` degreewise.
The functor `F ↦ f^*F ⊗ G` is exact ([Stacks, Tag 0GMU]), so it carries the quasi-isomorphism
`Q ⟶ F[-n]` to a quasi-isomorphism onto `(f^*F ⊗ G)[-n]`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For `G` flat over the base, the isomorphism `Lf^*L ⊗ᴸ G[0] ≅ T(L)` of the derived tensor
product with the image of a complex `L` of `𝒪_Y`-modules under the exact functor
`T : F ↦ f^*F ⊗ G`, applied degreewise. It is computed through a chosen K-flat resolution
`Q ⟶ L`: `Lf^*L ≅ f^*Q`, `f^*Q ⊗ᴸ G[0] ≅ Tot(f^*Q ⊗ G[0]) = T(Q)`, and `T(Q) ≅ T(L)` since `T`
is exact. -/
def derivedTensorDerivedPullbackQIso
    (L : CochainComplex Y.Modules ℤ) (G : X.Modules) (hG : IsFlatOver f.toLRSHom.toShHom G)
    [(Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom G).Additive] :
    ((derivedTensor X).obj ((derivedPullback f).obj (DerivedCategory.Q.obj L))).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≅
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom G).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) := by
  let hres := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y.toRingedSpace L
  let Q := hres.choose
  let q : Q ⟶ L := hres.choose_spec.choose
  have hQ := hres.choose_spec.choose_spec.1
  have hq : QuasiIso q := hres.choose_spec.choose_spec.2.2.1
  let T := Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom G
  have hT := Stacks.SheafOfModules.pullbackTensorFunctor_exact f.toLRSHom.toShHom G hG
  have : PreservesFiniteLimits T := ((exactFunctor_iff T).mp hT).1
  have : PreservesFiniteColimits T := ((exactFunctor_iff T).mp hT).2
  have := hq
  let P : TensorComplex X := ((RingedSpaceModuleAdjunction.modulePullback
    f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q
  have hP : KFlatComplex P :=
    Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional
      f.toLRSHom.toShHom Q hQ
  have hTq : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q T
  have : IsIso (DerivedCategory.Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  have hTQ : IsIso (DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hTq
  let e1 : (derivedPullback f).obj (DerivedCategory.Q.obj L) ≅
      (DerivedCategory.Q.obj P : DerivedCategory X.Modules) :=
    (derivedPullback f).mapIso (asIso (DerivedCategory.Q.map q)).symm ≪≫
    Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom Q hQ
  let e2 : ((derivedTensor X).obj (DerivedCategory.Q.obj P)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≅
      (DerivedCategory.Q.obj (totalTensorComplex P
        ((CochainComplex.singleFunctor X.Modules 0).obj G)) : DerivedCategory X.Modules) :=
    ((derivedTensor X).obj (DerivedCategory.Q.obj P)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app G) ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparisonLeft P _ hP
  have hflip :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj G).Additive :=
    @Functor.flip_obj_additive _ _ _ _ _ _ _ _ _
      (Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive X.sheaf) G
  let e3 : totalTensorComplex P ((CochainComplex.singleFunctor X.Modules 0).obj G) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q :=
    HomologicalComplex.mapBifunctorSingleRightIso
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) P G
  exact ((derivedTensor X).mapIso e1).app _ ≪≫ e2 ≪≫ DerivedCategory.Q.mapIso e3 ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map q))
      hTQ

/-- For `G` flat over the base, `Lf^*L ⊗ᴸ G[0]` is the image of a complex `L` of `𝒪_Y`-modules
under the exact functor `F ↦ f^*F ⊗ G`, applied degreewise. -/
private theorem nonempty_derivedTensor_derivedPullback_Q_iso
    (L : CochainComplex Y.Modules ℤ) (G : X.Modules) (hG : IsFlatOver f.toLRSHom.toShHom G)
    [(Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom G).Additive] :
    Nonempty (((derivedTensor X).obj ((derivedPullback f).obj (DerivedCategory.Q.obj L))).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≅
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom G).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) :=
  ⟨derivedTensorDerivedPullbackQIso f L G hG⟩

/-- **`Lf^*(F[-n]) ⊗ᴸ G[0] ≅ (f^*F ⊗ G)[-n]` for `G` flat over the base.** For a morphism of
schemes `f : X ⟶ Y`, an `𝒪_Y`-module `F` placed in degree `n` and an `𝒪_X`-module `G` flat
over `Y`, the derived tensor product of `Lf^*F` with `G[0]` is the module `f^*F ⊗_{𝒪_X} G`
placed in degree `n`. -/
theorem nonempty_derivedTensor_derivedPullback_single_iso (n : ℤ) (F : Y.Modules) (G : X.Modules)
    (hG : IsFlatOver f.toLRSHom.toShHom G) :
    Nonempty ((((derivedTensor X).obj ((derivedPullback f).obj
        ((DerivedCategory.singleFunctor Y.Modules n).obj F))).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)) ≅
      (DerivedCategory.singleFunctor X.Modules n).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          ((Scheme.Modules.pullback f).obj F)).obj G)) := by
  let T := Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom G
  have : T.Additive := Stacks.SheafOfModules.additive_pullbackTensorFunctor _ G
  obtain ⟨e⟩ := nonempty_derivedTensor_derivedPullback_Q_iso f
    ((CochainComplex.singleFunctor Y.Modules n).obj F) G hG
  let e5 : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor Y.Modules n).obj F) ≅
      (CochainComplex.singleFunctor X.Modules n).obj (T.obj F) :=
    (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n).app F
  exact ⟨((derivedTensor X).mapIso ((derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ Y.Modules n).app F))).app _ ≪≫ e ≪≫
    DerivedCategory.Q.mapIso e5 ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules n).app
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
        ((Scheme.Modules.pullback f).obj F)).obj G)).symm⟩

/-- **`Hⁱ(Lf^*K ⊗ᴸ G[0]) ≅ f^*Hⁱ(K) ⊗ G` for `G` flat over the base**, for every
`K ∈ D(𝒪_Y)`: with a K-flat resolution `Q ⟶ K`, the derived tensor product is `f^*Q ⊗ G`, and
`F ↦ f^*F ⊗ G` is exact ([Stacks, Tag 0GMU]), so it commutes with cohomology. The isomorphism
goes through a chosen representative `L` of `K` and `derivedTensorDerivedPullbackQIso`. -/
def homologyDerivedTensorDerivedPullbackIso (K : DerivedCategory Y.Modules)
    (G : X.Modules) (hG : IsFlatOver f.toLRSHom.toShHom G) (i : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules i).obj
        (((derivedTensor X).obj ((derivedPullback f).obj K)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          ((Scheme.Modules.pullback f).obj
            ((DerivedCategory.homologyFunctor Y.Modules i).obj K))).obj
        G := by
  let L := DerivedCategory.Q.objPreimage K
  let eL : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let T := Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom G
  have : T.Additive := Stacks.SheafOfModules.additive_pullbackTensorFunctor _ G
  have hT := Stacks.SheafOfModules.pullbackTensorFunctor_exact f.toLRSHom.toShHom G hG
  have : PreservesFiniteLimits T := ((exactFunctor_iff T).mp hT).1
  have : PreservesFiniteColimits T := ((exactFunctor_iff T).mp hT).2
  let e := derivedTensorDerivedPullbackQIso f L G hG
  let eD : ((derivedTensor X).obj ((derivedPullback f).obj K)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≅
      DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    ((derivedTensor X).mapIso ((derivedPullback f).mapIso eL.symm)).app _ ≪≫ e
  let e5 : (DerivedCategory.homologyFunctor X.Modules i).obj
      (DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) ≅
      T.obj ((HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℤ) i).obj L) :=
    (DerivedCategory.homologyFunctorFactors X.Modules i).app _ ≪≫
      (T.mapHomologicalComplexHomologyFunctorIso i).app L
  let e6 : T.obj ((HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℤ) i).obj L) ≅
      T.obj ((DerivedCategory.homologyFunctor Y.Modules i).obj K) :=
    T.mapIso (((DerivedCategory.homologyFunctorFactors Y.Modules i).app L).symm ≪≫
      (DerivedCategory.homologyFunctor Y.Modules i).mapIso eL)
  exact (DerivedCategory.homologyFunctor X.Modules i).mapIso eD ≪≫ e5 ≪≫ e6

/-- **`Hⁱ(Lf^*K ⊗ᴸ G[0]) ≅ f^*Hⁱ(K) ⊗ G` for `G` flat over the base**, for every
`K ∈ D(𝒪_Y)`: with a K-flat resolution `Q ⟶ K`, the derived tensor product is `f^*Q ⊗ G`, and
`F ↦ f^*F ⊗ G` is exact ([Stacks, Tag 0GMU]), so it commutes with cohomology. -/
theorem nonempty_homology_derivedTensor_derivedPullback_iso (K : DerivedCategory Y.Modules)
    (G : X.Modules) (hG : IsFlatOver f.toLRSHom.toShHom G) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor X.Modules i).obj
        (((derivedTensor X).obj ((derivedPullback f).obj K)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          ((Scheme.Modules.pullback f).obj
            ((DerivedCategory.homologyFunctor Y.Modules i).obj K))).obj
        G) :=
  ⟨homologyDerivedTensorDerivedPullbackIso f K G hG i⟩

end Stacks.Duality

end
