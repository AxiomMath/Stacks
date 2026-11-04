module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistMultiplication
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Veronese comparison and the multiplication of twisted modules (Tags 03GJ and 03GK)

Let `S` be a graded ring, `d ≥ 1`, `S' = S⁽ᵈ⁾`, `i : X = Proj S ≅ X' = Proj S'` the Veronese
isomorphism and `T_n : 𝒪_X(nd) ≅ i^*𝒪_{X'}(n)` the isomorphisms of Tag 0B5J's assertion (2). For
a sheaf of modules `ℱ'` on `X'` and `ℱ = i^*ℱ'`, `T_m` tensored with `ℱ` and followed by
Tag 01CD gives `ℱ(md) ≅ i^*(ℱ'(m))` (`Stacks.Veronese.veroneseTwistedModuleIso`). This file
proves that these isomorphisms are compatible with the multiplication maps
`𝒪(n) ⊗ ℱ(m) ⟶ ℱ(n + m)` of Tag 03GJ (`Stacks.Veronese.veroneseTwistSheafMulCompatibility`) and
hence with the products of global sections that define the module structure of Tag 03GK
(`Stacks.Veronese.veroneseMultiplyHomogeneousSectionsCompatibility`).

## Implementation notes

Both are deduced from the compatibility with the multiplication of twists,
`Stacks.Veronese.veroneseTwistMulCompatibility`, by a general argument for any isomorphism `g`
of projective spectra (`Stacks.Veronese.twistedMul_compatibility`). Since `g` is an isomorphism,
every open of the source is a preimage and every section of a pulled-back sheaf of modules over a
preimage is a pulled-back section (`exists_modulesPullbackUnit_eq`); so both sides of the square
may be compared on nested pure tensors `x ⊗ (y ⊗ z)` with `y` and the images of `x`, `z` pulled
back, where both send the triple to the pullback of `y ⊗ x'z'`
(`tensorSheaf_hom_ext_right_toTensorSheafSection`, `twistedMulLeft_tmul`,
`twistedMulRight_tmul`). The general statements carry no Veronese data, which keeps the kernel's
definitional checks cheap.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGrading twistingSheaf
  twistSheafOfModules twistSheafMultiplicationMap)
open scoped TensorProduct

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w

/-- Along an isomorphism of schemes, every section of a pulled-back sheaf of modules over the
preimage of an open is the pullback of a section over that open. -/
public theorem exists_modulesPullbackUnit_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (G : Y.Modules) (W : Y.Opens) (s : Γ((Scheme.Modules.pullback g).obj G, g ⁻¹ᵁ W)) :
    ∃ s' : Γ(G, W), Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g G W s' = s := by
  have h1 : (Scheme.Modules.pushforward g).IsEquivalence :=
    AlgebraicGeometry.Scheme.Hom.pushforward_isEquivalence_of_isIso.{u, u} g
  have h2 :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isEquivalence_left_of_isEquivalence_right
  have h3 : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app G) := inferInstance
  refine ⟨Scheme.Modules.Hom.app
    (inv ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app G)) W s, ?_⟩
  show Scheme.Modules.Hom.app (inv ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app G) ≫
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app G) W s = s
  rw [IsIso.inv_hom_id]
  rfl

/-- Every open of the source of an isomorphism of schemes is a preimage. -/
public theorem exists_preimage_eq_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (U : X.Opens) :
    ∃ W : Y.Opens, g ⁻¹ᵁ W = U :=
  ⟨inv g ⁻¹ᵁ U, by rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id, Scheme.Hom.id_preimage]⟩

section Generic

open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)

/-- **Two morphisms out of `A ⊗ (B ⊗ C)` agreeing on the nested pure tensors of local sections
are equal**, for the tensor product sheaf of a ringed space. -/
public theorem tensorSheaf_hom_ext_right_toTensorSheafSection
    (X : _root_.AlgebraicGeometry.RingedSpace.{u, u})
    {A B C Q : SheafOfModules.{u} (_root_.structureSheafRing X)}
    (φ ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (A)).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (B)).obj (C))))) ⟶ Q)
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) (z : C.val.obj U),
      (φ.val.app U).hom (toTensorSheafSection X A
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (B)).obj (C))) U
          (x ⊗ₜ toTensorSheafSection X B C U (y ⊗ₜ z))) =
        (ψ.val.app U).hom (toTensorSheafSection X A
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (B)).obj (C))) U
          (x ⊗ₜ toTensorSheafSection X B C U (y ⊗ₜ z)))) :
    φ = ψ := by
  have hls : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
        ((PresheafOfModules.tensorObj (O := (X).presheaf) (B.val) (C.val)))) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app _ _
  have key := @Stacks.SheafOfModules.TopWedge.tensorObj_hom_ext_of_isLocallySurjective_right
    _ _ (Opens.grothendieckTopology X.carrier) _ _ _ _ _ _ Q.isSheaf.isSeparated
    (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
      ((PresheafOfModules.tensorObj (O := (X).presheaf) (B.val) (C.val)))) hls
    (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
      ((PresheafOfModules.tensorObj (O := (X).presheaf) (A.val)
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (B)).obj (C))).val))) ≫ φ.val)
    (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
      ((PresheafOfModules.tensorObj (O := (X).presheaf) (A.val)
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (B)).obj (C))).val))) ≫ ψ.val)
    h
  exact Stacks.SheafOfModules.TensorStalkRingedSpace.hom_ext_toTensorSheafSection X φ ψ
    fun U x t => PresheafOfModules.hom_congr_apply' key U (x ⊗ₜ t)

variable {A B : Type u} {ςA ςB : Type*} [CommRing A] [CommRing B]
  [SetLike ςA A] [AddSubgroupClass ςA A] (𝒜 : ℕ → ςA) [GradedRing 𝒜]
  [SetLike ςB B] [AddSubgroupClass ςB B] (ℬ : ℕ → ςB) [GradedRing ℬ]
  (g : _root_.AlgebraicGeometry.Proj 𝒜 ⟶ _root_.AlgebraicGeometry.Proj ℬ)
  (F' : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top ℬ))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf ℬ)))

/-- The product of a section of `𝒪(a)` and a section of `ℱ(b)` over `⊤` by the multiplication of
Tag 03GJ, for integer `a`; at `a = n ∈ ℕ` this is the product of Tag 03GK,
`AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections`, by definition. -/
public abbrev _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections'
    {A : Type u} {ς : Type*} [CommRing A] [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς)
    [GradedRing 𝒜]
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒜)))
    (a b : ℤ) (x : (twistingSheaf 𝒜 a).val.obj (op ⊤))
    (w : (twistSheafOfModules 𝒜 F b).val.obj (op ⊤)) :
    (twistSheafOfModules 𝒜 F (a + b)).val.obj (op ⊤) :=
  ((twistSheafMultiplicationMap 𝒜 F a b).val.app (op ⊤)).hom
    (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
      (twistingSheaf 𝒜 a) (twistSheafOfModules 𝒜 F b) (op ⊤) (x ⊗ₜ w))

/-- The pullback of `F'` along `g`, as a sheaf of modules on `Proj 𝒜` in the spelling the twists
are formed in. -/
public abbrev pullbackProjModule :
    SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒜)) :=
  (Scheme.Modules.pullback g).obj F'

/-- A morphism `T : 𝒪(k) ⟶ g^*𝒪'(k')`, tensored with the pullback `g^*ℱ'` and followed by
Tag 01CD: the induced morphism `(g^*ℱ')(k) ⟶ g^*(ℱ'(k'))`. -/
public def twistedPullbackMap (k k' : ℤ)
    (T : twistingSheaf 𝒜 k ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ k')) :
    twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') k ⟶
      (Scheme.Modules.pullback g).obj (twistSheafOfModules ℬ F' k') := by
  exact (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf,
        (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace.IsSheaf⟩)).map
      (X := ((Scheme.Modules.pullback g).obj F', twistingSheaf 𝒜 k))
      (Y := ((Scheme.Modules.pullback g).obj F',
        (Scheme.Modules.pullback g).obj (twistingSheaf ℬ k')))
      (𝟙 _, T) ≫
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g F' (twistingSheaf ℬ k')).inv

/-- `twistedPullbackMap` on the pure tensor of a pulled-back section of `ℱ'` and a section of
`𝒪(k)` whose image under `T` is a pulled-back section. -/
public theorem twistedPullbackMap_tmul (k k' : ℤ)
    (T : twistingSheaf 𝒜 k ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ k'))
    (W : (_root_.AlgebraicGeometry.Proj ℬ).Opens) (y : F'.val.obj (op W))
    (z : (twistingSheaf 𝒜 k).val.obj (op (g ⁻¹ᵁ W))) (z' : (twistingSheaf ℬ k').val.obj (op W))
    (hz : (T.val.app (op (g ⁻¹ᵁ W))).hom z =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ k') W z') :
    ((twistedPullbackMap 𝒜 ℬ g F' k k' T).val.app (op (g ⁻¹ᵁ W))).hom
        (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
          ((Scheme.Modules.pullback g).obj F') (twistingSheaf 𝒜 k) (op (g ⁻¹ᵁ W))
          (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F' W y ⊗ₜ z)) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' k') W
        (toTensorSheafSection (_root_.AlgebraicGeometry.Proj ℬ).toRingedSpace F'
          (twistingSheaf ℬ k') (op W) (y ⊗ₜ z')) := by
  have h1 := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
    (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace _ _ _ _
    (𝟙 ((Scheme.Modules.pullback g).obj F')) T (g ⁻¹ᵁ W)
    (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F' W y) z
  have h2 := h1.trans (congrArg (fun t =>
    toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
      ((Scheme.Modules.pullback g).obj F')
      ((Scheme.Modules.pullback g).obj (twistingSheaf ℬ k')) (op (g ⁻¹ᵁ W))
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F' W y ⊗ₜ t)) hz)
  refine (congrArg (fun t => Scheme.Modules.Hom.app
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g F' (twistingSheaf ℬ k')).inv
    (g ⁻¹ᵁ W) t) h2).trans ?_
  exact schemePullbackTensorIso_inv_toTensorSheafSection g F' (twistingSheaf ℬ k') W y z'

/-- The upper path of the 03GJ square for a morphism `g` of projective spectra: multiply on
`Proj 𝒜`, then transport by `twistedPullbackMap`. -/
public def twistedMulLeft (a b a' b' : ℤ)
    (Tab : twistingSheaf 𝒜 (a + b) ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b'))) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace)).IsSheaf⟩).obj
        ((twistingSheaf 𝒜 a))).obj ((twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b))) ⟶
      (Scheme.Modules.pullback g).obj (twistSheafOfModules ℬ F' (a' + b')) :=
  twistSheafMultiplicationMap 𝒜 (pullbackProjModule 𝒜 ℬ g F') a b ≫
    twistedPullbackMap 𝒜 ℬ g F' (a + b) (a' + b') Tab

/-- The lower path of the 03GJ square for a morphism `g` of projective spectra. -/
public def twistedMulRight (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b')) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace)).IsSheaf⟩).obj
        ((twistingSheaf 𝒜 a))).obj ((twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b))) ⟶
      (Scheme.Modules.pullback g).obj (twistSheafOfModules ℬ F' (a' + b')) := by
  exact (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf,
        (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace.IsSheaf⟩)).map
      (X := (twistingSheaf 𝒜 a, twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b))
      (Y := ((Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'),
        (Scheme.Modules.pullback g).obj (twistSheafOfModules ℬ F' b')))
      (Ta, twistedPullbackMap 𝒜 ℬ g F' b b' Tb) ≫
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g (twistingSheaf ℬ a')
      (twistSheafOfModules ℬ F' b')).inv ≫
    (Scheme.Modules.pullback g).map (twistSheafMultiplicationMap ℬ F' a' b')

/-- The 01MO square for `g`: the maps `T` carry the multiplication of twists on `Proj ℬ` to the
one on `Proj 𝒜`. This is the hypothesis of `twistedMul_compatibility`. -/
public def TwistMulSquare (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (Tab : twistingSheaf 𝒜 (a + b) ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b'))) :
    Prop :=
  ∀ (U : (_root_.AlgebraicGeometry.Proj 𝒜).Opens)
    (x : (twistingSheaf 𝒜 a).val.obj (op U)) (z : (twistingSheaf 𝒜 b).val.obj (op U)),
    (Tab.val.app (op U)).hom
        ((Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒜 a b).val.app
          (op U) |>.hom
          (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
            (twistingSheaf 𝒜 a) (twistingSheaf 𝒜 b) (op U) (x ⊗ₜ z))) =
      (((Scheme.Modules.pullback g).map
          (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap ℬ a' b')).val.app
          (op U)).hom
        ((Scheme.Modules.Hom.app (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g
            (twistingSheaf ℬ a') (twistingSheaf ℬ b')).inv U)
          (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
            ((Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
            ((Scheme.Modules.pullback g).obj (twistingSheaf ℬ b')) (op U)
            ((Ta.val.app (op U)).hom x ⊗ₜ (Tb.val.app (op U)).hom z)))

/-- The pullback of a map out of a tensor product, applied to the pullback of a pure tensor of
pulled-back sections, is the pullback of the map applied to the pure tensor. -/
private theorem pullback_map_tensor_unit {X Y : Scheme.{u}} (g : X ⟶ Y) (A B C : Y.Modules)
    (φ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y.toRingedSpace)).presheaf,
            ((Y.toRingedSpace)).IsSheaf⟩).obj (A)).obj (B)) ⟶ C)
    (U : Y.Opens) (x : A.val.obj (op U)) (y : B.val.obj (op U)) :
    (((Scheme.Modules.pullback g).map φ).val.app (op (g ⁻¹ᵁ U))).hom
        (Scheme.Modules.Hom.app (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).inv
          (g ⁻¹ᵁ U)
          (toTensorSheafSection X.toRingedSpace ((Scheme.Modules.pullback g).obj A)
            ((Scheme.Modules.pullback g).obj B) (op (g ⁻¹ᵁ U))
            (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g A U x ⊗ₜ
              Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g B U y))) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g C U
        ((φ.val.app (op U)).hom (toTensorSheafSection Y.toRingedSpace A B (op U) (x ⊗ₜ y))) :=
  (congrArg _ (schemePullbackTensorIso_inv_toTensorSheafSection g A B U x y)).trans
    (modulesPullbackUnit_naturality g φ U _)

/-- Under the 01MO square, `T_{a+b}` sends the product of two sections whose images are pulled
back to the pullback of the product upstairs. -/
public theorem twistMulSquare_apply (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (Tab : twistingSheaf 𝒜 (a + b) ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b')))
    (H : TwistMulSquare 𝒜 ℬ g a b a' b' Ta Tb Tab)
    (W : (_root_.AlgebraicGeometry.Proj ℬ).Opens)
    (x : (twistingSheaf 𝒜 a).val.obj (op (g ⁻¹ᵁ W)))
    (z : (twistingSheaf 𝒜 b).val.obj (op (g ⁻¹ᵁ W)))
    (x' : (twistingSheaf ℬ a').val.obj (op W)) (z' : (twistingSheaf ℬ b').val.obj (op W))
    (hx : (Ta.val.app (op (g ⁻¹ᵁ W))).hom x =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ a') W x')
    (hz : (Tb.val.app (op (g ⁻¹ᵁ W))).hom z =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ b') W z') :
    (Tab.val.app (op (g ⁻¹ᵁ W))).hom
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyTwistSections 𝒜 a b (g ⁻¹ᵁ W) x z) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ (a' + b')) W
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyTwistSections ℬ a' b' W x' z') := by
  refine (H (g ⁻¹ᵁ W) x z).trans ?_
  rw [hx, hz]
  exact pullback_map_tensor_unit g _ _ _
    (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap ℬ a' b') W x' z'

/-- The upper path of the 03GJ square on a nested pure tensor of sections whose images are
pulled back. -/
public theorem twistedMulLeft_tmul (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (Tab : twistingSheaf 𝒜 (a + b) ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b')))
    (H : TwistMulSquare 𝒜 ℬ g a b a' b' Ta Tb Tab)
    (W : (_root_.AlgebraicGeometry.Proj ℬ).Opens)
    (x : (twistingSheaf 𝒜 a).val.obj (op (g ⁻¹ᵁ W))) (y : F'.val.obj (op W))
    (z : (twistingSheaf 𝒜 b).val.obj (op (g ⁻¹ᵁ W)))
    (x' : (twistingSheaf ℬ a').val.obj (op W)) (z' : (twistingSheaf ℬ b').val.obj (op W))
    (hx : (Ta.val.app (op (g ⁻¹ᵁ W))).hom x =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ a') W x')
    (hz : (Tb.val.app (op (g ⁻¹ᵁ W))).hom z =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ b') W z') :
    ((twistedMulLeft 𝒜 ℬ g F' a b a' b' Tab).val.app (op (g ⁻¹ᵁ W))).hom
        (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
          (twistingSheaf 𝒜 a) (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b)
          (op (g ⁻¹ᵁ W))
          (x ⊗ₜ toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
            ((Scheme.Modules.pullback g).obj F') (twistingSheaf 𝒜 b) (op (g ⁻¹ᵁ W))
            (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F' W y ⊗ₜ z))) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' (a' + b')) W
        (toTensorSheafSection (_root_.AlgebraicGeometry.Proj ℬ).toRingedSpace F'
          (twistingSheaf ℬ (a' + b')) (op W)
          (y ⊗ₜ
            AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyTwistSections ℬ a' b' W x' z')) := by
  have h1 := AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap_pureTensorSection
    𝒜 (pullbackProjModule 𝒜 ℬ g F') a b (g ⁻¹ᵁ W) x
    (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F' W y) z
  refine (congrArg (fun t => ((twistedPullbackMap 𝒜 ℬ g F' (a + b) (a' + b') Tab).val.app
    (op (g ⁻¹ᵁ W))).hom t) h1).trans ?_
  exact twistedPullbackMap_tmul 𝒜 ℬ g F' (a + b) (a' + b') Tab W y _ _
    (twistMulSquare_apply 𝒜 ℬ g a b a' b' Ta Tb Tab H W x z x' z' hx hz)

/-- The lower path of the 03GJ square on a nested pure tensor of sections whose images are
pulled back. -/
public theorem twistedMulRight_tmul (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (W : (_root_.AlgebraicGeometry.Proj ℬ).Opens)
    (x : (twistingSheaf 𝒜 a).val.obj (op (g ⁻¹ᵁ W))) (y : F'.val.obj (op W))
    (z : (twistingSheaf 𝒜 b).val.obj (op (g ⁻¹ᵁ W)))
    (x' : (twistingSheaf ℬ a').val.obj (op W)) (z' : (twistingSheaf ℬ b').val.obj (op W))
    (hx : (Ta.val.app (op (g ⁻¹ᵁ W))).hom x =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ a') W x')
    (hz : (Tb.val.app (op (g ⁻¹ᵁ W))).hom z =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ b') W z') :
    ((twistedMulRight 𝒜 ℬ g F' a b a' b' Ta Tb).val.app (op (g ⁻¹ᵁ W))).hom
        (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
          (twistingSheaf 𝒜 a) (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b)
          (op (g ⁻¹ᵁ W))
          (x ⊗ₜ toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
            ((Scheme.Modules.pullback g).obj F') (twistingSheaf 𝒜 b) (op (g ⁻¹ᵁ W))
            (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F' W y ⊗ₜ z))) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' (a' + b')) W
        (toTensorSheafSection (_root_.AlgebraicGeometry.Proj ℬ).toRingedSpace F'
          (twistingSheaf ℬ (a' + b')) (op W)
          (y ⊗ₜ
            AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyTwistSections ℬ a' b' W x' z')) := by
  have h1 := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
    (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace _ _ _ _ Ta
    (twistedPullbackMap 𝒜 ℬ g F' b b' Tb) (g ⁻¹ᵁ W) x
    (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
      ((Scheme.Modules.pullback g).obj F') (twistingSheaf 𝒜 b) (op (g ⁻¹ᵁ W))
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F' W y ⊗ₜ z))
  erw [hx, twistedPullbackMap_tmul 𝒜 ℬ g F' b b' Tb W y z z' hz] at h1
  refine (congrArg (fun t => (((Scheme.Modules.pullback g).map
      (twistSheafMultiplicationMap ℬ F' a' b')).val.app (op (g ⁻¹ᵁ W))).hom
      ((Scheme.Modules.Hom.app (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g
        (twistingSheaf ℬ a') (twistSheafOfModules ℬ F' b')).inv (g ⁻¹ᵁ W)) t)) h1).trans ?_
  refine (pullback_map_tensor_unit g _ _ _ (twistSheafMultiplicationMap ℬ F' a' b') W x' _).trans ?_
  exact congrArg (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g
      (twistSheafOfModules ℬ F' (a' + b')) W)
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap_pureTensorSection
      ℬ F' a' b' W x' y z')

/-- **The 03GJ square for an isomorphism of projective spectra.** If isomorphism `g` and maps
`T : 𝒪(k) ⟶ g^*𝒪'(k')` carry the multiplication of twists on `Proj ℬ` to that on `Proj 𝒜`, then
for every sheaf of modules `ℱ'` on `Proj ℬ` the induced maps `(g^*ℱ')(k) ⟶ g^*(ℱ'(k'))` carry
the multiplication `𝒪(a') ⊗ ℱ'(b') ⟶ ℱ'(a' + b')` to `𝒪(a) ⊗ (g^*ℱ')(b) ⟶ (g^*ℱ')(a + b)`. -/
public theorem twistedMul_compatibility [IsIso g] (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (Tab : twistingSheaf 𝒜 (a + b) ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b')))
    (H : TwistMulSquare 𝒜 ℬ g a b a' b' Ta Tb Tab) :
    twistedMulLeft 𝒜 ℬ g F' a b a' b' Tab = twistedMulRight 𝒜 ℬ g F' a b a' b' Ta Tb := by
  refine tensorSheaf_hom_ext_right_toTensorSheafSection
    (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
    (A := twistingSheaf 𝒜 a) (B := (Scheme.Modules.pullback g).obj F')
    (C := twistingSheaf 𝒜 b) _ _ ?_
  rintro ⟨U⟩ x y z
  obtain ⟨W, rfl⟩ := exists_preimage_eq_of_isIso g U
  obtain ⟨y', rfl⟩ := exists_modulesPullbackUnit_eq g F' W y
  obtain ⟨x', hx⟩ := exists_modulesPullbackUnit_eq g (twistingSheaf ℬ a') W
    ((Ta.val.app (op (g ⁻¹ᵁ W))).hom x)
  obtain ⟨z', hz⟩ := exists_modulesPullbackUnit_eq g (twistingSheaf ℬ b') W
    ((Tb.val.app (op (g ⁻¹ᵁ W))).hom z)
  exact (twistedMulLeft_tmul 𝒜 ℬ g F' a b a' b' Ta Tb Tab H W x y' z x' z' hx.symm hz.symm).trans
    (twistedMulRight_tmul 𝒜 ℬ g F' a b a' b' Ta Tb W x y' z x' z' hx.symm hz.symm).symm

/-- `twistedPullbackMap` of an isomorphism, as an isomorphism. -/
public def twistedPullbackIso (k k' : ℤ)
    (T : twistingSheaf 𝒜 k ≅ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ k')) :
    twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') k ≅
      (Scheme.Modules.pullback g).obj (twistSheafOfModules ℬ F' k') := by
  change (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(((_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace)).presheaf,
        (((_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace)).IsSheaf⟩).obj
      (((Scheme.Modules.pullback g).obj F'))).obj ((twistingSheaf 𝒜 k))) ≅ _
  exact Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl _) T ≪≫
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g F' (twistingSheaf ℬ k')).symm

/-- The isomorphism `twistedPullbackIso` is `twistedPullbackMap`. -/
public theorem twistedPullbackIso_hom (k k' : ℤ)
    (T : twistingSheaf 𝒜 k ≅ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ k')) :
    (twistedPullbackIso 𝒜 ℬ g F' k k' T).hom = twistedPullbackMap 𝒜 ℬ g F' k k' T.hom :=
  rfl

/-- Reindexing the source twist of `twistedPullbackMap`. -/
public theorem twistedPullbackMap_eqToHom {k₁ k₂ : ℤ} (h : k₁ = k₂) (k' : ℤ)
    (T : twistingSheaf 𝒜 k₂ ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ k')) :
    twistedPullbackMap 𝒜 ℬ g F' k₁ k' (eqToHom (congrArg (twistingSheaf 𝒜) h) ≫ T) =
      eqToHom (congrArg (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F')) h) ≫
        twistedPullbackMap 𝒜 ℬ g F' k₂ k' T := by
  subst h
  rfl

/-- The 01MO square survives reindexing the first source twist. -/
public theorem twistMulSquare_cast {a₁ a : ℤ} (h : a₁ = a) (b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (Tab : twistingSheaf 𝒜 (a + b) ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b')))
    (H : TwistMulSquare 𝒜 ℬ g a b a' b' Ta Tb Tab) :
    TwistMulSquare 𝒜 ℬ g a₁ b a' b' (eqToHom (congrArg (twistingSheaf 𝒜) h) ≫ Ta) Tb
      (eqToHom (congrArg (twistingSheaf 𝒜) (congrArg (· + b) h)) ≫ Tab) := by
  subst h
  exact fun U x z => H U x z

/-- The lower path of the 03GJ square on the pure tensor of a section whose image is pulled back
and a section of `(g^*ℱ')(b)` whose image is pulled back. -/
public theorem twistedMulRight_tmul' (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (W : (_root_.AlgebraicGeometry.Proj ℬ).Opens)
    (x : (twistingSheaf 𝒜 a).val.obj (op (g ⁻¹ᵁ W)))
    (w : (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b).val.obj (op (g ⁻¹ᵁ W)))
    (x' : (twistingSheaf ℬ a').val.obj (op W)) (w' : (twistSheafOfModules ℬ F' b').val.obj (op W))
    (hx : (Ta.val.app (op (g ⁻¹ᵁ W))).hom x =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ a') W x')
    (hw : ((twistedPullbackMap 𝒜 ℬ g F' b b' Tb).val.app (op (g ⁻¹ᵁ W))).hom w =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' b') W w') :
    ((twistedMulRight 𝒜 ℬ g F' a b a' b' Ta Tb).val.app (op (g ⁻¹ᵁ W))).hom
        (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
          (twistingSheaf 𝒜 a) (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b)
          (op (g ⁻¹ᵁ W)) (x ⊗ₜ w)) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' (a' + b')) W
        (((twistSheafMultiplicationMap ℬ F' a' b').val.app (op W)).hom
          (toTensorSheafSection (_root_.AlgebraicGeometry.Proj ℬ).toRingedSpace
            (twistingSheaf ℬ a') (twistSheafOfModules ℬ F' b') (op W) (x' ⊗ₜ w'))) := by
  have h1 := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
    (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace _ _ _ _ Ta
    (twistedPullbackMap 𝒜 ℬ g F' b b' Tb) (g ⁻¹ᵁ W) x w
  erw [hx, hw] at h1
  refine (congrArg (fun t => (((Scheme.Modules.pullback g).map
      (twistSheafMultiplicationMap ℬ F' a' b')).val.app (op (g ⁻¹ᵁ W))).hom
      ((Scheme.Modules.Hom.app (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g
        (twistingSheaf ℬ a') (twistSheafOfModules ℬ F' b')).inv (g ⁻¹ᵁ W)) t)) h1).trans ?_
  exact pullback_map_tensor_unit g _ _ _ (twistSheafMultiplicationMap ℬ F' a' b') W x' w'

/-- **The 03GJ square on global sections**, for an isomorphism of projective spectra: products
of global sections whose images are pulled back are carried to the pullback of the product. -/
public theorem twistedMul_globalSections [IsIso g] (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (Tab : twistingSheaf 𝒜 (a + b) ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b')))
    (H : TwistMulSquare 𝒜 ℬ g a b a' b' Ta Tb Tab)
    (x : (twistingSheaf 𝒜 a).val.obj (op ⊤))
    (w : (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b).val.obj (op ⊤))
    (x' : (twistingSheaf ℬ a').val.obj (op ⊤)) (w' : (twistSheafOfModules ℬ F' b').val.obj (op ⊤))
    (hx : (Ta.val.app (op ⊤)).hom x =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ a') ⊤ x')
    (hw : ((twistedPullbackMap 𝒜 ℬ g F' b b' Tb).val.app (op ⊤)).hom w =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' b') ⊤ w') :
    ((twistedPullbackMap 𝒜 ℬ g F' (a + b) (a' + b') Tab).val.app (op ⊤)).hom
        (((twistSheafMultiplicationMap 𝒜 (pullbackProjModule 𝒜 ℬ g F') a b).val.app (op ⊤)).hom
          (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
            (twistingSheaf 𝒜 a) (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b)
            (op ⊤) (x ⊗ₜ w))) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' (a' + b')) ⊤
        (((twistSheafMultiplicationMap ℬ F' a' b').val.app (op ⊤)).hom
          (toTensorSheafSection (_root_.AlgebraicGeometry.Proj ℬ).toRingedSpace
            (twistingSheaf ℬ a') (twistSheafOfModules ℬ F' b') (op ⊤) (x' ⊗ₜ w'))) := by
  have hc := congrArg (fun φ => (φ.val.app (op (g ⁻¹ᵁ ⊤))).hom
      (toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
        (twistingSheaf 𝒜 a) (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b)
        (op (g ⁻¹ᵁ ⊤)) (x ⊗ₜ w)))
    (twistedMul_compatibility 𝒜 ℬ g F' a b a' b' Ta Tb Tab H)
  exact hc.trans (twistedMulRight_tmul' 𝒜 ℬ g F' a b a' b' Ta Tb ⊤ x w x' w' hx hw)

/-- The 01MO square only depends on `T_{a+b}` through its values on sections. -/
public theorem twistMulSquare_of_app_eq (a b a' b' : ℤ)
    (Ta : twistingSheaf 𝒜 a ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (Tab Tab' : twistingSheaf 𝒜 (a + b) ⟶
      (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b')))
    (hT : ∀ (U : (_root_.AlgebraicGeometry.Proj 𝒜).Opens)
      (y : (twistingSheaf 𝒜 (a + b)).val.obj (op U)),
      (Tab.val.app (op U)).hom y = (Tab'.val.app (op U)).hom y)
    (H : TwistMulSquare 𝒜 ℬ g a b a' b' Ta Tb Tab) :
    TwistMulSquare 𝒜 ℬ g a b a' b' Ta Tb Tab' :=
  fun U x z => (hT U _).symm.trans (H U x z)

/-- Two transports of a section of a twisting sheaf along equalities of twists compose. -/
public theorem eqToHom_twistingSheaf_app_trans {k₁ k₂ k₃ : ℤ} (e₁ : k₁ = k₂) (e₂ : k₂ = k₃)
    (U : (_root_.AlgebraicGeometry.Proj 𝒜).Opens) (y : (twistingSheaf 𝒜 k₁).val.obj (op U)) :
    ((eqToHom (congrArg (twistingSheaf 𝒜) e₂)).val.app (op U)).hom
        (((eqToHom (congrArg (twistingSheaf 𝒜) e₁)).val.app (op U)).hom y) =
      ((eqToHom (congrArg (twistingSheaf 𝒜) (e₁.trans e₂))).val.app (op U)).hom y := by
  subst e₁
  subst e₂
  rfl

/-- `twistedMulLeft`, unfolded. -/
public theorem twistedMulLeft_eq (a b a' b' : ℤ)
    (Tab : twistingSheaf 𝒜 (a + b) ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b'))) :
    twistedMulLeft 𝒜 ℬ g F' a b a' b' Tab =
      twistSheafMultiplicationMap 𝒜 (pullbackProjModule 𝒜 ℬ g F') a b ≫
        twistedPullbackMap 𝒜 ℬ g F' (a + b) (a' + b') Tab :=
  rfl

/-- **The 03GK compatibility for an isomorphism of projective spectra**, in the form the Veronese
statement consumes: given `T_a` up to a reindexing `𝒪(a) = 𝒪(a₀)`, and the induced maps `Φ_b`,
`Φ_c` together with their identification with `twistedPullbackMap`, products of global sections
whose images are pulled back are carried to the pullback of the product. -/
public theorem twistedMul_homogeneous [IsIso g] (a a₀ b a' b' c : ℤ) (h₀ : a = a₀)
    (h : a + b = c)
    (T₀ : twistingSheaf 𝒜 a₀ ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ a'))
    (Tb : twistingSheaf 𝒜 b ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ b'))
    (Tc : twistingSheaf 𝒜 c ⟶ (Scheme.Modules.pullback g).obj (twistingSheaf ℬ (a' + b')))
    (H : TwistMulSquare 𝒜 ℬ g a b a' b' (eqToHom (congrArg (twistingSheaf 𝒜) h₀) ≫ T₀) Tb
      (eqToHom (congrArg (twistingSheaf 𝒜) h) ≫ Tc))
    (Φb : twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b ⟶
      (Scheme.Modules.pullback g).obj (twistSheafOfModules ℬ F' b'))
    (hΦb : Φb = twistedPullbackMap 𝒜 ℬ g F' b b' Tb)
    (Φc : twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') c ⟶
      (Scheme.Modules.pullback g).obj (twistSheafOfModules ℬ F' (a' + b')))
    (hΦc : Φc = twistedPullbackMap 𝒜 ℬ g F' c (a' + b') Tc)
    (x : (twistingSheaf 𝒜 a).val.obj (op ⊤))
    (w : (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F') b).val.obj (op ⊤))
    (x' : (twistingSheaf ℬ a').val.obj (op ⊤)) (w' : (twistSheafOfModules ℬ F' b').val.obj (op ⊤))
    (hx : (T₀.val.app (op ⊤)).hom
        (((eqToHom (congrArg (twistingSheaf 𝒜) h₀)).val.app (op ⊤)).hom x) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistingSheaf ℬ a') ⊤ x')
    (hw : (Φb.val.app (op ⊤)).hom w =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' b') ⊤ w') :
    (Φc.val.app (op ⊤)).hom
        (((eqToHom (congrArg (twistSheafOfModules 𝒜 (pullbackProjModule 𝒜 ℬ g F')) h)).val.app
          (op ⊤)).hom
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections' 𝒜
            (pullbackProjModule 𝒜 ℬ g F') a b x w)) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g (twistSheafOfModules ℬ F' (a' + b')) ⊤
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections' ℬ F' a' b' x'
          w') := by
  subst hΦb hΦc h h₀
  exact twistedMul_globalSections 𝒜 ℬ g F' a b a' b' _ Tb _ H x w x' w' hx hw

/-- The product of homogeneous global sections of Tag 03GK is the multiplication of Tag 03GJ on
their pure tensor. -/
public theorem multiplyHomogeneousSections_eq_prime
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒜)))
    (n : ℕ) (m : ℤ) (s : AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGlobalSections 𝒜 n)
    (t : (twistSheafOfModules 𝒜 F m).val.obj (op ⊤)) :
    AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections 𝒜 F n m s t =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections' 𝒜 F n m s t :=
  rfl

end Generic

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Assertion (2) of Tag 0B5J, tensored with a pulled-back module.** For a sheaf of modules
`ℱ'` on `X' = Proj S⁽ᵈ⁾` and `ℱ = i^*ℱ'`, the isomorphism `ℱ(md) = ℱ ⊗ 𝒪_X(md) ≅ i^*(ℱ'(m))`:
the identity of `ℱ` tensored with `T_m : 𝒪_X(md) ≅ i^*𝒪_{X'}(m)`, followed by Tag 01CD. -/
public def veroneseTwistedModuleIso (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (m : ℤ) :=
  letI := veroneseGradingGradedRing 𝒮 d hd
  twistedPullbackIso 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F' (m * d) m
    (veroneseTwistingSheafIso 𝒮 d hd m)

/-- `veroneseTwistedModuleIso` is `twistedPullbackMap` of assertion (2). -/
public theorem veroneseTwistedModuleIso_hom (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (veroneseTwistedModuleIso 𝒮 d hd F' m).hom =
      twistedPullbackMap 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F' (m * d) m
        (veroneseTwistingSheafIso 𝒮 d hd m).hom := by
  let := veroneseGradingGradedRing 𝒮 d hd
  exact twistedPullbackIso_hom 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F' (m * d) m
    (veroneseTwistingSheafIso 𝒮 d hd m)

/-- The square of the multiplication of twists, `veroneseTwistMulCompatibility`, in the form
`twistedMul_compatibility` consumes. -/
public theorem veroneseTwistMulSquare (d : ℕ) (hd : 0 < d) (n m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    TwistMulSquare 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom (n * d) (m * d) n m
      (veroneseTwistingSheafIso 𝒮 d hd n).hom (veroneseTwistingSheafIso 𝒮 d hd m).hom
      (eqToHom (congrArg (twistingSheaf 𝒮) (add_mul n m (d : ℤ)).symm) ≫
        (veroneseTwistingSheafIso 𝒮 d hd (n + m)).hom) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  intro U x z
  have h1 := congrArg (fun φ => (φ.val.app (op U)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
        (twistingSheaf 𝒮 (n * d)) (twistingSheaf 𝒮 (m * d)) (op U) (x ⊗ₜ z)))
    (veroneseTwistMulCompatibility 𝒮 d hd n m)
  have h2 := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
    (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace _ _ _ _
    (veroneseTwistingSheafIso 𝒮 d hd n).hom (veroneseTwistingSheafIso 𝒮 d hd m).hom U x z
  refine h1.trans ?_
  exact congrArg (fun t => (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
      (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
        (veroneseGrading 𝒮 d) n m)).val.app (op U)).hom
      ((Scheme.Modules.Hom.app (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso
        (veroneseProjIso 𝒮 d hd).hom (twistingSheaf (veroneseGrading 𝒮 d) n)
        (twistingSheaf (veroneseGrading 𝒮 d) m)).inv U) t)) h2

/-- The upper path of the 03GJ square: multiply `𝒪_X(nd) ⊗ ℱ(md) ⟶ ℱ(nd + md)` on `Proj S`,
identify `ℱ(nd + md) = ℱ((n+m)d)`, and transport by `veroneseTwistedModuleIso`. -/
public def veroneseTwistSheafMulLeft (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((twistingSheaf 𝒮 (n * d)))).obj
        ((twistSheafOfModules 𝒮 (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d)
          (veroneseProjIso 𝒮 d hd).hom F') (m * d)))) ⟶
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (twistSheafOfModules (veroneseGrading 𝒮 d) F' (n + m)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  exact twistedMulLeft 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F' (n * d) (m * d) n m
    (eqToHom (congrArg (twistingSheaf 𝒮) (add_mul n m (d : ℤ)).symm) ≫
      (veroneseTwistingSheafIso 𝒮 d hd (n + m)).hom)

/-- The lower path of the 03GJ square: transport `𝒪_X(nd)` by assertion (2) and `ℱ(md)` by
`veroneseTwistedModuleIso`, cross Tag 01CD, and pull back the multiplication
`𝒪_{X'}(n) ⊗ ℱ'(m) ⟶ ℱ'(n + m)` of `Proj S⁽ᵈ⁾`. -/
public def veroneseTwistSheafMulRight (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((twistingSheaf 𝒮 (n * d)))).obj
        ((twistSheafOfModules 𝒮 (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d)
          (veroneseProjIso 𝒮 d hd).hom F') (m * d)))) ⟶
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (twistSheafOfModules (veroneseGrading 𝒮 d) F' (n + m)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  exact twistedMulRight 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F' (n * d) (m * d) n m
    (veroneseTwistingSheafIso 𝒮 d hd n).hom (veroneseTwistingSheafIso 𝒮 d hd m).hom

/-- **Tag 0B5J's isomorphisms are compatible with the maps `𝒪(n) ⊗ ℱ(m) ⟶ ℱ(n + m)` of
Tag 03GJ.** For every sheaf of modules `ℱ'` on `X' = Proj S⁽ᵈ⁾`, with `ℱ = i^*ℱ'`, and all
integers `n` and `m`, the square

`𝒪_X(nd) ⊗ ℱ(md) ⟶ ℱ((n+m)d) ⟶ i^*(ℱ'(n+m))`
`= 𝒪_X(nd) ⊗ ℱ(md) ⟶ i^*𝒪_{X'}(n) ⊗ i^*(ℱ'(m)) ⟶ i^*(𝒪_{X'}(n) ⊗ ℱ'(m)) ⟶ i^*(ℱ'(n+m))`

commutes: the horizontal maps are the multiplication maps of Tag 03GJ, the vertical ones
assertion (2) and its transport `veroneseTwistedModuleIso` to `ℱ(md)`, and the crossing is
Tag 01CD. -/
@[ega "II 8.14.13" "special case"]
public theorem veroneseTwistSheafMulCompatibility (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n m : ℤ) :
    veroneseTwistSheafMulLeft 𝒮 d hd F' n m = veroneseTwistSheafMulRight 𝒮 d hd F' n m := by
  let := veroneseGradingGradedRing 𝒮 d hd
  exact twistedMul_compatibility 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F'
    (n * d) (m * d) n m (veroneseTwistingSheafIso 𝒮 d hd n).hom
    (veroneseTwistingSheafIso 𝒮 d hd m).hom
    (eqToHom (congrArg (twistingSheaf 𝒮) (add_mul n m (d : ℤ)).symm) ≫
      (veroneseTwistingSheafIso 𝒮 d hd (n + m)).hom)
    (veroneseTwistMulSquare 𝒮 d hd n m)

/-- `veroneseTwistSheafMulRight`, unfolded: assertion (2) on `𝒪_X(nd)` and
`veroneseTwistedModuleIso` on `ℱ(md)`, Tag 01CD backwards, then the pullback of the
multiplication of Tag 03GJ on `Proj S⁽ᵈ⁾`. -/
public theorem veroneseTwistSheafMulRight_eq (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    veroneseTwistSheafMulRight 𝒮 d hd F' n m =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf,
            (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.IsSheaf⟩)).map
          (X := (twistingSheaf 𝒮 (n * d), twistSheafOfModules 𝒮
            (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F') (m * d)))
          (Y := ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
              (twistingSheaf (veroneseGrading 𝒮 d) n),
            (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
              (twistSheafOfModules (veroneseGrading 𝒮 d) F' m)))
          ((veroneseTwistingSheafIso 𝒮 d hd n).hom, (veroneseTwistedModuleIso 𝒮 d hd F' m).hom) ≫
        (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso (veroneseProjIso 𝒮 d hd).hom
          (twistingSheaf (veroneseGrading 𝒮 d) n)
          (twistSheafOfModules (veroneseGrading 𝒮 d) F' m)).inv ≫
        (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
          (twistSheafMultiplicationMap (veroneseGrading 𝒮 d) F' n m) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  unfold veroneseTwistSheafMulRight twistedMulRight
  rw [veroneseTwistedModuleIso_hom]

/-- **Tag 0B5J's isomorphisms are compatible with the products of global sections of Tag 03GK.**
For a sheaf of modules `ℱ'` on `X' = Proj S⁽ᵈ⁾` and `ℱ = i^*ℱ'`: if a global section `s` of
`𝒪_X(nd)` corresponds under assertion (2) to the pullback of a global section `s'` of
`𝒪_{X'}(n)`, and a global section `t` of `ℱ(md)` corresponds under `veroneseTwistedModuleIso` to
the pullback of a global section `t'` of `ℱ'(m)`, then the product `s · t` — the multiplication
`𝒪(nd) ⊗ ℱ(md) ⟶ ℱ(nd + md)` of Tag 03GJ on global sections, read in `ℱ((n+m)d)` —
corresponds to the pullback of `s' · t'`. For `n ≥ 0` these products are those of the module
structure of Tag 03GK (`multiplyHomogeneousSections_eq_prime`); the statement holds for every
integer `n`. -/
public theorem veroneseMultiplyHomogeneousSectionsCompatibility (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    ∀ (s : (twistingSheaf 𝒮 (n * d)).val.obj (op ⊤))
    (t : (twistSheafOfModules 𝒮 (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d)
      (veroneseProjIso 𝒮 d hd).hom F') (m * d)).val.obj (op ⊤))
    (s' : (twistingSheaf (veroneseGrading 𝒮 d) n).val.obj (op ⊤))
    (t' : (twistSheafOfModules (veroneseGrading 𝒮 d) F' m).val.obj (op ⊤))
    (hs : ((veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤)).hom s =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (twistingSheaf (veroneseGrading 𝒮 d) n) ⊤ s')
    (ht : ((veroneseTwistedModuleIso 𝒮 d hd F' m).hom.val.app (op ⊤)).hom t =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (twistSheafOfModules (veroneseGrading 𝒮 d) F' m) ⊤ t'),
    ((veroneseTwistedModuleIso 𝒮 d hd F' (n + m)).hom.val.app (op ⊤)).hom
        (((eqToHom (congrArg (twistSheafOfModules 𝒮 (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d)
            (veroneseProjIso 𝒮 d hd).hom F'))
            (add_mul n m (d : ℤ)).symm)).val.app (op ⊤)).hom
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections' 𝒮
            (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F')
            (n * d) (m * d) s t)) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (twistSheafOfModules (veroneseGrading 𝒮 d) F' (n + m)) ⊤
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections'
          (veroneseGrading 𝒮 d) F' n m s' t') := by
  let := veroneseGradingGradedRing 𝒮 d hd
  intro s t s' t' hs ht
  have H := twistMulSquare_cast 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom
    (rfl : n * (d : ℤ) = n * d) (m * d) n m _ _ _ (veroneseTwistMulSquare 𝒮 d hd n m)
  exact twistedMul_homogeneous 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F'
    (n * d) (n * d) (m * d) n m ((n + m) * d) rfl (add_mul n m (d : ℤ)).symm
    (veroneseTwistingSheafIso 𝒮 d hd n).hom (veroneseTwistingSheafIso 𝒮 d hd m).hom
    (veroneseTwistingSheafIso 𝒮 d hd (n + m)).hom H _
    (veroneseTwistedModuleIso_hom 𝒮 d hd F' m) _ (veroneseTwistedModuleIso_hom 𝒮 d hd F' (n + m))
    s t s' t' hs ht

end Stacks.Veronese

end
