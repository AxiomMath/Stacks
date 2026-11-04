module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.SymmetricAlgebraEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ModuleTransposeSets

/-!
# The transposition identity of a cartesian affine square

For a cartesian square of algebraic spaces `W ⟶ W'` affine over `t : Z ⟶ Z'` and a morphism
`ι' : Z' ⟶ X`, the transpose `W'_* 𝒪 ⟶ t_* (W_* 𝒪)` of the base-change transition
`t^* (W'_* 𝒪) ≅ W_* 𝒪`, pushed forward along `ι'`, is the direct-image map over `X` of the top
edge `W ⟶ W'`.  This is the identity `AlgebraicGeometry.Space.IsPushforwardTransposeCompatible`
used to make the embeddings of a finite tower into a relative spectrum compatible (Stacks 0A01).

The proof is a comparison of sections: the ring-level identity
`AlgebraicGeometry.Space.map_pushforwardSquareMap_comp_pushforwardCompIso_hom` of iterated direct
images of structure sheaves is matched, section by section, with the module-level composite.

## Main results

* `AlgebraicGeometry.Space.isPushforwardTransposeCompatible_cartesianTransition`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If `F.map e.hom ≫ q = γ ≫ δ` and `F.map p ≫ q = r ≫ m`, then
`F.map (p ≫ e.inv) ≫ γ ≫ δ = r ≫ m`. Stated separately so that it is applied with every
intervening object fixed by its arguments. -/
theorem _root_.CategoryTheory.Functor.map_comp_inv_comp_eq_of_eq {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) {a b c : C} {d y z : D} (p : a ⟶ b) (e : c ≅ b) (γ : F.obj c ⟶ d)
    (δ : d ⟶ z) (q : F.obj b ⟶ z) (r : F.obj a ⟶ y) (m : y ⟶ z)
    (hq : F.map e.hom ≫ q = γ ≫ δ) (hp : F.map p ≫ q = r ≫ m) :
    F.map (p ≫ e.inv) ≫ γ ≫ δ = r ≫ m := by
  rw [← hq, ← hp, F.map_comp, Category.assoc, ← Category.assoc (F.map e.inv), ← F.map_comp,
    Iso.inv_hom_id, F.map_id, Category.id_comp]

/-- If `e₁.inv ≫ g = m ≫ e₂.inv` then `g ≫ e₂.hom = e₁.hom ≫ m`. -/
theorem _root_.CategoryTheory.comp_hom_eq_hom_comp_of_inv_comp_eq {C : Type*} [Category C]
    {A A' B B' : C} (e₁ : A ≅ A') (e₂ : B ≅ B') (g : A ⟶ B) (m : A' ⟶ B')
    (h : e₁.inv ≫ g = m ≫ e₂.inv) : g ≫ e₂.hom = e₁.hom ≫ m := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section RingLevel

variable {A₁ A₂ A₃ X : AlgebraicSpaces B S hS}

/-- **The transposition identity at the level of sheaves of rings.**  For a commutative square
`s : W ⟶ W'` over `t : Z ⟶ Z'` and `ι' : Z' ⟶ X`, the direct image along `ι'` of the comparison
`W'_* 𝒪 ⟶ t_* (W_* 𝒪)` of the square, read through the comparisons of iterated direct images,
is the direct-image map over `X` of `s`. -/
theorem map_pushforwardSquareMap_comp_pushforwardCompIso_hom {Z Z' : AlgebraicSpaces B S hS}
    (t : Z ⟶ Z') (ι' : Z' ⟶ X) (W : Over Z) (W' : Over Z') (s : W.left ⟶ W'.left)
    (hw : s ≫ W'.hom = W.hom ≫ t) (hw' : s ≫ W'.hom ≫ ι' = W.hom ≫ t ≫ ι') :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS ι').toToposHom).map
        (pushforwardSquareMap B S hS t W' W s hw) ≫
      (pushforwardCommRingCompIsoOfSpaces B S hS t ι'
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS W.hom).toToposHom).obj
          (smallEtaleRingedTopos B S hS W.left).O)).hom ≫
      (pushforwardCompIso B S hS W.hom (t ≫ ι')).hom =
    (pushforwardCompIso B S hS W'.hom ι').hom ≫
      pushforwardRingMap B S hS (X := X) (Y := Over.mk (W.hom ≫ t ≫ ι'))
        (Z := Over.mk (W'.hom ≫ ι')) (Over.homMk s hw') := by
  have hc₁ := map_pushforwardCompIso_hom_comp_pushforwardCompIso_hom B S hS
    (A₁ := W.left) (A₂ := Z) (A₃ := Z') (X := X) W.hom t ι'
  have hnat := pushforwardCompIso_inv_comp_map_pushforwardRingMap B S hS (X := X) (Y := Z') ι'
    (W₁ := overComp B S hS t W) (W₂ := W') (Over.homMk s hw)
  rw [pushforwardSquareMap_eq B S hS t W' W s hw]
  exact Functor.map_comp_inv_comp_eq_of_eq _ _ _ _ _ _ _ _ hc₁
    (comp_hom_eq_hom_comp_of_inv_comp_eq _ _ _ _ hnat)

/-- `AlgebraicGeometry.Space.map_pushforwardSquareMap_comp_pushforwardCompIso_hom` for any morphism
over `X` with underlying morphism `s`. -/
theorem map_pushforwardSquareMap_comp_pushforwardCompIso_hom' {Z Z' : AlgebraicSpaces B S hS}
    (t : Z ⟶ Z') (ι' : Z' ⟶ X) (W : Over Z) (W' : Over Z') (s : W.left ⟶ W'.left)
    (hw : s ≫ W'.hom = W.hom ≫ t) (hw' : s ≫ W'.hom ≫ ι' = W.hom ≫ t ≫ ι')
    (f : Over.mk (W.hom ≫ t ≫ ι') ⟶ Over.mk (W'.hom ≫ ι')) (hf : f.left = s) :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS ι').toToposHom).map
        (pushforwardSquareMap B S hS t W' W s hw) ≫
      (pushforwardCommRingCompIsoOfSpaces B S hS t ι'
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS W.hom).toToposHom).obj
          (smallEtaleRingedTopos B S hS W.left).O)).hom ≫
      (pushforwardCompIso B S hS W.hom (t ≫ ι')).hom =
    (pushforwardCompIso B S hS W'.hom ι').hom ≫
      pushforwardRingMap B S hS (X := X) (Y := Over.mk (W.hom ≫ t ≫ ι'))
        (Z := Over.mk (W'.hom ≫ ι')) f := by
  obtain rfl : f = Over.homMk s hw' := Over.OverMorphism.ext hf
  exact map_pushforwardSquareMap_comp_pushforwardCompIso_hom B S hS t ι' W W' s hw hw'

end RingLevel

/-- An `eqToHom` followed by a morphism of sheaves of modules, on sections. -/
theorem _root_.SheafOfModules.eqToHom_comp_val_app_heq.{w, w', w''} {C : Type w''}
    [Category.{w'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M M' N : SheafOfModules.{w} R} (h : M = M') (m : M' ⟶ N) (V : Cᵒᵖ) (z : M.val.obj V)
    (z' : M'.val.obj V) (hz : HEq z z') : HEq ((eqToHom h ≫ m).val.app V z) (m.val.app V z') := by
  subst h
  cases hz
  rw [eqToHom_refl, Category.id_comp]

/-- An isomorphism of sheaves of modules conjugated by `eqToIso`s, on sections. -/
theorem _root_.SheafOfModules.eqToIso_trans_trans_eqToIso_hom_val_app_heq.{w, w', w''}
    {C : Type w''} [Category.{w'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M M' N N' : SheafOfModules.{w} R} (i : M ≅ N') (h : M = M') (e : M' ≅ N) (h' : N = N')
    (hi : i = eqToIso h ≪≫ e ≪≫ eqToIso h') (V : Cᵒᵖ)
    (z : M.val.obj V) (z' : M'.val.obj V) (hz : HEq z z') :
    HEq (i.hom.val.app V z) (e.hom.val.app V z') := by
  subst h h' hi
  cases hz
  simp

/-- A morphism of sheaves of modules followed by an `eqToHom`, on sections. -/
theorem _root_.SheafOfModules.comp_eqToHom_val_app_heq.{w, w', w''} {C : Type w''}
    [Category.{w'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M N N' : SheafOfModules.{w} R} (m : M ⟶ N) (h : N = N') (V : Cᵒᵖ) (z : M.val.obj V) :
    HEq ((m ≫ eqToHom h).val.app V z) (m.val.app V z) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]

/-- Components of a natural transformation of functors to sheaves of sets at equal objects, on
heterogeneously equal sections. -/
theorem _root_.CategoryTheory.NatTrans.app_hom_app_heq {C D : Type*} [Category C]
    {J : GrothendieckTopology C} [Category D] {F G : D ⥤ Sheaf J (Type u)} (τ : F ⟶ G)
    {P P' : D} (hP : P = P') (V : Cᵒᵖ) {z : (F.obj P).obj.obj V} {z' : (F.obj P').obj.obj V}
    (hz : HEq z z') : HEq ((τ.app P).hom.app V z) ((τ.app P').hom.app V z') := by
  subst hP
  cases hz
  rfl

/-- A morphism of sheaves of sets is heterogeneously equal to a morphism between equal sheaves
which agrees with it on sections. -/
theorem _root_.CategoryTheory.Sheaf.hom_heq_of_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P Q P' Q' : Sheaf J (Type u)} (hP : P = P') (hQ : Q = Q')
    (f : P ⟶ Q) (f' : P' ⟶ Q')
    (h : ∀ (V : Cᵒᵖ) (x : P.obj.obj V) (x' : P'.obj.obj V), HEq x x' →
      HEq (f.hom.app V x) (f'.hom.app V x')) :
    HEq f f' := by
  subst hP hQ
  exact heq_of_eq (Sheaf.hom_ext_sections fun V x => eq_of_heq (h V x x HEq.rfl))

/-- The underlying morphism of sheaves of sets of a morphism of sheaves of modules, on a
section. -/
theorem _root_.CategoryTheory.Sheaf.moduleSheafFunctor_map_hom_app_heq.{w, w', w''}
    {C : Type w''} [Category.{w'} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] (R : Sheaf J RingCat.{w})
    {N N' : SheafOfModules.{w} R} (ψ : N ⟶ N') (V : Cᵒᵖ) (x : N.val.obj V) :
    HEq (((Sheaf.moduleSheafFunctor R).map ψ).hom.app V x) (ψ.val.app V x) :=
  HEq.rfl

/-- A functor carries heterogeneously equal morphisms between equal objects to heterogeneously
equal morphisms. -/
theorem _root_.CategoryTheory.Functor.map_heq_map {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a b a' b' : C} (ha : a = a') (hb : b = b') {f : a ⟶ b} {f' : a' ⟶ b'}
    (h : HEq f f') : HEq (F.map f) (F.map f') := by
  subst ha hb
  cases h
  rfl

section ModuleLevel

variable {X Y : AlgebraicSpaces B S hS}

/-- **The transpose of the base-change transition of a cartesian affine square along
`g^* ⊣ g_*` is, on sections, the comparison of the square.** -/
theorem modulePullbackAdjunction_homEquiv_cartesianTransition_val_app_heq (g : Y ⟶ X)
    (W : AffineOver B S hS Y) (W' : AffineOver B S hS X) (s : W.obj.left ⟶ W'.obj.left)
    (h : IsPullback s W.obj.hom W'.obj.hom g) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (pushforwardAlgebra B S hS W'.obj).underlyingModule.val.obj V) :
    HEq (((modulePullbackAdjunction B S hS g).homEquiv
        (pushforwardAlgebra B S hS W'.obj).underlyingModule
        (pushforwardAlgebra B S hS W.obj).underlyingModule
        ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g _).hom ≫
          AlgebraSheaf.underlyingModuleMap
            (haveI := isIso_affineOverBaseChangeAlgebraHom B S hS g W'
            asIso (affineOverBaseChangeAlgebraHom B S hS g W') ≪≫
              pushforwardAlgebraIsoOfIso B S hS
                (affineOverIsoBaseChangeOfIsPullback B S hS g W W' s h)).hom)).val.app V x)
      ((pushforwardSquareMap B S hS g W'.obj W.obj s h.w).hom.app V x) :=
  (modulePullbackAdjunction_homEquiv_underlyingModuleMap_val_app_heq B S hS g _ _ _ V x).trans
    (heq_of_eq (congrArg (fun φ => φ.hom.app V x)
      (commRingImageAdjunction_homEquiv_affineCartesianTransition B S hS g W W' s h)))

/-- On sections, the comparison of iterated direct images of modules at the module underlying an
algebra is the comparison of iterated direct images of its sheaf of rings. -/
theorem modulePushforwardCompIso_hom_app_underlyingModule_val_app_heq
    {A₂ A₃ : AlgebraicSpaces B S hS}
    (b : A₂ ⟶ A₃) (y : A₃ ⟶ X) (C : AlgebraSheaf.{u, u} B S hS A₂.1 A₂.2)
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : ((modulePushforward B S hS y).obj
      ((modulePushforward B S hS b).obj C.underlyingModule)).val.obj V) :
    HEq (((modulePushforwardCompIso B S hS b y).hom.app C.underlyingModule).val.app V z)
      ((pushforwardCommRingCompIsoOfSpaces B S hS b y C.right).hom.hom.app V z) := by
  refine (heq_of_eq (modulePushforwardCompIso_hom_app_val_app B S hS b y _ V z)).trans ?_
  refine HEq.trans HEq.rfl (heq_of_eq (congrArg (fun φ => φ.hom.app V z)
    (forgetRing_map_pushforwardCommRingCompIsoOfSpaces_hom B S hS b y C.right)).symm)

/-- `AlgebraicGeometry.Space.modulePushforwardPushforwardAlgebraIso`, unfolded. -/
theorem modulePushforwardPushforwardAlgebraIso_eq {Z : AlgebraicSpaces B S hS} (ι : Z ⟶ X)
    (W : Over Z) :
    modulePushforwardPushforwardAlgebraIso B S hS ι W =
      eqToIso (congrArg (modulePushforward B S hS ι).obj
          (underlyingModule_pushforwardAlgebra B S hS W.hom)) ≪≫
        (modulePushforwardCompIso B S hS W.hom ι).app
          (SheafOfModules.unit (structureRingSheaf B S hS W.left)) ≪≫
        eqToIso (underlyingModule_pushforwardAlgebra B S hS (W.hom ≫ ι)).symm :=
  rfl

/-- On sections, the identification of the direct image along `ι` of the direct-image algebra of
`W` with the direct-image algebra of `W` read over `X` is the comparison of iterated direct images
of structure sheaves. -/
theorem modulePushforwardPushforwardAlgebraIso_hom_val_app_heq {Z : AlgebraicSpaces B S hS}
    (ι : Z ⟶ X) (W : Over Z) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : ((modulePushforward B S hS ι).obj
      (pushforwardAlgebra B S hS W).underlyingModule).val.obj V) :
    HEq ((modulePushforwardPushforwardAlgebraIso B S hS ι W).hom.val.app V z)
      ((pushforwardCompIso B S hS W.hom ι).hom.hom.app V z) := by
  have h1 : (pushforwardAlgebra B S hS W).underlyingModule =
      (modulePushforward B S hS W.hom).obj
        (SheafOfModules.unit (structureRingSheaf B S hS W.left)) :=
    underlyingModule_pushforwardAlgebra B S hS W.hom
  let z' := cast (congrArg (fun N : Modules.{u, u} B S hS Z.1 Z.2 =>
    (((modulePushforward B S hS ι).obj N).val.obj V : Type u)) h1) z
  have hz : HEq z z' := (cast_heq _ _).symm
  refine (SheafOfModules.eqToIso_trans_trans_eqToIso_hom_val_app_heq
    (modulePushforwardPushforwardAlgebraIso B S hS ι W)
    (congrArg (modulePushforward B S hS ι).obj h1)
    ((modulePushforwardCompIso B S hS W.hom ι).app
      (SheafOfModules.unit (structureRingSheaf B S hS W.left)))
    (underlyingModule_pushforwardAlgebra B S hS (W.hom ≫ ι)).symm
    (modulePushforwardPushforwardAlgebraIso_eq B S hS ι W) V z z' hz).trans ?_
  refine (heq_of_eq (modulePushforwardCompIso_hom_app_val_app B S hS W.hom ι _ V z')).trans ?_
  refine HEq.trans ?_ (heq_of_eq (congrArg (fun φ => φ.hom.app V z)
    (forgetRing_map_pushforwardCompIso_hom B S hS W.hom ι)).symm)
  exact NatTrans.app_hom_app_heq (smallToposMorphismTypeU_comp B S hS W.hom ι).hom
    (P' := structureSetSheaf B S hS W.left) rfl V hz.symm

/-- On underlying sheaves of sets, the direct image of modules is the direct image of sheaves of
sets. -/
theorem moduleSheafFunctor_map_modulePushforward_map_geometric' {Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Z) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((modulePushforward B S hS f).map φ) =
      (smallToposMorphismTypeU B S hS f).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map φ) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- A morphism of sheaves of modules is, as a morphism of sheaves of sets, heterogeneously equal to
a morphism of sheaves of sets which agrees with it on heterogeneously equal sections. -/
private theorem moduleSheafFunctor_map_heq_of_app_heq {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{u})]
    [J.HasSheafCompose (forget AddCommGrpCat.{u})] (R : Sheaf J RingCat.{u})
    {N N' : SheafOfModules.{u} R} (ψ : N ⟶ N') {P Q : Sheaf J (Type u)}
    (hP : (Sheaf.moduleSheafFunctor R).obj N = P) (hQ : (Sheaf.moduleSheafFunctor R).obj N' = Q)
    (f : P ⟶ Q)
    (h : ∀ (V : Cᵒᵖ) (x : N.val.obj V) (x' : P.obj.obj V), HEq x x' →
      HEq (ψ.val.app V x) (f.hom.app V x')) :
    HEq ((Sheaf.moduleSheafFunctor R).map ψ) f := by
  subst hP hQ
  exact Sheaf.hom_heq_of_app rfl rfl _ _ fun V x x' hx =>
    (Sheaf.moduleSheafFunctor_map_hom_app_heq R ψ V x).trans (h V x x' hx)

/-- On sections, the direct image along `ι'` of the transpose of the base-change transition of a
cartesian affine square is the direct image of the comparison of the square. -/
theorem modulePushforward_map_homEquiv_cartesianTransition_val_app_heq {Z : AlgebraicSpaces B S hS}
    (ι' : X ⟶ Z) (g : Y ⟶ X)
    (W : AffineOver B S hS Y) (W' : AffineOver B S hS X) (s : W.obj.left ⟶ W'.obj.left)
    (h : IsPullback s W.obj.hom W'.obj.hom g) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : ((modulePushforward B S hS ι').obj
      (pushforwardAlgebra B S hS W'.obj).underlyingModule).val.obj V) :
    HEq (((modulePushforward B S hS ι').map ((modulePullbackAdjunction B S hS g).homEquiv
        (pushforwardAlgebra B S hS W'.obj).underlyingModule
        (pushforwardAlgebra B S hS W.obj).underlyingModule
        ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g _).hom ≫
          AlgebraSheaf.underlyingModuleMap
            (haveI := isIso_affineOverBaseChangeAlgebraHom B S hS g W'
            asIso (affineOverBaseChangeAlgebraHom B S hS g W') ≪≫
              pushforwardAlgebraIsoOfIso B S hS
                (affineOverIsoBaseChangeOfIsPullback B S hS g W W' s h)).hom))).val.app V x)
      (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS ι').toToposHom).map
        (pushforwardSquareMap B S hS g W'.obj W.obj s h.w)).hom.app V x) := by
  have hsh := moduleSheafFunctor_map_heq_of_app_heq (structureRingSheaf B S hS X)
      ((modulePullbackAdjunction B S hS g).homEquiv
        (pushforwardAlgebra B S hS W'.obj).underlyingModule
        (pushforwardAlgebra B S hS W.obj).underlyingModule
        ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g _).hom ≫
          AlgebraSheaf.underlyingModuleMap
            (have := isIso_affineOverBaseChangeAlgebraHom B S hS g W'
            asIso (affineOverBaseChangeAlgebraHom B S hS g W') ≪≫
              pushforwardAlgebraIsoOfIso B S hS
                (affineOverIsoBaseChangeOfIsPullback B S hS g W W' s h)).hom))
    rfl rfl ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
      (pushforwardSquareMap B S hS g W'.obj W.obj s h.w))
    (fun V' x' x'' hx =>
      (modulePullbackAdjunction_homEquiv_cartesianTransition_val_app_heq B S hS g W W' s
        h V' x').trans (heq_of_eq (congrArg
          ((pushforwardSquareMap B S hS g W'.obj W.obj s h.w).hom.app V') (eq_of_heq hx))))
  have hgeo := moduleSheafFunctor_map_modulePushforward_map_geometric' B S hS ι'
    ((modulePullbackAdjunction B S hS g).homEquiv
        (pushforwardAlgebra B S hS W'.obj).underlyingModule
        (pushforwardAlgebra B S hS W.obj).underlyingModule
        ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g _).hom ≫
          AlgebraSheaf.underlyingModuleMap
            (have := isIso_affineOverBaseChangeAlgebraHom B S hS g W'
            asIso (affineOverBaseChangeAlgebraHom B S hS g W') ≪≫
              pushforwardAlgebraIsoOfIso B S hS
                (affineOverIsoBaseChangeOfIsPullback B S hS g W W' s h)).hom))
  have hring := underlyingRingSheaf_map_pullbackCommRingSheafMap (SmallEtale.topology B S hS Z.1)
    (Φ := (smallEtaleRingedToposHom B S hS ι').toToposHom.pushforward)
    (pushforwardSquareMap B S hS g W'.obj W.obj s h.w)
  have hall := (heq_of_eq hgeo).trans
    ((Functor.map_heq_map (smallToposMorphismTypeU B S hS ι').pushforward rfl rfl hsh).trans
      (heq_of_eq hring.symm))
  exact (Sheaf.moduleSheafFunctor_map_hom_app_heq (structureRingSheaf B S hS Z) _ V x).symm.trans
    (Sheaf.hom_app_heq rfl rfl hall V x)

/-- `AlgebraicGeometry.Space.modulePushforward_map_homEquiv_cartesianTransition_val_app_heq`, with
the transition written as an isomorphism. -/
theorem modulePushforward_map_homEquiv_cartesianTransition_val_app_heq' {Z : AlgebraicSpaces B S hS}
    (ι' : X ⟶ Z) (g : Y ⟶ X)
    (W : AffineOver B S hS Y) (W' : AffineOver B S hS X) (s : W.obj.left ⟶ W'.obj.left)
    (h : IsPullback s W.obj.hom W'.obj.hom g) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : ((modulePushforward B S hS ι').obj
      (pushforwardAlgebra B S hS W'.obj).underlyingModule).val.obj V) :
    HEq (((modulePushforward B S hS ι').map ((modulePullbackAdjunction B S hS g).homEquiv
        (pushforwardAlgebra B S hS W'.obj).underlyingModule
        (pushforwardAlgebra B S hS W.obj).underlyingModule
        (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g _ ≪≫
          (AlgebraSheaf.underlyingModuleFunctor (F := Y.1) (hF := Y.2)).mapIso
            (haveI := isIso_affineOverBaseChangeAlgebraHom B S hS g W'
            asIso (affineOverBaseChangeAlgebraHom B S hS g W') ≪≫
              pushforwardAlgebraIsoOfIso B S hS
                (affineOverIsoBaseChangeOfIsPullback B S hS g W W' s h))).hom)).val.app V x)
      (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS ι').toToposHom).map
        (pushforwardSquareMap B S hS g W'.obj W.obj s h.w)).hom.app V x) :=
  modulePushforward_map_homEquiv_cartesianTransition_val_app_heq B S hS ι' g W W' s h V x

/-- `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_underlyingModule_val_app_heq` at a
direct-image algebra, with the direct image of the structure sheaf spelled as such. -/
theorem modulePushforwardCompIso_hom_app_pushforwardAlgebra_val_app_heq
    {A₂ A₃ : AlgebraicSpaces B S hS} (b : A₂ ⟶ A₃) (y : A₃ ⟶ X) (W : Over A₂)
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : ((modulePushforward B S hS y).obj
      ((modulePushforward B S hS b).obj
        (pushforwardAlgebra B S hS W).underlyingModule)).val.obj V) :
    HEq (((modulePushforwardCompIso B S hS b y).hom.app
        (pushforwardAlgebra B S hS W).underlyingModule).val.app V z)
      ((pushforwardCommRingCompIsoOfSpaces B S hS b y
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS W.hom).toToposHom).obj
          (smallEtaleRingedTopos B S hS W.left).O)).hom.hom.app V z) :=
  modulePushforwardCompIso_hom_app_underlyingModule_val_app_heq B S hS b y _ V z

/-- A composite of morphisms of sheaves of commutative rings agrees on sections with a composite
of morphisms of sheaves of modules agreeing with it factor by factor. -/
private theorem _root_.SheafOfModules.comp_val_app_heq_of_aux.{w, w', w''} {C : Type w''}
    [Category.{w'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M N P : SheafOfModules.{w} R} {M' N' P' : Sheaf J CommRingCat.{w}}
    (f : M ⟶ N) (g : N ⟶ P) (f' : M' ⟶ N') (g' : N' ⟶ P') (V : Cᵒᵖ)
    (hM : (M.val.obj V : Type w) = M'.obj.obj V) (hN : (N.val.obj V : Type w) = N'.obj.obj V)
    (hf : ∀ y : M.val.obj V, HEq (f.val.app V y) (f'.hom.app V (cast hM y)))
    (hg : ∀ y : N.val.obj V, HEq (g.val.app V y) (g'.hom.app V (cast hN y)))
    (x : M.val.obj V) :
    HEq ((f ≫ g).val.app V x) ((f' ≫ g').hom.app V (cast hM x)) := by
  have e1 : cast hN (f.val.app V x) = f'.hom.app V (cast hM x) :=
    eq_of_heq ((cast_heq _ _).trans (hf x))
  exact (hg _).trans (heq_of_eq (congrArg (g'.hom.app V) e1))

/-- A triple composite of morphisms of sheaves of modules agrees on sections with a triple
composite of morphisms of sheaves of commutative rings agreeing with it factor by factor. -/
theorem _root_.SheafOfModules.comp_comp_val_app_heq_of.{w, w', w''} {C : Type w''}
    [Category.{w'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M N P Q : SheafOfModules.{w} R} {M' N' P' Q' : Sheaf J CommRingCat.{w}}
    (f : M ⟶ N) (g : N ⟶ P) (h : P ⟶ Q) (f' : M' ⟶ N') (g' : N' ⟶ P') (h' : P' ⟶ Q')
    (V : Cᵒᵖ) (hM : (M.val.obj V : Type w) = M'.obj.obj V)
    (hN : (N.val.obj V : Type w) = N'.obj.obj V) (hP : (P.val.obj V : Type w) = P'.obj.obj V)
    (hf : ∀ y : M.val.obj V, HEq (f.val.app V y) (f'.hom.app V (cast hM y)))
    (hg : ∀ y : N.val.obj V, HEq (g.val.app V y) (g'.hom.app V (cast hN y)))
    (hh : ∀ y : P.val.obj V, HEq (h.val.app V y) (h'.hom.app V (cast hP y)))
    (x : M.val.obj V) :
    HEq ((f ≫ g ≫ h).val.app V x) ((f' ≫ g' ≫ h').hom.app V (cast hM x)) :=
  SheafOfModules.comp_val_app_heq_of_aux f (g ≫ h) f' (g' ≫ h') V hM hN hf
    (SheafOfModules.comp_val_app_heq_of_aux g h g' h' V hN hP hg hh) x

/-- A composite of morphisms of sheaves of commutative rings agrees on sections with a composite
of morphisms of sheaves of modules agreeing with it factor by factor. -/
theorem _root_.SheafOfModules.comp_val_app_heq_of.{w, w', w''} {C : Type w''}
    [Category.{w'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M N P : SheafOfModules.{w} R} {M' N' P' : Sheaf J CommRingCat.{w}}
    (f : M ⟶ N) (g : N ⟶ P) (f' : M' ⟶ N') (g' : N' ⟶ P') (V : Cᵒᵖ)
    (hM : (M.val.obj V : Type w) = M'.obj.obj V) (hN : (N.val.obj V : Type w) = N'.obj.obj V)
    (hf : ∀ y : M.val.obj V, HEq (f.val.app V y) (f'.hom.app V (cast hM y)))
    (hg : ∀ y : N.val.obj V, HEq (g.val.app V y) (g'.hom.app V (cast hN y)))
    (x : M.val.obj V) :
    HEq ((f ≫ g).val.app V x) ((f' ≫ g').hom.app V (cast hM x)) :=
  SheafOfModules.comp_val_app_heq_of_aux f g f' g' V hM hN hf hg x

/-- A morphism of algebra sheaves and its underlying morphism of modules agree on
heterogeneously equal sections. -/
theorem AlgebraSheaf.right_hom_app_heq_underlyingModuleMap_val_app
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C)
    (V : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj V) (b : A.underlyingModule.val.obj V)
    (h : HEq a b) :
    HEq (φ.right.hom.app V a) ((AlgebraSheaf.underlyingModuleMap φ).val.app V b) := by
  cases eq_of_heq h
  rfl

/-- Morphisms of sheaves of modules agreeing on sections are equal. -/
theorem _root_.SheafOfModules.hom_ext_of_val_app_heq.{w, w', w''} {C : Type w''}
    [Category.{w'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M N : SheafOfModules.{w} R} {f g : M ⟶ N}
    (h : ∀ (V : Cᵒᵖ) (x : M.val.obj V), HEq (f.val.app V x) (g.val.app V x)) : f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => eq_of_heq (h V x)))

/-- The right-hand side of the transposition identity, on underlying sheaves of sets. -/
theorem transpose_rhs_sheaf_heq {Z' : AlgebraicSpaces B S hS} (ι' : Z' ⟶ X)
    (W' : AffineOver B S hS Z') {Y : Over X} (f : Y ⟶ Over.mk (W'.obj.hom ≫ ι')) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforwardPushforwardAlgebraIso B S hS ι' W'.obj).hom ≫
          AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap B S hS f)))
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        ((pushforwardCompIso B S hS W'.obj.hom ι').hom ≫
          pushforwardRingMap B S hS (X := X) (Y := Y) (Z := Over.mk (W'.obj.hom ≫ ι')) f)) := by
  have hc := moduleSheafFunctor_map_heq_of_app_heq (structureRingSheaf B S hS X)
    (modulePushforwardPushforwardAlgebraIso B S hS ι' W'.obj).hom rfl rfl
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
      (pushforwardCompIso B S hS W'.obj.hom ι').hom)
    (fun V y y' hy =>
      (modulePushforwardPushforwardAlgebraIso_hom_val_app_heq B S hS ι' W'.obj V y).trans
        (heq_of_eq (congrArg ((pushforwardCompIso B S hS W'.obj.hom ι').hom.hom.app V)
          (eq_of_heq hy))))
  have hg := moduleSheafFunctor_map_heq_of_app_heq (structureRingSheaf B S hS X)
    (AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap B S hS f)) rfl rfl
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
      (pushforwardRingMap B S hS (X := X) (Y := Y) (Z := Over.mk (W'.obj.hom ≫ ι')) f))
    (fun V y y' hy => (AlgebraSheaf.right_hom_app_heq_underlyingModuleMap_val_app B S hS
      (pushforwardAlgebraMap B S hS f) V y' y hy.symm).symm)
  have hcomp := comp_heq_comp rfl rfl rfl hc hg
  refine (heq_of_eq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _)).trans
    (hcomp.trans (heq_of_eq ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget CommRingCat.{u})).map_comp _ _).symm))

/-- The commutativity of a cartesian square, after a further morphism. -/
theorem _root_.CategoryTheory.comp_comp_eq_of_isPullback {C : Type*} [Category C]
    {Z Z' X P P' : C} (t : Z ⟶ Z') (ι' : Z' ⟶ X) {s : P ⟶ P'} {w : P ⟶ Z} {w' : P' ⟶ Z'}
    (hs : IsPullback s w w' t) : s ≫ w' ≫ ι' = w ≫ t ≫ ι' :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ι') hs.w).trans (Category.assoc _ _ _))

/-- The transposition identity, on sections, up to its right-hand side read on sheaves of rings. -/
theorem transpose_val_app_heq_ring {Z Z' : AlgebraicSpaces B S hS}
    (t : Z ⟶ Z') (ι' : Z' ⟶ X) (W : AffineOver B S hS Z) (W' : AffineOver B S hS Z')
    (s : W.obj.left ⟶ W'.obj.left) (hs : IsPullback s W.obj.hom W'.obj.hom t)
    (f : Over.mk (W.obj.hom ≫ t ≫ ι') ⟶ Over.mk (W'.obj.hom ≫ ι')) (hf : f.left = s)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ)
    (x : ((modulePushforward B S hS ι').obj
      (pushforwardAlgebra B S hS W'.obj).underlyingModule).val.obj V) :
    HEq (((modulePushforward B S hS ι').map ((modulePullbackAdjunction B S hS t).homEquiv
        (pushforwardAlgebra B S hS W'.obj).underlyingModule
        (pushforwardAlgebra B S hS W.obj).underlyingModule
        (underlyingModuleAlgebraPullbackModulePullbackIso B S hS t _ ≪≫
          (AlgebraSheaf.underlyingModuleFunctor (F := Z.1) (hF := Z.2)).mapIso
            (haveI := isIso_affineOverBaseChangeAlgebraHom B S hS t W'
            asIso (affineOverBaseChangeAlgebraHom B S hS t W') ≪≫
              pushforwardAlgebraIsoOfIso B S hS
                (affineOverIsoBaseChangeOfIsPullback B S hS t W W' s hs))).hom) ≫
      (modulePushforwardCompIso B S hS t ι').hom.app
        (pushforwardAlgebra B S hS W.obj).underlyingModule ≫
        (modulePushforwardPushforwardAlgebraIso B S hS (t ≫ ι') W.obj).hom).val.app V x)
      (((pushforwardCompIso B S hS W'.obj.hom ι').hom ≫
        pushforwardRingMap B S hS (X := X) (Y := Over.mk (W.obj.hom ≫ t ≫ ι'))
          (Z := Over.mk (W'.obj.hom ≫ ι')) f).hom.app V x) := by
  have hw'' := comp_comp_eq_of_isPullback t ι' hs
  have hring := congrArg (fun φ => φ.hom.app V x)
    (map_pushforwardSquareMap_comp_pushforwardCompIso_hom' B S hS t ι' W.obj W'.obj s hs.w hw''
      f hf)
  refine (SheafOfModules.comp_comp_val_app_heq_of _ _ _ _ _ _ V rfl rfl rfl
    (fun y => modulePushforward_map_homEquiv_cartesianTransition_val_app_heq' B S hS ι' t
      W W' s hs V y)
    (fun y => modulePushforwardCompIso_hom_app_pushforwardAlgebra_val_app_heq B S hS t ι' W.obj V y)
    (fun y => modulePushforwardPushforwardAlgebraIso_hom_val_app_heq B S hS (t ≫ ι') W.obj V y)
    x).trans ?_
  exact heq_of_eq hring

/-- The right-hand side of the transposition identity, on sections. -/
theorem transpose_rhs_val_app_heq {Z' : AlgebraicSpaces B S hS} (ι' : Z' ⟶ X)
    (W' : AffineOver B S hS Z') {Y : Over X} (f : Y ⟶ Over.mk (W'.obj.hom ≫ ι'))
    (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ)
    (x : ((modulePushforward B S hS ι').obj
      (pushforwardAlgebra B S hS W'.obj).underlyingModule).val.obj V) :
    HEq (((pushforwardCompIso B S hS W'.obj.hom ι').hom ≫
        pushforwardRingMap B S hS (X := X) (Y := Y) (Z := Over.mk (W'.obj.hom ≫ ι')) f).hom.app V x)
      (((modulePushforwardPushforwardAlgebraIso B S hS ι' W'.obj).hom ≫
        AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap B S hS f)).val.app V x) :=
  (Sheaf.hom_app_heq rfl rfl (transpose_rhs_sheaf_heq B S hS ι' W' f) V x).symm.trans
    (Sheaf.moduleSheafFunctor_map_hom_app_heq (structureRingSheaf B S hS X) _ V x)

/-- **The transposition identity of a cartesian affine square.**  For algebraic spaces `W` and
`W'` affine over `Z` and `Z'` forming a cartesian square over `t : Z ⟶ Z'`, the base-change
transition `t^* (W'_* 𝒪) ≅ W_* 𝒪` satisfies
`AlgebraicGeometry.Space.IsPushforwardTransposeCompatible` along any `ι' : Z' ⟶ X`. -/
theorem isPushforwardTransposeCompatible_cartesianTransition {Z Z' : AlgebraicSpaces B S hS}
    (t : Z ⟶ Z') (ι' : Z' ⟶ X) (W : AffineOver B S hS Z) (W' : AffineOver B S hS Z')
    (s : W.obj.left ⟶ W'.obj.left) (hs : IsPullback s W.obj.hom W'.obj.hom t) :
    (modulePushforward B S hS ι').map ((modulePullbackAdjunction B S hS t).homEquiv
        (pushforwardAlgebra B S hS W'.obj).underlyingModule
        (pushforwardAlgebra B S hS W.obj).underlyingModule
        (underlyingModuleAlgebraPullbackModulePullbackIso B S hS t _ ≪≫
          (AlgebraSheaf.underlyingModuleFunctor (F := Z.1) (hF := Z.2)).mapIso
            (haveI := isIso_affineOverBaseChangeAlgebraHom B S hS t W'
            asIso (affineOverBaseChangeAlgebraHom B S hS t W') ≪≫
              pushforwardAlgebraIsoOfIso B S hS
                (affineOverIsoBaseChangeOfIsPullback B S hS t W W' s hs))).hom) ≫
      (modulePushforwardCompIso B S hS t ι').hom.app
        (pushforwardAlgebra B S hS W.obj).underlyingModule ≫
        (modulePushforwardPushforwardAlgebraIso B S hS (t ≫ ι') W.obj).hom =
    (modulePushforwardPushforwardAlgebraIso B S hS ι' W'.obj).hom ≫
      AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap B S hS
        (Over.homMk s (comp_comp_eq_of_isPullback t ι' hs) :
          Over.mk (W.obj.hom ≫ t ≫ ι') ⟶ Over.mk (W'.obj.hom ≫ ι'))) := by
  refine SheafOfModules.hom_ext_of_val_app_heq fun V x => ?_
  exact (transpose_val_app_heq_ring B S hS t ι' W W' s hs _ rfl V x).trans
    (transpose_rhs_val_app_heq B S hS ι' W' _ V x)

end ModuleLevel

end AlgebraicGeometry.Space

end
