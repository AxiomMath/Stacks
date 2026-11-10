module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovePrecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMoveRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData

/-!
# Equation 0619 under postcomposition with the canonical map of differentials

Let `θ : e^*Ω_{R/T} ⟶ C` be `𝒪_Q`-linear, `e : Q ⟶ R`, and let `f₀ : R ⟶ R''` lie over
`t : T ⟶ T''` (`f₀ ≫ b'' = b ≫ t`).  Precomposing `θ` with the inverse image along `e` of the
canonical map `c_{f₀} : f₀^*Ω_{R''/T''} ⟶ Ω_{R/T}` of [Stacks Project, Tag 04CX] gives
`θ'' : (e ≫ f₀)^*Ω_{R''/T''} ⟶ C`.  The derivation attached to `θ''` by Equation
[Stacks Project, Tag 0619] is the derivation attached to `θ` precomposed with `f₀^♯`
(`AlgebraicGeometry.Space.derivationFamilyOfHom_comp_sheafOfDifferentialsMap`).

This is the derivation clause of the postcomposition law of the action `θ · a'` of
[Stacks Project, Tag 0CK6] with a morphism of thickenings `(f₀, f')`, the general-`f` half of
[Stacks Project, Tag 0CK8].

## References

* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

/-! ### A difference of two ring maps under a direct image -/

section PushforwardDifference

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {J : GrothendieckTopology 𝒞} {K : GrothendieckTopology 𝒟}
  [J.HasSheafCompose (forget RingCat.{w₁})] [K.HasSheafCompose (forget RingCat.{w₂})]
  (Φ : Sheaf J (Type w₁) ⥤ Sheaf K (Type w₂)) [PreservesFiniteProducts Φ]

omit [K.HasSheafCompose (forget RingCat.{w₂})] in
/-- **A direct image of sheaves of rings carries a difference of two ring maps to the difference
of their images.**  If the sectionwise difference `φ - ψ` of two morphisms of sheaves of rings
is the morphism of underlying sheaves of sets `δ`, then on sections of the image under a
finite-product-preserving functor `Φ` the difference of the images of `φ` and `ψ` is `Φ δ`. -/
theorem pullbackRingSheafMap_sub_app_apply {A R : Sheaf J RingCat.{w₁}} (φ ψ : A ⟶ R)
    (δ : (sheafCompose J (forget RingCat.{w₁})).obj A ⟶
      (sheafCompose J (forget RingCat.{w₁})).obj R)
    (hδ : ∀ (X : 𝒞ᵒᵖ) (x : ToType (A.obj.obj X)),
      δ.hom.app X x = φ.hom.app X x - ψ.hom.app X x)
    (Y : 𝒟ᵒᵖ) (y : ToType ((pullbackRingSheaf K Φ A).obj.obj Y)) :
    (pullbackRingSheafMap K Φ φ).hom.app Y y - (pullbackRingSheafMap K Φ ψ).hom.app Y y =
      (Φ.map δ).hom.app Y y := by
  have hset : (sheafCompose J (forget RingCat.{w₁})).map φ =
      prod.lift ((sheafCompose J (forget RingCat.{w₁})).map ψ) δ ≫ Sheaf.ringAddHom R :=
    Sheaf.hom_ext_sections fun X x ↦ by
      rw [Functor.map_comp_apply, Functor.map_lift_apply, Sheaf.sectionsFunctor_map_ringAddHom]
      exact ((congrArg (fun z : ToType (R.obj.obj X) ↦ ψ.hom.app X x + z) (hδ X x)).trans
        (add_sub_cancel _ _)).symm
  have key : (pullbackRingSheafMap K Φ φ).hom.app Y y =
      (pullbackRingSheafMap K Φ ψ).hom.app Y y +
        (show ToType ((pullbackRingSheaf K Φ R).obj.obj Y) from (Φ.map δ).hom.app Y y) := by
    change (Φ ⋙ Sheaf.sectionsFunctor K Y).map ((sheafCompose J (forget RingCat.{w₁})).map φ) y =
      Sheaf.ringAddObj R (Φ ⋙ Sheaf.sectionsFunctor K Y)
        ((Φ ⋙ Sheaf.sectionsFunctor K Y).map ((sheafCompose J (forget RingCat.{w₁})).map ψ) y)
        ((Φ ⋙ Sheaf.sectionsFunctor K Y).map δ y)
    refine (congrArg (fun m ↦ (Φ ⋙ Sheaf.sectionsFunctor K Y).map m y) hset).trans ?_
    refine ((Φ ⋙ Sheaf.sectionsFunctor K Y).map_comp_apply _ _ y).trans ?_
    exact congrArg ((Φ ⋙ Sheaf.sectionsFunctor K Y).map (Sheaf.ringAddHom R))
      (Functor.map_lift_apply (P := Φ ⋙ Sheaf.sectionsFunctor K Y)
        ((sheafCompose J (forget RingCat.{w₁})).map ψ) δ y)
  rw [key, add_sub_cancel_left]

end PushforwardDifference

/-! ### A chase in a category -/

section Chase

variable {𝒜 : Type*} [Category 𝒜]

/-- The category-level chase behind
`AlgebraicGeometry.Space.restrictedDerivationSetHom_postcomp`, with every object, morphism and
equation a variable. -/
theorem comp_chase_postcomp {A O M'' E R'' F FO FM FE FR : 𝒜} (j' : A ⟶ O) (u'' : O ⟶ M'')
    (m'' : M'' ⟶ E) (ι' : E ⟶ R'') (σ : A ⟶ F) (Fj : F ⟶ FO) (Fu : FO ⟶ FM) (Fg : FM ⟶ FE)
    (Fι : FE ⟶ FR) (cmp : FR ⟶ R'') (s : O ⟶ FO) (mc : FE ⟶ E) (FD : F ⟶ FR) (P : O ⟶ FM)
    (mm : FM ⟶ E) (e1 : u'' ≫ m'' = P ≫ mm) (hP : P = s ≫ Fu) (hm : mm = Fg ≫ mc)
    (e2 : mc ≫ ι' = Fι ≫ cmp) (e3 : j' ≫ s = σ ≫ Fj) (hFD : FD = Fj ≫ Fu ≫ Fg ≫ Fι) :
    j' ≫ u'' ≫ m'' ≫ ι' = σ ≫ FD ≫ cmp := by
  subst hP hm hFD
  rw [← Category.assoc u'' m'' ι', e1]
  simp only [Category.assoc]
  rw [e2, ← Category.assoc j' s, e3]
  simp only [Category.assoc]

/-- A functor applied to a factored morphism, after a morphism into its source whose composite
with the first factor is known. -/
theorem comp_map_eq_of_factorization {ℬ : Type*} [Category ℬ] (F : 𝒜 ⥤ ℬ) {a b c : 𝒜} {X : ℬ}
    (u : X ⟶ F.obj a) (h : a ⟶ c) (x : a ⟶ b) (G : b ⟶ c) (P : X ⟶ F.obj b)
    (hM : h = x ≫ G) (hP : u ≫ F.map x = P) : u ≫ F.map h = P ≫ F.map G := by
  subst hM hP
  rw [F.map_comp, Category.assoc]

/-- A functor applied to a composite of four morphisms. -/
theorem map_comp_comp_comp {ℬ : Type*} [Category ℬ] (F : 𝒜 ⥤ ℬ) {a b c d e : 𝒜} (w : a ⟶ b)
    (x : b ⟶ c) (y : c ⟶ d) (z : d ⟶ e) :
    F.map (w ≫ x ≫ y ≫ z) = F.map w ≫ F.map x ≫ F.map y ≫ F.map z := by
  simp only [Functor.map_comp]

/-- Cancelling an isomorphism and its inverse in a composite of five morphisms. -/
theorem comp_comp_comp_comp_cancel {A₀ A₁ A₂ A₃ : 𝒜} (i : A₀ ⟶ A₁)
    (c : A₁ ⟶ A₂) (ci : A₂ ⟶ A₁) (k : A₁ ⟶ A₀) (x : A₀ ⟶ A₃) (hc : c ≫ ci = 𝟙 A₁)
    (hi : i ≫ k = 𝟙 A₀) : i ≫ c ≫ ci ≫ k ≫ x = x := by
  rw [reassoc_of% hc, reassoc_of% hi]

end Chase

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local irreducible] modulePullback

variable {Q R R'' T T'' : AlgebraicSpaces B S hS}

/-- **Equation [Stacks Project, Tag 0619] under postcomposition with the canonical map of
differentials.**  For `θ : e^*Ω_{R/T} ⟶ C` and `f₀ : R ⟶ R''` over `t : T ⟶ T''`, the
derivation attached to `θ'' = (e ≫ f₀)^*Ω_{R''/T''} ≅ e^*f₀^*Ω_{R''/T''} ⟶ e^*Ω_{R/T} ⟶ C`
(the middle map the inverse image of the map `c_{f₀}` of Stacks 04CX) is the derivation attached
to `θ` read on `f₀^♯ y`, followed by the comparison `f₀_*e_* ≅ (e ≫ f₀)_*`. -/
theorem derivationFamilyOfHom_comp_sheafOfDifferentialsMap (b : R ⟶ T) (b'' : R'' ⟶ T'')
    (f₀ : R ⟶ R'') (t : T ⟶ T'') (hcomm : f₀ ≫ b'' = b ≫ t) (e : Q ⟶ R)
    (C : Modules.{u, u} B S hS Q.1 Q.2)
    (θ : (modulePullback B S hS e).obj (sheafOfDifferentials B S hS b) ⟶ C)
    (V : (SmallEtale B S hS R''.1)ᵒᵖ) (y : (structureRingSheaf B S hS R'').obj.obj V) :
    derivationFamilyOfHom B S hS b'' (e ≫ f₀) C
        ((modulePullbackCompIso B S hS e f₀).inv.app (sheafOfDifferentials B S hS b'') ≫
          (modulePullback B S hS e).map
            (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm) ≫ θ) V y =
      (((modulePushforward B S hS f₀).map
            ((modulePullbackAdjunction B S hS e).homEquiv _ _ θ) ≫
          (modulePushforwardCompIso B S hS e f₀).hom.app C).val.app V).hom
        ((pushforwardUniversalDerivationHom B S hS f₀ b).hom.app V y) :=
  (derivationFamilyOfHom_comp B S hS b'' e f₀ (sheafOfDifferentials B S hS b) C
    (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm) θ V y).trans
    (congrArg (fun z => (((modulePushforward B S hS f₀).map
            ((modulePullbackAdjunction B S hS e).homEquiv _ _ θ) ≫
          (modulePushforwardCompIso B S hS e f₀).hom.app C).val.app V).hom z)
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm V y))

/-! ### Morphisms into the underlying sheaf of sets of a module, on sections -/

section SetSheafApp

variable {Y Y' : AlgebraicSpaces B S hS}

/-- A morphism of sheaves of sets into a module followed by a morphism of modules, on a
section.  Stated at a variable morphism of modules, so that no consumer unfolds it. -/
theorem setSheafHom_comp_moduleSheafFunctor_map_app
    {A : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)} {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (P : A ⟶ (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj M) (g : M ⟶ N)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) (a : A.obj.obj V) :
    (P ≫ (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map g).hom.app V a =
      (g.val.app V).hom (P.hom.app V a) :=
  rfl

/-- The universal derivation followed by a morphism of modules, on a section. -/
theorem universalDerivationHom_comp_moduleSheafFunctor_map_app (b : Y ⟶ Y')
    {N : Modules.{u, u} B S hS Y.1 Y.2} (g : sheafOfDifferentials B S hS b ⟶ N)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) (y : (structureRingSheaf B S hS Y).obj.obj V) :
    (universalDerivationHom B S hS b ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map g).hom.app V y =
      (g.val.app V).hom ((universalDerivation B S hS b).d y) :=
  rfl

end SetSheafApp

section DerivationSet

variable {Q R R'' T T'' : AlgebraicSpaces B S hS}

/-- The transpose along `(e ≫ f₀)^* ⊣ (e ≫ f₀)_*` of `(e ≫ f₀)^*M ≅ e^*f₀^*M ⟶ e^*N ⟶ C`: the
transpose of `c` along `f₀`, the direct image along `f₀` of the transpose of `θ` along `e`, and
the comparison of iterated direct images. -/
theorem homEquiv_modulePullbackCompIso_inv_app_map_comp (f₀ : R ⟶ R'') (e : Q ⟶ R)
    (M : Modules.{u, u} B S hS R''.1 R''.2) (N : Modules.{u, u} B S hS R.1 R.2)
    (C : Modules.{u, u} B S hS Q.1 Q.2) (c : (modulePullback B S hS f₀).obj M ⟶ N)
    (θ : (modulePullback B S hS e).obj N ⟶ C) :
    (modulePullbackAdjunction B S hS
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e f₀)).homEquiv M C
        ((modulePullbackCompIso B S hS e f₀).inv.app M ≫ (modulePullback B S hS e).map c ≫ θ) =
      (modulePullbackAdjunction B S hS f₀).homEquiv M N c ≫
        (modulePushforward B S hS f₀).map ((modulePullbackAdjunction B S hS e).homEquiv N C θ) ≫
        (modulePushforwardCompIso B S hS e f₀).hom.app C := by
  rw [homEquiv_modulePullbackCompIso_inv_app_comp, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Category.assoc]

/-- The pulled-back section `θ'' : (e ≫ f₀)^*Ω_{R''/T''} ≅ e^*f₀^*Ω_{R''/T''} ⟶ e^*Ω_{R/T} ⟶ C`
of the postcomposition law, the middle map the inverse image of the canonical map of
[Stacks Project, Tag 04CX]. -/
noncomputable def postcompDerivationDatum (b : R ⟶ T) (b'' : R'' ⟶ T'') (f₀ : R ⟶ R'')
    (t : T ⟶ T'')
    (hcomm : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f₀ b'' =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ b t) (e : Q ⟶ R)
    (C : Modules.{u, u} B S hS Q.1 Q.2)
    (θ : (modulePullback B S hS e).obj (sheafOfDifferentials B S hS b) ⟶ C) :
    (modulePullback B S hS (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e f₀)).obj
        (sheafOfDifferentials B S hS b'') ⟶ C :=
  (modulePullbackCompIso B S hS e f₀).inv.app (sheafOfDifferentials B S hS b'') ≫
    (modulePullback B S hS e).map (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm) ≫ θ

/-- **The datum of the postcomposition law undoes an inverse.**  When the canonical map
`c_{f₀}` of [Stacks Project, Tag 04CX] is an isomorphism, the datum `θ''` attached to
`e^*(c_{f₀})^{-1}` followed by `e^*f₀^* = (e ≫ f₀)^*` and by `x` is `x`. -/
theorem postcompDerivationDatum_map_inv_comp (b : R ⟶ T) (b'' : R'' ⟶ T'') (f₀ : R ⟶ R'')
    (t : T ⟶ T'')
    (hcomm : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f₀ b'' =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ b t) (e : Q ⟶ R)
    (C : Modules.{u, u} B S hS Q.1 Q.2) [IsIso (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm)]
    (x : (modulePullback B S hS (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e f₀)).obj
        (sheafOfDifferentials B S hS b'') ⟶ C) :
    postcompDerivationDatum B S hS b b'' f₀ t hcomm e C
        ((modulePullback B S hS e).map (inv (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm)) ≫
          (modulePullbackCompIso B S hS e f₀).hom.app (sheafOfDifferentials B S hS b'') ≫ x) =
      x :=
  comp_comp_comp_comp_cancel _ _ _ _ x
    (((modulePullback B S hS e).map_comp _ _).symm.trans
      ((congrArg (modulePullback B S hS e).map (IsIso.hom_inv_id _)).trans
        ((modulePullback B S hS e).map_id _)))
    (Iso.inv_hom_id_app (modulePullbackCompIso B S hS e f₀) _)

/-- The section `e^*(c_{f₀})^{-1}` followed by `e^*f₀^* = (e ≫ f₀)^*` and by `x`, for `c_{f₀}`
the canonical map of [Stacks Project, Tag 04CX] when it is an isomorphism: the inverse of the
passage `θ ↦ θ''` of the postcomposition law. -/
noncomputable def postcompInverseDatum (b : R ⟶ T) (b'' : R'' ⟶ T'') (f₀ : R ⟶ R'')
    (t : T ⟶ T'')
    (hcomm : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f₀ b'' =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ b t) (e : Q ⟶ R)
    (C : Modules.{u, u} B S hS Q.1 Q.2)
    [hiso : IsIso (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm)]
    (x : (modulePullback B S hS (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e f₀)).obj
        (sheafOfDifferentials B S hS b'') ⟶ C) :
    (modulePullback B S hS e).obj (sheafOfDifferentials B S hS b) ⟶ C :=
  (modulePullback B S hS e).map (inv (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm)) ≫
    (modulePullbackCompIso B S hS e f₀).hom.app (sheafOfDifferentials B S hS b'') ≫ x

/-- `θ ↦ θ''` undoes `AlgebraicGeometry.Space.postcompInverseDatum`. -/
theorem postcompDerivationDatum_postcompInverseDatum (b : R ⟶ T) (b'' : R'' ⟶ T'')
    (f₀ : R ⟶ R'') (t : T ⟶ T'')
    (hcomm : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f₀ b'' =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ b t) (e : Q ⟶ R)
    (C : Modules.{u, u} B S hS Q.1 Q.2)
    [hiso : IsIso (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm)]
    (x : (modulePullback B S hS (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e f₀)).obj
        (sheafOfDifferentials B S hS b'') ⟶ C) :
    postcompDerivationDatum B S hS b b'' f₀ t hcomm e C
        (postcompInverseDatum B S hS b b'' f₀ t hcomm e C (hiso := hiso) x) = x :=
  postcompDerivationDatum_map_inv_comp B S hS b b'' f₀ t hcomm e C x

/-- Equation 0619 under postcomposition with the canonical map of differentials, on underlying
sheaves of sets: the universal derivation `d_{R''/T''}` followed by the transpose of `θ''` is
`f₀_*d_{R/T} ∘ f₀^♯` followed by the direct image of the transpose of `θ` and the comparison of
iterated direct images. -/
theorem universalDerivationHom_comp_homEquiv_comp_sheafOfDifferentialsMap (b : R ⟶ T)
    (b'' : R'' ⟶ T'') (f₀ : R ⟶ R'') (t : T ⟶ T'')
    (hcomm : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f₀ b'' =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ b t) (e : Q ⟶ R)
    (C : Modules.{u, u} B S hS Q.1 Q.2)
    (θ : (modulePullback B S hS e).obj (sheafOfDifferentials B S hS b) ⟶ C) :
    universalDerivationHom B S hS b'' ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS R'')).map
          ((modulePullbackAdjunction B S hS
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e f₀)).homEquiv _ _
            (postcompDerivationDatum B S hS b b'' f₀ t hcomm e C θ)) =
      pushforwardUniversalDerivationHom B S hS f₀ b ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS R'')).map
          ((modulePushforward B S hS f₀).map
              ((modulePullbackAdjunction B S hS e).homEquiv _ _ θ) ≫
            (modulePushforwardCompIso B S hS e f₀).hom.app C) :=
  comp_map_eq_of_factorization (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS R''))
    (universalDerivationHom B S hS b'')
    ((modulePullbackAdjunction B S hS
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e f₀)).homEquiv _ _
      (postcompDerivationDatum B S hS b b'' f₀ t hcomm e C θ))
    ((modulePullbackAdjunction B S hS f₀).homEquiv _ _
      (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm))
    ((modulePushforward B S hS f₀).map ((modulePullbackAdjunction B S hS e).homEquiv _ _ θ) ≫
      (modulePushforwardCompIso B S hS e f₀).hom.app C)
    (pushforwardUniversalDerivationHom B S hS f₀ b)
    (homEquiv_modulePullbackCompIso_inv_app_map_comp B S hS f₀ e _ _ C
      (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm) θ)
    ((universalDerivationHom_comp_homEquiv B S hS f₀ b'' b
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm)).trans
      (pushforwardUniversalDerivationHom_eq B S hS f₀ b).symm)

end DerivationSet

/-- The comparison of iterated direct images of modules followed by the direct image along the
composite of a morphism of sheaves of sets out of the module: the iterated direct image of the
morphism followed by the comparison of iterated direct images of sheaves of sets. -/
theorem moduleSheafFunctor_map_modulePushforwardCompIso_hom_app_comp
    {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (M : Modules.{u, u} B S hS V₁.1 V₁.2)
    {A : Sheaf (SmallEtale.topology B S hS V₁.1) (Type u)}
    (m : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₁)).obj M ⟶ A) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₃)).map
        ((modulePushforwardCompIso B S hS f g).hom.app M) ≫
      (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.map m =
      (smallToposMorphismTypeU B S hS g).pushforward.map
          ((smallToposMorphismTypeU B S hS f).pushforward.map m) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app A :=
  (congrArg (fun k ↦ k ≫ (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.map m)
      (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f g M)).trans
    ((smallToposMorphismTypeU_comp B S hS f g).hom.naturality m).symm

/-- The sheaf-of-sets functor on a composite of morphisms of modules, on a section.  Stated at
variable modules, so that using it at a composite is an instantiation. -/
theorem moduleSheafFunctor_map_comp_app {V : AlgebraicSpaces B S hS}
    {L M N : Modules.{u, u} B S hS V.1 V.2} (a : L ⟶ M) (b : M ⟶ N)
    (W : (SmallEtale B S hS V.1)ᵒᵖ)
    (z : ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V)).obj L).obj.obj W) :
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V)).map (a ≫ b)).hom.app W z =
      (b.val.app W).hom ((a.val.app W).hom z) :=
  rfl

/-- The direct image of a morphism of modules followed by the comparison of iterated direct
images of modules, on underlying sheaves of sets: the direct image of the underlying morphism,
then the comparison of iterated direct images of sheaves of sets.  Glued from sections
(`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app`), as on sheaves the kernel
would have to reduce the transports inside the comparison. -/
theorem moduleSheafFunctor_map_modulePushforward_map_comp_modulePushforwardCompIso_hom_app
    {V₀ V₁ V₂ : AlgebraicSpaces B S hS} (f₁ : V₀ ⟶ V₁) (f : V₁ ⟶ V₂)
    (C : Modules.{u, u} B S hS V₀.1 V₀.2) {M : Modules.{u, u} B S hS V₁.1 V₁.2}
    (h : M ⟶ (modulePushforward B S hS f₁).obj C) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₂)).map
        ((modulePushforward B S hS f).map h ≫ (modulePushforwardCompIso B S hS f₁ f).hom.app C) =
      (smallEtaleDirectImage B S hS f).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₁)).map h) ≫
        (smallToposMorphismTypeU_comp B S hS f₁ f).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₀)).obj C) :=
  CategoryTheory.Sheaf.hom_ext_sections fun W z ↦
    (moduleSheafFunctor_map_comp_app B S hS (M := (modulePushforward B S hS f).obj
        ((modulePushforward B S hS f₁).obj C))
      ((modulePushforward B S hS f).map h) ((modulePushforwardCompIso B S hS f₁ f).hom.app C)
      W z).trans
    (modulePushforwardCompIso_hom_app_val_app B S hS f₁ f C W
      ((((modulePushforward B S hS f).map h).val.app W).hom z))

/-- The comparison of iterated direct images of sheaves of sets is natural. -/
theorem smallToposMorphismTypeU_comp_hom_app_comp_map {V₀ V₁ V₂ : AlgebraicSpaces B S hS}
    (f₁ : V₀ ⟶ V₁) (f : V₁ ⟶ V₂) (C : Modules.{u, u} B S hS V₀.1 V₀.2)
    {A' : Sheaf (SmallEtale.topology B S hS V₀.1) (Type u)}
    (m : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₀)).obj C ⟶ A') :
    CategoryStruct.comp
        (X := (smallToposMorphismTypeU B S hS f).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₁)).obj
            ((modulePushforward B S hS f₁).obj C)))
        (Y := (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₂)).obj
          ((modulePushforward B S hS (f₁ ≫ f)).obj C))
        ((smallToposMorphismTypeU_comp B S hS f₁ f).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₀)).obj C))
        ((smallToposMorphismTypeU B S hS (f₁ ≫ f)).pushforward.map m) =
      CategoryStruct.comp
        (X := (smallToposMorphismTypeU B S hS f).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₁)).obj
            ((modulePushforward B S hS f₁).obj C)))
        ((smallToposMorphismTypeU B S hS f).pushforward.map
          ((smallToposMorphismTypeU B S hS f₁).pushforward.map m))
        ((smallToposMorphismTypeU_comp B S hS f₁ f).hom.app A') :=
  ((smallToposMorphismTypeU_comp B S hS f₁ f).hom.naturality m).symm

/-! ### The action of 0CK6 under postcomposition with a morphism of thickenings -/

section Postcomposition

variable {X W W' Tq Tq' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (W₀' : ClosedSubspaces B S hS W'.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (f₀ : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))
  (f' : W ⟶ W')
  (hf : subspaceInclusion B S hS W W₀ ≫ f' = f₀ ≫ subspaceInclusion B S hS W' W₀')
  (q : W ⟶ Tq) (q' : W' ⟶ Tq') (t : Tq ⟶ Tq')
  (hcomm : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f₀
      (subspaceInclusion B S hS W' W₀' ≫ q') =
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (subspaceInclusion B S hS W W₀ ≫ q) t)
  (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- The derivation `ι ∘ D ∘ j^♯` attached by Equation [Stacks Project, Tag 0619] to the
transpose `g : Ω_{W₀/T} ⟶ (e₀)_*𝒞_{Z/X}` of `θ`, read on underlying sheaves of sets:
`j^{-1}𝒪_W ⟶ 𝒪_{W₀} ⟶ (e₀)_*𝒞_{Z/X} ⟶ (e₀)_*(i^{-1}𝒪_X)`. -/
noncomputable def restrictedDerivationSetHom
    (g : sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q) ⟶
      (modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)) :
    (sheafCompose (SmallEtale.topology B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)) ⟶
      (sheafCompose (SmallEtale.topology B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).obj
        (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀) :=
  (sheafCompose (SmallEtale.topology B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
      (CategoryTheory.forget RingCat.{u})).map
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)) ≫
    universalDerivationHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) ≫
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map g ≫
    (smallToposMorphismTypeU B S hS e₀).pushforward.map (conormalSetInclusion B S hS Z hZ)

/-- `AlgebraicGeometry.Space.restrictedDerivationSetHom` written out. -/
theorem restrictedDerivationSetHom_eq
    (g : sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q) ⟶
      (modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)) :
    restrictedDerivationSetHom B S hS Z W₀ e₀ q hZ g =
      (sheafCompose (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)) ≫
        universalDerivationHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map g ≫
        (smallToposMorphismTypeU B S hS e₀).pushforward.map (conormalSetInclusion B S hS Z hZ) :=
  rfl

/-- `AlgebraicGeometry.Space.restrictedDerivationSetHom` on a section, at a variable `g`. -/
theorem restrictedDerivationSetHom_app_eq
    (g : sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q) ⟶
      (modulePushforward B S hS e₀).obj (conormalModule B S hS X Z))
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V)) :
    (restrictedDerivationSetHom B S hS Z W₀ e₀ q hZ g).hom.app V x =
      ((smallToposMorphismTypeU B S hS e₀).pushforward.map
          (conormalSetInclusion B S hS Z hZ)).hom.app V
        ((g.val.app V).hom ((universalDerivation B S hS (subspaceInclusion B S hS W W₀ ≫ q)).d
          ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
            x))) :=
  rfl

/-- `AlgebraicGeometry.Space.restrictedDerivationSetHom` on a section is the inclusion of the
derivation of Equation 0619 into the ideal of values. -/
theorem restrictedDerivationSetHom_app
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V)) :
    (restrictedDerivationSetHom B S hS Z W₀ e₀ q hZ
        ((modulePullbackAdjunction B S hS e₀).homEquiv _ _ θ)).hom.app V x =
      (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
        (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
          (conormalModule B S hS X Z) θ V
          ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x)) :=
  (restrictedDerivationSetHom_app_eq B S hS Z W₀ e₀ q hZ _ V x).trans
    ((restrictedSquareZeroValues_ι_eq_conormalSetInclusion B S hS Z W₀ e₀ hZ _).symm.trans
      (congrArg (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
        (derivationFamilyOfHom_eq_homEquiv B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
          (conormalModule B S hS X Z) θ V _).symm))

/-- **The derivation clause, pushed forward along `f₀`.**  If the transported comorphisms of `c`
and `b` differ by the derivation attached to `θ`, then their direct images along `f₀` differ by
the direct image of that derivation. -/
theorem pushforward_restrictedSharpThroughThickening_sub (c b : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hb : subspaceInclusion B S hS X Z ≫ b = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (hD : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V)),
        (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
            (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
              (conormalModule B S hS X Z) θ V
              ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
                x)) =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
            (restrictedSharpThroughThickening B S hS Z W₀ b e₀ hb).hom.app V x)
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (y : ToType ((restrictedThickeningLiftRingSheaf B S hS W₀ W₀' f₀).obj.obj V)) :
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS f₀)).map
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)).hom.app V y -
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS f₀)).map
        (restrictedSharpThroughThickening B S hS Z W₀ b e₀ hb)).hom.app V y =
      ((smallToposMorphismTypeU B S hS f₀).pushforward.map
        (restrictedDerivationSetHom B S hS Z W₀ e₀ q hZ
          ((modulePullbackAdjunction B S hS e₀).homEquiv _ _ θ))).hom.app V y :=
  pullbackRingSheafMap_sub_app_apply (smallToposMorphismTypeU B S hS f₀).pushforward
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)
    (restrictedSharpThroughThickening B S hS Z W₀ b e₀ hb)
    (restrictedDerivationSetHom B S hS Z W₀ e₀ q hZ
          ((modulePullbackAdjunction B S hS e₀).homEquiv _ _ θ))
    (fun V x ↦ (restrictedDerivationSetHom_app B S hS Z W₀ e₀ q hZ θ V x).trans (hD V x)) V y

/-- The structure comorphism of `W₀' ⊂ W'` followed by `f₀^♯`, on underlying sheaves of sets, is
the transported comorphism of `(f₀, f')` followed by the direct image of the structure
comorphism of `W₀ ⊂ W`. -/
theorem structureSharpRingInverseImage_comp_structureSharpSet :
    (sheafCompose (SmallEtale.topology B S hS
        (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).map
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W' W₀')) ≫
      structureSharpSet B S hS f₀ =
      (sheafCompose (SmallEtale.topology B S hS
          (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS W₀ W₀' f' f₀ hf) ≫
        (smallToposMorphismTypeU B S hS f₀).pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).map
            (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))) :=
  ((sheafCompose (SmallEtale.topology B S hS
      (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)
      (CategoryTheory.forget RingCat.{u})).map_comp _ _).symm.trans
    ((congrArg (sheafCompose (SmallEtale.topology B S hS
        (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).map
      (restrictedSharpThroughThickening_comp_reduction_structureSharp B S hS W₀ W₀' f₀ f'
        hf).symm).trans
      (((sheafCompose (SmallEtale.topology B S hS
        (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).map_comp _ _).trans
        (congrArg (fun m ↦ (sheafCompose (SmallEtale.topology B S hS
            (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).map
            (restrictedSharpThroughThickening B S hS W₀ W₀' f' f₀ hf) ≫ m)
          (ringSheafMap_pullbackRingSheafMap _ _ _))))

/-- For `g₀ : Ω_{W₀/T} ⟶ (e₀)_*𝒞_{Z/X}`, the direct image `(f₀)_*g₀` followed by the comparison
`(f₀)_*(e₀)_* ≅ (e₀ ≫ f₀)_*` of iterated direct images of modules, on underlying sheaves of sets,
is the direct image of the underlying morphism of `g₀` along `f₀` followed by the comparison of
iterated direct images of sheaves of sets: the instance of
`moduleSheafFunctor_map_modulePushforward_map_comp_modulePushforwardCompIso_hom_app` at `g₀`. -/
theorem probeH1
    (g₀ : sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q) ⟶
      (modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
        (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))).map
        ((modulePushforward B S hS f₀).map g₀ ≫
          (modulePushforwardCompIso B S hS e₀ f₀).hom.app (conormalModule B S hS X Z)) =
      (smallEtaleDirectImage B S hS f₀).map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map g₀) ≫
        (smallToposMorphismTypeU_comp B S hS e₀ f₀).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj (conormalModule B S hS X Z)) :=
  moduleSheafFunctor_map_modulePushforward_map_comp_modulePushforwardCompIso_hom_app B S hS
      e₀ f₀ (conormalModule B S hS X Z) g₀

/-- On the underlying morphism of sheaves of sets of `g₀ : Ω_{W₀/T} ⟶ (e₀)_*𝒞_{Z/X}`, the direct
image `AlgebraicGeometry.Space.smallEtaleDirectImage` along `f₀` is the pushforward of
`AlgebraicGeometry.Space.smallToposMorphismTypeU` of `f₀`, by definition. -/
theorem probeH2
    (g₀ : sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q) ⟶
      (modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)) :
    (smallEtaleDirectImage B S hS f₀).map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map g₀) =
      (smallToposMorphismTypeU B S hS f₀).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map g₀) := rfl

/-- `AlgebraicGeometry.Space.probeH1` with the direct image along `f₀` spelled as the pushforward
of `AlgebraicGeometry.Space.smallToposMorphismTypeU` of `f₀`. -/
theorem probeH3
    (g₀ : sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q) ⟶
      (modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
        (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))).map
        ((modulePushforward B S hS f₀).map g₀ ≫
          (modulePushforwardCompIso B S hS e₀ f₀).hom.app (conormalModule B S hS X Z)) =
      (smallToposMorphismTypeU B S hS f₀).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map g₀) ≫
        (smallToposMorphismTypeU_comp B S hS e₀ f₀).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj (conormalModule B S hS X Z)) :=
  moduleSheafFunctor_map_modulePushforward_map_comp_modulePushforwardCompIso_hom_app B S hS
      e₀ f₀ (conormalModule B S hS X Z) g₀

/-- **The derivation clause under postcomposition, on underlying sheaves of sets.**  If the
universal derivation of `W₀'` followed by `g` is `f₀_*d ∘ f₀^♯` followed by the direct image of
`g₀` and the comparison of iterated direct images, then the derivation `ι' ∘ D'' ∘ j'^♯`
attached to `g` is the transported comorphism `σ` of `(f₀, f')`, followed by the direct image
along `f₀` of the derivation `ι ∘ D ∘ j^♯` attached to `g₀` and by the comparison of iterated
direct images. -/
theorem restrictedDerivationSetHom_postcomp
    (g₀ : sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q) ⟶
      (modulePushforward B S hS e₀).obj (conormalModule B S hS X Z))
    (g : sheafOfDifferentials B S hS (subspaceInclusion B S hS W' W₀' ≫ q') ⟶
      (modulePushforward B S hS (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)).obj
        (conormalModule B S hS X Z))
    (hg : universalDerivationHom B S hS (subspaceInclusion B S hS W' W₀' ≫ q') ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))).map g =
      pushforwardUniversalDerivationHom B S hS f₀ (subspaceInclusion B S hS W W₀ ≫ q) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))).map
          ((modulePushforward B S hS f₀).map g₀ ≫
          (modulePushforwardCompIso B S hS e₀ f₀).hom.app (conormalModule B S hS X Z))) :
    restrictedDerivationSetHom B S hS Z W₀'
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀) q' hZ g =
      (sheafCompose (SmallEtale.topology B S hS
          (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS W₀ W₀' f' f₀ hf) ≫
        (smallToposMorphismTypeU B S hS f₀).pushforward.map
          (restrictedDerivationSetHom B S hS Z W₀ e₀ q hZ g₀) ≫
        (smallToposMorphismTypeU_comp B S hS e₀ f₀).hom.app
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).obj
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) := by
  refine (restrictedDerivationSetHom_eq B S hS Z W₀'
    (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀) q' hZ g).trans ?_
  refine comp_chase_postcomp
    (Fu := (smallToposMorphismTypeU B S hS f₀).pushforward.map
        (universalDerivationHom B S hS (subspaceInclusion B S hS W W₀ ≫ q)))
    (Fg := (smallToposMorphismTypeU B S hS f₀).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map g₀))
    (Fj := (smallToposMorphismTypeU B S hS f₀).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))))
    (Fι := (smallToposMorphismTypeU B S hS f₀).pushforward.map
        ((smallToposMorphismTypeU B S hS e₀).pushforward.map (conormalSetInclusion B S hS Z hZ)))
    (s := structureSharpSet B S hS f₀)
    (mc := (smallToposMorphismTypeU_comp B S hS e₀ f₀).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj (conormalModule B S hS X Z)))
    (P := pushforwardUniversalDerivationHom B S hS f₀ (subspaceInclusion B S hS W W₀ ≫ q))
    (mm := (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
        (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))).map
        ((modulePushforward B S hS f₀).map g₀ ≫
          (modulePushforwardCompIso B S hS e₀ f₀).hom.app (conormalModule B S hS X Z)))
    _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hg
  · exact pushforwardUniversalDerivationHom_eq B S hS f₀ (subspaceInclusion B S hS W W₀ ≫ q)
  · exact moduleSheafFunctor_map_modulePushforward_map_comp_modulePushforwardCompIso_hom_app B S hS
        e₀ f₀ (conormalModule B S hS X Z) g₀
  · exact smallToposMorphismTypeU_comp_hom_app_comp_map B S hS e₀ f₀ (conormalModule B S hS X Z)
        (conormalSetInclusion B S hS Z hZ)
  · exact structureSharpRingInverseImage_comp_structureSharpSet B S hS W₀ W₀' f₀ f' hf
  · refine (congrArg (smallToposMorphismTypeU B S hS f₀).pushforward.map
      (restrictedDerivationSetHom_eq B S hS Z W₀ e₀ q hZ g₀)).trans ?_
    exact map_comp_comp_comp (smallToposMorphismTypeU B S hS f₀).pushforward
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).map
            (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)))
        (universalDerivationHom B S hS (subspaceInclusion B S hS W W₀ ≫ q))
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map g₀)
        ((smallToposMorphismTypeU B S hS e₀).pushforward.map (conormalSetInclusion B S hS Z hZ))

end Postcomposition

section PostcompositionLaw

variable {X W W' Tq Tq' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (W₀' : ClosedSubspaces B S hS W'.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (f₀ : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))
  (f' : W ⟶ W')
  (hf : subspaceInclusion B S hS W W₀ ≫ f' = f₀ ≫ subspaceInclusion B S hS W' W₀')
  (q : W ⟶ Tq) (q' : W' ⟶ Tq') (t : Tq ⟶ Tq')
  (hcomm : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f₀
      (subspaceInclusion B S hS W' W₀' ≫ q') =
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (subspaceInclusion B S hS W W₀ ≫ q) t)
  (hft : f' ≫ q' = q ≫ t)
  (hZ : IsFirstOrderThickening B S hS X Z.1)
  (hW : IsFirstOrderThickening B S hS W W₀.1) (hW' : IsFirstOrderThickening B S hS W' W₀'.1)

include hft in
/-- A morphism over `T`, postcomposed with `f'` over `t : T ⟶ T'`, lies over `T'`. -/
theorem comp_comp_eq_comp_of_comp_eq (c : X ⟶ W) (p : X ⟶ Tq) (hcq : c ≫ q = p) :
    (c ≫ f') ≫ q' = p ≫ t :=
  (Category.assoc _ _ _).trans ((congrArg (c ≫ ·) hft).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) hcq)))

/-- **The conormal clause under postcomposition.**  Two morphisms of thickenings `(e₀, c)` and
`(e₀, b)` with the same conormal map keep the same conormal map after postcomposition with
`(f₀, f')`, by the composition law of conormal maps of [Stacks Project, Tag 04G2]. -/
theorem conormalMap_comp_target_eq (c b : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hb : subspaceInclusion B S hS X Z ≫ b = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hcm : conormalMap B S hS Z W₀ c e₀ hc = conormalMap B S hS Z W₀ b e₀ hb) :
    conormalMap B S hS Z W₀' (c ≫ f')
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
        (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' c e₀ f₀ hc f' hf) =
      conormalMap B S hS Z W₀' (b ≫ f')
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
        (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' b e₀ f₀ hb f' hf) := by
  have key (g : X ⟶ W)
      (hg : subspaceInclusion B S hS X Z ≫ g = e₀ ≫ subspaceInclusion B S hS W W₀) :=
    conormalMap_comp_triangle B S hS (g := g) (g' := f') (Z := Z) (Z' := W₀) (Z'' := W₀')
      (f := e₀) (f' := f₀) (hsq := hg) (hsq' := hf)
      (fc := @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀) (hfc := rfl)
      (hsqc := comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' g e₀ f₀ hg f' hf)
  rw [key c hc, key b hb, hcm]

/-- The transported comorphism of `c ≫ f'` on a section: `σ`, then the direct image along `f₀`
of that of `c`, then the comparison of iterated direct images. -/
theorem restrictedSharpThroughThickening_comp_target_app (c : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W' W₀')).obj.obj V)) :
    (restrictedSharpThroughThickening B S hS Z W₀' (c ≫ f')
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
        (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' c e₀ f₀ hc f' hf)).hom.app V x =
      (pushforwardRingSheafCompHom B S hS e₀ f₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V
        (((pushforwardRingFunctor (smallToposMorphismTypeU B S hS f₀)).map
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)).hom.app V
          ((restrictedSharpThroughThickening B S hS W₀ W₀' f' f₀ hf).hom.app V x)) :=
  (ringSheafHom_congr_app_apply
    (restrictedSharpThroughThickening_comp_source_algebraicSpaces B S hS Z W₀ W₀' c e₀ f₀ hc f'
      hf) V x).trans
    ((ringSheafHom_comp_app_apply _ _ V x).trans (ringSheafHom_comp_app_apply _ _ V _))

/-- **The derivation clause under postcomposition**, at a variable datum `θ''` equal to the
pulled-back section of `AlgebraicGeometry.Space.postcompDerivationDatum`. -/
theorem ι_derivationFamilyOfHom_comp_target_of_eq (c b : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hb : subspaceInclusion B S hS X Z ≫ b = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (hD : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V)),
        (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
            (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
              (conormalModule B S hS X Z) θ V
              ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
                x)) =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
            (restrictedSharpThroughThickening B S hS Z W₀ b e₀ hb).hom.app V x)
    (θ'' : (modulePullback B S hS (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W' W₀' ≫ q')) ⟶
      conormalModule B S hS X Z)
    (hθ'' : θ'' = postcompDerivationDatum B S hS (subspaceInclusion B S hS W W₀ ≫ q)
          (subspaceInclusion B S hS W' W₀' ≫ q') f₀ t hcomm e₀ (conormalModule B S hS X Z) θ)
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W' W₀')).obj.obj V)) :
    (restrictedSquareZeroValues B S hS Z W₀'
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀) hZ).ι
        (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W' W₀' ≫ q')
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
          (conormalModule B S hS X Z)
          θ'' V
          ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W' W₀')).hom.app V
            x)) =
      (restrictedSharpThroughThickening B S hS Z W₀' (c ≫ f')
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
          (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' c e₀ f₀ hc f' hf)).hom.app V x -
        (restrictedSharpThroughThickening B S hS Z W₀' (b ≫ f')
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
          (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' b e₀ f₀ hb f' hf)).hom.app V
          x := by
  have hg : universalDerivationHom B S hS (subspaceInclusion B S hS W' W₀' ≫ q') ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))).map
          ((modulePullbackAdjunction B S hS
            (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)).homEquiv _ _ θ'') =
      pushforwardUniversalDerivationHom B S hS f₀ (subspaceInclusion B S hS W W₀ ≫ q) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))).map
          ((modulePushforward B S hS f₀).map
            ((modulePullbackAdjunction B S hS e₀).homEquiv _ _ θ) ≫
          (modulePushforwardCompIso B S hS e₀ f₀).hom.app (conormalModule B S hS X Z)) := by
    subst hθ''
    exact universalDerivationHom_comp_homEquiv_comp_sheafOfDifferentialsMap B S hS
      (subspaceInclusion B S hS W W₀ ≫ q) (subspaceInclusion B S hS W' W₀' ≫ q') f₀ t hcomm e₀
      (conormalModule B S hS X Z) θ
  refine (restrictedDerivationSetHom_app B S hS Z W₀'
    (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀) q' hZ θ'' V x).symm.trans ?_
  refine (setSheafHom_congr_app_apply
    (restrictedDerivationSetHom_postcomp B S hS Z W₀ W₀' e₀ f₀ f' hf q q' hZ
      ((modulePullbackAdjunction B S hS e₀).homEquiv _ _ θ)
      ((modulePullbackAdjunction B S hS
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)).homEquiv _ _ θ'') hg)
    V x).trans ?_
  refine (congrArg ((pushforwardRingSheafCompHom B S hS e₀ f₀
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V)
    (pushforward_restrictedSharpThroughThickening_sub B S hS Z W₀ W₀' e₀ f₀ q hZ c b hc hb θ hD V
      ((restrictedSharpThroughThickening B S hS W₀ W₀' f' f₀ hf).hom.app V x)).symm).trans ?_
  refine (map_sub _ _ _).trans ?_
  exact congrArg₂ (· - ·)
    (restrictedSharpThroughThickening_comp_target_app B S hS Z W₀ W₀' e₀ f₀ f' hf c hc V x).symm
    (restrictedSharpThroughThickening_comp_target_app B S hS Z W₀ W₀' e₀ f₀ f' hf b hb V x).symm


/-- **The derivation clause under postcomposition.**  If the transported comorphisms of `c` and
`b` differ by the derivation attached to `θ`, then those of `c ≫ f'` and `b ≫ f'` differ by the
derivation attached to `θ''`. -/
theorem ι_derivationFamilyOfHom_comp_target (c b : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hb : subspaceInclusion B S hS X Z ≫ b = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (hD : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V)),
        (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
            (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
              (conormalModule B S hS X Z) θ V
              ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
                x)) =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
            (restrictedSharpThroughThickening B S hS Z W₀ b e₀ hb).hom.app V x)
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W' W₀')).obj.obj V)) :
    (restrictedSquareZeroValues B S hS Z W₀'
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀) hZ).ι
        (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W' W₀' ≫ q')
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
          (conormalModule B S hS X Z)
          (postcompDerivationDatum B S hS (subspaceInclusion B S hS W W₀ ≫ q)
          (subspaceInclusion B S hS W' W₀' ≫ q') f₀ t hcomm e₀ (conormalModule B S hS X Z) θ) V
          ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W' W₀')).hom.app V
            x)) =
      (restrictedSharpThroughThickening B S hS Z W₀' (c ≫ f')
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
          (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' c e₀ f₀ hc f' hf)).hom.app V x -
        (restrictedSharpThroughThickening B S hS Z W₀' (b ≫ f')
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
          (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' b e₀ f₀ hb f' hf)).hom.app V
          x :=
  ι_derivationFamilyOfHom_comp_target_of_eq B S hS Z W₀ W₀' e₀ f₀ f' hf q q' t hcomm hZ c b hc hb θ
    hD _ rfl V x
include hft hW' in
/-- **A morphism with the properties of `θ · c`, postcomposed with `(f₀, f')`, is
`θ'' · (c ≫ f')`.**  The three conditions of `AlgebraicGeometry.Space.eq_derivationMove` are
checked on `b ≫ f'`. -/
theorem comp_eq_derivationMove_target (c : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ Tq) (hcq : c ≫ q = p) (b : X ⟶ W)
    (hb : subspaceInclusion B S hS X Z ≫ b = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hbq : b ≫ q = p)
    (hcm : conormalMap B S hS Z W₀ c e₀ hc = conormalMap B S hS Z W₀ b e₀ hb)
    (hD : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V)),
        (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
            (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
              (conormalModule B S hS X Z) θ V
              ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
                x)) =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
            (restrictedSharpThroughThickening B S hS Z W₀ b e₀ hb).hom.app V x) :
    b ≫ f' =
      derivationMove B S hS Z W₀' (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
        q' hZ (c ≫ f') (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' c e₀ f₀ hc f' hf)
        (postcompDerivationDatum B S hS (subspaceInclusion B S hS W W₀ ≫ q)
          (subspaceInclusion B S hS W' W₀' ≫ q') f₀ t hcomm e₀ (conormalModule B S hS X Z) θ)
        (p ≫ t) (comp_comp_eq_comp_of_comp_eq B S hS f' q q' t hft c p hcq) :=
  eq_derivationMove B S hS Z W₀' (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
    q' hZ hW' (c ≫ f') (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' c e₀ f₀ hc f' hf)
    _ (p ≫ t) (comp_comp_eq_comp_of_comp_eq B S hS f' q q' t hft c p hcq) (b ≫ f')
    ⟨comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' b e₀ f₀ hb f' hf,
      comp_comp_eq_comp_of_comp_eq B S hS f' q q' t hft b p hbq,
      conormalMap_comp_target_eq B S hS Z W₀ W₀' e₀ f₀ f' hf c b hc hb hcm,
      ι_derivationFamilyOfHom_comp_target B S hS Z W₀ W₀' e₀ f₀ f' hf q q' t hcomm hZ c b hc hb
        θ hD⟩

include hft hW hW' in
/-- **The action of [Stacks Project, Tag 0CK6] under postcomposition with a morphism of
thickenings.**  For a morphism of first order thickenings `(e₀, c) : (Z ⊂ X) ⟶ (W₀ ⊂ W)` over
`T`, `θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` and a morphism of first order thickenings
`(f₀, f') : (W₀ ⊂ W) ⟶ (W₀' ⊂ W')` lying over `t : T ⟶ T'`:
`(θ · c) ≫ f' = θ'' · (c ≫ f')`, where
`θ'' : (e₀ ≫ f₀)^*Ω_{W₀'/T'} ≅ e₀^*f₀^*Ω_{W₀'/T'} ⟶ e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` is `θ` precomposed
with the inverse image along `e₀` of the canonical map of [Stacks Project, Tag 04CX]. -/
theorem derivationMove_comp (c : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ Tq) (hcq : c ≫ q = p) :
    derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq ≫ f' =
      derivationMove B S hS Z W₀' (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ f₀)
        q' hZ (c ≫ f') (comp_assoc_of_square_algebraicSpaces B S hS Z W₀ W₀' c e₀ f₀ hc f' hf)
        (postcompDerivationDatum B S hS (subspaceInclusion B S hS W W₀ ≫ q)
          (subspaceInclusion B S hS W' W₀' ≫ q') f₀ t hcomm e₀ (conormalModule B S hS X Z) θ)
        (p ≫ t) (comp_comp_eq_comp_of_comp_eq B S hS f' q q' t hft c p hcq) := by
  obtain ⟨hb, hbq, hcm, hD⟩ := derivationMove_spec B S hS Z W₀ e₀ q hZ hW c hc θ p hcq
  exact comp_eq_derivationMove_target B S hS Z W₀ W₀' e₀ f₀ f' hf q q' t hcomm hft hZ hW' c hc θ
    p hcq _ hb hbq hcm hD

end PostcompositionLaw

end AlgebraicGeometry.Space

end
