module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardModulesTransportMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTransport

/-!
# Stacks 07A4 for algebraic spaces is compatible with composition

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the compositor
`c : Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D6D carries the isomorphism of Stacks 07A4 for `f ≫ g`
to `Lf^*` of the one for `g`, followed by the one for `f` and `c` in each tensor factor.

The compositor is the compositor of the morphisms of small étale ringed topoi followed by the
transport along the 2-isomorphism comparing their composite with the morphism of ringed topoi of
`f ≫ g`; the first step is `derivedPullbackTensorIso_comp`, the second
`derivedPullbackTensorIso_transport`, whose input is the compatibility of Stacks 03EL with the
transport (`pullbackModulesIsoOfNatIso_hom_app_pullbackTensorIso`).

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_comp`

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y Z : AlgebraicSpaces B S hS}

/-- The transport of pullbacks in the compositor of Stacks 0D6D for algebraic spaces is the
transport along the 2-isomorphism of Stacks 03G2 comparing the two morphisms of ringed topoi. -/
theorem pullbackModulesCompTransport_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackModulesCompTransport B S hS f g =
      RingedToposHom.pullbackModulesIsoOfNatIso (smallEtaleRingedToposHomComp B S hS f g)
              (smallEtaleRingedToposHom B S hS (f ≫ g)) (smallToposMorphismTypeU_comp B S hS f g)
        (smallEtaleRingedToposHom_comp_fSharpRing B S hS f g) := rfl

/-- **Stacks 07A4 for algebraic spaces along the transport in the compositor.** -/
theorem derivedPullbackTensorIso_pullbackModulesCompTransport (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerLeft (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
          (derivedPullbackIsoOfPullbackModulesIso
            (RingedToposHom.pullbackModulesIsoOfNatIso (smallEtaleRingedToposHomComp B S hS f g)
              (smallEtaleRingedToposHom B S hS (f ≫ g)) (smallToposMorphismTypeU_comp B S hS f g)
              (smallEtaleRingedToposHom_comp_fSharpRing B S hS f g))).hom ≫
        (derivedPullbackTensorIso (smallEtaleRingedToposHom B S hS (f ≫ g))
          (smallEtaleDerivedTensorProduct B S hS X) (smallEtaleDerivedTensorProduct B S hS Z)).hom =
      (derivedPullbackTensorIso (smallEtaleRingedToposHomComp B S hS f g)
          (smallEtaleDerivedTensorProduct B S hS X) (smallEtaleDerivedTensorProduct B S hS Z)).hom ≫
        Functor.whiskerRight (NatTrans.prod
          (derivedPullbackIsoOfPullbackModulesIso
            (RingedToposHom.pullbackModulesIsoOfNatIso (smallEtaleRingedToposHomComp B S hS f g)
              (smallEtaleRingedToposHom B S hS (f ≫ g)) (smallToposMorphismTypeU_comp B S hS f g)
              (smallEtaleRingedToposHom_comp_fSharpRing B S hS f g))).hom
          (derivedPullbackIsoOfPullbackModulesIso
            (RingedToposHom.pullbackModulesIsoOfNatIso (smallEtaleRingedToposHomComp B S hS f g)
              (smallEtaleRingedToposHom B S hS (f ≫ g)) (smallToposMorphismTypeU_comp B S hS f g)
              (smallEtaleRingedToposHom_comp_fSharpRing B S hS f g))).hom)
          (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X)) :=
  derivedPullbackTensorIso_pullbackModulesIsoOfNatIso (smallEtaleRingedToposHomComp B S hS f g)
    (smallEtaleRingedToposHom B S hS (f ≫ g)) (smallToposMorphismTypeU_comp B S hS f g)
    (smallEtaleRingedToposHom_comp_fSharpRing B S hS f g)
    (smallEtaleDerivedTensorProduct B S hS X) (smallEtaleDerivedTensorProduct B S hS Z)

/-- Composing a composition law with a transport law, for abstract transformations. -/
private lemma comp_law_comp_transport {CZ CY CX : Type*} [Category CZ] [Category CY]
    [Category CX] {TZ : CZ × CZ ⥤ CZ} {TY : CY × CY ⥤ CY} {TX : CX × CX ⥤ CX}
    {Lg : CZ ⥤ CY} {Lf : CY ⥤ CX} {Lc Lχ : CZ ⥤ CX}
    (cmp : Lg ⋙ Lf ⟶ Lc) (tr : Lc ⟶ Lχ) (αg : TZ ⋙ Lg ⟶ Lg.prod Lg ⋙ TY)
    (αf : TY ⋙ Lf ⟶ Lf.prod Lf ⋙ TX) (αc : TZ ⋙ Lc ⟶ Lc.prod Lc ⋙ TX)
    (αχ : TZ ⋙ Lχ ⟶ Lχ.prod Lχ ⋙ TX)
    (h₁ : Functor.whiskerLeft TZ cmp ≫ αc =
      Functor.whiskerRight αg Lf ≫ Functor.whiskerLeft (Lg.prod Lg) αf ≫
        Functor.whiskerRight (NatTrans.prod cmp cmp) TX)
    (h₂ : Functor.whiskerLeft TZ tr ≫ αχ = αc ≫ Functor.whiskerRight (NatTrans.prod tr tr) TX) :
    Functor.whiskerLeft TZ (cmp ≫ tr) ≫ αχ =
      Functor.whiskerRight αg Lf ≫ Functor.whiskerLeft (Lg.prod Lg) αf ≫
        Functor.whiskerRight (NatTrans.prod (cmp ≫ tr) (cmp ≫ tr)) TX := by
  ext x
  have e₁ := NatTrans.congr_app h₁ x
  have e₂ := NatTrans.congr_app h₂ x
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj] at e₁ e₂ ⊢
  rw [Category.assoc, e₂, ← Category.assoc, e₁]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

/-- **Stacks 07A4 for algebraic spaces is compatible with composition.** For `f : X ⟶ Y` and
`g : Y ⟶ Z`, the compositor `c : Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D6D carries the isomorphism
of Stacks 07A4 for `f ≫ g` to `Lf^*` of the one for `g`, followed by the one for `f` and `c` in
each tensor factor. -/
theorem smallEtaleDerivedPullbackTensorIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerLeft (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
          (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom ≫
        (smallEtaleDerivedPullbackTensorIso (f ≫ g)).hom =
      Functor.whiskerRight (smallEtaleDerivedPullbackTensorIso g).hom
          (smallEtaleDerivedModulePullback B S hS f) ≫
        Functor.whiskerLeft ((smallEtaleDerivedModulePullback B S hS g).prod
            (smallEtaleDerivedModulePullback B S hS g))
          (smallEtaleDerivedPullbackTensorIso f).hom ≫
        Functor.whiskerRight
          (NatTrans.prod (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom
            (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom)
          (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X)) :=
  comp_law_comp_transport _ _ _ _ _ _
    (derivedPullbackTensorIso_comp (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g) (smallEtaleDerivedTensorProduct B S hS X)
      (smallEtaleDerivedTensorProduct B S hS Y) (smallEtaleDerivedTensorProduct B S hS Z))
    (derivedPullbackTensorIso_pullbackModulesCompTransport f g)

/-- Moving an `eqToIso` from one side of a square to the other does not change the comparison of
the two composites around it. -/
private lemma squareCompositeIso_eqToIso {S T S' T' : Type*} [Category S] [Category T]
    [Category S'] [Category T'] {Lg : S ⥤ S'} {Lf' : S' ⥤ T'} {Lf : S ⥤ T} {Lg' : T ⥤ T'}
    {ι : Type*} (Φ : ι → (S ⥤ T')) {a b : ι} (e : b = a) (c₁ : Lg ⋙ Lf' ≅ Φ a)
    (c₂ : Lf ⋙ Lg' ≅ Φ b) :
    Stacks.AffineProjectionFormula.squareCompositeIso c₁ (c₂ ≪≫ eqToIso (congrArg Φ e)) =
      Stacks.AffineProjectionFormula.squareCompositeIso (c₁ ≪≫ eqToIso (congrArg Φ e.symm)) c₂ := by
  subst e
  simp only [Stacks.AffineProjectionFormula.squareCompositeIso, eqToIso_refl, Iso.trans_refl]

/-- The compatibility of four comparisons around a square, after moving an `eqToIso` from one
side of the square to the other. -/
private lemma tensorComparisonCompatible_of_eqToIso {S T S' T' : Type*} [Category S]
    [Category T] [Category S'] [Category T'] {Lg : S ⥤ S'} {Lf' : S' ⥤ T'} {Lf : S ⥤ T}
    {Lg' : T ⥤ T'} {ι : Type*} (Φ : ι → (S ⥤ T')) {a b : ι} (e : b = a) (c₁ : Lg ⋙ Lf' ≅ Φ a)
    (c₂ : Lf ⋙ Lg' ≅ Φ b) (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T)
    (B' : T' × T' ⥤ T') (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
    (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B') (M N : S)
    (h : Stacks.AffineProjectionFormula.TensorComparisonCompatible
      (c₁ ≪≫ eqToIso (congrArg Φ e.symm)) c₂ A A' B B' αf αf' αg αg' M N) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible c₁
      (c₂ ≪≫ eqToIso (congrArg Φ e)) A A' B B' αf αf' αg αg' M N := by
  unfold Stacks.AffineProjectionFormula.TensorComparisonCompatible at h ⊢
  rw [squareCompositeIso_eqToIso Φ e c₁ c₂]
  exact h

variable {X' Y' : AlgebraicSpaces B S hS}

/-- **The four isomorphisms of Stacks 07A4 around a commutative square of algebraic spaces are
compatible**, across the identifications of the two composites around the square used by the
base change map `smallEtaleDerivedModuleBaseChangeMap`. This is the input of the hexagon of
Stacks 0E48 for algebraic spaces. -/
theorem tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (M N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
      (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y'))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X'))
      (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedPullbackTensorIso f').hom
      (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso g').hom
      M N := by
  refine tensorComparisonCompatible_of_eqToIso (fun f ↦ smallEtaleDerivedModulePullback B S hS f) w
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackCompIso B S hS g' f) _ _ _ _ _ _ _ _ M N ?_
  exact Stacks.Cohomology.DerivedProjectionFormula.tensorComparisonCompatible_of_comparisonSquare
    _ _ _ _ _ _ _ _
    (Stacks.Cohomology.DerivedRelativeCupProduct.comparisonCompatibleWithSquare_of_composition_laws
      _ _ _ _ _ _ _ _ (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
      (fun k ↦ (smallEtaleDerivedPullbackTensorIso k).hom) w.symm
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
      (smallEtaleDerivedModulePullbackCompIso B S hS g' f) _ rfl
      (smallEtaleDerivedPullbackTensorIso_comp f' g)
      (smallEtaleDerivedPullbackTensorIso_comp g' f)) M N

end AlgebraicGeometry.Space

end
