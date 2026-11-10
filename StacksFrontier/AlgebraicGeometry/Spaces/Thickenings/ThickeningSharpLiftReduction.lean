module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData

/-!
# A solution of the lifting problem moved by a derivation has the same reduction

Let `Z ⊆ X` be a first order thickening of algebraic spaces over a scheme `S` with inclusion
`i : Z ⟶ X`, let `W₀ ⊆ W` be a closed subspace with inclusion `j : W₀ ⟶ W` and let
`e₀ : Z ⟶ W₀`.  A solution of the lifting problem is a morphism of sheaves of rings

`g : j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`

and the *reduction* of such a solution is its composite with the direct image along `e₀` of
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`, a morphism `j^{-1}𝒪_W ⟶ (e₀)_*𝒪_Z`.  For the transported comorphism of
a morphism `c : X ⟶ W` with `i ≫ c = e₀ ≫ j` the reduction is `j^♯` followed by the comorphism
of `e₀`, by
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_reduction_structureSharp`: it
records that `c` restricts to `e₀ ≫ j` on the thickening.

This file proves that **moving a solution by a derivation does not change its reduction.**  The
difference of the two solutions takes its values in the ideal `(e₀)_*𝒞_{Z/X}`, and the conormal
module is exactly the kernel of `i^♯`; so the difference is killed by the reduction.  For the
pair of solutions attached to an `𝒪_X`-linear map by
`AlgebraicGeometry.Space.liftDifferenceDataOfHom` this says that the second solution still
restricts to `e₀ ≫ j` on the thickening, which is what a morphism of algebraic spaces built from
it has to satisfy to be a lift of `e₀`.

## Main results

* `Stacks.Sheaves.ToposPullback.app_pullbackRingSheafMap_pullbackModuleMap_eq_zero`: **the
  transport of an ideal of `O` is killed by the transport of a morphism killing that ideal.**
  This is the companion of
  `Stacks.Sheaves.ToposPullback.exists_app_pullbackModuleMap_eq`, which is the other half of the
  exactness of a transported ideal sequence.
* `Stacks.Sites.derivationActionHom_comp_eq`: **the lift modified by a derivation has the same
  composite with any morphism killing the ideal of values.**
* `AlgebraicGeometry.Space.app_reduction_restrictedSquareZeroValues_ι_eq_zero`: **the reduction
  kills the ideal of values**, the conormal module being the kernel of `i^♯`.
* `AlgebraicGeometry.Space.liftDifferenceDataOfHom_g_comp_eq`: **the second solution of the pair
  attached to an `𝒪_X`-linear map has the same reduction as the first**, so it restricts to
  `e₀ ≫ j` on the thickening.

## Implementation notes

The transported-ideal lemma is proved exactly as the first step of
`Stacks.Sheaves.ToposPullback.exists_app_pullbackModuleMap_eq`: the composite of the inclusion
with the morphism is the zero generalized element, and applying the transport followed by the
sections functor to that equation of morphisms of sheaves of sets is the statement.  It is
stated here rather than beside that lemma so that no file of the module-sheaf layer has to
change.

**No `@[stacks]` attribute is placed.**  What is proved is a property of the correspondence of
[Stacks Project, Tag 0618] internal to this development.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2), inverse images of
  sheaves of modules.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the correspondence
  between lifts and linear maps.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this step is an
  input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u uu uu' vv vv' ww ww'

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory.Sheaf

variable {Cc : Type uu} [Category.{vv} Cc] {Dd : Type uu'} [Category.{vv'} Dd]
  (J : GrothendieckTopology Cc) {K : GrothendieckTopology Dd}
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {O O' : Sheaf K RingCat.{ww'}} {G : SheafOfModules.{ww'} O}

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})] in
/-- **The transport of an ideal of `O` is killed by the transport of a morphism of sheaves of
rings which kills that ideal.**

The composite of the inclusion with the morphism is the zero generalized element of sheaves of
sets, and both the transport of the inclusion and the transport of the morphism are the functor
`Φ` followed by the sections functor applied to the corresponding morphism of sheaves of sets;
so the composite is the image of the zero generalized element, which is zero.

This is the other half of the exactness of a transported ideal sequence from
`Stacks.Sheaves.ToposPullback.exists_app_pullbackModuleMap_eq`, which produces the preimage of a
section killed by the transport. -/
theorem app_pullbackRingSheafMap_pullbackModuleMap_eq_zero
    (φ : G ⟶ SheafOfModules.unit O) (ρ : O ⟶ O') (V : Ccᵒᵖ)
    (hzero : ∀ (Y : Ddᵒᵖ) (n : G.val.obj Y),
      ρ.hom.app Y (show ToType (O.obj.obj Y) from (φ.val.app Y).hom n) = 0)
    (m : (pullbackModuleObj J Φ O G).val.obj V) :
    (pullbackRingSheafMap J Φ ρ).hom.app V
        (show ToType ((pullbackRingSheaf J Φ O).obj.obj V) from
          ((pullbackModuleMap J Φ O φ).val.app V).hom m) = 0 := by
  set g := (moduleSheafFunctor O).map φ with hg
  have h : g ≫ (sheafCompose K (CategoryTheory.forget RingCat.{ww'})).map ρ =
      g ≫ (0 : Sheaf.ringSheaf O ⟶ Sheaf.ringSheaf O') := by
    refine Sheaf.hom_ext_sections fun Y n ↦ ?_
    have e1 : (Sheaf.sectionsFunctor K Y).map
          (g ≫ (sheafCompose K (CategoryTheory.forget RingCat.{ww'})).map ρ) n =
        ρ.hom.app Y (show ToType (O.obj.obj Y) from (φ.val.app Y).hom n) :=
      (Sheaf.sectionsFunctor K Y).map_comp_apply _ _ n
    have e2 : (Sheaf.sectionsFunctor K Y).map
          (g ≫ (0 : Sheaf.ringSheaf O ⟶ Sheaf.ringSheaf O')) n = 0 :=
      ((Sheaf.sectionsFunctor K Y).map_comp_apply g
          (0 : Sheaf.ringSheaf O ⟶ Sheaf.ringSheaf O') n).trans
        (Sheaf.sectionsFunctor_map_hom_ringZero Y _)
    rw [e1, e2, hzero Y n]
    rfl
  have hval : (pullbackRingSheafMap J Φ ρ).hom.app V
      (show ToType ((pullbackRingSheaf J Φ O).obj.obj V) from
        ((pullbackModuleMap J Φ O φ).val.app V).hom m) =
      (Φ ⋙ Sheaf.sectionsFunctor J V).map
        (g ≫ (sheafCompose K (CategoryTheory.forget RingCat.{ww'})).map ρ) m :=
    ((Φ ⋙ Sheaf.sectionsFunctor J V).map_comp_apply g
      ((sheafCompose K (CategoryTheory.forget RingCat.{ww'})).map ρ) m).symm
  rw [hval, h]
  exact ((Φ ⋙ Sheaf.sectionsFunctor J V).map_comp_apply g
      (0 : Sheaf.ringSheaf O ⟶ Sheaf.ringSheaf O') m).trans
    (Sheaf.map_hom_ringZero (Φ ⋙ Sheaf.sectionsFunctor J V) _)

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sites

variable {Cc : Type uu} [Category.{vv} Cc] {J : GrothendieckTopology Cc}
  {A O : Sheaf J RingCat.{u}} {q : A ⟶ O} {M : SheafOfModules.{u} O}
  (E : SquareZeroValues M) (f : A ⟶ E.ambient)
  (D : ∀ V : Ccᵒᵖ, O.obj.obj V →+ M.val.obj V)
  (hmul : ∀ (V : Ccᵒᵖ) (s t : O.obj.obj V), D V (s * t) = s • D V t + t • D V s)
  (hmap : ∀ (V W : Ccᵒᵖ) (h : V ⟶ W) (s : O.obj.obj V),
    D W (O.obj.map h s) = M.val.map h (D V s))
  (ι_smul : ∀ (V : Ccᵒᵖ) (x : A.obj.obj V) (m : M.val.obj V),
    E.ι (q.hom.app V x • m) = f.hom.app V x * E.ι m)

/-- **The lift modified by a derivation has the same composite with any morphism of sheaves of
rings killing the ideal of values.**  The two differ sectionwise by a section of the ideal, and
an additive map killing the ideal kills it. -/
theorem derivationActionHom_comp_eq {Aa : Sheaf J RingCat.{u}} (ρ : E.ambient ⟶ Aa)
    (hρ : ∀ (V : Ccᵒᵖ) (m : M.val.obj V), ρ.hom.app V (E.ι m) = 0) :
    derivationActionHom E f D hmul hmap ι_smul ≫ ρ = f ≫ ρ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ RingCat.hom_ext (RingHom.ext fun x ↦ by
    change ρ.hom.app V (f.hom.app V x - E.ι (D V (q.hom.app V x))) = ρ.hom.app V (f.hom.app V x)
    rw [map_sub, hρ V _, sub_zero])))

end Stacks.Sites

namespace AlgebraicGeometry.Space

open Stacks.Sites

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- **The reduction kills the ideal of values.**  The ideal of values is the direct image along
`e₀` of the conormal module, included into `i^{-1}𝒪_X`, and the conormal module is exactly the
kernel of `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`
(`AlgebraicGeometry.Space.app_conormalInverseImageι_eq_zero`); the transport along the direct
image preserves that, by
`Stacks.Sheaves.ToposPullback.app_pullbackRingSheafMap_pullbackModuleMap_eq_zero`. -/
theorem app_reduction_restrictedSquareZeroValues_ι_eq_zero
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m : ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)).val.obj V) :
    (pullbackRingSheafMap
          (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).hom.app V
        ((restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι m) = 0 :=
  app_pullbackRingSheafMap_pullbackModuleMap_eq_zero
    (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
    (smallToposMorphismTypeU B S hS e₀).pushforward
    (conormalInverseImageι B S hS Z hZ)
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) V
    (app_conormalInverseImageι_eq_zero B S hS Z hZ) m

variable {Y T : AlgebraicSpaces B S hS} (b : Y ⟶ T)
  {A : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}}
  {q : A ⟶ structureRingSheaf B S hS Y} [Sheaf.IsLocallySurjective q]
  {X' : AlgebraicSpaces B S hS} (aa : X' ⟶ Y) (Cm : Modules B S hS X'.1 X'.2)
  {E : SquareZeroValues ((modulePushforward B S hS aa).obj Cm)}
  (f : A ⟶ E.ambient)
  (ι_smul : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : A.obj.obj V)
    (m : ((modulePushforward B S hS aa).obj Cm).val.obj V),
    E.ι (@HSMul.hSMul
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj V)
      _ _ _ (q.hom.app V x) m) = f.hom.app V x * E.ι m)
  (θ : (modulePullback B S hS aa).obj (sheafOfDifferentials B S hS b) ⟶ Cm)

omit [Sheaf.IsLocallySurjective q] in
/-- **The second solution of the pair attached to an `𝒪_X`-linear map has the same composite
with a morphism killing the ideal of values as the first.**  This is
`Stacks.Sites.derivationActionHom_comp_eq` at the pair
`AlgebraicGeometry.Space.liftDifferenceDataOfHom`, so that a consumer never has to see the
underlying `Stacks.Sites.derivationActionHom`. -/
theorem liftDifferenceDataOfHom_g_comp_eq
    {Aa : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}} (ρ : E.ambient ⟶ Aa)
    (hρ : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ)
      (m : ((modulePushforward B S hS aa).obj Cm).val.obj V), ρ.hom.app V (E.ι m) = 0) :
    (liftDifferenceDataOfHom B S hS b aa Cm f ι_smul θ).g ≫ ρ = f ≫ ρ :=
  derivationActionHom_comp_eq E f (derivationFamilyOfHom B S hS b aa Cm θ)
    (derivationFamilyOfHom_mul B S hS b aa Cm θ) (derivationFamilyOfHom_map B S hS b aa Cm θ)
    ι_smul ρ hρ

end AlgebraicGeometry.Space

end
