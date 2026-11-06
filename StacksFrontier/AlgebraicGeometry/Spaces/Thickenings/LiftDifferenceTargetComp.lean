module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferencePairHomComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf

/-!
# The difference of two morphisms of thickenings under postcomposition

Let `Z ⊆ X` be a first order thickening of algebraic spaces over a scheme `S`, let
`(e₀, c), (e₀, c') : (Z ⊆ X) ⟶ (W₀ ⊆ W)` be two morphisms of pairs agreeing on `Z`, over a
morphism `qb : W ⟶ Bas`, and let `(g₀, g) : (W₀ ⊆ W) ⟶ (W₀' ⊆ W')` be a further morphism of
pairs over `qb' : W' ⟶ Bas'`.  The difference of `c` and `c'`
([Stacks Project, Tag 0618] with Equation (0619)) is a linear map
`θ(c, c') : e₀^*Ω_{W₀/Bas} ⟶ 𝒞_{Z/X}`, and so is the difference of the postcomposed pair
`c ≫ g, c' ≫ g`.  This file proves that the second is the first precomposed with the comparison
map `c_{g₀} : g₀^*Ω_{W₀'/Bas'} ⟶ Ω_{W₀/Bas}` of [Stacks Project, Tag 04CX]:

`θ(c ≫ g, c' ≫ g) = (e₀ ≫ g₀)^* ≅ e₀^*g₀^* --e₀^*c_{g₀}--> e₀^*Ω_{W₀/Bas} --θ(c, c')--> 𝒞_{Z/X}`.

This is the target half of the compatibility of the action of [Stacks Project, Tag 0CK6] with
étale localization, [Stacks Project, Tag 0CK8]; the source half, under precomposition by a
morphism of first order thickenings, is
`AlgebraicGeometry.Space.restrictedLiftDifferenceHom_comp`.

## Main results

* `Stacks.Sheaves.ToposPullback.app_pullbackRingSheafMap_eq_of_app_eq_zero`: agreement of two
  morphisms of sheaves of rings on a kernel transports along a left exact functor.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_target_app_eq`: hypothesis (2)
  of [Stacks Project, Tag 0618] is stable under postcomposition.
* `AlgebraicGeometry.Space.eq_liftDifferenceDifferentialsHom_of_spec`: the descended difference
  is determined by its values at reduced sections.
* `AlgebraicGeometry.Space.restrictedLiftDifferenceHom_comp_target`: **the difference of the
  postcomposed pair**.

## Implementation notes

**The comorphism of the morphism of pairs is a transported comorphism.**  The map
`γ : j'^{-1}𝒪_{W'} ⟶ (g₀)_*(j^{-1}𝒪_W)` through which the comorphism of `c ≫ g` factors is
`AlgebraicGeometry.Space.restrictedSharpThroughThickening` of the pair `(g₀, g)` itself, with the
closed subspace `W₀ ⊆ W` in the role of the source thickening — that definition asks nothing of
its source but to be a closed subspace — and the factorization is the source-side composition
law `AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp` with the roles of the two
morphisms exchanged.  So no comorphism of a square is constructed here.

**Everything is compared on underlying sheaves of sets and on sections.**  The difference is
pushed forward along `g₀` as a morphism of sheaves of sets,
`AlgebraicGeometry.Space.restrictedLiftDifferenceDiffHom`; the ring operations are transported
by `CategoryTheory.Sheaf.map_hom_add`.  Statements that meet two spellings of one sheaf of sets
— the conormal module as an `𝒪_Z`-module and as an `i^{-1}𝒪_X`-module, or a direct image of
modules and the direct image of its underlying sheaf of sets — are split so that each spelling
is reached by an equation proved at variable objects, never by unification at the concrete ones.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the comparison of
  inverse and direct images along a composite.
* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8), the consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u vv uu vv' uu'

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory.Sheaf

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget RingCat.{u})]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget AddCommGrpCat.{u})]

omit [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- **Agreement on a kernel transports along a left exact functor.**  If two morphisms of sheaves
of rings `a, b : O ⟶ E` agree on every section killed by `ρ : O ⟶ O'`, then their transports
along a finite-limit-preserving functor `Φ` of sheaves of sets agree on every section killed by
the transport of `ρ`.  The kernel of `ρ` is an equalizer, which `Φ` preserves, by
`Stacks.Sheaves.ToposPullback.exists_app_pullbackModuleMap_eq` at the kernel ideal of `ρ`. -/
theorem app_pullbackRingSheafMap_eq_of_app_eq_zero
    (Φ : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [PreservesFiniteLimits Φ]
    {O O' E : Sheaf K RingCat.{u}} (ρ : O ⟶ O') (a b : O ⟶ E)
    (hab : ∀ (X : Dᵒᵖ) (x : O.obj.obj X), ρ.hom.app X x = 0 → a.hom.app X x = b.hom.app X x)
    (V : Cᵒᵖ) (y : (pullbackRingSheaf J Φ O).obj.obj V)
    (hy : (pullbackRingSheafMap J Φ ρ).hom.app V y = 0) :
    (pullbackRingSheafMap J Φ a).hom.app V y = (pullbackRingSheafMap J Φ b).hom.app V y := by
  have : PreservesFiniteProducts Φ := inferInstance
  obtain ⟨m, hm⟩ := exists_app_pullbackModuleMap_eq J Φ (SheafOfModules.kerIdeal ρ).ι ρ V
    (fun X n => RingHom.mem_ker.1 ((SheafOfModules.mem_kerIdeal ρ X n.1).1 n.2))
    (fun X => Subtype.val_injective)
    (fun X s hs => ⟨⟨s, (SheafOfModules.mem_kerIdeal ρ X s).2 (RingHom.mem_ker.2 hs)⟩, rfl⟩)
    y hy
  have hset : (moduleSheafFunctor O).map (SheafOfModules.kerIdeal ρ).ι ≫
        (sheafCompose K (forget RingCat.{u})).map a =
      (moduleSheafFunctor O).map (SheafOfModules.kerIdeal ρ).ι ≫
        (sheafCompose K (forget RingCat.{u})).map b :=
    hom_ext_sections fun X n =>
      hab X n.1 (RingHom.mem_ker.1 ((SheafOfModules.mem_kerIdeal ρ X n.1).1 n.2))
  rw [← hm]
  exact (Functor.map_comp_apply (Φ ⋙ sectionsFunctor J V) _ _ m).symm.trans
    ((congrArg (fun t => (Φ ⋙ sectionsFunctor J V).map t m) hset).trans
      (Functor.map_comp_apply (Φ ⋙ sectionsFunctor J V) _ _ m))

/-- A morphism of sheaves of modules acts on local sections through its underlying morphism of
sheaves of sets.  Stated at an abstract site and with the module a variable, where it is
definitional at no cost; the sheaf-composition instance is an implicit argument, so that it is
read off the term it is applied to rather than searched for. -/
theorem sectionsFunctor_map_moduleSheafFunctor_map' {D' : Type uu'} [Category.{vv'} D']
    {K' : GrothendieckTopology D'} {_i : K'.HasSheafCompose (forget AddCommGrpCat.{u})}
    {R : Sheaf K' RingCat.{u}} {M N : SheafOfModules.{u} R} (α : M ⟶ N) (V : D'ᵒᵖ)
    (z : M.val.obj V) :
    (sectionsFunctor K' V).map ((moduleSheafFunctor R).map α) z = (α.val.app V).hom z := rfl

omit [K.HasSheafCompose (forget RingCat.{u})]
  [K.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- A composite of three morphisms of sheaves of rings on a local section.  Stated at an abstract
site, where it is definitional at no cost. -/
theorem comp_comp_hom_app_apply {R₁ R₂ R₃ R₄ : Sheaf K RingCat.{u}} (a : R₁ ⟶ R₂) (b : R₂ ⟶ R₃)
    (c : R₃ ⟶ R₄) (V : Dᵒᵖ) (x : R₁.obj.obj V) :
    (a ≫ b ≫ c).hom.app V x = c.hom.app V (b.hom.app V (a.hom.app V x)) := rfl

omit [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- **A difference of two morphisms of sheaves of rings, transported along a functor of sheaves
of sets.**  If `δ ≫ ι + g = f` as generalized elements of a sheaf of rings `E` — that is, `δ` is a
morphism of sheaves of sets whose image under `ι` is the sectionwise difference `f - g` — then the
same holds after transport along a finite-product-preserving `Φ`, on every section of `Φ_*R`. -/
theorem map_map_app_eq_sub (Φ : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [PreservesFiniteProducts Φ]
    {R E : Sheaf K RingCat.{u}} {f g : R ⟶ E} {M : Sheaf K (Type u)}
    {δ : (sheafCompose K (forget RingCat.{u})).obj R ⟶ M}
    {ι : M ⟶ (sheafCompose K (forget RingCat.{u})).obj E}
    (hδ : δ ≫ ι + (sheafCompose K (forget RingCat.{u})).map g =
      (sheafCompose K (forget RingCat.{u})).map f)
    (V : Cᵒᵖ) (y : (pullbackRingSheaf J Φ R).obj.obj V) :
    (show (pullbackRingSheaf J Φ E).obj.obj V from (Φ.map ι).hom.app V ((Φ.map δ).hom.app V y)) =
      (pullbackRingSheafMap J Φ f).hom.app V y - (pullbackRingSheafMap J Φ g).hom.app V y := by
  have e := map_hom_add (Φ ⋙ sectionsFunctor J V) (δ ≫ ι)
    ((sheafCompose K (forget RingCat.{u})).map g) y
  rw [hδ] at e
  refine eq_sub_of_add_eq ?_
  refine Eq.trans ?_ e.symm
  exact congrArg (fun t => ringAddObj E (Φ ⋙ sectionsFunctor J V) t _)
    (Functor.map_comp_apply (Φ ⋙ sectionsFunctor J V) δ ι y).symm

/-- A functor of sheaves of sets applied to a composite of three morphisms, on a local section.
Stated with every object a variable. -/
theorem map_comp_comp_hom_app_apply {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    (P : Sheaf J₁ (Type u) ⥤ Sheaf J₂ (Type u)) {A₁ A₂ A₃ A₄ : Sheaf J₁ (Type u)}
    (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄) (V : C₂ᵒᵖ) (y : (P.obj A₁).obj.obj V) :
    (P.map (a ≫ b ≫ c)).hom.app V y =
      (P.map c).hom.app V ((P.map b).hom.app V ((P.map a).hom.app V y)) := by
  rw [P.map_comp, P.map_comp]
  rfl

/-- A composite of two morphisms of sheaves of sets on a local section. -/
theorem _root_.CategoryTheory.Sheaf.comp_hom_app_apply' {C₁ : Type*} [Category C₁]
    {J₁ : GrothendieckTopology C₁} {A₁ A₂ A₃ : Sheaf J₁ (Type u)} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃)
    (V : C₁ᵒᵖ) (x : A₁.obj.obj V) :
    (a ≫ b).hom.app V x = b.hom.app V (a.hom.app V x) := rfl

omit [K.HasSheafCompose (forget RingCat.{u})]
  [K.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- A composite of two morphisms of sheaves of rings on a local section. -/
theorem comp_hom_app_apply_ring {R₁ R₂ R₃ : Sheaf K RingCat.{u}} (a : R₁ ⟶ R₂) (b : R₂ ⟶ R₃)
    (V : Dᵒᵖ) (x : R₁.obj.obj V) :
    (a ≫ b).hom.app V x = b.hom.app V (a.hom.app V x) := rfl

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

section Uniqueness

open Stacks.Sites

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y T X : AlgebraicSpaces B S hS} (b : Y ⟶ T)
  {A : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}}
  {q : A ⟶ structureRingSheaf B S hS Y} [Sheaf.IsLocallySurjective q]
  (a : X ⟶ Y) (C : Modules B S hS X.1 X.2)
  {E : SquareZeroValues ((modulePushforward B S hS a).obj C)} (L : LiftDifferenceData q E)
  (hz : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS b).obj.obj V),
    L.toQuotientDerivation.descend ((structureSharpInverseImage B S hS b).hom.app V s) = 0)

/-- **The descended difference is determined by its values at the reduced sections.**  A linear
map `θ : a^*Ω_{Y/T} ⟶ C` whose transpose carries `d_{Y/T}(q x)` to the difference at `x`, for
every local section `x` of `A`, is the descended difference: every section of `𝒪_Y` is locally
of the form `q x`, and both sides commute with restriction. -/
theorem eq_liftDifferenceDifferentialsHom_of_spec
    (θ : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶ C)
    (hθ : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : A.obj.obj V),
      ((modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS b) C
          θ).val.app V ((universalDerivation B S hS b).d (q.hom.app V x)) = L.diff x) :
    θ = liftDifferenceDifferentialsHom B S hS b a C L hz := by
  refine eq_descendedDifferentialsHom_of_spec B S hS b a C L.toQuotientDerivation hz θ ?_
  intro V t
  refine ((modulePushforward B S hS a).obj C).isSheaf.isSeparated V.unop
    (Presheaf.imageSieve q.hom t) (Presheaf.imageSieve_mem (SmallEtale.topology B S hS Y.1)
      q.hom t) _ _ ?_
  intro Y' f hf
  obtain ⟨x, hx⟩ := hf
  have n1 := PresheafOfModules.naturality_apply
    ((modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS b) C θ).val f.op
    ((universalDerivation B S hS b).d t)
  have n2 := (universalDerivation B S hS b).d_map f.op t
  have n3 := QuotientDerivation.descend_map L.toQuotientDerivation f.op t
  show ((modulePushforward B S hS a).obj C).val.map f.op _ =
    ((modulePushforward B S hS a).obj C).val.map f.op _
  refine n1.symm.trans (Eq.trans ?_ n3)
  refine (congrArg (((modulePullbackAdjunction B S hS a).homEquiv _ C θ).val.app
    (Opposite.op Y')) n2.symm).trans ?_
  refine Eq.trans ?_ ((QuotientDerivation.descend_app L.toQuotientDerivation x).symm.trans
    (congrArg L.toQuotientDerivation.descend hx))
  have hd := congrArg (universalDerivation B S hS b).d hx
  refine (congrArg (((modulePullbackAdjunction B S hS a).homEquiv _ C θ).val.app
    (Opposite.op Y')) hd.symm).trans ?_
  exact hθ _ x

end Uniqueness

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W W' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (W₀' : ClosedSubspaces B S hS W'.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (g : W ⟶ W')
  (g₀ : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS))
  (hg : subspaceInclusion B S hS W W₀ ≫ g = g₀ ≫ subspaceInclusion B S hS W' W₀')

/-- The comorphism `γ` of `(g₀, g)` followed by the transport of the reduction `j^♯` is the
reduction `j'^♯` followed by the structure sharp of `g₀`, on sections. -/
private theorem pullbackRingSheafMap_structureSharp_restrictedSharp_apply
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W' W₀')).obj.obj V) :
    (pullbackRingSheafMap
      (SmallEtale.topology B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)
      (smallToposMorphismTypeU B S hS g₀).pushforward
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))).hom.app V
        ((restrictedSharpThroughThickening B S hS W₀ W₀' g g₀ hg).hom.app V x) =
      (structureSharp B S hS g₀).hom.app V
        ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W' W₀')).hom.app V x) :=
  ConcreteCategory.congr_hom (congrArg (fun n => n.hom.app V)
    (restrictedSharpThroughThickening_comp_reduction_structureSharp B S hS W₀ W₀' g₀ g hg)) x

include hg in
/-- **Hypothesis (2) of [Stacks Project, Tag 0618] is stable under postcomposition by a morphism
of pairs.** -/
theorem restrictedSharpThroughThickening_comp_target_app_eq (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₂ : subspaceInclusion B S hS X Z ≫ c ≫ g =
      (e₀ ≫ g₀) ≫ subspaceInclusion B S hS W' W₀')
    (h₂' : subspaceInclusion B S hS X Z ≫ c' ≫ g =
      (e₀ ≫ g₀) ≫ subspaceInclusion B S hS W' W₀')
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x)
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W' W₀')).obj.obj V)
    (hx : (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W' W₀')).hom.app V x = 0) :
    (restrictedSharpThroughThickening B S hS Z W₀' (c ≫ g) (e₀ ≫ g₀) h₂).hom.app V x =
      (restrictedSharpThroughThickening B S hS Z W₀' (c' ≫ g) (e₀ ≫ g₀) h₂').hom.app V x := by
  rw [restrictedSharpThroughThickening_comp B S hS W₀ Z c e₀ h W₀' g g₀ hg h₂,
    restrictedSharpThroughThickening_comp B S hS W₀ Z c' e₀ h' W₀' g g₀ hg h₂']
  have := preservesFiniteLimits_smallToposMorphismTypeU_pushforward B S hS g₀
  exact congrArg (fun t => (pushforwardRingSheafCompHom B S hS e₀ g₀
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V t)
    (app_pullbackRingSheafMap_eq_of_app_eq_zero (smallToposMorphismTypeU B S hS g₀).pushforward
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)
      (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h') hker V
      ((restrictedSharpThroughThickening B S hS W₀ W₀' g g₀ hg).hom.app V x)
      (by rw [pullbackRingSheafMap_structureSharp_restrictedSharp_apply B S hS W₀ W₀' g g₀ hg V x,
        hx]; exact map_zero _))

/-- `AlgebraicGeometry.Space.pushforwardRingSheafCompHom_hom_app` with the underlying sheaf of
sets of the sheaf of rings spelled as the underlying sheaf of sets of its unit module, the
spelling in which the comparison meets morphisms of sheaves of modules into the unit. -/
theorem pushforwardRingSheafCompHom_hom_app_unit {V₁ V₂ V₃ : AlgebraicSpaces B S hS}
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u})
    (V : (SmallEtale B S hS V₃.1)ᵒᵖ)
    (z : (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS g).pushforward
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
          (smallToposMorphismTypeU B S hS f).pushforward O)).obj.obj V) :
    (pushforwardRingSheafCompHom B S hS f g O).hom.app V z =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} O).obj (SheafOfModules.unit O))).hom.app V z :=
  pushforwardRingSheafCompHom_hom_app B S hS f g O V z

variable (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- **The inclusion of the ideal of values against the comparison of iterated direct images.**
The comparison `(g₀)_*(e₀)_*𝒞_{Z/X} ⟶ (e₀ ≫ g₀)_*𝒞_{Z/X}` of [Stacks Project, Tag 03LU],
followed by the inclusion of the ideal of values for `e₀ ≫ g₀`, is the iterated direct image of
the inclusion of the conormal module followed by the comparison of iterated direct images of
`i^{-1}𝒪_X`: both are the geometric comparison of [Stacks Project, Tag 03G2], part (3), and
the square is its naturality. -/
theorem ι_modulePushforwardCompIso_hom_app
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m : ((modulePushforward B S hS g₀).obj
      ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z))).val.obj V) :
    (restrictedSquareZeroValues B S hS Z W₀' (e₀ ≫ g₀) hZ).ι
        (((modulePushforwardCompIso B S hS e₀ g₀).hom.app (conormalModule B S hS X Z)).val.app
          V m) =
      (pushforwardRingSheafCompHom B S hS e₀ g₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V
        (((smallToposMorphismTypeU B S hS g₀).pushforward.map
          ((smallToposMorphismTypeU B S hS e₀).pushforward.map
            ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).map
              (conormalInverseImageι B S hS Z hZ)))).hom.app V m) := by
  have t1 := restrictedSquareZeroValues_ι_eq_set B S hS Z W₀' hZ (e₀ ≫ g₀)
    (((modulePushforwardCompIso B S hS e₀ g₀).hom.app (conormalModule B S hS X Z)).val.app V m)
  have s2 := modulePushforwardCompIso_hom_app_val_app B S hS e₀ g₀ (conormalModule B S hS X Z)
    V m
  have t2 := congrArg (((smallToposMorphismTypeU B S hS (e₀ ≫ g₀)).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).map (conormalInverseImageι B S hS Z hZ))).hom.app V)
    s2
  have tb := congrArg (((smallToposMorphismTypeU B S hS (e₀ ≫ g₀)).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).map (conormalInverseImageι B S hS Z hZ))).hom.app V)
    (smallToposMorphismTypeU_comp_app_restrictScalars B S hS Z e₀ g₀
      (conormalModule B S hS X Z) V m)
  have t3 := Sheaf.natTrans_comp_naturality_apply (smallToposMorphismTypeU B S hS e₀).pushforward
    (smallToposMorphismTypeU B S hS g₀).pushforward
    (smallToposMorphismTypeU B S hS (e₀ ≫ g₀)).pushforward
    (smallToposMorphismTypeU_comp B S hS e₀ g₀).hom _
    ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).map (conormalInverseImageι B S hS Z hZ)) V m
  have t5 := pushforwardRingSheafCompHom_hom_app_unit B S hS e₀ g₀
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) V
    (((smallToposMorphismTypeU B S hS g₀).pushforward.map
      ((smallToposMorphismTypeU B S hS e₀).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).map (conormalInverseImageι B S hS Z hZ)))).hom.app
      V m)
  exact t1.trans (t2.trans (tb.trans (t3.trans t5.symm)))

section Diff

variable (c c' : X ⟶ W)
  (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
  (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
  (hker : ∀ (V : (SmallEtale B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V),
    (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
        (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x)

/-- **The difference of two morphisms agreeing on the thickening, as a morphism of sheaves of
sets** `j^{-1}𝒪_W ⟶ (e₀)_*𝒞_{Z/X}` on the small étale site of `W₀`: the sectionwise difference
of `AlgebraicGeometry.Space.restrictedLiftDifferenceData`, which commutes with restriction.  It
is the form in which the difference can be pushed forward along a further morphism. -/
def restrictedLiftDifferenceDiffHom :
    (sheafCompose (SmallEtale.topology B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).obj
          ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)) :=
  Sheaf.unaryOpHom
    (fun _ y => (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).diff y)
    (fun g y => ((restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).diff_map
      g y).symm)

/-- `AlgebraicGeometry.Space.restrictedLiftDifferenceDiffHom` on sections. -/
theorem sectionsFunctor_map_restrictedLiftDifferenceDiffHom
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (y : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj V) :
    (Sheaf.sectionsFunctor _ V).map
        (restrictedLiftDifferenceDiffHom B S hS Z W₀ e₀ hZ c c' h h' hker) y =
      (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).diff y :=
  rfl

/-- The difference, followed by the inclusion of the ideal of values, plus the second transported
comorphism, is the first transported comorphism, as morphisms of sheaves of sets. -/
theorem restrictedLiftDifferenceDiffHom_comp_ι_add :
    @CategoryStruct.comp _ _ _
        ((smallToposMorphismTypeU B S hS e₀).pushforward.obj
          ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj ((SheafOfModules.restrictScalars
              (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))).obj
                (conormalModule B S hS X Z))))
        ((sheafCompose (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀))
        (restrictedLiftDifferenceDiffHom B S hS Z W₀ e₀ hZ c c' h h' hker)
        ((smallToposMorphismTypeU B S hS e₀).pushforward.map
          ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z))).map (conormalInverseImageι B S hS Z hZ))) +
      (sheafCompose (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
        (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h') =
    (sheafCompose (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h) := by
  refine Sheaf.hom_ext_sections fun V y => ?_
  rw [Sheaf.sectionsFunctor_map_hom_add]
  have hd := (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).ι_diff y
  exact (congrArg (· + (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V y)
    hd).trans (sub_add_cancel _ _)

variable {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas) (hcc : c ≫ qb = c' ≫ qb)

/-- **The difference of two morphisms is the descended derivation after the reduction**, as
morphisms of sheaves of sets on the small étale site of `W₀`: the reduction
`j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`, the universal derivation `d_{W₀/Bas}` and the transpose of the linear
map `θ(c, c')` compose to the sectionwise difference.  This is Equation (0619) at the
descended difference, `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_spec`. -/
theorem reduction_comp_universalDerivationHom_comp_homEquiv :
    (sheafCompose (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)) ≫
      universalDerivationHom B S hS (subspaceInclusion B S hS W W₀ ≫ qb) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map
          ((modulePullbackAdjunction B S hS e₀).homEquiv _ _
            (restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hker hcc)) =
    restrictedLiftDifferenceDiffHom B S hS Z W₀ e₀ hZ c c' h h' hker := by
  refine Sheaf.hom_ext_sections fun V y => ?_
  have hz : (Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1) V).map
        (universalDerivationHom B S hS (subspaceInclusion B S hS W W₀ ≫ qb))
        ((Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1) V).map
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).map
            (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))) y) =
      (universalDerivation B S hS (subspaceInclusion B S hS W W₀ ≫ qb)).d
        ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V y) :=
    rfl
  refine (Functor.map_comp_apply (Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1) V) _ _ y).trans ?_
  refine (Functor.map_comp_apply (Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1) V) _ _ _).trans ?_
  rw [hz]
  refine (sectionsFunctor_map_moduleSheafFunctor_map' _ V _).trans ?_
  refine Eq.trans ?_ (sectionsFunctor_map_restrictedLiftDifferenceDiffHom B S hS Z W₀ e₀ hZ c c'
    h h' hker V y).symm
  rw [restrictedLiftDifferenceHom_eq]
  exact liftDifferenceDifferentialsHom_spec B S hS (subspaceInclusion B S hS W W₀ ≫ qb) e₀
    (conormalModule B S hS X Z)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c c' h h' hker qb hcc) y

end Diff

section Postcomposition

variable (c c' : X ⟶ W)
  (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
  (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
  (hker : ∀ (V : (SmallEtale B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V),
    (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
        (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x)
  (h₂ : subspaceInclusion B S hS X Z ≫ c ≫ g =
    (e₀ ≫ g₀) ≫ subspaceInclusion B S hS W' W₀')
  (h₂' : subspaceInclusion B S hS X Z ≫ c' ≫ g =
    (e₀ ≫ g₀) ≫ subspaceInclusion B S hS W' W₀')

include hg in
/-- **The difference of the postcomposed pair is the pushed-forward difference**, read in the
ideal of values on the small étale site of `W₀'`: the difference of `c` and `c'`, pushed forward
along `g₀`, evaluated at the image of a section under the comorphism `γ` of `(g₀, g)` and read
through the comparison of iterated direct images, is the difference of the two transported
comorphisms of `c ≫ g` and `c' ≫ g`. -/
theorem ι_modulePushforwardCompIso_pushforward_diff
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W' W₀')).obj.obj V) :
    (restrictedSquareZeroValues B S hS Z W₀' (e₀ ≫ g₀) hZ).ι
        (((modulePushforwardCompIso B S hS e₀ g₀).hom.app (conormalModule B S hS X Z)).val.app V
          (((smallToposMorphismTypeU B S hS g₀).pushforward.map
            (restrictedLiftDifferenceDiffHom B S hS Z W₀ e₀ hZ c c' h h' hker)).hom.app V
            ((restrictedSharpThroughThickening B S hS W₀ W₀' g g₀ hg).hom.app V x))) =
      (restrictedSharpThroughThickening B S hS Z W₀' (c ≫ g) (e₀ ≫ g₀) h₂).hom.app V x -
        (restrictedSharpThroughThickening B S hS Z W₀' (c' ≫ g) (e₀ ≫ g₀) h₂').hom.app V x := by
  refine (ι_modulePushforwardCompIso_hom_app B S hS Z W₀ W₀' e₀ g₀ hZ V _).trans ?_
  have hsub := map_map_app_eq_sub (smallToposMorphismTypeU B S hS g₀).pushforward
    (restrictedLiftDifferenceDiffHom_comp_ι_add B S hS Z W₀ e₀ hZ c c' h h' hker) V
    ((restrictedSharpThroughThickening B S hS W₀ W₀' g g₀ hg).hom.app V x)
  have hc := congrArg (fun t => t.hom.app V x)
    (restrictedSharpThroughThickening_comp B S hS W₀ Z c e₀ h W₀' g g₀ hg h₂)
  have hc' := congrArg (fun t => t.hom.app V x)
    (restrictedSharpThroughThickening_comp B S hS W₀ Z c' e₀ h' W₀' g g₀ hg h₂')
  refine Eq.trans ?_ (congrArg₂ (· - ·) hc hc').symm
  refine Eq.trans (congrArg (fun t => (pushforwardRingSheafCompHom B S hS e₀ g₀
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V t) hsub) ?_
  exact map_sub _ _ _

variable {Bas Bas' : AlgebraicSpaces B S hS} (qb : W ⟶ Bas) (qb' : W' ⟶ Bas')
  (hcc : c ≫ qb = c' ≫ qb)
  (cmap : (modulePullback B S hS g₀).obj
      (sheafOfDifferentials B S hS (subspaceInclusion B S hS W' W₀' ≫ qb')) ⟶
    sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb))
  (hcmap : IsSheafOfDifferentialsMap B S hS g₀ (subspaceInclusion B S hS W' W₀' ≫ qb')
    (subspaceInclusion B S hS W W₀ ≫ qb) cmap)

include hg hcmap in
/-- **The transpose of the restricted difference, at the universal differential of a reduced
section.**  The transpose along `g₀^* ⊣ g₀_*` of the comparison map `c_{g₀}` of
[Stacks Project, Tag 04CX], followed by the direct image of the transpose of `θ(c, c')` and the
comparison of iterated direct images, carries `d_{W₀'/Bas'}(j'^♯ x)` to the pushed-forward
difference evaluated at the image of `x` under the comorphism `γ` of `(g₀, g)`. -/
theorem homEquiv_comp_val_app_universalDerivation_reduction
    (V : (SmallEtale B S hS (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W' W₀')).obj.obj V) :
    (((modulePullbackAdjunction B S hS g₀).homEquiv _ _ cmap ≫
        (modulePushforward B S hS g₀).map ((modulePullbackAdjunction B S hS e₀).homEquiv _ _
          (restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hker hcc)) ≫
        (modulePushforwardCompIso B S hS e₀ g₀).hom.app (conormalModule B S hS X Z)).val.app V)
        ((universalDerivation B S hS (subspaceInclusion B S hS W' W₀' ≫ qb')).d
          ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W' W₀')).hom.app V x)) =
      ((modulePushforwardCompIso B S hS e₀ g₀).hom.app (conormalModule B S hS X Z)).val.app V
        (((smallToposMorphismTypeU B S hS g₀).pushforward.map
          (restrictedLiftDifferenceDiffHom B S hS Z W₀ e₀ hZ c c' h h' hker)).hom.app V
          ((restrictedSharpThroughThickening B S hS W₀ W₀' g g₀ hg).hom.app V x)) := by
  have s2 := hcmap V ((structureSharpRingInverseImage B S hS
    (subspaceInclusion B S hS W' W₀')).hom.app V x)
  have s6 := Sheaf.hom_congr_app_apply (congrArg (smallToposMorphismTypeU B S hS g₀).pushforward.map
    (reduction_comp_universalDerivationHom_comp_homEquiv B S hS Z W₀ e₀ hZ c c' h h' hker qb hcc))
    V ((restrictedSharpThroughThickening B S hS W₀ W₀' g g₀ hg).hom.app V x)
  replace s6 := (map_comp_comp_hom_app_apply (smallToposMorphismTypeU B S hS g₀).pushforward
    _ _ _ V _).symm.trans s6
  refine (modules_comp_val_app B S hS _ _ V _).trans ?_
  refine (modules_comp_val_app B S hS _ _ V _).trans ?_
  refine congrArg (((modulePushforwardCompIso B S hS e₀ g₀).hom.app
    (conormalModule B S hS X Z)).val.app V) ?_
  refine Eq.trans ?_ s6
  refine (modulePushforward_map_val_app_typeU B S hS g₀ _ V _).trans ?_
  refine congrArg (((smallToposMorphismTypeU B S hS g₀).pushforward.map
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).map
      ((modulePullbackAdjunction B S hS e₀).homEquiv _ _
        (restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hker hcc)))).hom.app V) ?_
  refine s2.trans ?_
  refine (Sheaf.comp_hom_app_apply' _ _ V _).trans ?_
  refine congrArg (((smallToposMorphismTypeU B S hS g₀).pushforward.map
    (universalDerivationHom B S hS (subspaceInclusion B S hS W W₀ ≫ qb))).hom.app V) ?_
  exact (pullbackRingSheafMap_structureSharp_restrictedSharp_apply B S hS W₀ W₀' g g₀ hg V
    x).symm

include hg hcmap in
/-- **[Stacks Project, Tag 0618] under postcomposition by a morphism of pairs.**  Let
`(g₀, g) : (W₀ ⊆ W) ⟶ (W₀' ⊆ W')` be a morphism of pairs over a morphism of bases, with comparison
map `c_{g₀} : g₀^*Ω_{W₀'/Bas'} ⟶ Ω_{W₀/Bas}` of [Stacks Project, Tag 04CX], and let `c, c'` be
two morphisms out of a first order thickening `Z ⊆ X` agreeing on `Z`.  Then the difference of
`c ≫ g` and `c' ≫ g` is the difference of `c` and `c'` precomposed with `e₀^*c_{g₀}`, read
through the comparison `(e₀ ≫ g₀)^* ≅ e₀^*g₀^*` of [Stacks Project, Tag 03LU]. -/
theorem restrictedLiftDifferenceHom_comp_target
    (hker₂ : ∀ (V : (SmallEtale B S hS
        (⟨W₀'.1.toFunctor, W₀'.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W' W₀')).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W' W₀')).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀' (c ≫ g) (e₀ ≫ g₀) h₂).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀' (c' ≫ g) (e₀ ≫ g₀) h₂').hom.app V x)
    (hcc₂ : (c ≫ g) ≫ qb' = (c' ≫ g) ≫ qb') :
    restrictedLiftDifferenceHom B S hS Z W₀' hZ (e₀ ≫ g₀) qb' (c ≫ g) (c' ≫ g) h₂ h₂' hker₂
        hcc₂ =
      (modulePullbackCompIso B S hS e₀ g₀).inv.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS W' W₀' ≫ qb')) ≫
        (modulePullback B S hS e₀).map cmap ≫
          restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hker hcc := by
  rw [restrictedLiftDifferenceHom_eq]
  refine (eq_liftDifferenceDifferentialsHom_of_spec B S hS
    (subspaceInclusion B S hS W' W₀' ≫ qb') (e₀ ≫ g₀) (conormalModule B S hS X Z)
    (restrictedLiftDifferenceData B S hS Z W₀' (e₀ ≫ g₀) hZ (c ≫ g) (c' ≫ g) h₂ h₂' hker₂)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀' hZ (e₀ ≫ g₀) (c ≫ g) (c' ≫ g) h₂ h₂' hker₂ qb' hcc₂)
    ((modulePullbackCompIso B S hS e₀ g₀).inv.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS W' W₀' ≫ qb')) ≫
        (modulePullback B S hS e₀).map cmap ≫
          restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hker hcc) ?_).symm
  intro V x
  have hE : (modulePullbackAdjunction B S hS (e₀ ≫ g₀)).homEquiv _ _
      ((modulePullbackCompIso B S hS e₀ g₀).inv.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS W' W₀' ≫ qb')) ≫
        (modulePullback B S hS e₀).map cmap ≫
          restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hker hcc) =
      (modulePullbackAdjunction B S hS g₀).homEquiv _ _ cmap ≫
        (modulePushforward B S hS g₀).map ((modulePullbackAdjunction B S hS e₀).homEquiv _ _
          (restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hker hcc)) ≫
        (modulePushforwardCompIso B S hS e₀ g₀).hom.app (conormalModule B S hS X Z) := by
    rw [homEquiv_modulePullbackCompIso_inv_app_comp, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right, Category.assoc]
  refine (congrArg (fun T => T.val.app V
    ((universalDerivation B S hS (subspaceInclusion B S hS W' W₀' ≫ qb')).d
      ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W' W₀')).hom.app V x)))
    hE).trans ?_
  refine (homEquiv_comp_val_app_universalDerivation_reduction B S hS Z W₀ W₀' e₀ g g₀ hg hZ c c'
    h h' hker qb qb' hcc cmap hcmap V x).trans ?_
  refine (restrictedSquareZeroValues B S hS Z W₀' (e₀ ≫ g₀) hZ).ι_injective ?_
  refine (ι_modulePushforwardCompIso_pushforward_diff B S hS Z W₀ W₀' e₀ g g₀ hg hZ c c' h h'
    hker h₂ h₂' V x).trans ?_
  exact (restrictedSquareZeroValues_ι_restrictedSharpDiff B S hS Z W₀' (e₀ ≫ g₀) hZ (c ≫ g)
    (c' ≫ g) h₂ h₂' x).symm

end Postcomposition

end AlgebraicGeometry.Space

end
