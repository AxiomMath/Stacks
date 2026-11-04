module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOne
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceShrinkSiteBridge

/-!
# The source square of clause (1) of Stacks 0D2Z at a scheme point of `U(ψ)`

Clause (1) of [Stacks, Tag 0D2Z] on the algebraic space `U(ψ)` is descended from the identity
`w^*(ψ_P leg) ≫ χ_w = w^*(ψ leg)` at the scheme points `w : W ⟶ U(ψ)`
(`…InvertibleTwistingRestriction.clauseOneSections_thetaOfFamily`).  The chart map `χ_w` begins
with the identification `…InvertibleTwistingRestriction.chartSourceIso` of its source, and the
first step of the identity is the **source square**: `w^*` of the `ψ_P` leg followed by that
identification is the source identification
`…InvertibleTwistingRestriction.clauseOnePointSourceIso` followed by the module attached to the
inverse image along the section `c_w` of `ψ` of Tag 01NR.

This file proves that square at variables
(`…InvertibleTwistingRestriction.clauseOneSourceShaped_square`), from the naturality of the
comparison `a^*b^* ≅ a'^*b'^*` of two factorisations
(`…InvertibleTwistingRestriction.modulePullbackCompTransportIso_hom_naturality`), the base change
identification of Stacks 084D carrying `ψ` to `ψ` of Tag 01NR
(`…modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom`)
and the naturality of Stacks 03DX (2), and instantiates it at the source identification of the
chart map (`…InvertibleTwistingRestriction.clauseOneSource_square_of_chartSourceIso`).

## Main results

* `…InvertibleTwistingRestriction.modulePullbackCompTransportIso_hom_naturality`: the comparison
  of two factorisations is natural.
* `…InvertibleTwistingRestriction.clauseOneSourceShaped_square`: **the source square of clause (1)
  at a scheme point, at variables.**
* `…InvertibleTwistingRestriction.modulePullback_map_comp_hom_eq_of_heq`: the base change square
  of `ψ` read in a second spelling of the site, by comparing leaves only.
* `…InvertibleTwistingRestriction.clauseOneSource_square_of_chartSourceIso`: the square at a
  scheme point `w` of `U(ψ)` over the site of `s.shrink`, with the source identification of the
  chart map `χ_w` read through its value and the `ψ_P` leg and the source identification of the
  square still variables.

## Implementation notes

The `ψ_P` leg and the chart maps `…chartMap` live over the site of `s.shrink`, the source
identifications `…chartSourceIso` and `…clauseOnePointSourceIso` over `s.site`; the two are the same
site by definition but not syntactically, and a composite spelled over one is not compared cheaply
with the same composite spelled over the other. The square is therefore stated with every composite
a variable, with its value as a hypothesis, and with the second spelling `A'` of the point and `κ₀`
of the leading factor compared by hypotheses `A' = A` and `κ₀ = pre₁ ≫ pre₂`, so that each value is
substituted in its own declaration.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open AlgebraicGeometry

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

section Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The comparison `a^*b^* ≅ a'^*b'^*` of two factorisations, on underlying morphisms, as the
composite of the underlying morphisms of its three factors. -/
theorem modulePullbackCompTransportIso_hom_eq_trans {A Y Z P : AlgebraicSpaces B S hS}
    (a : A ⟶ Y) (b : Y ⟶ P) (a' : A ⟶ Z) (b' : Z ⟶ P) (h : a ≫ b = a' ≫ b')
    (N : Modules.{u, u} B S hS P.1 P.2) :
    (modulePullbackCompTransportIso a b a' b' h N).hom =
      ((modulePullbackCompIso B S hS a b).app N).hom ≫
        (eqToIso (congrArg (fun k => (modulePullback B S hS k).obj N) h)).hom ≫
          ((modulePullbackCompIso B S hS a' b').app N).symm.hom :=
  trans_trans_hom (modulePullbackCompTransportIso a b a' b' h N) rfl

/-- The comparison `a^*b^* ≅ a'^*b'^*` of two factorisations, written out. -/
theorem modulePullbackCompTransportIso_hom_eq {A Y Z P : AlgebraicSpaces B S hS}
    (a : A ⟶ Y) (b : Y ⟶ P) (a' : A ⟶ Z) (b' : Z ⟶ P) (h : a ≫ b = a' ≫ b')
    (N : Modules.{u, u} B S hS P.1 P.2) :
    (modulePullbackCompTransportIso a b a' b' h N).hom =
      (modulePullbackCompIso B S hS a b).hom.app N ≫
        eqToHom (congrArg (fun k => (modulePullback B S hS k).obj N) h) ≫
          (modulePullbackCompIso B S hS a' b').inv.app N := by
  rw [modulePullbackCompTransportIso_hom_eq_trans, Iso.app_hom, eqToIso.hom, Iso.symm_hom,
    Iso.app_inv]

/-- The inverse images along `a` and `b` of a morphism, read along `a ≫ b`. -/
theorem modulePullback_map_map_comp_compIso_hom_app {A Y P : AlgebraicSpaces B S hS}
    (a : A ⟶ Y) (b : Y ⟶ P) {M N : Modules.{u, u} B S hS P.1 P.2} (g : M ⟶ N) :
    (modulePullback B S hS a).map ((modulePullback B S hS b).map g) ≫
        (modulePullbackCompIso B S hS a b).hom.app N =
      (modulePullbackCompIso B S hS a b).hom.app M ≫ (modulePullback B S hS (a ≫ b)).map g :=
  (modulePullbackCompIso B S hS a b).hom.naturality g

/-- The inverse image along `a ≫ b` of a morphism, read along `a` and `b`. -/
theorem modulePullback_map_comp_compIso_inv_app {A Y P : AlgebraicSpaces B S hS}
    (a : A ⟶ Y) (b : Y ⟶ P) {M N : Modules.{u, u} B S hS P.1 P.2} (g : M ⟶ N) :
    (modulePullback B S hS (a ≫ b)).map g ≫ (modulePullbackCompIso B S hS a b).inv.app N =
      (modulePullbackCompIso B S hS a b).inv.app M ≫
        (modulePullback B S hS a).map ((modulePullback B S hS b).map g) :=
  (modulePullbackCompIso B S hS a b).inv.naturality g

/-- The inverse image along `k` of a morphism commutes with the transport along `k = k'`. -/
theorem modulePullback_map_comp_eqToHom {A P : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS P.1 P.2} (g : M ⟶ N) (k k' : A ⟶ P) (hk : k = k') :
    (modulePullback B S hS k).map g ≫
        eqToHom (congrArg (fun k => (modulePullback B S hS k).obj N) hk) =
      eqToHom (congrArg (fun k => (modulePullback B S hS k).obj M) hk) ≫
        (modulePullback B S hS k').map g := by
  subst hk
  simp

/-- **The comparison `a^*b^* ≅ a'^*b'^*` of two factorisations is natural.** -/
theorem modulePullbackCompTransportIso_hom_naturality {A Y Z P : AlgebraicSpaces B S hS}
    (a : A ⟶ Y) (b : Y ⟶ P) (a' : A ⟶ Z) (b' : Z ⟶ P) (h : a ≫ b = a' ≫ b')
    {M N : Modules.{u, u} B S hS P.1 P.2} (g : M ⟶ N) :
    (modulePullback B S hS a).map ((modulePullback B S hS b).map g) ≫
        (modulePullbackCompTransportIso a b a' b' h N).hom =
      (modulePullbackCompTransportIso a b a' b' h M).hom ≫
        (modulePullback B S hS a').map ((modulePullback B S hS b').map g) := by
  rw [modulePullbackCompTransportIso_hom_eq, modulePullbackCompTransportIso_hom_eq,
    reassoc_of% (modulePullback_map_map_comp_compIso_hom_app a b g),
    reassoc_of% (modulePullback_map_comp_eqToHom g _ _ h),
    modulePullback_map_comp_compIso_inv_app]
  simp only [Category.assoc]

section Shaped

attribute [local irreducible] modulePullback

/-- `…clauseOneSourceShaped_square` with one spelling of the point and of the leading factor. -/
theorem clauseOneSourceShaped_square_core {T F : BigFppfOver B S hS} {L P : AlgebraicSpaces B S hS}
    {b' : representedAlgebraicSpace B S hS F ⟶ P} {Ms Tm : Modules.{u, u} B S hS P.1 P.2}
    {N Ns : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj F).ringCatSheaf).FullSubcategory}
    {ψP : Ms ⟶ Tm}
    {E₀ : (modulePullback B S hS b').obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj N).obj}
    {Es : (modulePullback B S hS b').obj Ms ≅
      ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj}
    {φ : Ns ⟶ N}
    (hE : (modulePullback B S hS b').map ψP ≫ E₀.hom =
      Es.hom ≫ ((representedQuasicoherentSchemeEquivalence B S hS F).functor.map φ).hom)
    {A : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ L}
    {r : L ⟶ P} (c : T ⟶ F) {hab : A ≫ r = representedSpaceMap B S hS c ≫ b'}
    (J : (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Tm) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c N)).obj)
    (hJ : J = modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Tm ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS c)).mapIso E₀ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS c N)
    {X₀ X₁ : Modules.{u, u} B S hS L.1 L.2}
    {pre₁ : X₀ ⟶ X₁} {pre₂ : X₁ ⟶ (modulePullback B S hS r).obj Ms}
    (PL : X₀ ⟶ (modulePullback B S hS r).obj Tm)
    (hPL : PL = pre₁ ≫ pre₂ ≫ (modulePullback B S hS r).map ψP)
    (K : (modulePullback B S hS A).obj X₀ ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c Ns)).obj)
    {κ : (modulePullback B S hS A).obj X₀ ⟶
      (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Ms)}
    {τ : (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Ms) ⟶
      (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((modulePullback B S hS b').obj Ms)}
    {μ : (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((modulePullback B S hS b').obj Ms) ⟶
      (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj}
    {ρ : (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c Ns)).obj}
    (hK : K = κ ≫ τ ≫ μ ≫ ρ)
    (hκ : κ = (modulePullback B S hS A).map (pre₁ ≫ pre₂))
    (hτ : τ = (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom)
    (hμ : μ = (modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom)
    (hρ : ρ = (modulePullbackRepresentedQuasicoherentIso B S hS c Ns).hom) :
    (modulePullback B S hS A).map PL ≫ J.hom =
      K ≫ ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (quasicoherentPullbackMap B S hS c φ)).hom := by
  have hJh : J.hom =
      (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Tm).hom ≫
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom := by
    rw [hJ]; rfl
  have hPLm : (modulePullback B S hS A).map PL = ((modulePullback B S hS A).map (pre₁ ≫ pre₂)) ≫
      ((modulePullback B S hS A).map ((modulePullback B S hS r).map ψP)) := by
    rw [hPL, ← Category.assoc, Functor.map_comp]
  have h1 : ((modulePullback B S hS A).map ((modulePullback B S hS r).map ψP)) ≫
      (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Tm).hom =
      (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map
      ((modulePullback B S hS b').map ψP)) :=
    modulePullbackCompTransportIso_hom_naturality A r (representedSpaceMap B S hS c) b' hab ψP
  have h2 :
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map
      ((modulePullback B S hS b').map ψP)) ≫
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom) =
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom) ≫
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map
      ((representedQuasicoherentSchemeEquivalence B S hS F).functor.map φ).hom) :=
    ((modulePullback B S hS (representedSpaceMap B S hS c)).map_comp _ _).symm.trans
        ((congrArg (modulePullback B S hS (representedSpaceMap B S hS c)).map hE).trans
        ((modulePullback B S hS (representedSpaceMap B S hS c)).map_comp _ _))
  have h3 :
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map
      ((representedQuasicoherentSchemeEquivalence B S hS F).functor.map φ).hom) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom =
      (modulePullbackRepresentedQuasicoherentIso B S hS c Ns).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
      (quasicoherentPullbackMap B S hS c φ)).hom :=
    modulePullbackRepresentedQuasicoherentIso_naturality B S hS c φ
  have inner : ((modulePullback B S hS A).map ((modulePullback B S hS r).map ψP)) ≫
      (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Tm).hom ≫
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom =
      (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS c Ns).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
      (quasicoherentPullbackMap B S hS c φ)).hom :=
    calc ((modulePullback B S hS A).map ((modulePullback B S hS r).map ψP)) ≫
        (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Tm).hom ≫
        ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom) ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom
        =
            (((modulePullback B S hS A).map ((modulePullback B S hS r).map ψP)) ≫
            (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Tm).hom) ≫
            ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom) ≫
            (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom :=
            (Category.assoc ((modulePullback B S hS A).map ((modulePullback B S hS r).map ψP))
            (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab
            Tm).hom _).symm
      _ =
          ((modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map
          ((modulePullback B S hS b').map ψP))) ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom) ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom :=
          congrArg
          (· ≫ ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom) ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom) h1
      _ = (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map
          ((modulePullback B S hS b').map ψP)) ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom) ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom :=
          Category.assoc
          (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map
          ((modulePullback B S hS b').map ψP)) _
      _ = (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
          (((modulePullback B S hS (representedSpaceMap B S hS c)).map
          ((modulePullback B S hS b').map ψP)) ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom)) ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom :=
          congrArg
              ((modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab
              Ms).hom ≫ ·)
              (Category.assoc
              ((modulePullback B S hS (representedSpaceMap B S hS c)).map
              ((modulePullback B S hS b').map ψP))
              ((modulePullback B S hS (representedSpaceMap B S hS c)).map E₀.hom)
              (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom).symm
      _ = (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
          (((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom) ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map
          ((representedQuasicoherentSchemeEquivalence B S hS F).functor.map φ).hom)) ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom :=
          congrArg
          (fun x =>
          (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫ x ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom) h2
      _ = (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom) ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map
          ((representedQuasicoherentSchemeEquivalence B S hS F).functor.map φ).hom) ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom :=
          congrArg
          ((modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫ ·)
          (Category.assoc ((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom)
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map
          ((representedQuasicoherentSchemeEquivalence B S hS F).functor.map φ).hom)
          (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom)
      _ = (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom) ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS c Ns).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (quasicoherentPullbackMap B S hS c φ)).hom :=
          congrArg
          (fun x =>
          (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
          ((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom) ≫ x) h3
  subst hκ hτ hμ hρ
  have eK : K ≫
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
      (quasicoherentPullbackMap B S hS c φ)).hom = ((modulePullback B S hS A).map (pre₁ ≫ pre₂)) ≫
      (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫
      ((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS c Ns).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
      (quasicoherentPullbackMap B S hS c φ)).hom := by
    rw [hK]
    exact
        (Category.assoc ((modulePullback B S hS A).map (pre₁ ≫ pre₂)) _
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (quasicoherentPullbackMap B S hS c φ)).hom).trans
        (congrArg (((modulePullback B S hS A).map (pre₁ ≫ pre₂)) ≫ ·)
      ((Category.assoc
          (modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom _
          ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (quasicoherentPullbackMap B S hS c φ)).hom).trans
          (congrArg
          ((modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Ms).hom ≫ ·)
          (Category.assoc ((modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom)
          (modulePullbackRepresentedQuasicoherentIso B S hS c Ns).hom
          ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (quasicoherentPullbackMap B S hS c φ)).hom))))
  rw [hPLm, hJh, eK]
  exact
      (Category.assoc ((modulePullback B S hS A).map (pre₁ ≫ pre₂))
      ((modulePullback B S hS A).map ((modulePullback B S hS r).map ψP)) _).trans
      (congrArg (((modulePullback B S hS A).map (pre₁ ≫ pre₂)) ≫ ·) inner)

/-- **The source square of clause (1) of Stacks 0D2Z at a scheme point, at variables.**  Let
`A : T ⟶ L` and `r : L ⟶ P` be morphisms of algebraic spaces with `A ≫ r = c ≫ b'` for a morphism
`c : T ⟶ F` of the site and `b' : F ⟶ P`, let `ψ_P : M ⟶ N_P` be a morphism of `𝒪_P`-modules and
let `E₀ : b'^*N_P ≅ N^a`, `E_s : b'^*M ≅ N_s^a` be identifications with modules attached to
quasi-coherent modules on `F` under which `b'^*ψ_P` is the module attached to `φ : N_s ⟶ N`.  Let
`J = (A^*r^* ≅ c^*b'^*) ≪≫ c^*E₀ ≪≫ (c^*(N^a) ≅ (c^*N)^a)`, `PL = pre₁ ≫ pre₂ ≫ r^*ψ_P` and
`K = A'^*κ₀ ≫ (A'^*r^* ≅ c^*b'^*) ≫ c^*E_s ≫ (c^*(N_s^a) ≅ (c^*N_s)^a)` for `A' = A` and
`κ₀ = pre₁ ≫ pre₂`.  Then `A^*PL` followed by `J` is `K` followed by the module attached to `c^*φ`.

Every composite is a variable with its value as a hypothesis, and the two spellings `A`, `A'` of
the point and `κ₀`, `pre₁ ≫ pre₂` of the leading factor are compared by hypotheses, so that an
instance compares only the factors. -/
theorem clauseOneSourceShaped_square {T F : BigFppfOver B S hS} {L P : AlgebraicSpaces B S hS}
    {b' : representedAlgebraicSpace B S hS F ⟶ P} {Ms Tm : Modules.{u, u} B S hS P.1 P.2}
    {N Ns : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj F).ringCatSheaf).FullSubcategory}
    {ψP : Ms ⟶ Tm}
    {E₀ : (modulePullback B S hS b').obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj N).obj}
    {Es : (modulePullback B S hS b').obj Ms ≅
      ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj}
    {φ : Ns ⟶ N}
    (hE : (modulePullback B S hS b').map ψP ≫ E₀.hom =
      Es.hom ≫ ((representedQuasicoherentSchemeEquivalence B S hS F).functor.map φ).hom)
    {A : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ L}
    {r : L ⟶ P} {c : T ⟶ F} {hab : A ≫ r = representedSpaceMap B S hS c ≫ b'}
    (J : (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Tm) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c N)).obj)
    (hJ : J = modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Tm ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS c)).mapIso E₀ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS c N)
    {X₀ X₁ : Modules.{u, u} B S hS L.1 L.2}
    {pre₁ : X₀ ⟶ X₁} {pre₂ : X₁ ⟶ (modulePullback B S hS r).obj Ms}
    (PL : X₀ ⟶ (modulePullback B S hS r).obj Tm)
    (hPL : PL = pre₁ ≫ pre₂ ≫ (modulePullback B S hS r).map ψP)
    {A' : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ L}
    {hab' : A' ≫ r = representedSpaceMap B S hS c ≫ b'}
    (K : (modulePullback B S hS A).obj X₀ ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c Ns)).obj)
    {κ : (modulePullback B S hS A).obj X₀ ⟶
      (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Ms)}
    {τ : (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Ms) ⟶
      (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((modulePullback B S hS b').obj Ms)}
    {μ : (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((modulePullback B S hS b').obj Ms) ⟶
      (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj}
    {ρ : (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c Ns)).obj}
    (hK : K = κ ≫ τ ≫ μ ≫ ρ)
    {κ₀ : X₀ ⟶ (modulePullback B S hS r).obj Ms}
    (hκ : HEq κ ((modulePullback B S hS A').map κ₀))
    (hτ : HEq τ
      (modulePullbackCompTransportIso A' r (representedSpaceMap B S hS c) b' hab' Ms).hom)
    (hμ : μ = (modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom)
    (hρ : ρ = (modulePullbackRepresentedQuasicoherentIso B S hS c Ns).hom)
    (hA : A' = A) (hκ₀ : κ₀ = pre₁ ≫ pre₂) :
    (modulePullback B S hS A).map PL ≫ J.hom =
      K ≫ ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (quasicoherentPullbackMap B S hS c φ)).hom := by
  subst hA hκ₀ hμ hρ
  exact clauseOneSourceShaped_square_core hE c J hJ PL hPL K hK (eq_of_heq hκ) (eq_of_heq hτ) rfl
    rfl

end Shaped

/-- **The base change square of `ψ` (the hypothesis `hE` of
`…clauseOneSourceShaped_square`), read in a second spelling of the site**: heterogeneously equal
leaves over `B₂ = B₁` give the same square. -/
theorem modulePullback_map_comp_hom_eq_of_heq {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {F₁ : BigFppfOver B₁ S₁ hS₁} {P₁ : AlgebraicSpaces B₁ S₁ hS₁}
    {b₁ : representedAlgebraicSpace B₁ S₁ hS₁ F₁ ⟶ P₁} {M₁ T₁ : Modules.{u, u} B₁ S₁ hS₁ P₁.1 P₁.2}
    {N₁ Ns₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj F₁).ringCatSheaf).FullSubcategory}
    {g₁ : M₁ ⟶ T₁}
    {E₁ : (modulePullback B₁ S₁ hS₁ b₁).obj T₁ ≅
      ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ F₁).functor.obj N₁).obj}
    {Es₁ : (modulePullback B₁ S₁ hS₁ b₁).obj M₁ ≅
      ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ F₁).functor.obj Ns₁).obj}
    {φ₁ : Ns₁ ⟶ N₁}
    (H : (modulePullback B₁ S₁ hS₁ b₁).map g₁ ≫ E₁.hom =
      Es₁.hom ≫ ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ F₁).functor.map φ₁).hom)
    {F₂ : BigFppfOver B₂ S₂ hS₂} {P₂ : AlgebraicSpaces B₂ S₂ hS₂}
    (b₂ : representedAlgebraicSpace B₂ S₂ hS₂ F₂ ⟶ P₂) {M₂ T₂ : Modules.{u, u} B₂ S₂ hS₂ P₂.1 P₂.2}
    {N₂ Ns₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj F₂).ringCatSheaf).FullSubcategory}
    (g₂ : M₂ ⟶ T₂)
    (E₂ : (modulePullback B₂ S₂ hS₂ b₂).obj T₂ ≅
      ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ F₂).functor.obj N₂).obj)
    (Es₂ : (modulePullback B₂ S₂ hS₂ b₂).obj M₂ ≅
      ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ F₂).functor.obj Ns₂).obj)
    (φ₂ : Ns₂ ⟶ N₂)
    (hF : HEq F₁ F₂) (hP : HEq P₁ P₂) (hb : HEq b₁ b₂) (hM : HEq M₁ M₂) (hT : HEq T₁ T₂)
    (hN : HEq N₁ N₂) (hNs : HEq Ns₁ Ns₂) (hg : HEq g₁ g₂) (hE : HEq E₁ E₂) (hEs : HEq Es₁ Es₂)
    (hφ : HEq φ₁ φ₂) :
    (modulePullback B₂ S₂ hS₂ b₂).map g₂ ≫ E₂.hom =
      Es₂.hom ≫ ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ F₂).functor.map φ₂).hom := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hF hP
  subst hb hM hT hN hNs
  subst hg hE hEs hφ
  exact H

end Generic

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

section Fibre

attribute [local irreducible] modulePullback

/-- **`ψ` of Stacks 084D at the base change of a scheme point `v : T ⟶ Y`**: the inverse image of
`ψ_n` along `T ×_Y P ⟶ P`, followed by the base change identification of Stacks 084D, is the
identification `…RelativeProjSituation.fibrePsiSourceIso` of its source followed by the module
attached to `ψ` of Tag 01NR on `T ×_Y P` (`…RelativeProjSituation.fibrePsiQcohHom`); the
hypothesis `hE` of `…InvertibleTwistingRestriction.clauseOneSourceShaped_square`. -/
theorem modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom
    (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
    (v : yoneda.obj T ⟶ s.shrink.space.1) (n : ℕ) :
    (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T v)).map
        (s.psiTwistHom Px n) ≫
      (s.fibreToSpaceTwistModuleIso Px T v (n : ℤ)).hom =
    (s.fibrePsiSourceIso T v (n : ℤ)).hom ≫
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre T v)).functor.map (s.fibrePsiQcohHom T v n)).hom :=
  (s.modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso Px T v n).trans
    (s.fibrePsiHom_eq T v n)

/-- `…modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom` over the site of
`s.shrink`, the spelling of the chart maps. -/
theorem modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom_shrink
    (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
    (v : yoneda.obj T ⟶ s.shrink.space.1) (n : ℕ) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (s.fibreToSpaceHom T v)).map (s.psiTwistHom Px n) ≫
      (s.fibreToSpaceTwistModuleIso Px T v (n : ℤ)).hom =
    (s.fibrePsiSourceIso T v (n : ℤ)).hom ≫
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase (s.relativeProjPoints.fibre T v)).functor.map
          (s.fibrePsiQcohHom T v n)).hom :=
  modulePullback_map_comp_hom_eq_of_heq s.shrink_site.symm s.shrink_base.symm
    (modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom s Px T v n)
    (s.fibreToSpaceHom T v) (s.psiTwistHom Px n) (s.fibreToSpaceTwistModuleIso Px T v (n : ℤ))
    (s.fibrePsiSourceIso T v (n : ℤ)) (s.fibrePsiQcohHom T v n)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

end Fibre

section Point

variable {s} {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase}
  {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- `…clauseOneSourceShaped_square` at the source identification
`…InvertibleTwistingRestriction.chartSourceIso` at `w`, over the site of `s.shrink` (the spelling
of the chart maps), read through its value
`…InvertibleTwistingRestriction.chartSourceIso_eq_shrink` and with the base change square of `ψ`
in that spelling
(`…modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom_shrink`). -/
theorem clauseOneSource_square_of_chartSourceIso :
    type_of% (@clauseOneSourceShaped_square s.shrink.site s.shrink.base s.shrink.containsBase
      _ _ _ _ _ _ _ _ _ _ _ _ _
      (modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom_shrink s Px W
        (locusPoint w ≫ f.hom) d : _) _ _ _ (pointHom_comp_invertibleSpaceMorphism w)
      (chartSourceIso Px w (locusOpen_locusPoint w) (d : ℤ) : _)
      (chartSourceIso_eq_shrink Px w (d : ℤ) : _)) :=
  @clauseOneSourceShaped_square s.shrink.site s.shrink.base s.shrink.containsBase
    _ _ _ _ _ _ _ _ _ _ _ _ _
    (modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom_shrink s Px W
      (locusPoint w ≫ f.hom) d : _) _ _ _ (pointHom_comp_invertibleSpaceMorphism w)
    (chartSourceIso Px w (locusOpen_locusPoint w) (d : ℤ) : _)
    (chartSourceIso_eq_shrink Px w (d : ℤ) : _)

end Point

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
