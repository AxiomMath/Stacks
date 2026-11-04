module

public import StacksFrontier.AlgebraicGeometry.Quot.PullSheafHomRelHom

/-!
# The base change step of the relative Hom functors is bijective

Let `X' = X ×_Y Y'` be a commutative square of algebraic spaces with projections
`p : X' ⟶ X` and `f' : X' ⟶ Y'`, let `q : Y' ⟶ Y`, and let `R ∈ D(𝒪_X)`.  Pulling a morphism
`β : Lq^*𝒪_Y ⟶ Lq^*Rf_*R` back along `f'`, identifying `Lf'^*Lq^*` with `Lp^*Lf^*` through the
comparison triangles of the derived pullback pseudofunctor datum, and composing with `Lp^*` of the
counit `Lf^*Rf_*R ⟶ R` is a bijection onto `Hom(Lp^*Lf^*𝒪_Y, Lp^*R)` as soon as the base change
map `Lq^*Rf_*R ⟶ Rf'_*Lp^*R` of Stacks 07A7 is an isomorphism.  The reason is that the composite
is, up to an isomorphism of the source, the transpose under `Lf'^* ⊣ Rf'_*` of composition with
the base change map.

## Main results

* `CategoryTheory.Functor.bijective_comp_counit_of_isIso`: the abstract statement.
* `AlgebraicGeometry.Space.bijective_pullBaseChangeRelHom`: the statement for algebraic spaces.

## References

* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

/-- **Pulling back and composing with a counit is bijective when the base change map is
invertible.**  For an adjunction `Lf' ⊣ Rf'`, morphisms `σ : Lf'(Lq N) ⟶ Lp(Lf N)` and
`ε : Lf N ⟶ R`, and `bc : Lq N ⟶ Rf'(Lp R)` whose transpose is `σ ≫ Lp ε`, if `bc` is invertible
then `β ↦ ι ≫ Lf' β ≫ σ ≫ Lp ε` is a bijection for every isomorphism `ι`. -/
theorem bijective_comp_counit_of_isIso {CY CY' CX CX' : Type*} [Category* CY] [Category* CY']
    [Category* CX] [Category* CX'] {Lq : CY ⥤ CY'} {Lf' : CY' ⥤ CX'} {Rf' : CX' ⥤ CY'}
    (adj : Lf' ⊣ Rf') {Lf : CY ⥤ CX} {Lp : CX ⥤ CX'} {O N : CY} {R : CX} {M' : CX'}
    (ι : M' ≅ Lf'.obj (Lq.obj O)) (σ : Lf'.obj (Lq.obj N) ⟶ Lp.obj (Lf.obj N))
    (ε : Lf.obj N ⟶ R) (bc : Lq.obj N ⟶ Rf'.obj (Lp.obj R))
    (hbc : (adj.homEquiv _ _).symm bc = σ ≫ Lp.map ε) (hiso : IsIso bc) :
    Function.Bijective (fun β : Lq.obj O ⟶ Lq.obj N => ι.hom ≫ Lf'.map β ≫ σ ≫ Lp.map ε) := by
  have e : (fun β : Lq.obj O ⟶ Lq.obj N => ι.hom ≫ Lf'.map β ≫ σ ≫ Lp.map ε) =
      (fun γ => ι.hom ≫ γ) ∘ (adj.homEquiv _ _).symm ∘ (fun β => β ≫ bc) := by
    funext β
    simp only [Function.comp_apply, Adjunction.homEquiv_naturality_left_symm, hbc]
  rw [e]
  exact (bijective_iso_hom_comp ι _).comp
    ((Equiv.bijective _).comp (bijective_comp_isIso (hi := hiso) _ _))

/-- The transpose of a base change map, given as the comparison `c₁` followed by the inverse of
`c₂ ≪≫ eqToIso h` and the image of the counit, rewritten through the comparisons
`eqToIso h ≪≫ c₁.symm` and `c₂.symm`. -/
theorem homEquiv_symm_eq_of_square {CY CY' CX CX' : Type*} [Category* CY] [Category* CY']
    [Category* CX] [Category* CX'] {Lq : CY ⥤ CY'} {Lf' : CY' ⥤ CX'} {Rf' : CX' ⥤ CY'}
    (adj : Lf' ⊣ Rf') {Lf : CY ⥤ CX} {Lp : CX ⥤ CX'} {K₁ K₂ : CY ⥤ CX'}
    (c₁ : Lq ⋙ Lf' ≅ K₁) (c₂ : Lf ⋙ Lp ≅ K₂) (h : K₂ = K₁) (sq : Lf ⋙ Lp ≅ K₁)
    (hsq : sq = c₂ ≪≫ eqToIso h) {N : CY} {R : CX}
    (ε : Lf.obj N ⟶ R) (bc : Lq.obj N ⟶ Rf'.obj (Lp.obj R))
    (hbc : (adj.homEquiv _ _).symm bc = c₁.hom.app N ≫ sq.inv.app N ≫ Lp.map ε) :
    (adj.homEquiv _ _).symm bc =
      (eqToIso h ≪≫ c₁.symm).inv.app N ≫ c₂.symm.hom.app N ≫ Lp.map ε := by
  subst hsq
  rw [hbc]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Category.assoc]

end CategoryTheory.Functor

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `Rf_*` for a morphism of algebraic spaces, the derived direct image of the morphism of small
étale ringed topoi, typed on `AlgebraicGeometry.Space.derivedModules`. -/
abbrev derivedModulesPushforward {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    derivedModules B S hS X ⥤ derivedModules B S hS Y :=
  Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := smallEtaleRingedTopos B S hS _)
    (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)

/-- `Lf^* ⊣ Rf_*` (Stacks 07A6), `AlgebraicGeometry.Space.smallEtaleDerivedModuleAdjunction`,
with the derived pullback of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. -/
def derivedModulesAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleDerivedPullbackData B S hS).pull f ⊣ derivedModulesPushforward f :=
  smallEtaleDerivedModuleAdjunction B S hS f

/-- The composition isomorphism of Stacks 0D6D,
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`, typed with the derived pullback
of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. -/
def derivedModulesPullbackCompIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleDerivedPullbackData B S hS).pull g ⋙ (smallEtaleDerivedPullbackData B S hS).pull f ≅
      (smallEtaleDerivedPullbackData B S hS).pull (f ≫ g) :=
  smallEtaleDerivedModulePullbackCompIso B S hS f g

/-- The comparison `Lf^* ⋙ Lp^* ≅ L(f' ≫ q)^*` around a commutative square `p ≫ f = f' ≫ q`,
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackSquareIso`, typed with the derived pullback
of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. -/
def derivedModulesPullbackSquareIso {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (q : Y' ⟶ Y)
    (f' : X' ⟶ Y') (p : X' ⟶ X) (w : p ≫ f = f' ≫ q) :
    (smallEtaleDerivedPullbackData B S hS).pull f ⋙ (smallEtaleDerivedPullbackData B S hS).pull p ≅
      (smallEtaleDerivedPullbackData B S hS).pull (f' ≫ q) :=
  derivedModulesPullbackCompIso p f ≪≫
    eqToIso (congrArg (fun k => (smallEtaleDerivedPullbackData B S hS).pull k) w)

/-- The base change map of Stacks 07A7,
`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`, typed with the derived pullback of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. -/
def derivedModulesBaseChangeMap {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (q : Y' ⟶ Y)
    (f' : X' ⟶ Y') (p : X' ⟶ X) (w : p ≫ f = f' ≫ q) (R : derivedModules B S hS X) :
    ((smallEtaleDerivedPullbackData B S hS).pull q).obj ((derivedModulesPushforward f).obj R) ⟶
      (derivedModulesPushforward f').obj (((smallEtaleDerivedPullbackData B S hS).pull p).obj R) :=
  Stacks.CategoryTheory.BaseChange.map (derivedModulesAdjunction f) (derivedModulesAdjunction f')
    (derivedModulesPullbackCompIso f' q) (derivedModulesPullbackSquareIso f q f' p w) R

/-- `AlgebraicGeometry.Space.SmallEtaleDerivedPullbackDataCompIsoEq` with the composition
isomorphism typed with the derived pullback of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. -/
theorem compIso_eq_derivedModulesPullbackCompIso
    (hc : SmallEtaleDerivedPullbackDataCompIsoEq B S hS) {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleDerivedPullbackData B S hS).compIso f g = (derivedModulesPullbackCompIso f g).symm :=
  hc f g

/-- If the base change map `AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap` of
Stacks 07A7 is an isomorphism, then so is `AlgebraicGeometry.Space.derivedModulesBaseChangeMap`. -/
theorem isIso_derivedModulesBaseChangeMap {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (q : Y' ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X) (w : p ≫ f = f' ≫ q) (R : derivedModules B S hS X)
    (h : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f q f' p w R)) :
    IsIso (derivedModulesBaseChangeMap f q f' p w R) :=
  h

/-- The transpose of the base change map of Stacks 07A7 under `Lf'^* ⊣ Rf'_*`, through the
composition isomorphisms. -/
theorem homEquiv_symm_derivedModulesBaseChangeMap_eq {X Y X' Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (q : Y' ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X) (w : p ≫ f = f' ≫ q)
    (R : derivedModules B S hS X) :
    ((derivedModulesAdjunction f').homEquiv _ _).symm (derivedModulesBaseChangeMap f q f' p w R) =
      (eqToIso (congrArg (fun k => (smallEtaleDerivedPullbackData B S hS).pull k) w) ≪≫
        (derivedModulesPullbackCompIso f' q).symm).inv.app ((derivedModulesPushforward f).obj R) ≫
        (derivedModulesPullbackCompIso p f).symm.hom.app ((derivedModulesPushforward f).obj R) ≫
          ((smallEtaleDerivedPullbackData B S hS).pull p).map
            ((derivedModulesAdjunction f).counit.app R) :=
  Functor.homEquiv_symm_eq_of_square (derivedModulesAdjunction f')
    (derivedModulesPullbackCompIso f' q) (derivedModulesPullbackCompIso p f)
    (congrArg (fun k => (smallEtaleDerivedPullbackData B S hS).pull k) w)
    (derivedModulesPullbackSquareIso f q f' p w) rfl _ _
    (Stacks.CategoryTheory.BaseChange.homEquiv_symm_map _ _ _ _ R)

/-- The transpose of the base change map of Stacks 07A7 under `Lf'^* ⊣ Rf'_*`, read through the
comparison triangles of the derived pullback pseudofunctor datum. -/
theorem homEquiv_symm_derivedModulesBaseChangeMap
    (hc : SmallEtaleDerivedPullbackDataCompIsoEq B S hS)
    {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (q : Y' ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X)
    (w : p ≫ f = f' ≫ q) (R : derivedModules B S hS X) :
    ((derivedModulesAdjunction f').homEquiv _ _).symm (derivedModulesBaseChangeMap f q f' p w R) =
      ((smallEtaleDerivedPullbackData B S hS).triangle w.symm).inv.app _ ≫
        ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : p ≫ f = p ≫ f)).hom.app _ ≫
          ((smallEtaleDerivedPullbackData B S hS).pull p).map
            ((derivedModulesAdjunction f).counit.app R) := by
  have h₁ : (smallEtaleDerivedPullbackData B S hS).triangle w.symm =
      eqToIso (congrArg (fun k => (smallEtaleDerivedPullbackData B S hS).pull k) w) ≪≫
        (derivedModulesPullbackCompIso f' q).symm := by
    rw [PullbackData.triangle_eq, compIso_eq_derivedModulesPullbackCompIso hc]
  have h₂ : (smallEtaleDerivedPullbackData B S hS).triangle (rfl : p ≫ f = p ≫ f) =
      (derivedModulesPullbackCompIso p f).symm := by
    rw [PullbackData.triangle_rfl, compIso_eq_derivedModulesPullbackCompIso hc]
  rw [h₁, h₂]
  exact homEquiv_symm_derivedModulesBaseChangeMap_eq f q f' p w R

/-- **The base change step of the relative Hom functors is bijective.**  For a commutative square
`p ≫ f = f' ≫ q` whose base change map at `R` (Stacks 07A7) is invertible, the map
`β ↦ ι ≫ Lf'^*β ≫ (comparison) ≫ Lp^*(counit)` from `Hom(Lq^*𝒪_Y, Lq^*Rf_*R)` to
`Hom(M', Lp^*R)` is bijective for every isomorphism `ι : M' ≅ Lf'^*Lq^*𝒪_Y`. -/
theorem bijective_pullBaseChangeRelHom (hc : SmallEtaleDerivedPullbackDataCompIsoEq B S hS)
    {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (q : Y' ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X)
    (w : p ≫ f = f' ≫ q) (R : derivedModules B S hS X)
    (hbc : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f q f' p w R))
    {M' : derivedModules B S hS X'}
    (ι : M' ≅ ((smallEtaleDerivedPullbackData B S hS).pull f').obj
      (((smallEtaleDerivedPullbackData B S hS).pull q).obj (structureObject B S hS Y))) :
    Function.Bijective (fun β : ((smallEtaleDerivedPullbackData B S hS).pull q).obj
          (structureObject B S hS Y) ⟶ ((smallEtaleDerivedPullbackData B S hS).pull q).obj
            ((derivedModulesPushforward f).obj R) =>
      ι.hom ≫ ((smallEtaleDerivedPullbackData B S hS).pull f').map β ≫
        (((smallEtaleDerivedPullbackData B S hS).triangle w.symm).inv.app _ ≫
          ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : p ≫ f = p ≫ f)).hom.app _) ≫
          ((smallEtaleDerivedPullbackData B S hS).pull p).map
            ((derivedModulesAdjunction f).counit.app R)) :=
  Functor.bijective_comp_counit_of_isIso (derivedModulesAdjunction f') ι _ _ _
    ((homEquiv_symm_derivedModulesBaseChangeMap hc f q f' p w R).trans (Category.assoc _ _ _).symm)
    (isIso_derivedModulesBaseChangeMap f q f' p w R hbc)

end AlgebraicGeometry.Space

end
