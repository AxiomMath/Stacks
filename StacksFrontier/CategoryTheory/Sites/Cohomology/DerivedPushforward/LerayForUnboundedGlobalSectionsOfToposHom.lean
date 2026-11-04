module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSectionsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.BoundedBelowRestriction
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit

/-!
# Leray for unbounded derived global sections along a morphism of ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi in the two-field sense of
Stacks 01D3, part (2): a morphism of the underlying topoi together with the structure map, and
no continuous functor between the underlying sites.  The global-sections clause of Stacks 0D6H
asserts

`RΓ(D, -) ∘ Rf_* = RΓ(C, -)`

as functors `D(𝒪_C) ⟶ D(Γ(𝒪_D))`, the right hand side read through restriction of scalars along
the ring map `Γ(𝒪_D) ⟶ Γ(𝒪_C)` induced by `f`.  This file proves it for every such `f`, with the
unbounded derived functors of the topos framework
(`Stacks.Cohomology.DerivedPushforward.derivedPushforward`), and builds from it the canonical base
change map on global sections

`RΓ(D, K) ⊗^L_{Γ(𝒪_D)} Γ(𝒪_C) ⟶ RΓ(C, Lf^*K)`,

the transpose across the adjunction `- ⊗^L ⊣ res` of Stacks 0GMT of `RΓ(D, -)` applied to the unit
`K ⟶ Rf_* Lf^* K`, followed by the identification above.

## Main definitions

All in the namespace `Stacks.Cohomology.LerayOfToposHom`.

* `toposGlobalSectionsRingHom`: the ring map `Γ(𝒪_D) ⟶ Γ(𝒪_C)` of `f`.
* `pushforwardModulesCompGlobalSectionsIso`: the underived identity `Γ(D, f_* -) ≅ Γ(C, -)` of
  `Γ(𝒪_D)`-modules.
* `derivedGlobalSectionsPushforwardIso`: **Stacks 0D6H, the global-sections clause**, for an
  arbitrary morphism of ringed topoi, read over any ring `R` mapping to `Γ(𝒪_D)`.
* `derivedGlobalSectionsSemilinearMap`: the comparison `RΓ(D, K) ⟶ ρ_* RΓ(C, Lf^* K)`.
* `derivedGlobalSectionsBaseChangeMap`: the base change map on global sections above, for any
  left adjoint `- ⊗^L_{R'} R` of restriction of scalars along `ρ : R' ⟶ R`.

## Main results

* `computesSecond_pushforwardModules_globalSections`: `f_* I` computes `RΓ(D, -)` for every
  K-injective complex `I` of `𝒪_C`-modules.
* `derivedGlobalSectionsBaseChangeMap_homEquiv`: the base change map is the transpose of
  `derivedGlobalSectionsSemilinearMap`.

## Implementation notes

*The route.*  It is the one of `LerayForUnboundedGlobalSectionsGeneral.lean`, which proves the
same clause for a morphism of ringed *sites*: global sections are corepresented by the structure
sheaf (`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`), so the degree-`n`
cohomology of `Γ(D, -)` at a K-injective resolution `s : f_* I ⟶ J` is the map induced by `s` on
morphisms `𝒪_D[0] ⟶ -[n]` in the homotopy category, and that map is bijective by the derived
adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6 and its counit factorization of Stacks 0FPI, both of which
are available for an arbitrary morphism of ringed topoi
(`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`,
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction_counit_fac`).  The one geometric
input is that `Lf^* ⟶ f^*` is invertible at `𝒪_D[0]`, a K-flat complex with flat terms.  The
ringed-site statements cannot be reused: a morphism of ringed topoi has no functor of sites, and
its pullback of modules is a different construction.

*Universes.*  `Γ(C, -)` takes values in `ModuleCat.{max u_C w_C}` and `Γ(D, -) ∘ f_*` in
`ModuleCat.{max u_D w_D}`, for the object universes `u_C`, `u_D` of the sites and the section
universes `w_C`, `w_D`; restriction of scalars does not change the module universe, so the clause
is stated at `C ∈ Type (max u t)`, `D ∈ Type (max u s)` with sections in `Type (max w t s)`, where
both are `max u w t s`.  This covers a crystalline topos, with objects one universe above those of
the Zariski topos it maps to (`t = u + 1`, `s = 0`), as well as two Zariski topoi (`t = s = 0`).
A consumer passes the universes explicitly, the unifier not inverting `max`.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.SiteModules
open CochainComplex.HomComplex

noncomputable section

namespace Stacks.Cohomology.LerayOfToposHom

universe v v' u u' w w' t s r r'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

-- The ambient-universe instances of `Stacks.Cohomology.SiteModules` are stated at
-- `SheafOfModules.{max u v r w}` and leave instance search with a stuck universe constraint at
-- the free universes of this file; the abelian structure comes from `HasSheafify` instead.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-! ### The structure sheaf in degree zero -/

section Unit

universe v₀ u₀ w₀

variable (Y : RingedTopos.{v₀, u₀, w₀})
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [HasSheafify Y.J AddCommGrpCat.{w₀}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₀}]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})] in
/-- Every term of the complex `𝒪_Y[0]` is flat: the one in degree zero is the structure sheaf,
flat by `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`, and the others are zero. -/
theorem isFlat_single_unit_X (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v₀, u₀, w₀, w₀} (O := Y.O)
      (((CochainComplex.singleFunctor
          (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) 0).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))).X i) := by
  by_cases h : i = 0
  · subst h
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).symm
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := ⟨Y.C, Y.J, Y.O⟩))
  · exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero
      (Y := ⟨Y.C, Y.J, Y.O⟩) _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})] in
/-- The complex `𝒪_Y[0]`, as an object of the unbounded homotopy category, is K-flat with flat
terms: K-flatness is `Stacks.SheafOfModules.isKFlat_single_unit` and the flatness of the terms is
`isFlat_single_unit_X`. -/
theorem isKFlat_single_unit :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)
      ((HomotopyCategory.quotient
          (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
        (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
            (SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) 0).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))) :=
  ⟨Stacks.SheafOfModules.isKFlat_single_unit Y.O, isFlat_single_unit_X Y⟩

end Unit

/-! ### The corepresentability argument -/

section Leray

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  [IsGrothendieckAbelian.{w}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))]
  [IsGrothendieckAbelian.{w'}
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))]
  (f : RingedToposHom X Y)

/-- The comparison `f_* K ⟶ Rf_* K` from degreewise direct image to the derived direct image. -/
abbrev derivedPushforwardUnit :
    pushforwardOnHomotopy f ⟶ DerivedCategory.Qh ⋙ derivedPushforward f :=
  (pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh (sourceQuasiIso X)

/-- **The ring map `Γ(𝒪_D) ⟶ Γ(𝒪_C)` of a morphism of ringed topoi**, induced on global
sections by the structure map: `Stacks.Cohomology.SiteModules.globalSectionsRingHom` of the
four-field form of `f`. -/
abbrev toposGlobalSectionsRingHom :
    RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj →+*
      RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O).obj :=
  globalSectionsRingHom f.toModulesHom

omit [IsGrothendieckAbelian.{w'}
    (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))] in
/-- **The derived transposition is the degreewise one.** For `g : P ⟶ f_* K` in the unbounded
homotopy category of `𝒪_D`-modules, transposing `Q(g)` followed by the comparison
`f_* K ⟶ Rf_* K` along the derived adjunction `Lf^* ⊣ Rf_*` gives the comparison
`Lf^* P ⟶ f^* P` followed by the localization of the degreewise transpose of `g`. This is
Stacks 0FPI at `K`, preceded by the naturality of `Lf^* ⟶ f^*` at `g`. -/
theorem derivedAdjunction_homEquiv_symm_qh_map
    (P : HomotopyCategory
        (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (ComplexShape.up ℤ))
    (K : HomotopyCategory
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
      (ComplexShape.up ℤ))
    (g : P ⟶ (pushforwardMapHomotopy f).obj K) :
    ((derivedAdjunction f).homEquiv (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj K)).symm
        (DerivedCategory.Qh.map g ≫ (derivedPushforwardUnit f).app K) =
      (derivedPullbackComparison f).app P ≫ DerivedCategory.Qh.map
        (((pullbackAdjPushforwardMapHomotopy f).homEquiv P K).symm g) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    derivedAdjunction_counit_fac f K, Adjunction.homEquiv_counit, Functor.map_comp,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ DerivedCategory.Qh.map
    ((pullbackAdjPushforwardMapHomotopy f).counit.app K))
    ((derivedPullbackComparison f).naturality g)

omit [IsGrothendieckAbelian.{w'}
    (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))] in
/-- **Localization is bijective on morphisms into the direct image of a K-injective complex**,
out of an object at which `Lf^* ⟶ f^*` is invertible:
`Hom_{K(𝒪_D)}(P, f_* I) ⟶ Hom_{D(𝒪_D)}(P, f_* I)` is bijective. Both sides are `Hom(f^* P, I)`,
by the degreewise and by the derived adjunction, and the two identifications agree by
`derivedAdjunction_homEquiv_symm_qh_map`. -/
theorem bijective_qh_map_pushforward_of_isKInjective
    (P : HomotopyCategory
        (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (ComplexShape.up ℤ))
    [IsIso ((derivedPullbackComparison f).app P)]
    (I : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) ℤ)
    (hI : I.IsKInjective) :
    Function.Bijective (DerivedCategory.Qh.map :
      (P ⟶ (pushforwardMapHomotopy f).obj
        ((HomotopyCategory.quotient
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          (ComplexShape.up ℤ)).obj I)) → _) := by
  set Iq := (HomotopyCategory.quotient
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (ComplexShape.up ℤ)).obj I with hIq
  have : IsIso ((derivedPushforwardUnit f).app Iq) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ _ _ _ I hI
  let e₁ : (DerivedCategory.Qh.obj P ⟶ DerivedCategory.Qh.obj
      ((pushforwardMapHomotopy f).obj Iq)) ≃
      (DerivedCategory.Qh.obj P ⟶ (derivedPushforward f).obj (DerivedCategory.Qh.obj Iq)) :=
    (asIso ((derivedPushforwardUnit f).app Iq)).homToEquiv
  let e₂ : (DerivedCategory.Qh.obj ((pullbackMapHomotopy f).obj P) ⟶ DerivedCategory.Qh.obj Iq) ≃
      ((derivedPullback f).obj (DerivedCategory.Qh.obj P) ⟶ DerivedCategory.Qh.obj Iq) :=
    (asIso ((derivedPullbackComparison f).app P)).symm.homFromEquiv
  have hu : Function.Bijective
      (fun q => ((derivedAdjunction f).homEquiv (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj Iq)).symm (q ≫ (derivedPushforwardUnit f).app Iq)) :=
    (((derivedAdjunction f).homEquiv (DerivedCategory.Qh.obj P)
      (DerivedCategory.Qh.obj Iq)).symm.bijective).comp e₁.bijective
  refine (Function.Bijective.of_comp_iff' hu _).1 ?_
  have hfun : (fun q => ((derivedAdjunction f).homEquiv (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj Iq)).symm (q ≫ (derivedPushforwardUnit f).app Iq)) ∘
      (DerivedCategory.Qh.map : (P ⟶ (pushforwardMapHomotopy f).obj Iq) → _) =
      e₂ ∘ (DerivedCategory.Qh.map :
          ((pullbackMapHomotopy f).obj P ⟶ Iq) → _) ∘
        ((pullbackAdjPushforwardMapHomotopy f).homEquiv P Iq).symm :=
    funext fun g => derivedAdjunction_homEquiv_symm_qh_map f P Iq g
  have := hI
  exact hfun ▸ (e₂.bijective.comp
    ((CochainComplex.IsKInjective.Qh_map_bijective ((pullbackMapHomotopy f).obj P) I).comp
      ((pullbackAdjPushforwardMapHomotopy f).homEquiv P Iq).symm.bijective))

/-- The image of a quasi-isomorphism in the derived category, through the homotopy category, is
invertible. -/
private theorem isIso_qh_map_quotient_map_of_quasiIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (s : K ⟶ L) (hs : QuasiIso s) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map s)) := by
  rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff]
  exact hs

omit [IsGrothendieckAbelian.{w'}
    (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))] in
/-- **Postcomposition with a K-injective resolution of `f_* I`, shifted, is bijective** on
morphisms out of an object at which `Lf^* ⟶ f^*` is invertible. Localization is bijective on
morphisms into `(f_* I)⟦n⟧` (by `bijective_qh_map_pushforward_of_isKInjective` at `I⟦n⟧`, the
direct image commuting with the shift) and into `J⟦n⟧`, and in the derived category
postcomposition with `Q(s⟦n⟧)` is bijective because `s⟦n⟧` is a quasi-isomorphism. -/
theorem bijective_postcomp_quotient_shift_of_isKInjective
    (P : HomotopyCategory
        (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (ComplexShape.up ℤ))
    [IsIso ((derivedPullbackComparison f).app P)]
    (I : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) ℤ)
    (hI : I.IsKInjective)
    {J : CochainComplex
        (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) ℤ}
    (s : ((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) (n : ℤ) :
    Function.Bijective
      (fun a : P ⟶ (HomotopyCategory.quotient
          (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
            (ComplexShape.up ℤ)).obj
          ((((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)⟦n⟧) =>
        a ≫ (HomotopyCategory.quotient
            (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
          (ComplexShape.up ℤ)).map (s⟦n⟧')) := by
  have := hI
  have := hJ
  have := hs
  let Q := HomotopyCategory.quotient
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
    (ComplexShape.up ℤ)
  let e : Q.obj (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (I⟦n⟧)) ≅
      Q.obj ((((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)⟦n⟧) :=
    Q.mapIso ((((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
      n).app I)
  have h₀ : Function.Bijective (DerivedCategory.Qh.map : (P ⟶ Q.obj
      (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (I⟦n⟧))) → _) :=
    bijective_qh_map_pushforward_of_isKInjective f P (I⟦n⟧) inferInstance
  have hleft : Function.Bijective (DerivedCategory.Qh.map : (P ⟶ Q.obj
      ((((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)⟦n⟧)) → _) := by
    have hc : (DerivedCategory.Qh.map : (P ⟶ Q.obj
          ((((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)⟦n⟧)) → _) ∘
          e.homToEquiv =
        (DerivedCategory.Qh.mapIso e).homToEquiv ∘ (DerivedCategory.Qh.map : (P ⟶ Q.obj
          (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (I⟦n⟧))) → _) :=
      funext fun a => DerivedCategory.Qh.map_comp a e.hom
    exact (Function.Bijective.of_comp_iff _ e.homToEquiv.bijective).1
      (hc ▸ (DerivedCategory.Qh.mapIso e).homToEquiv.bijective.comp h₀)
  have := isIso_qh_map_quotient_map_of_quasiIso (s⟦n⟧') inferInstance
  have hright := CochainComplex.IsKInjective.Qh_map_bijective P (J⟦n⟧)
  have hcomp : (DerivedCategory.Qh.map : (P ⟶ Q.obj (J⟦n⟧)) → _) ∘
        (fun a : P ⟶ Q.obj ((((pushforwardModules f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)⟦n⟧) => a ≫ Q.map (s⟦n⟧')) =
      (asIso (DerivedCategory.Qh.map (Q.map (s⟦n⟧')))).homToEquiv ∘
        (DerivedCategory.Qh.map : (P ⟶ Q.obj ((((pushforwardModules f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)⟦n⟧)) → _) :=
    funext fun a => DerivedCategory.Qh.map_comp a _
  exact (Function.Bijective.of_comp_iff' hright _).1
    (hcomp ▸ (asIso (DerivedCategory.Qh.map (Q.map (s⟦n⟧')))).homToEquiv.bijective.comp hleft)

omit [IsGrothendieckAbelian.{w}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))]
  [IsGrothendieckAbelian.{w'}
    (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))] in
/-- **The comparison `Lf^* ⟶ f^*` is invertible at `𝒪_D[0]`**, a K-flat complex with flat
terms (Stacks 06YY at the resolving class of Stacks 06YS). -/
theorem isIso_derivedPullbackComparison_app_single_unit :
    IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient
          (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
        (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
            (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) 0).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))))) :=
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.isIso_derivedPullbackComparison_app_isKFlat
    f _ (isKFlat_single_unit Y)

omit [IsGrothendieckAbelian.{w'}
    (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))] in
/-- **The degree-`n` piece, in abelian groups.** The map that a K-injective resolution `s` of
`f_* I` induces on the degree-`n` cohomology of the complexes of global sections, read in abelian
groups, is invertible: global sections are corepresented by the structure sheaf
(`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`), so the induced map is the one on
the cohomology of a Hom complex out of `𝒪_D[0]`, and
`Stacks.Injectives.isIso_homologyMap_homComplexPostcomp` reduces its invertibility to
`bijective_postcomp_quotient_shift_of_isKInjective`. -/
theorem isIso_homologyMap_globalSections_forget_map
    (I : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) ℤ)
    (hI : I.IsKInjective)
    {J : CochainComplex
        (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) ℤ}
    (s : ((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      (((globalSectionsFunctor.{u', v', w', w'}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
        forget₂ (ModuleCat.{max u' w'}
            (RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj))
          AddCommGrpCat.{max u' w'}).mapHomologicalComplex (ComplexShape.up ℤ)).map s) n) := by
  have := isIso_derivedPullbackComparison_app_single_unit f
  have : IsIso (HomologicalComplex.homologyMap (homComplexPostcomp
      ((CochainComplex.singleFunctor
          (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) 0).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) s) n) :=
    Stacks.Injectives.isIso_homologyMap_homComplexPostcomp _ s n
      (bijective_postcomp_quotient_shift_of_isKInjective f _ I hI s hJ hs n)
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (coyonedaUnitGlobalSectionsIso (J := Y.J)
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u' w'} (ComplexShape.up ℤ) n)) s).1 ?_
  exact isIso_homologyMap_coyonedaComplexMap _ s n

omit [IsGrothendieckAbelian.{w'}
    (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))] in
/-- **Global sections carry a K-injective resolution of `f_* I` to a quasi-isomorphism** of
complexes of `Γ(𝒪_D)`-modules. The degreewise statement is
`isIso_homologyMap_globalSections_forget_map`, in abelian groups; `forget₂` preserves and
reflects homology. -/
theorem quasiIso_globalSections_map
    (I : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) ℤ)
    (hI : I.IsKInjective)
    {J : CochainComplex
        (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) ℤ}
    (s : ((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) :
    QuasiIso (((globalSectionsFunctor.{u', v', w', w'}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{max u' w'}
        (RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj))
      AddCommGrpCat.{max u' w'}), quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_globalSections_forget_map f I hI s hJ hs n

/-- **`f_* I` computes `RΓ(D, -)`, read over any ring mapping to `Γ(𝒪_D)`.** For every
K-injective complex `I` of `𝒪_C`-modules and every ring map `ψ : R ⟶ Γ(𝒪_D)`, the comparison of
the derived functor of `Γ(D, -)` followed by restriction of scalars along `ψ` is invertible at
`f_* I`. Testing on a K-injective resolution `s : f_* I ⟶ J` reduces this to `Γ(D, s)` being a
quasi-isomorphism, `quasiIso_globalSections_map`, restriction of scalars being exact. -/
theorem computesSecond_pushforwardModules_globalSections {R : Type*} [Ring R]
    [HasDerivedCategory (ModuleCat.{max u' w'} R)]
    (ψ : R →+* RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj) :
    Stacks.Cohomology.LerayUnbounded.ComputesSecond (pushforwardModules f)
      (globalSectionsFunctor.{u', v', w', w'}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
        ModuleCat.restrictScalars ψ) := by
  intro I hI
  obtain ⟨J, s, hJ, hs⟩ := Stacks.Cohomology.Localization.enoughKInjectives
    (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have : QuasiIso (((globalSectionsFunctor.{u', v', w', w'}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s) :=
    quasiIso_globalSections_map f I hI s hJ hs
  have hq : QuasiIso (((globalSectionsFunctor.{u', v', w', w'}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
      ModuleCat.restrictScalars ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
    inferInstanceAs (QuasiIso (((ModuleCat.restrictScalars ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (((globalSectionsFunctor.{u', v', w', w'}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map s)))
  refine Stacks.Cohomology.LerayUnbounded.isIso_of_comp_sq
    ((Stacks.Cohomology.LerayUnbounded.totalDerivedUnit
      (globalSectionsFunctor.{u', v', w', w'}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
        ModuleCat.restrictScalars ψ)).naturality
      ((HomotopyCategory.quotient
          (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
        (ComplexShape.up ℤ)).map s)) ?_ ?_ ?_
  · exact isIso_qh_map_quotient_map_of_quasiIso _ hq
  · have := hJ
    exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ J
  · have := isIso_qh_map_quotient_map_of_quasiIso s hs
    exact ((Stacks.DerivedFunctor.totalRightDerived
      (globalSectionsFunctor.{u', v', w', w'}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
        ModuleCat.restrictScalars ψ)).mapIso
      (asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient
        (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
            (ComplexShape.up ℤ)).map s)))).isIso_hom

end Leray

/-! ### The global-sections clause of Stacks 0D6H -/

section LerayIso

variable {X : RingedTopos.{v, max u t, max w t s}} {Y : RingedTopos.{v', max u s, max w t s}}
  [X.J.HasSheafCompose (forget RingCat.{max w t s})]
  [Y.J.HasSheafCompose (forget RingCat.{max w t s})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max w t s} RingCat.{max w t s})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max w t s} RingCat.{max w t s})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max w t s})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{max w t s})]
  [HasSheafify X.J AddCommGrpCat.{max w t s}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max w t s}]
  [HasSheafify Y.J AddCommGrpCat.{max w t s}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max w t s}]
  [HasSheafify X.J (Type (max w t s))] [HasSheafify Y.J (Type (max w t s))]
  [IsGrothendieckAbelian.{max w t s}
      (SheafOfModules.{max w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))]
  [IsGrothendieckAbelian.{max w t s}
      (SheafOfModules.{max w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))]
  (f : RingedToposHom X Y)

/-- **The underived identity behind the global-sections clause of Stacks 0D6H:**
`Γ(D, f_* M) = Γ(C, M)` as `Γ(𝒪_D)`-modules, naturally in the `𝒪_C`-module `M`, the right hand
side read through restriction of scalars along `toposGlobalSectionsRingHom f`. It is
`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIsoGeneral` for the four-field form of
`f`, transported along `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`. -/
def pushforwardModulesCompGlobalSectionsIso :
    pushforwardModules f ⋙ globalSectionsFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ≅
      globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        ModuleCat.restrictScalars (toposGlobalSectionsRingHom f) :=
  Functor.isoWhiskerRight f.toModulesPushforwardIso.symm _ ≪≫
    globalSectionsPushforwardIsoGeneral.{w, v, u, v', t, s} f.toModulesHom

variable {R : Type r} [Ring R] [HasDerivedCategory (ModuleCat.{max u w t s} R)]

/-- **Stacks 0D6H, the global-sections clause, for a morphism of ringed topoi.** Let
`f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi and `ψ : R ⟶ Γ(𝒪_D)` a ring
map. Then `RΓ(D, -) ∘ Rf_* = RΓ(C, -)` as functors `D(𝒪_C) ⟶ D(R)`: derived global sections
on `D` of the unbounded derived direct image, with scalars restricted along `ψ`, are derived
global sections on `C` with scalars restricted along `Γ(𝒪_D) ⟶ Γ(𝒪_C)` and `ψ`. For `ψ` the
identity this is the clause as the source states it, in `D(Γ(𝒪_D))`.

No hypothesis on `f`: `f_* I` computes `RΓ(D, -)` for every K-injective `I`, which is
`computesSecond_pushforwardModules_globalSections`. -/
def derivedGlobalSectionsPushforwardIso
    (ψ : R →+* RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj) :
    derivedPushforward f ⋙ Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
            ModuleCat.restrictScalars ψ) ≅
      Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          ModuleCat.restrictScalars ((toposGlobalSectionsRingHom f).comp ψ)) :=
  Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes (pushforwardModules f)
    (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
        ModuleCat.restrictScalars ψ)
    (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
      ModuleCat.restrictScalars ((toposGlobalSectionsRingHom f).comp ψ))
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardModulesCompGlobalSectionsIso.{v, v', u, w, t, s} f)
        (ModuleCat.restrictScalars ψ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
          (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        (ModuleCat.restrictScalarsComp' ψ (toposGlobalSectionsRingHom f) _ rfl).symm)
    (computesSecond_pushforwardModules_globalSections f ψ)

/-! ### The base change map on global sections -/

variable {R' : Type r'} [Ring R'] [HasDerivedCategory (ModuleCat.{max u w t s} R')]
  (ψ : R →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O).obj)
  (ψ' : R' →+* RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj) (ρ : R' →+* R)
  (h : (toposGlobalSectionsRingHom f).comp ψ' = ψ.comp ρ)

/-- Derived global sections followed by restriction of scalars along `ρ`, read on the derived
category: `RΓ(C, -)` over `R` followed by the exact functor `ρ_*`, is `RΓ(C, -)` over `R'` along
the composite ring map `(toposGlobalSectionsRingHom f).comp ψ' = ψ.comp ρ`. -/
def derivedGlobalSectionsRestrictScalarsIso :
    Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          ModuleCat.restrictScalars ((toposGlobalSectionsRingHom f).comp ψ')) ≅
      Stacks.DerivedFunctor.totalRightDerived
          (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
              ModuleCat.restrictScalars ψ) ⋙
        (ModuleCat.restrictScalars ρ).mapDerivedCategory :=
  Stacks.DerivedFunctor.totalRightDerivedIsoOfIso _
      (Functor.isoWhiskerLeft
          (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          (ModuleCat.restrictScalarsComp' ρ ψ _ h) ≪≫ (Functor.associator _ _ _).symm) ≪≫
    (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
      (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          ModuleCat.restrictScalars ψ)
      (ModuleCat.restrictScalars ρ)).symm

/-- **The semilinear comparison on derived global sections along `f`**:
`RΓ(D, K) ⟶ ρ_* RΓ(C, Lf^* K)` in `D(R')`, for `K ∈ D(𝒪_D)`. It is `RΓ(D, -)` of the unit
`K ⟶ Rf_* Lf^* K` of the derived adjunction of Stacks 07A6, followed by the global-sections
clause of Stacks 0D6H (`derivedGlobalSectionsPushforwardIso`) and the compatibility `h` of the
ring maps. -/
def derivedGlobalSectionsSemilinearMap
    (K : DerivedCategory
        (SheafOfModules.{max w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    (Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
            ModuleCat.restrictScalars ψ')).obj
        K ⟶
      (ModuleCat.restrictScalars ρ).mapDerivedCategory.obj
        ((Stacks.DerivedFunctor.totalRightDerived
          (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
            ModuleCat.restrictScalars ψ)).obj ((derivedPullback f).obj K)) :=
  (Stacks.DerivedFunctor.totalRightDerived
      (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
          ModuleCat.restrictScalars ψ')).map
      ((derivedAdjunction f).unit.app K) ≫
    (derivedGlobalSectionsPushforwardIso.{v, v', u, w, t, s, r'} f ψ').hom.app
        ((derivedPullback f).obj K) ≫
      (derivedGlobalSectionsRestrictScalarsIso.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h).hom.app
        ((derivedPullback f).obj K)

variable {L : DerivedCategory (ModuleCat.{max u w t s} R') ⥤
    DerivedCategory (ModuleCat.{max u w t s} R)}
  (adj : L ⊣ (ModuleCat.restrictScalars ρ).mapDerivedCategory)

/-- **The canonical base change map on global sections along a morphism of ringed topoi**:

`RΓ(D, K) ⊗^L_{R'} R ⟶ RΓ(C, Lf^* K)`   in `D(R)`,

for `K ∈ D(𝒪_D)`, where `- ⊗^L_{R'} R` is any left adjoint `L` of restriction of scalars along
`ρ : R' ⟶ R` on the derived categories (Stacks 0GMT). It is the transpose across `adj` of
`derivedGlobalSectionsSemilinearMap`. It is a map, not in general an isomorphism. -/
def derivedGlobalSectionsBaseChangeMap
    (K : DerivedCategory
        (SheafOfModules.{max w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    L.obj ((Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
            ModuleCat.restrictScalars ψ')).obj
          K) ⟶
      (Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          ModuleCat.restrictScalars ψ)).obj ((derivedPullback f).obj K) :=
  (adj.homEquiv _ _).symm
    (derivedGlobalSectionsSemilinearMap.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h K)

/-- **The base change map is the transpose of the semilinear comparison**: read across `adj`, it
is `RΓ(D, -)` of the unit `K ⟶ Rf_* Lf^* K` followed by the identification of Stacks 0D6H. This
determines the map. -/
theorem derivedGlobalSectionsBaseChangeMap_homEquiv
    (K : DerivedCategory
        (SheafOfModules.{max w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    adj.homEquiv _ _
        (derivedGlobalSectionsBaseChangeMap.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h adj K) =
      derivedGlobalSectionsSemilinearMap.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h K :=
  Equiv.apply_symm_apply _ _

end LerayIso

end Stacks.Cohomology.LerayOfToposHom

end

end
