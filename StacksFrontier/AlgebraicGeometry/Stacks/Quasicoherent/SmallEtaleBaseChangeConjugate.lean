module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PushforwardIndexIso
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# Conjugates of the comparisons of pullbacks of sheaves of modules on small étale sites

The comparisons `PresheafOfModules.pullbackCongr`, `SheafOfModules.pullbackIso` and
`SheafOfModules.pullbackSquareIso` of pullback functors are characterised by the morphisms of
pushforward functors they are conjugate to under `CategoryTheory.conjugateEquiv`. The pullbacks of
modules along the morphisms of ringed small étale sites, and along the maps `a_{small}^♯` below
the arrows of a category fibred in groupoids, compose, by comparisons conjugate to the
composition laws of the pushforwards.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso`: for `a : X ⟶ Y` and `b : Y ⟶ Z` of
  a big étale site, `ε_b^*` followed by `ε_a^*` is `ε_{b ∘ a}^*`.
* `AlgebraicGeometry.Stack.smallEtalePullbackComparisonCompIso`: for arrows `φ : x ⟶ y` and
  `ψ : y ⟶ z` of `𝒳`, the pullback along `b_{small}^♯` followed by the pullback along
  `a_{small}^♯` is the pullback along `(b ∘ a)_{small}^♯`.
* `AlgebraicGeometry.SmallEtale.smallEtalePushforwardCompIso` and
  `AlgebraicGeometry.Stack.smallEtalePushforwardComparisonCompIso`: the corresponding
  comparisons of the pushforwards.

## Main results

* `PresheafOfModules.conjugateEquiv_pullbackCongr_inv`: the conjugate of
  `PresheafOfModules.pullbackCongr` is the `eqToHom` of the equality of the two pushforwards.
* `SheafOfModules.conjugateEquiv_pullbackIso_hom`: the conjugate of `SheafOfModules.pullbackIso`
  is the identity of the pushforward.
* `SheafOfModules.conjugateEquiv_pullbackSquareIso_inv`: the conjugate of
  `SheafOfModules.pullbackSquareIso` is the comparison of the two composite pushforwards of the
  square.
* `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_comparisonComp`: the composition law
  for the structure maps of the morphisms of ringed small étale sites, as an equality of
  morphisms of sheaves of rings.
* `AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv` and
  `AlgebraicGeometry.Stack.conjugateEquiv_smallEtalePullbackComparisonCompIso_inv`: the two
  composition laws of the pullbacks are conjugate to the composition laws of the pushforwards.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open CategoryTheory

universe v v₁ v₂ u₁ u₂ u u₃ u₄ v₃ v₄

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{v}} {S : Cᵒᵖ ⥤ RingCat.{v}}

/-- For two equal maps `φ = ψ` of presheaves of rings, the comparison of the two pullback
functors is conjugate, with respect to the two pullback-pushforward adjunctions, to the `eqToHom`
of the resulting equality of the two pushforward functors. -/
public theorem conjugateEquiv_pullbackCongr_inv {φ ψ : S ⟶ F.op ⋙ R} (hφψ : φ = ψ)
    [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{v} ψ).IsRightAdjoint] :
    conjugateEquiv (pullbackPushforwardAdjunction.{v} φ)
        (pullbackPushforwardAdjunction.{v} ψ) (pullbackCongr.{v} hφψ).inv =
      eqToHom (congrArg (fun k => pushforward.{v} k) hφψ) := by
  have h := Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (pullbackPushforwardAdjunction.{v} ψ)
    (eqToIso (congrArg (fun k ↦ pushforward.{v} k) hφψ.symm))
    (pullbackPushforwardAdjunction.{v} φ)
  exact Eq.trans (congrArg _ (NatTrans.ext (funext fun _ ↦ rfl))) h

end PresheafOfModules

namespace SheafOfModules

section PullbackIso

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The identification of the pullback of sheaves of modules with the sheafification of the
pullback of presheaves of modules is conjugate to the identity of the pushforward. -/
public theorem conjugateEquiv_pullbackIso_hom :
    conjugateEquiv (PullbackConstruction.adjunction.{v} φ)
        (pullbackPushforwardAdjunction.{v} φ) (pullbackIso.{v} φ).hom = 𝟙 _ :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom
    (pullbackPushforwardAdjunction.{v} φ) (PullbackConstruction.adjunction.{v} φ)

end PullbackIso

section SquareIso

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {a : C ⥤ C'} {b : C' ⥤ D'} {c : C ⥤ D} {d : D ⥤ D'}
  [a.IsContinuous J J'] [b.IsContinuous J' K'] [c.IsContinuous J K] [d.IsContinuous K K']
  [(a ⋙ b).IsContinuous J K'] [(c ⋙ d).IsContinuous J K']
  {RC : Sheaf J RingCat.{u}} {RC' : Sheaf J' RingCat.{u}}
  {RD : Sheaf K RingCat.{u}} {RD' : Sheaf K' RingCat.{u}}
  (φa : RC ⟶ (a.sheafPushforwardContinuous RingCat.{u} J J').obj RC')
  (φb : RC' ⟶ (b.sheafPushforwardContinuous RingCat.{u} J' K').obj RD')
  (φc : RC ⟶ (c.sheafPushforwardContinuous RingCat.{u} J K).obj RD)
  (φd : RD ⟶ (d.sheafPushforwardContinuous RingCat.{u} K K').obj RD')
  [(pushforward.{v} φa).IsRightAdjoint] [(pushforward.{v} φb).IsRightAdjoint]
  [(pushforward.{v} φc).IsRightAdjoint] [(pushforward.{v} φd).IsRightAdjoint]

/-- Round a commuting square of morphisms of ringed sites, the comparison of the two composite
pullbacks is conjugate to the comparison of the two composite pushforwards that the square
supplies: pushforward of a composite, reindexed along the isomorphism `e` of the two composite
continuous functors, and pushforward of the other composite backwards. -/
public theorem conjugateEquiv_pullbackSquareIso_inv (e : a ⋙ b ≅ c ⋙ d)
    (he : comparisonComp φc φd ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K').app RD' =
      comparisonComp φa φb) :
    conjugateEquiv
        ((pullbackPushforwardAdjunction.{v} φa).comp (pullbackPushforwardAdjunction.{v} φb))
        ((pullbackPushforwardAdjunction.{v} φc).comp (pullbackPushforwardAdjunction.{v} φd))
        (pullbackSquareIso.{v} φa φb φc φd e he).inv =
      (pushforwardComp.{v} φc φd ≪≫ pushforwardCongr₂.{v} _ e he ≪≫
        (pushforwardComp.{v} φa φb).symm).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    ((pullbackPushforwardAdjunction.{v} φc).comp (pullbackPushforwardAdjunction.{v} φd))
    (pushforwardComp.{v} φc φd ≪≫ pushforwardCongr₂.{v} _ e he ≪≫
      (pushforwardComp.{v} φa φb).symm)
    ((pullbackPushforwardAdjunction.{v} φa).comp (pullbackPushforwardAdjunction.{v} φb))

end SquareIso

end SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- Base-changing along `b` and then along `a` is a continuous functor of small étale sites. -/
public instance isContinuous_smallEtaleBaseChange_comp :
    (smallEtaleBaseChange B b ⋙ smallEtaleBaseChange B a).IsContinuous
      (topology B Z.obj Z.property) (topology B X.obj X.property) :=
  Functor.isContinuous_comp _ _ _ (topology B Y.obj Y.property) _

/-- The composition law for the structure maps of the morphisms of ringed small étale sites, as a
morphism of sheaves of rings: pulling global functions back along the base-change projection of
`b` and then along that of `a` is pulling them back along the projection of `b ∘ a`, read
through the identification of the two successive base changes with the base change along the
composite. -/
public theorem smallEtaleStructureMapRing_comparisonComp :
    smallEtaleStructureMapRing B (a ≫ b) ≫
        (Functor.sheafPushforwardContinuousNatTrans
            (smallEtaleBaseChange_factoredCompIso B X Y Z a b (a ≫ b) rfl).hom RingCat.{u}
            (topology B Z.obj Z.property) (topology B X.obj X.property)).app
          (structureSheaf B X.obj X.property) =
      SheafOfModules.comparisonComp (smallEtaleStructureMapRing B b)
        (smallEtaleStructureMapRing B a) := by
  apply ObjectProperty.hom_ext
  exact NatTrans.ext (funext fun W ↦ ConcreteCategory.hom_ext _ _ fun r ↦
    (smallEtaleStructureMapRingHom_app_comp B a b W r).symm)

/-- The structure map of the composite of the two morphisms of ringed small étale sites, at the
spelling indexed by the composite of the two base changes. -/
public noncomputable abbrev smallEtaleStructureMapRingComp :
    structureSheaf B Z.obj Z.property ⟶
      ((smallEtaleBaseChange B b ⋙ smallEtaleBaseChange B a).sheafPushforwardContinuous
        RingCat.{u} (topology B Z.obj Z.property) (topology B X.obj X.property)).obj
          (structureSheaf B X.obj X.property) :=
  SheafOfModules.comparisonComp (smallEtaleStructureMapRing B b) (smallEtaleStructureMapRing B a)

/-- The pushforwards of sheaves of modules along the morphisms of ringed small étale sites
compose: the pushforward along `ε_{b ∘ a}` is the pushforward along the composite structure map,
reindexed along the identification of the two successive base changes with the base change along
the composite. -/
public noncomputable abbrev smallEtalePushforwardCompIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (a ≫ b)) ≅
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRingComp B a b) :=
  SheafOfModules.pushforwardCongr₂.{u} _
    (smallEtaleBaseChange_factoredCompIso B X Y Z a b (a ≫ b) rfl)
    (smallEtaleStructureMapRing_comparisonComp B a b)

/-- The pullbacks of sheaves of modules along the morphisms of ringed small étale sites compose:
for `a : X ⟶ Y` and `b : Y ⟶ Z` of a big étale site, pulling a sheaf of modules on the small
étale site of `Z` back along `ε_b` and then along `ε_a` is pulling it back along `ε_{b ∘ a}`. -/
public noncomputable def smallEtalePullbackCompIso :
    SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b) ⋙
        SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a) ≅
      SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (a ≫ b)) :=
  SheafOfModules.pullbackComp.{u} (smallEtaleStructureMapRing B b)
      (smallEtaleStructureMapRing B a) ≪≫
    Adjunction.leftAdjointUniq
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRingComp B a b))
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureMapRing B (a ≫ b))).ofNatIsoRight
          (smallEtalePushforwardCompIso B a b))

/-- The conjugate of `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` is the composite of
the comparison of the two composite pushforwards with the reindexing
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardCompIso`. -/
public theorem conjugateEquiv_smallEtalePullbackCompIso_inv :
    conjugateEquiv
        ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B b)).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a)))
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B (a ≫ b)))
        (smallEtalePullbackCompIso B a b).inv =
      (SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B b)
          (smallEtaleStructureMapRing B a)).hom ≫
        (smallEtalePushforwardCompIso B a b).inv := by
  rw [show (smallEtalePullbackCompIso B a b).inv =
      (Adjunction.leftAdjointUniq
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRingComp B a b))
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B (a ≫ b))).ofNatIsoRight
              (smallEtalePushforwardCompIso B a b))).inv ≫
        (SheafOfModules.pullbackComp.{u} (smallEtaleStructureMapRing B b)
          (smallEtaleStructureMapRing B a)).inv from rfl,
    ← conjugateEquiv_comp _
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRingComp B a b)),
    SheafOfModules.conjugateEquiv_pullbackComp_inv]
  congr 1
  exact Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)

/-- The composite of the maps `a_{small}^♯` below two composable arrows, at the spelling indexed
by the composite of the two base changes. -/
public noncomputable abbrev smallEtaleStructureComparisonComp :
    (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj ⟶
      (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ) ⋙
          smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op ⋙
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
  smallEtaleStructureComparison B E h S hS p hp ψ τ hτ ≫
    Functor.whiskerLeft
      (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).op
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)

/-- The pushforward of presheaves of modules along the map `a_{small}^♯` has a left adjoint. -/
public instance presheafPushforward_smallEtaleStructureComparison_isRightAdjoint :
    (PresheafOfModules.pushforward.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)

/-- The composition law for the maps `a_{small}^♯`, as a morphism of presheaves of rings: the map
below `ψ ∘ φ`, followed by restriction along the identification of the two successive base
changes with the base change along the composite, is the map below `ψ` followed by the map below
`φ`. -/
public theorem smallEtaleStructureComparison_whiskerRight_comp :
    smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ ≫
        Functor.whiskerRight
          (NatIso.op (smallEtaleBaseChangeCompIso B E h S hS p φ ψ).symm).inv
          (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj =
      smallEtaleStructureComparisonComp B E h S hS p hp τ hτ φ ψ :=
  NatTrans.ext (funext fun W ↦ ConcreteCategory.hom_ext _ _ fun r ↦
    (smallEtaleStructureComparison_app_comp B E h S hS p hp τ hτ φ ψ W r).symm)

/-- The pushforwards of presheaves of modules along the maps `a_{small}^♯` compose: the
pushforward along the map below `ψ ∘ φ` is the pushforward along the composite of the maps below
`ψ` and below `φ`, reindexed along the identification of the two successive base changes with
the base change along the composite. -/
public noncomputable def smallEtalePushforwardComparisonCompIso :
    PresheafOfModules.pushforward.{u}
        (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ) ≅
      PresheafOfModules.pushforward.{u}
        (smallEtaleStructureComparisonComp B E h S hS p hp τ hτ φ ψ) :=
  Stacks.PresheafOfModules.pushforwardIsoOfIndexIso.{u}
    (smallEtaleBaseChangeCompIso B E h S hS p φ ψ).symm
    (smallEtaleStructureComparison_whiskerRight_comp B E h S hS p hp τ hτ φ ψ)

/-- The pullbacks of presheaves of modules along the maps `a_{small}^♯` compose: for arrows
`φ : x ⟶ y` and `ψ : y ⟶ z` of `𝒳` lying over `a : U ⟶ V` and `b : V ⟶ W`, pulling a presheaf of
modules on the small étale site of `W` back along `b_{small}^♯` and then along `a_{small}^♯` is
pulling it back along `(b ∘ a)_{small}^♯`. -/
public noncomputable def smallEtalePullbackComparisonCompIso :
    PresheafOfModules.pullback.{u} (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ) ⋙
        PresheafOfModules.pullback.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ) ≅
      PresheafOfModules.pullback.{u}
        (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ) :=
  PresheafOfModules.pullbackComp.{u}
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ) ≪≫
    Adjunction.leftAdjointUniq
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureComparisonComp B E h S hS p hp τ hτ φ ψ))
      ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ)).ofNatIsoRight
          (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ))

/-- The conjugate of `AlgebraicGeometry.Stack.smallEtalePullbackComparisonCompIso` is the
composite of the comparison of the two composite pushforwards with the reindexing
`AlgebraicGeometry.Stack.smallEtalePushforwardComparisonCompIso`. -/
public theorem conjugateEquiv_smallEtalePullbackComparisonCompIso_inv :
    conjugateEquiv
        ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).comp
          (PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)))
        (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ))
        (smallEtalePullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv =
      (PresheafOfModules.pushforwardComp.{u}
          (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).hom ≫
        (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv := by
  rw [show (smallEtalePullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv =
      (Adjunction.leftAdjointUniq
          (PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparisonComp B E h S hS p hp τ hτ φ ψ))
          ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ)).ofNatIsoRight
              (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ))).inv ≫
        (PresheafOfModules.pullbackComp.{u}
          (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).inv from rfl,
    ← conjugateEquiv_comp _
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureComparisonComp B E h S hS p hp τ hτ φ ψ))]
  rw [show conjugateEquiv
        ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).comp
          (PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)))
        (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparisonComp B E h S hS p hp τ hτ φ ψ))
        (PresheafOfModules.pullbackComp.{u}
          (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).inv =
      (PresheafOfModules.pushforwardComp.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).hom from
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _]
  congr 1
  exact Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

end AlgebraicGeometry.Stack
