module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeConormal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.SupportedTensorPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDegreeCBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ConormalWedgePair

/-!
# The vertical arrows of the Gysin base-change square of Tag 0G89

Let

```
Z' → X' → S'
↓h   ↓g    ↓t
Z  → X  → S
```

be a commutative diagram of schemes whose left square is cartesian, with `i : Z ⟶ X` and
`i' : Z' ⟶ X'` closed immersions. [Stacks, Tag 0G89] compares the Gysin maps of the two closed
immersions through a square whose vertical arrows are built in this file:

* the **left vertical arrow**, functoriality of relative differential forms along `h`, as a
  morphism of sheaves `i_*Ω^p_{Z/S} ⟶ g_* i'_*Ω^p_{Z'/S'}` on `X`:
  `Stacks.Gysin.gysinBaseChangeSourceHom`;
* the **right vertical arrow**, `g^*(i_*ℋ^c_Z(Ω^{p+c}_{X/S})) ⟶ i'_*ℋ^c_{Z'}(Ω^{p+c}_{X'/S'})`,
  built as the source builds it: the map of Cohomology, Remark [Stacks, Tag 0G78],
  `Lg^* i_*R𝓗_Z(K) ⟶ i'_*R𝓗_{Z'}(Lg^*K)`, followed by `i'_*R𝓗_{Z'}` of the derived-to-ordinary
  comparison and functoriality of differentials `Lg^*K ⟶ K'`, read in degree `c`. Passing from
  `ℋ^c(Lg^*(-))` to `g^*ℋ^c(-)` needs the vanishing of the local cohomology sheaves above degree
  `c`, [Stacks, Tag 0G7N]; that is `isLE_supportPush_range_of_conormalRank`, proved at the
  hypotheses of [Stacks, Tag 0G86], `c = 0` included. The arrow is
  `Stacks.Gysin.gysinBaseChangePull`, and its transpose along `g^* ⊣ g_*` in the spelling of the
  cohomological Gysin map is `Stacks.Gysin.gysinBaseChangeTargetHom`.

## Main definitions

* `Stacks.Gysin.formsBaseChangeDerived`: `α : Lg^*(Ω^n_{X/S}[0]) ⟶ Ω^n_{X'/S'}[0]`, the
  derived-to-ordinary comparison followed by `relativeDifferentialFormsMap`.
* `Stacks.Gysin.formsBaseChangeHom`: its ordinary transpose `Ω^n_{X/S} ⟶ g_*Ω^n_{X'/S'}`.
* `Stacks.Gysin.supportedBaseChangeDerived`: `θ = (0G78 map) ≫ i'_*R𝓗_{Z'}(α)`, for an arbitrary
  closed subset and an arbitrary `α`.
* `Stacks.Gysin.supportedBaseChangePull`: `θ` read in degree `c`, through the top-degree
  comparison `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback`.
* `Stacks.Gysin.gysinBaseChangePull`, `Stacks.Gysin.gysinBaseChangeTargetHom`: the right vertical
  arrow of the Gysin square.
* `Stacks.Gysin.gysinBaseChangeSourceHom`: the left vertical arrow of the Gysin square.

## Main results

* `Stacks.Gysin.supportedBaseChangeDerived_comp_counit`: the triangle of [Stacks, Tag 0G78] for
  `θ`: followed by the counit `i'_*R𝓗_{Z'}(K') ⟶ K'` it is `Lg^*` of the counit followed by `α`.
* `Stacks.Gysin.isLE_supportPush_range_of_conormalRank`: [Stacks, Tag 0G7N] at the hypotheses of
  [Stacks, Tag 0G86], for every conormal rank.
* `Stacks.Gysin.range_base_eq_closedSubsetPreimage`: `Z' = g⁻¹(Z)` for a cartesian left square,
  which is the shape [Stacks, Tag 0G78] is stated at.
* `Stacks.Gysin.gysinBaseChangePull_eq`: the right vertical arrow unfolded into `θ`.
* `Stacks.Gysin.gysinBaseChangeSourceHom_app`: the left vertical arrow on sections is
  `Stacks.Gysin.subschemeFormBaseChange`.

## Implementation notes

**`c = 0`.** At rank `0` the closed subset `Z` is clopen. Over `Z` it is cut out by the empty
family, and [Stacks, Tag 0G7N] applies there after excision. Away from `Z` the cohomology sheaves
have no stalks, since `i_*R𝓗_Z` is supported on `Z`.

## References

* [Stacks Project, Tag 0G89](https://stacks.math.columbia.edu/tag/0G89)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7N](https://stacks.math.columbia.edu/tag/0G7N)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Perfect.SupportedFraction (supportPush supportCohomologySheaf
  supportCohomologySheafFunctor)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open Stacks.Perfect.SupportedDerivedBaseChange (supportedPullbackRoute
  supportedPullbackRoute_comp_counit)
open AlgebraicGeometry.RingedSpaceThickening (derivedPullbackSingleObj)
open Stacks.DeRham.GysinCohomologyBaseChange (ambientLocalCohomology)
open Stacks.Perfect.SupportCounitComparison
  (derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

/-- A rearrangement used in term mode, where `rw` cannot see through the two spellings of the
category of modules. -/
theorem transverse_glue_triangle {𝒞 : Type*} [Category 𝒞] {A B D E F : 𝒞} (r : A ⟶ B)
    (m : B ⟶ D) (e : D ⟶ F) (e₂ : B ⟶ E) (a : E ⟶ F) (l : A ⟶ E)
    (h₁ : m ≫ e = e₂ ≫ a) (h₂ : r ≫ e₂ = l) : (r ≫ m) ≫ e = l ≫ a := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂]

/-- Inverting the two vertical isomorphisms of a commuting square. -/
theorem transverse_inv_square {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞} (a : A ⟶ B)
    (x : A ⟶ C) (y : B ⟶ D) (b : C ⟶ D) (xi : C ⟶ A) (yi : D ⟶ B) (h : a ≫ y = x ≫ b)
    (hx : xi ≫ x = 𝟙 _) (hy : y ≫ yi = 𝟙 _) : xi ≫ a = b ≫ yi := by
  calc xi ≫ a = xi ≫ a ≫ y ≫ yi := by rw [hy, comp_id]
    _ = (xi ≫ x) ≫ b ≫ yi := by rw [← assoc a, h]; simp only [assoc]
    _ = b ≫ yi := by rw [hx, id_comp]

/-- The rearrangement behind `supportedBaseChangeDerived_naturality`, at variables. -/
theorem transverse_naturality_chain {𝒞 : Type*} [Category 𝒞] {A B C D E F : 𝒞}
    (Lw : A ⟶ B) (θβ : B ⟶ C) (ε : C ⟶ F) (θw : A ⟶ C) (Lε₂ : B ⟶ D) (β : D ⟶ F)
    (Lε₁ : A ⟶ E) (Lw' : E ⟶ D)
    (t₁ : θβ ≫ ε = Lε₂ ≫ β) (t₂ : θw ≫ ε = Lε₁ ≫ Lw' ≫ β) (n : Lw ≫ Lε₂ = Lε₁ ≫ Lw') :
    (Lw ≫ θβ) ≫ ε = θw ≫ ε := by
  rw [assoc, t₁, t₂, ← assoc, n, assoc]

section Coefficients

variable {X X' S S' : Scheme.{u}} (g : X' ⟶ X) (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)
  (hcomm : g ≫ π = π' ≫ t)

/-- **The derived arrow on coefficients** `Lg^*(Ω^n_{X/S}[0]) ⟶ Ω^n_{X'/S'}[0]`: the
derived-to-ordinary comparison followed by functoriality of relative differential forms. -/
def formsBaseChangeDerived (n : ℤ) :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (relativeDifferentialForms π n)) ⟶
      (DerivedCategory.singleFunctor X'.Modules 0).obj (relativeDifferentialForms π' n) :=
  derivedPullbackSingleObj g.toLRSHom.toShHom (relativeDifferentialForms π n) ≫
    (DerivedCategory.singleFunctor X'.Modules 0).map
      (relativeDifferentialFormsMap g π π' t hcomm n)

/-- **The ambient arrow** `Ω^n_{X/S} ⟶ g_*Ω^n_{X'/S'}`: the transpose along `g^* ⊣ g_*` of
functoriality of relative differential forms. -/
def formsBaseChangeHom (n : ℤ) :
    relativeDifferentialForms π n ⟶
      (modulePushforward g.toLRSHom.toShHom).obj (relativeDifferentialForms π' n) :=
  (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
    (relativeDifferentialFormsMap g π π' t hcomm n)

end Coefficients

section HomExt

/-- For an adjunction `F ⊣ G`, if the counit is invertible at `F(G K)` then `F(G(counit_K))` is
invertible. -/
theorem isIso_map_map_counit_app {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) (K : D) [IsIso (adj.counit.app (F.obj (G.obj K)))] :
    IsIso (F.map (G.map (adj.counit.app K))) := by
  have : IsIso (F.map (adj.unit.app (G.obj K))) := by
    rw [show F.map (adj.unit.app (G.obj K)) = CategoryTheory.inv (adj.counit.app (F.obj (G.obj K)))
      from IsIso.eq_inv_of_inv_hom_id (adj.left_triangle_components (G.obj K))]
    infer_instance
  have hcomp : F.map (adj.unit.app (G.obj K)) ≫ F.map (G.map (adj.counit.app K)) = 𝟙 _ := by
    rw [← F.map_comp, adj.right_triangle_components K]
    exact F.map_id _
  rw [IsIso.eq_inv_of_hom_inv_id hcomp]
  infer_instance

/-- For an adjunction `F ⊣ G` whose counit is invertible at `A` and at `F(G K)`, maps
`A ⟶ F(G K)` are determined by their composite with the counit at `K`. -/
theorem adjunction_hom_ext_of_isIso_counit {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {A K : D} [IsIso (adj.counit.app A)]
    [IsIso (adj.counit.app (F.obj (G.obj K)))] {α β : A ⟶ F.obj (G.obj K)}
    (h : α ≫ adj.counit.app K = β ≫ adj.counit.app K) : α = β := by
  have := isIso_map_map_counit_app adj K
  have hmap : F.map (G.map α) = F.map (G.map β) := by
    refine (cancel_mono (F.map (G.map (adj.counit.app K)))).1 ?_
    rw [← F.map_comp, ← G.map_comp, h, G.map_comp, F.map_comp]
  refine (cancel_epi (adj.counit.app A)).1 ?_
  exact (adj.counit_naturality α).symm.trans ((congrArg (· ≫ _) hmap).trans
    (adj.counit_naturality β))

variable {Y : RingedSpace.{u, u}} {T : Set Y.carrier} (hT : IsClosed T)

/-- **Maps into `i_*R𝓗_T(K)` out of a complex supported on `T` are determined by their composite
with the counit**, on a ringed space. -/
theorem derivedSupportedPushforward_hom_ext
    {A K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (hA : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing Y) T A)
    {α β : A ⟶ (derivedSupportedPushforward Y T hT).obj K}
    (h : letI := pushforward_preservesFiniteLimits Y T
      letI := pushforward_preservesFiniteColimits Y T hT
      α ≫ (derivedPushforwardAdjunction Y T hT).counit.app K =
        β ≫ (derivedPushforwardAdjunction Y T hT).counit.app K) : α = β := by
  let := pushforward_preservesFiniteLimits Y T
  let := pushforward_preservesFiniteColimits Y T hT
  have hcounit := derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit Y T hT
  have hLRK : IsIso ((derivedPushforwardAdjunction Y T hT).counit.app
      ((derivedSupportedPushforward Y T hT).obj K)) :=
    hcounit ▸
      Stacks.Perfect.SupportedQuasicoherent.isIso_derivedSupportedSectionsToId_app_of_supported
      Y T hT _ (pushforward_supported Y T hT _)
  have hA' : IsIso ((derivedPushforwardAdjunction Y T hT).counit.app A) :=
    hcounit ▸
      Stacks.Perfect.SupportedQuasicoherent.isIso_derivedSupportedSectionsToId_app_of_supported
      Y T hT A hA
  have : IsIso ((derivedPushforwardAdjunction Y T hT).counit.app
      (((modulePushforward (closedSubsetInclusion Y T)).mapDerivedCategory).obj
        ((derivedSupportedSectionsOnClosed Y T hT).obj K))) := hLRK
  exact adjunction_hom_ext_of_isIso_counit (derivedPushforwardAdjunction Y T hT) h

end HomExt

section Derived

variable {X X' : RingedSpace.{u, u}} (g : X' ⟶ X) (Zs : Set X.carrier) (hZs : IsClosed Zs)

/-- **The derived arrow `θ`**: the map of Cohomology, Remark [Stacks, Tag 0G78], read on `X`
as `Lg^* i_*R𝓗_Z(K) ⟶ i'_*R𝓗_{Z'}(Lg^*K)` (`supportedPullbackRoute`), followed by
`i'_*R𝓗_{Z'}(α)`. -/
def supportedBaseChangeDerived
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (α : (derivedPullback g).obj K ⟶ K') :
    (derivedPullback g).obj ((derivedSupportedPushforward X Zs hZs).obj K) ⟶
      (derivedSupportedPushforward X'
          (closedSubsetPreimage g Zs)
          (isClosed_closedSubsetPreimage g Zs hZs)).obj K' :=
  supportedPullbackRoute g Zs hZs K ≫
    (derivedSupportedPushforward X'
          (closedSubsetPreimage g Zs)
          (isClosed_closedSubsetPreimage g Zs hZs)).map α

/-- **The triangle of [Stacks, Tag 0G78] for θ.** -/
theorem supportedBaseChangeDerived_comp_counit
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (α : (derivedPullback g).obj K ⟶ K') :
    letI := pushforward_preservesFiniteLimits X Zs
    letI := pushforward_preservesFiniteColimits X Zs hZs
    letI := pushforward_preservesFiniteLimits X'
      (closedSubsetPreimage g Zs)
    letI := pushforward_preservesFiniteColimits X'
      (closedSubsetPreimage g Zs)
      (isClosed_closedSubsetPreimage g Zs hZs)
    supportedBaseChangeDerived g Zs hZs α ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage g Zs)
          (isClosed_closedSubsetPreimage g Zs hZs)).counit.app K' =
      (derivedPullback g).map
          ((derivedPushforwardAdjunction X Zs hZs).counit.app K) ≫ α := by
  exact transverse_glue_triangle _ _ _ _ _ _
    ((derivedPushforwardAdjunction X' (closedSubsetPreimage g Zs)
      (isClosed_closedSubsetPreimage g Zs hZs)).counit.naturality α)
    (supportedPullbackRoute_comp_counit g Zs hZs K)

/-- **`θ` in degree `c`, as a map out of `g^*ℋ^c`.** When `i_*R𝓗_Z(K)` has no cohomology above
degree `c`, the top-degree comparison identifies `H^c(Lg^*(-))` with `g^*H^c(-)`, and this is its
inverse followed by `H^c(θ)`. -/
def supportedBaseChangePull (c : ℤ)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (α : (derivedPullback g).obj K ⟶ K')
    (hLE : ((derivedSupportedPushforward X Zs hZs).obj K).IsLE c) :
    (modulePullback g).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) c).obj
          ((derivedSupportedPushforward X Zs hZs).obj K)) ⟶
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X')) c).obj
        ((derivedSupportedPushforward X'
          (closedSubsetPreimage g Zs)
          (isClosed_closedSubsetPreimage g Zs hZs)).obj K') :=
  (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
      g ((derivedSupportedPushforward X Zs hZs).obj K) c hLE).inv ≫
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X')) c).map
      (supportedBaseChangeDerived g Zs hZs α)

/-- The derived pullback of `i_*R𝓗_T(K)` is supported on the preimage of `T`. -/
theorem cohomologySupportedOn_derivedPullback_supportPush
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X')
      (closedSubsetPreimage g Zs)
      ((derivedPullback g).obj ((derivedSupportedPushforward X Zs hZs).obj K)) :=
  cohomologySupportedOn_derivedPullback g Zs _ (pushforward_supported X Zs hZs _)

/-- `θ` is functorial in the coefficient on the target. -/
theorem supportedBaseChangeDerived_comp_map
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {K' K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (α : (derivedPullback g).obj K ⟶ K') (v : K' ⟶ K'') :
    supportedBaseChangeDerived g Zs hZs (α ≫ v) =
      supportedBaseChangeDerived g Zs hZs α ≫
        (derivedSupportedPushforward X' (closedSubsetPreimage g Zs)
          (isClosed_closedSubsetPreimage g Zs hZs)).map v := by
  simp only [supportedBaseChangeDerived, Functor.map_comp, assoc]

/-- **`θ` is natural in the coefficient on the source.** -/
theorem supportedBaseChangeDerived_naturality
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))} (w : K₁ ⟶ K₂)
    (β : (derivedPullback g).obj K₂ ⟶ K') :
    (derivedPullback g).map ((derivedSupportedPushforward X Zs hZs).map w) ≫
        supportedBaseChangeDerived g Zs hZs β =
      supportedBaseChangeDerived g Zs hZs ((derivedPullback g).map w ≫ β) := by
  refine derivedSupportedPushforward_hom_ext _
    (cohomologySupportedOn_derivedPullback_supportPush g Zs hZs K₁) ?_
  have t₁ := supportedBaseChangeDerived_comp_counit g Zs hZs β
  have t₂ := supportedBaseChangeDerived_comp_counit g Zs hZs ((derivedPullback g).map w ≫ β)
  have n := congrArg (derivedPullback g).map
    ((derivedPushforwardAdjunction X Zs hZs).counit.naturality w)
  simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at n
  exact transverse_naturality_chain _ _ _ _ _ _ _ _ t₁ t₂ n

/-- **The right vertical arrow is functorial in the coefficient on the target.** -/
theorem supportedBaseChangePull_comp_map (c : ℤ)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {K' K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (α : (derivedPullback g).obj K ⟶ K') (v : K' ⟶ K'')
    (hLE : ((derivedSupportedPushforward X Zs hZs).obj K).IsLE c) :
    supportedBaseChangePull g Zs hZs c (α ≫ v) hLE =
      supportedBaseChangePull g Zs hZs c α hLE ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X')) c).map
          ((derivedSupportedPushforward X' (closedSubsetPreimage g Zs)
            (isClosed_closedSubsetPreimage g Zs hZs)).map v) := by
  simp only [supportedBaseChangePull, supportedBaseChangeDerived_comp_map, Functor.map_comp, assoc]

/-- **The right vertical arrow is natural in the coefficient on the source.** -/
theorem supportedBaseChangePull_naturality (c : ℤ)
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))} (w : K₁ ⟶ K₂)
    (β : (derivedPullback g).obj K₂ ⟶ K')
    (hLE₁ : ((derivedSupportedPushforward X Zs hZs).obj K₁).IsLE c)
    (hLE₂ : ((derivedSupportedPushforward X Zs hZs).obj K₂).IsLE c) :
    (modulePullback g).map ((DerivedCategory.homologyFunctor _ c).map
        ((derivedSupportedPushforward X Zs hZs).map w)) ≫
        supportedBaseChangePull g Zs hZs c β hLE₂ =
      supportedBaseChangePull g Zs hZs c ((derivedPullback g).map w ≫ β) hLE₁ := by
  have hn := transverse_inv_square _ _ _ _ _ _
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback_hom_naturality
      g ((derivedSupportedPushforward X Zs hZs).map w) c hLE₁ hLE₂)
    (Iso.inv_hom_id _) (Iso.hom_inv_id _)
  simp only [supportedBaseChangePull, ← supportedBaseChangeDerived_naturality]
  rw [← assoc, ← hn, assoc, Functor.map_comp]

end Derived


section Vanishing

open Stacks.AlgebraicGeometry.ConormalEquations

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]

/-- The common zero locus of an empty family is everything. -/
theorem equationsClosedSet_fin_zero {Y : Scheme.{u}} (f : Fin 0 → Γ(Y, ⊤)) :
    Stacks.Perfect.CechDerivedSupport.equationsClosedSet f = Set.univ := by
  ext y
  simp [Stacks.Perfect.CechDerivedSupport.equationsClosedSet]

/-- **[Stacks, Tag 0G7N] at the hypotheses of [Stacks, Tag 0G86]**: for a closed immersion of
finite presentation whose conormal sheaf is locally free of rank `c`, `i_*R𝓗_Z(ℱ)` has no
cohomology above degree `c` for quasi-coherent `ℱ`. Every `c` is allowed, `0` included. -/
theorem isLE_supportPush_range_of_conormalRank {c : ℕ} (hE : ConormalRank i c)
    (F : X.Modules) [F.IsQuasicoherent] :
    ((supportPush (isClosed_range_base i)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsLE (c : ℤ) := by
  match c, hE with
  | d + 1, hE =>
    refine isLE_derivedSupportedPushforward_of_locallyCutOut (Set.range i.base)
      (isClosed_range_base i) (d + 1) (fun x => ?_) F
    have hx : x ∈ (⨆ a : EquationChart i (d + 1), a.ambient : X.Opens) := by
      rw [iSup_equationChart_ambient i hE]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨a.ambient, ha, restrictEquations a.ambient a.equations,
      (equationsClosedSet_restrictEquations i a.ambient
        (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)).symm⟩
  | 0, hE =>
    have hopen : IsOpen (Set.range i.base) := isOpen_range_base_of_conormalRank_zero i hE
    let W : X.Opens := ⟨Set.range i.base, hopen⟩
    have hTW : IsClosed (W.ι ⁻¹' Set.range i.base) :=
      (isClosed_range_base i).preimage W.ι.continuous
    rw [DerivedCategory.isLE_iff]
    intro n hn
    refine isZero_of_forall_isZero_stalk _ fun x => ?_
    by_cases hx : x ∈ Set.range i.base
    · refine Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict
        W _ x hx ?_
      refine IsZero.of_iso ?_ (supportCohomologyRestrictIso W (isClosed_range_base i) hTW n F)
      have hLE := isLE_derivedSupportedPushforward_of_locallyCutOut (W.ι ⁻¹' Set.range i.base)
        hTW 0 (fun y => ⟨⊤, trivial, Fin.elim0, by
          rw [equationsClosedSet_fin_zero]
          ext z
          simp only [Set.mem_preimage, Set.mem_univ, iff_true]
          exact z.1.2⟩) ((Scheme.Modules.restrictFunctor W.ι).obj F)
      exact @DerivedCategory.isZero_of_isLE _ _ _ _ _ 0 n hn hLE
    · exact Stacks.Perfect.SupportedQuasicoherent.cohomologySupportedOn_derivedSupportedPushforward
        X _ (isClosed_range_base i) _ n x hx

end Vanishing

section Gysin

variable {Z X S Z' X' S' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z) (g : X' ⟶ X)
  (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)

/-- **`Z' = g⁻¹(Z)`**, as closed subsets, for a cartesian left square. -/
theorem range_base_eq_closedSubsetPreimage (hcart : IsPullback h i' i g) :
    Set.range i'.base = closedSubsetPreimage g.toLRSHom.toShHom (Set.range i.base) :=
  range_eq_preimage_range_of_isPullback hcart.flip

/-- `i_*ℋ^c_T(ℱ)` depends only on the closed subset `T`. -/
theorem homology_supportPush_congr {Y : Scheme.{u}} {T T' : Set Y} (hTT' : T = T')
    (hT : IsClosed T) (hT' : IsClosed T') (n : ℤ) (K : DerivedCategory Y.Modules) :
    (DerivedCategory.homologyFunctor Y.Modules n).obj ((supportPush hT).obj K) =
      (DerivedCategory.homologyFunctor Y.Modules n).obj ((supportPush hT').obj K) := by
  subst hTT'
  rfl

variable [IsClosedImmersion i] [LocallyOfFinitePresentation i] [IsClosedImmersion i']

/-- **The right vertical arrow of the Gysin square of [Stacks, Tag 0G89]**, in the shape
`g^*(i_*ℋ^c_Z(Ω^{p+c}_{X/S})) ⟶ i'_*ℋ^c_{Z'}(Ω^{p+c}_{X'/S'})`. -/
def gysinBaseChangePull (hcart : IsPullback h i' i g) (right_comm : g ≫ π = π' ≫ t) {c : ℕ}
    (p : ℕ) (hE : Stacks.AlgebraicGeometry.ConormalEquations.ConormalRank i c) :
    (Scheme.Modules.pullback g).obj (gysinTarget i π c p) ⟶ gysinTarget i' π' c p :=
  haveI : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p c
  supportedBaseChangePull g.toLRSHom.toShHom (Set.range i.base) (isClosed_range_base i) (c : ℤ)
      (formsBaseChangeDerived g π π' t right_comm ((p : ℤ) + (c : ℤ)))
      (isLE_supportPush_range_of_conormalRank i hE _) ≫
    eqToHom (homology_supportPush_congr (range_base_eq_closedSubsetPreimage i i' h g hcart).symm
      _ (isClosed_range_base i') (c : ℤ) _)

/-- **The right vertical arrow is built from θ.** `gysinBaseChangePull` is the inverse of the
top-degree comparison `H^c(Lg^* K) ≅ g^* H^c(K)` followed by `H^c(θ)`, for
`θ = supportedBaseChangeDerived` at `formsBaseChangeDerived`, and then the identification of the
two spellings `g⁻¹(Z)` and `Z'` of the closed subset. -/
theorem gysinBaseChangePull_eq (hcart : IsPullback h i' i g) (right_comm : g ≫ π = π' ≫ t)
    {c : ℕ} (p : ℕ) (hE : Stacks.AlgebraicGeometry.ConormalEquations.ConormalRank i c) :
    haveI : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
      isQuasicoherent_relativeDifferentialForms_natCast_add π p c
    gysinBaseChangePull i i' h g π π' t hcart right_comm p hE =
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
          g.toLRSHom.toShHom ((supportPush (isClosed_range_base i)).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj
              (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) (c : ℤ)
          (isLE_supportPush_range_of_conormalRank i hE _)).inv ≫
        (DerivedCategory.homologyFunctor X'.Modules (c : ℤ)).map
          (supportedBaseChangeDerived g.toLRSHom.toShHom (Set.range i.base) (isClosed_range_base i)
            (formsBaseChangeDerived g π π' t right_comm ((p : ℤ) + (c : ℤ)))) ≫
        eqToHom (homology_supportPush_congr
          (range_base_eq_closedSubsetPreimage i i' h g hcart).symm _ (isClosed_range_base i')
          (c : ℤ) _) :=
  rfl

/-- **The right vertical arrow of the Gysin square of [Stacks, Tag 0G89], as a morphism of
sheaves on `X`**: `i_*ℋ^c_Z(Ω^{p+c}_{X/S}) ⟶ g_* i'_*ℋ^c_{Z'}(Ω^{p+c}_{X'/S'})`, in the spelling
`ambientLocalCohomology` of the cohomological Gysin map. -/
def gysinBaseChangeTargetHom [IsClosedImmersion i'] (hcart : IsPullback h i' i g)
    (right_comm : g ≫ π = π' ≫ t) {c : ℕ} (p : ℕ)
    (hE : Stacks.AlgebraicGeometry.ConormalEquations.ConormalRank i c) :
    ambientLocalCohomology π (Set.range i.base) (isClosed_range_base i) c p ⟶
      (modulePushforward g.toLRSHom.toShHom).obj
        (ambientLocalCohomology π' (Set.range i'.base) (isClosed_range_base i') c p) :=
  (Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso i π c p).inv ≫
    (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
      (gysinBaseChangePull i i' h g π π' t hcart right_comm p hE) ≫
    (modulePushforward g.toLRSHom.toShHom).map
      (Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso i' π' c p).hom

/-- **The left vertical arrow of the Gysin square, as a morphism of sheaves on `X`**:
`i_*Ω^p_{Z/S} ⟶ g_* i'_*Ω^p_{Z'/S'}`, pullback of relative forms along `h`. -/
def gysinBaseChangeSourceHom (left_comm : h ≫ i = i' ≫ g) (right_comm : g ≫ π = π' ≫ t)
    (n : ℤ) :
    pushforwardRelativeForms i π n ⟶
      (modulePushforward g.toLRSHom.toShHom).obj (pushforwardRelativeForms i' π' n) :=
  (Scheme.Modules.pushforward i).map
      ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (relativeDifferentialFormsMap h (i ≫ π) (i' ≫ π') t (outer_comm left_comm right_comm) n)) ≫
    (Scheme.Modules.pushforwardComp h i).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr left_comm).hom.app _ ≫
    (Scheme.Modules.pushforwardComp i' g).inv.app _

omit [IsClosedImmersion i] [LocallyOfFinitePresentation i] [IsClosedImmersion i'] in
/-- **The left vertical arrow on sections is `subschemeFormBaseChange`.** -/
theorem gysinBaseChangeSourceHom_app (left_comm : h ≫ i = i' ≫ g)
    (right_comm : g ≫ π = π' ≫ t) (n : ℤ) (V : X.Opens)
    (x : Γ(pushforwardRelativeForms i π n, V)) :
    Scheme.Modules.Hom.app (gysinBaseChangeSourceHom i i' h g π π' t left_comm right_comm n) V x =
      subschemeFormBaseChange i i' h g π π' t left_comm right_comm n V x := by
  rfl

end Gysin

end Stacks.Gysin
