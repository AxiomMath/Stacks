module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Derived pushforward along a closed immersion is the induced functor on derived categories

Pushforward of sheaves of modules along a morphism of ringed spaces whose underlying map is a
closed embedding is an exact functor, so it induces a functor on unbounded derived categories
directly, without any resolution. That induced functor is canonically the total right derived
functor of pushforward, and this file produces the comparison isomorphism together with the
equation saying that it is compatible with the two canonical maps out of the homotopy category.

## Main definitions

* `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`: for *any* exact additive
  functor between abelian categories with derived categories, the canonical isomorphism between
  the induced functor on derived categories and the chosen total right derived functor.

## Main results

* `Stacks.ClosedImmersion.preservesEpimorphisms_modulePushforward`: pushforward of sheaves of
  modules along a closed embedding of ringed spaces preserves epimorphisms.
* `Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward`: hence it is right exact,
  and (being a right adjoint) exact.
* `Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isIso_base`: the same for
  a morphism whose base map is merely a homeomorphism, the morphism itself being arbitrary. This
  is the case of a thickening and of a retraction of one.
* `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app`: that isomorphism is
  compatible with the two canonical maps out of the homotopy category.
* `Stacks.ClosedImmersion.exists_mapDerivedCategoryIsoTotalRightDerived`: the existential
  packaging of the previous two, which is the form Stacks 0E2K consumes.
* `Stacks.ClosedImmersion.exists_closedImmersionDerivedPushforwardComparison`: the special case
  of a closed immersion of schemes, which is what Stacks 0E2K uses.

## Implementation notes

Exactness is assembled from three ingredients. Left exactness is free: `modulePushforward` is a
right adjoint. Preservation of epimorphisms is the only place the closed-embedding hypothesis
enters, and it is checked on stalks: epimorphisms of sheaves of modules are exactly the locally
surjective morphisms (`Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`), local
surjectivity is surjectivity on all stalks
(`TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`), and the underlying presheaf of
abelian groups of a pushforward of sheaves of modules *is* the pushforward presheaf — the
identification `PresheafOfModules.pushforwardCompToPresheaf` is `Iso.refl`. At a point of the
image, `TopCat.Presheaf.stalkPushforward` is an isomorphism because a closed embedding is
inducing, and `stalkPushforward_naturality` transports surjectivity across it. At a point
outside the image the stalk of the pushforward is a terminal object of `AddCommGrpCat` by
Stacks 00AE (`ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange`), hence zero, so
surjectivity is automatic. Left exactness plus preservation of epimorphisms gives preservation
of homology (`CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels`) and thus
of finite colimits.

The derived-category statement is pure category theory and is proved for a general exact
functor. `Functor.mapDerivedCategoryFactorsh` exhibits `F.mapDerivedCategory` as a lift of
`F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh` through the localization `DerivedCategory.Qh`,
so `Functor.isRightDerivedFunctor_of_inverts` makes it a right derived functor for the
transformation `mapDerivedCategoryFactorsh.inv`. Uniqueness of right derived functors
(`Functor.rightDerivedUnique`) then supplies the isomorphism, and the required equation is its
defining factorization `Functor.rightDerivedNatTrans_app`. In particular the isomorphism is
canonical rather than merely existent; the existential form is the one Stacks 0E2K consumes.

## References

* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open TopCat.Presheaf

namespace Stacks.ClosedImmersion

universe w₁ w₂ v₁ v₂ u₁ u₂ v u

/-! ### Stalks of a pushforward of presheaves -/

attribute [local implicit_reducible] TopCat.Presheaf.stalk TopCat.Presheaf.stalkFunctor in
/-- `TopCat.Presheaf.stalkPushforward` is natural in the presheaf: the stalk at `f x` of the
pushforward of a morphism, followed by the comparison with the stalk of the target at `x`,
agrees with the comparison for the source followed by the stalk of the morphism at `x`. -/
theorem stalkPushforward_naturality {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) {F G : X.Presheaf C} (α : F ⟶ G) (x : X) :
    (stalkFunctor C (f x)).map ((TopCat.Presheaf.pushforward C f).map α) ≫
        G.stalkPushforward C f x =
      F.stalkPushforward C f x ≫ (stalkFunctor C x).map α := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  rw [stalkFunctor_map_germ_assoc, stalkPushforward_germ, stalkPushforward_germ_assoc]
  exact (stalkFunctor_map_germ ((Opens.map f).obj U) x hxU α).symm

/-! ### Exactness of pushforward along a closed embedding of ringed spaces -/

/-- Pushforward of sheaves of modules is additive: on underlying presheaves of abelian groups
it is precomposition with the map of open sets. -/
instance additive_modulePushforward {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) :
    (modulePushforward i).Additive where
  map_add := rfl

/-- **Stacks Project, Tag 08KS.** Pushforward of sheaves of modules is left exact, being a
right adjoint. -/
@[stacks 08KS "exactness only; full faithfulness and the essential image are not covered"]
instance preservesFiniteLimits_modulePushforward
    {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) :
    PreservesFiniteLimits (modulePushforward i) :=
  have : (modulePushforward i).IsRightAdjoint := modulePushforward_isRightAdjoint i
  inferInstance

attribute [local implicit_reducible] TopCat.Presheaf.stalk TopCat.Presheaf.stalkFunctor in
/-- **Stacks Project, Tag 08KS.** Pushforward of sheaves of modules along a morphism of ringed
spaces whose underlying continuous map is a closed embedding preserves epimorphisms.

An epimorphism of sheaves of modules is a locally surjective morphism, equivalently one that is
surjective on every stalk. Over a point in the image of `i` the stalk of the pushforward is the
stalk of the original sheaf, because a closed embedding is inducing; over a point outside the
image it is the zero group, where there is nothing to prove. -/
theorem preservesEpimorphisms_modulePushforward {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    (modulePushforward i).PreservesEpimorphisms where
  preserves {M N} f hf := by
    have hf' : Epi f := hf
    have hsurj : TopCat.Presheaf.IsLocallySurjective
        ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).map f.val) :=
      Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi f
    rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks] at hsurj
    apply Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective
    rw [show Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
        ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
          ((modulePushforward i).map f).val) =
        TopCat.Presheaf.IsLocallySurjective
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i.hom.base).map
            ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).map f.val)) from rfl,
      TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
    intro x
    by_cases hx : x ∈ Set.range (ConcreteCategory.hom i.hom.base)
    · obtain ⟨z, rfl⟩ := hx
      have hiso (P : SheafOfModules (structureSheafRing Z)) : IsIso
          (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.hom.base
            ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).obj P.val) z) :=
        stalkPushforward.stalkPushforward_iso_of_isInducing _ hi.isInducing _ _
      have key := stalkPushforward_naturality i.hom.base
        ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).map f.val) z
      set pfA := TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.hom.base
        ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).obj M.val) z
      set pfB := TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.hom.base
        ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).obj N.val) z
      have h1 : Function.Surjective ⇑(ConcreteCategory.hom
          ((stalkFunctor AddCommGrpCat.{u} (i.hom.base z)).map
            ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i.hom.base).map
              ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).map f.val)) ≫ pfB)) := by
        rw [key]
        exact (hsurj z).comp (ConcreteCategory.bijective_of_isIso pfA).2
      have hinj : Function.Injective ⇑(ConcreteCategory.hom pfB) :=
        (ConcreteCategory.bijective_of_isIso pfB).1
      intro b
      obtain ⟨a, ha⟩ := h1 ((ConcreteCategory.hom pfB) b)
      refine ⟨a, hinj ?_⟩
      simpa using ha
    · have hterm := ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
        i.hom.base N.isSheaf hi x hx
      intro b
      refine ⟨0, ?_⟩
      have h1 : (𝟙 _ : _ ⟶ _) = 0 := hterm.hom_ext _ _
      have h2 := congrArg (fun φ => (ConcreteCategory.hom φ) b) h1
      rw [map_zero]
      simp only [AddCommGrpCat.hom_zero] at h2
      exact h2.symm

/-- **Stacks Project, Tag 08KS.** Pushforward of sheaves of modules along a morphism of ringed
spaces whose underlying continuous map is a closed embedding is right exact.

Together with `preservesFiniteLimits_modulePushforward` this says that the functor is exact. -/
@[stacks 08KS "exactness only; full faithfulness and the essential image are not covered"]
theorem preservesFiniteColimits_modulePushforward {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    PreservesFiniteColimits (modulePushforward i) :=
  have := preservesEpimorphisms_modulePushforward i hi
  have : (modulePushforward i).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Pushforward of sheaves of modules along a morphism of ringed spaces whose underlying
continuous map is a homeomorphism is right exact.

The morphism itself need not be an isomorphism of ringed spaces: only its base map is
inverted, while the comorphism `𝒪_Y ⟶ f_* 𝒪_X` is arbitrary. On sections `f_*` is then
reindexing of opens along a homeomorphism followed by restriction of scalars along that
comorphism, and both are exact. This is the case of a thickening and, more generally, of a
retraction of one, where `f ≫ g = 𝟙` holds on one side only.

A homeomorphism is a closed embedding, so this is `preservesFiniteColimits_modulePushforward`
with `TopCat.isIso_iff_isHomeomorph` supplying the hypothesis. It subsumes the case of an
isomorphism of ringed spaces. -/
instance preservesFiniteColimits_modulePushforward_of_isIso_base
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) [hf : IsIso f.hom.base] :
    PreservesFiniteColimits (modulePushforward f) :=
  preservesFiniteColimits_modulePushforward f
    ((TopCat.isIso_iff_isHomeomorph f.hom.base).mp hf).isClosedEmbedding

/-- Pushforward of sheaves of modules along a closed immersion of schemes preserves
epimorphisms. -/
instance preservesEpimorphisms_modulePushforward_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] :
    (modulePushforward i.toLRSHom.toShHom).PreservesEpimorphisms :=
  preservesEpimorphisms_modulePushforward _ (isClosedEmbedding_base_toShHom i)

/-- Pushforward of sheaves of modules along a closed immersion of schemes is right exact. -/
instance preservesFiniteColimits_modulePushforward_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] :
    PreservesFiniteColimits (modulePushforward i.toLRSHom.toShHom) :=
  preservesFiniteColimits_modulePushforward _ (isClosedEmbedding_base_toShHom i)

/-- Direct image of modules along a closed immersion of schemes is right exact. This is the
ringed-space statement for the underlying morphism of ringed spaces, which is the same
functor. -/
instance preservesFiniteColimits_pushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    PreservesFiniteColimits (Scheme.Modules.pushforward i) :=
  inferInstanceAs (PreservesFiniteColimits
    (RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom))

/-! ### An exact functor is its own total right derived functor -/

section ExactFunctor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The functor induced on derived categories by an exact functor is a right derived functor of
`F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh`, with unit
`F.mapDerivedCategoryFactorsh.inv`. -/
instance isRightDerivedFunctor_mapDerivedCategory :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh

/-- An exact functor has a total right derived functor, namely the functor it induces on
derived categories. -/
instance hasRightDerivedFunctor_mapHomotopyCategory_comp_Qh :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) :=
  Functor.HasRightDerivedFunctor.mk' F.mapDerivedCategory F.mapDerivedCategoryFactorsh.inv

/-- For an exact functor `F` between abelian categories, the canonical isomorphism between the
functor `F.mapDerivedCategory` induced on derived categories and the chosen total right derived
functor of `F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh`.

This is the uniqueness of right derived functors: both models are right derived functors of the
same functor on the homotopy category, so `Functor.rightDerivedUnique` applies. -/
noncomputable def mapDerivedCategoryIsoTotalRightDerived :
    F.mapDerivedCategory ≅
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) :=
  Functor.rightDerivedUnique F.mapDerivedCategory _
    F.mapDerivedCategoryFactorsh.inv
    ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))

/-- `mapDerivedCategoryIsoTotalRightDerived` carries the canonical map out of the homotopy
category for `F.mapDerivedCategory` to the one for the total right derived functor.

This is the defining factorization of `Functor.rightDerivedNatTrans`, i.e.
`Functor.rightDerivedNatTrans_app`. -/
@[reassoc]
theorem mapDerivedCategoryIsoTotalRightDerived_fac_app
    (M : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    F.mapDerivedCategoryFactorsh.inv.app M ≫
        (mapDerivedCategoryIsoTotalRightDerived F).hom.app (DerivedCategory.Qh.obj M) =
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))).app M := by
  simp [mapDerivedCategoryIsoTotalRightDerived]

/-- For an exact functor `F` between abelian categories, the functor `F.mapDerivedCategory`
induced on derived categories and the chosen total right derived functor of
`F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh` are isomorphic, by an isomorphism carrying the
canonical map out of the homotopy category for the first model to the one for the second.

This is the existential form of `mapDerivedCategoryIsoTotalRightDerived` together with
`mapDerivedCategoryIsoTotalRightDerived_fac_app`; it is the form Stacks 0E2K consumes. -/
theorem exists_mapDerivedCategoryIsoTotalRightDerived :
    ∃ e : F.mapDerivedCategory ≅
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)),
      ∀ M, F.mapDerivedCategoryFactorsh.inv.app M ≫ e.hom.app (DerivedCategory.Qh.obj M) =
        ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))).app M :=
  ⟨mapDerivedCategoryIsoTotalRightDerived F,
    mapDerivedCategoryIsoTotalRightDerived_fac_app F⟩

end ExactFunctor

/-! ### The comparison for a closed immersion of schemes -/

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- The exact-functor and right-derived-functor models of pushforward along a closed immersion
of schemes have a comparison isomorphism compatible with their maps from the homotopy
category of complexes of sheaves of modules.

Pushforward along a closed immersion is exact
(`preservesFiniteColimits_modulePushforward_of_isClosedImmersion`), so it induces a functor on
derived categories which is its own total right derived functor; the comparison is the
uniqueness isomorphism of `exists_mapDerivedCategoryIsoTotalRightDerived`. -/
theorem exists_closedImmersionDerivedPushforwardComparison {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    ∃ e : (modulePushforward i.toLRSHom.toShHom).mapDerivedCategory ≅
        ((modulePushforward i.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) (ComplexShape.up ℤ)),
      ∀ M,
        ((modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactorsh.inv.app M) ≫
          e.hom.app (DerivedCategory.Qh.obj M) =
        (((modulePushforward i.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
              (ComplexShape.up ℤ))).app M :=
  exists_mapDerivedCategoryIsoTotalRightDerived (modulePushforward i.toLRSHom.toShHom)

end Scheme

end Stacks.ClosedImmersion

end
