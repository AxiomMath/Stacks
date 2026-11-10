module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base change map for abelian sheaves on topological spaces

Let
$$
\begin{matrix} X' & \to & X \\ \downarrow & & \downarrow \\ S' & \to & S \end{matrix}
$$
be a commutative square of topological spaces, with horizontal maps `g' : X' ⟶ X` and
`g : S' ⟶ S` and vertical maps `f' : X' ⟶ S'` and `f : X ⟶ S`. This file constructs the
canonical base change map
$$
g^{-1} Rf_* \longrightarrow Rf'_* (g')^{-1}
$$
of functors `D⁺(S) ⥤ D⁺(S')` on bounded below derived categories of sheaves of abelian
groups, and characterizes it by compatibility with the derived-functor unit of `Rf_*`.

The construction has two halves. The first is a general recipe, valid for any commutative
square of additive functors between abelian categories in which the horizontal functors are
left adjoints: the mate of the square under the two adjunctions is a transformation
`F ⋙ G ⟶ G' ⋙ F'` of underived functors, and `derived` descends it to the bounded below
right derived functors, using the universal property of `RF ⋙ RG` as a right derived
functor of `F ⋙ G`. The descent needs the comparison between `RG` and degreewise `G` to be
invertible, which `exactUnit_isIso` supplies whenever `G` is exact. The second half applies
the recipe to inverse and direct image of abelian sheaves. Inverse image of sheaves of
abelian groups is exact for *every* continuous map, so — unlike the module-valued case,
where flatness of the horizontal morphisms is needed — the abelian base change map exists
with no hypothesis on the square beyond commutativity. This is the form in which the map is
used for proper base change.

## Main definitions

* `Stacks.Cohomology.BaseChange.mate`: the mate `F ⋙ G ⟶ G' ⋙ F'` of a commutative square
  of functors whose horizontal arrows `G`, `G'` are left adjoints.
* `Stacks.Cohomology.BaseChange.onHomotopy`: the induced map out of the bounded below
  homotopy category of the source.
* `Stacks.Cohomology.BaseChange.derived`: the descent `RF ⋙ RG ⟶ RG' ⋙ RF'` of the mate to
  bounded below derived categories.
* `Stacks.Cohomology.BaseChange.abelianPullback`: inverse image of abelian sheaves on
  bounded below derived categories.
* `Stacks.Cohomology.BaseChange.abelianSheafBaseChange`: the underived base change map
  `g^{-1} f_* ⟶ f'_* (g')^{-1}`.
* `Stacks.Cohomology.BaseChange.abelianBaseChange`: the derived base change map
  `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}`.

## Main results

* `Stacks.Cohomology.BaseChange.exactUnit_isIso`: an exact additive functor between abelian
  categories has an invertible right-derived-functor unit, so its right derived functor is
  computed degreewise.
* `Stacks.Cohomology.BaseChange.derived_fac`: `derived` composed with the derived-functor
  unit of `RF` is `onHomotopy`. Since `RF ⋙ RG` is a right derived functor of `F ⋙ G` with
  that unit, this equation determines `derived`.
* `Stacks.Cohomology.BaseChange.abelianBaseChange_fac`: the same characterization for the
  base change map of abelian sheaves.
* `Stacks.Cohomology.BaseChange.unit_comp_map_mate`: **what the mate does.** Transposing it
  back across the adjunction of `G` returns `F` applied to the unit of the adjunction of `G'`,
  followed by `e`. Transposition being a bijection, this determines the mate.
* `Stacks.Cohomology.BaseChange.abelianSheafBaseChange_unit` and
  `abelianSheafBaseChange_hom_app_unit`: the same for the underived base change map of abelian
  sheaves, as an equation of sheaf morphisms and read at one open of `S`. This is what an
  identification of `abelianSheafBaseChange` with a concretely given map must be compared
  against; it needs no hypothesis on the square beyond commutativity.

## Implementation notes

`derived` and `derived_fac` produce a *morphism* of right derived functors from a morphism
of underived composites. They are therefore not an instance of
`Stacks.Cohomology.DerivedPushforwardSections.squareIso`, which produces an *isomorphism*
of right derived functors from an isomorphism of underived composites; a base change map is
not invertible in general, and the mate of a commuting square of adjunctions is not an
isomorphism even when the square of direct images is.

Commutativity of the square enters only through
`eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat) comm)`: direct image of abelian
sheaves is a functor of the continuous map, so the equality `g' ≫ f = f' ≫ g` already gives
the isomorphism `(g' ≫ f)_* ≅ (f' ≫ g)_*` of the two composites that `mate` expects.

Mathlib's concrete sheaf pullback uses one universe for the spaces and for the coefficient
category, so the spaces of the square and the abelian groups live in the same universe `u`.

## References

* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 09V6](https://stacks.math.columbia.edu/tag/09V6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard

/-! ### The mate of a commutative square of adjunctions -/

section Mate

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- The mate of a commutative square of functors whose horizontal arrows `G` and `G'` are
left adjoints: from an isomorphism `P' ⋙ F ≅ F' ⋙ P` between the composites built from the
right adjoints, it produces a transformation `F ⋙ G ⟶ G' ⋙ F'` between the composites built
from the left adjoints. -/
noncomputable def mate {G : B ⥤ D} {P : D ⥤ B} (adj : G ⊣ P)
    {G' : A ⥤ C} {P' : C ⥤ A} (adj' : G' ⊣ P')
    (F : A ⥤ B) (F' : C ⥤ D) (e : P' ⋙ F ≅ F' ⋙ P) :
    F ⋙ G ⟶ G' ⋙ F' :=
  Functor.whiskerRight (Functor.whiskerRight adj'.unit F) G ≫
    Functor.whiskerRight (Functor.associator G' P' F).hom G ≫
    Functor.whiskerRight (Functor.whiskerLeft G' e.hom) G ≫
    (Functor.associator G' (F' ⋙ P) G).hom ≫
    Functor.whiskerLeft G' ((Functor.associator F' P G).hom ≫
      Functor.whiskerLeft F' adj.counit ≫ F'.rightUnitor.hom)

/-- **What the mate does: it carries the unit of one adjunction to the unit of the other.**
Transposing `mate adj adj' F F' e` back across `adj` returns the transformation it was built
from: `F` applied to the unit of `adj'`, followed by `e`.

This is the computation a consumer of `mate` needs, and it is the whole of the mate's content:
`mate adj adj' F F' e` is the unique transformation `F ⋙ G ⟶ G' ⋙ F'` with this property,
because transposition across `adj` is a bijection. It is
`CategoryTheory.unit_mateEquiv_symm` for this spelling of the mate, proved here
directly from the two unit naturalities and the triangle identity of `adj`. -/
theorem unit_comp_map_mate {G : B ⥤ D} {P : D ⥤ B} (adj : G ⊣ P)
    {G' : A ⥤ C} {P' : C ⥤ A} (adj' : G' ⊣ P')
    (F : A ⥤ B) (F' : C ⥤ D) (e : P' ⋙ F ≅ F' ⋙ P) (a : A) :
    adj.unit.app (F.obj a) ≫ P.map ((mate adj adj' F F' e).app a) =
      F.map (adj'.unit.app a) ≫ e.hom.app (G'.obj a) := by
  have key : (mate adj adj' F F' e).app a =
      G.map (F.map (adj'.unit.app a) ≫ e.hom.app (G'.obj a)) ≫
        adj.counit.app (F'.obj (G'.obj a)) := by
    simp [mate]
  rw [key]
  simp

/-- **A left adjoint of the identity functor has an invertible unit.** Both `G` and `𝟭` are left
adjoint to `𝟭`, so `CategoryTheory.Adjunction.leftAdjointUniq` compares them and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` factors the unit of `Adjunction.id` —
the identity — through the unit of `adj`.

This is what makes the base change map of a square whose horizontal arrows are identities
invertible, with no computation of the unit on sections; see
`Stacks.Cohomology.BaseChange.isIso_abelianSheafBaseChange_id`. -/
theorem isIso_unit_of_adj_id {E : Type*} [Category* E] {G : E ⥤ E} (adj : G ⊣ 𝟭 E) :
    IsIso adj.unit := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun F => ?_
  have : IsIso ((Adjunction.id (C := E)).unit.app F) := (inferInstance : IsIso (𝟙 F))
  exact IsIso.of_isIso_fac_right (Adjunction.unit_leftAdjointUniq_hom_app adj Adjunction.id F)

end Mate

/-! ### Descending a square to bounded below derived categories -/

section Derived

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]

/-- Apply a natural transformation degreewise on the bounded below homotopy category. -/
noncomputable def mapPlus {E H : A ⥤ D} [E.Additive] [H.Additive] (τ : E ⟶ H) :
    E.mapHomotopyCategoryPlus ⟶ H.mapHomotopyCategoryPlus where
  app K := ObjectProperty.homMk ((τ.mapHomotopyCategory (.up ℤ)).app K.obj)
  naturality _ _ φ := by
    ext
    exact (τ.mapHomotopyCategory (.up ℤ)).naturality φ.hom

/-- The transformation out of the bounded below homotopy category of `A` induced by a
comparison `τ : F ⋙ G ⟶ G' ⋙ F'`: apply `τ` degreewise, then the derived-functor units of
`RG'` and `RF'`. The comparison `e` is used to replace `RG` applied to the image of a
complex under `F` by `G` applied degreewise. -/
@[sga "4 XVII 4.2.13" "special case"]
noncomputable def onHomotopy (τ : F ⋙ G ⟶ G' ⋙ F')
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ G.rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.Qh ⋙ (G'.rightDerivedFunctorPlus ⋙ F'.rightDerivedFunctorPlus) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus e.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom ≫
        mapPlus τ ≫ (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv)
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft G'.mapHomotopyCategoryPlus F'.rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight G'.rightDerivedFunctorPlusUnith F'.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- The descent of a comparison `τ : F ⋙ G ⟶ G' ⋙ F'` to bounded below derived categories.
It exists because `RF ⋙ RG` is a right derived functor of `F ⋙ G`: the unit of `RF`,
followed by `RG`, is already invertible on bounded below complexes of injectives. -/
noncomputable def derived (τ : F ⋙ G ⟶ G' ⋙ F')
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus) :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
      G'.rightDerivedFunctorPlus ⋙ F'.rightDerivedFunctorPlus := by
  let α := Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom
  letI : (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor α
      (HomotopyCategory.Plus.quasiIso A) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso α
      (fun K ↦ by dsimp [α]; infer_instance)
  exact (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).rightDerivedDesc α
    (HomotopyCategory.Plus.quasiIso A) _ (onHomotopy F F' G G' τ e)

/-- **The descended square is the canonical one.** Composed with the derived-functor unit of
`RF`, `derived` is the comparison `onHomotopy` through the other side of the square. Since
`RF ⋙ RG` is a right derived functor of `F ⋙ G` with that unit, this equation determines
`derived`. -/
theorem derived_fac (τ : F ⋙ G ⟶ G' ⋙ F')
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus) :
    Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (derived F F' G G' τ e) =
        onHomotopy F F' G G' τ e := by
  let α := Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom
  let _ : (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor α
      (HomotopyCategory.Plus.quasiIso A) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso α
      (fun K ↦ by dsimp [α]; infer_instance)
  unfold derived
  rw [← Category.assoc]
  apply Functor.rightDerived_fac

end Derived

/-- An exact additive functor between abelian categories, the source having enough
injectives, has an invertible right-derived-functor unit: its right derived functor is
computed degreewise. -/
theorem exactUnit_isIso {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    IsIso F.rightDerivedFunctorPlusUnith := by
  apply Functor.isIso_of_isRightDerivedFunctor_of_inverts
    (W := HomotopyCategory.Plus.quasiIso A)
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
  intro K L φ hφ
  have : IsIso (DerivedCategory.Qh.map φ.hom) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ)) _ hφ
  have : IsIso ((DerivedCategory.Plus.ι).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map φ)) := by
    change IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map φ.hom))
    exact (NatIso.isIso_map_iff F.mapDerivedCategoryFactorsh φ.hom).mp (by
      change IsIso (F.mapDerivedCategory.map (DerivedCategory.Qh.map φ.hom))
      infer_instance)
  exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι

attribute [instance] exactUnit_isIso

/-! ### Abelian sheaves on topological spaces -/

universe u

/-- Direct image of abelian sheaves is additive. -/
noncomputable instance abelianPushforward_additive {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).additive_of_preserves_binary_products

/-- Inverse image of abelian sheaves is additive. -/
noncomputable instance abelianInverseImage_additive {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive := by
  let _ : PreservesBinaryBiproducts (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Inverse image of abelian sheaves preserves finite limits: it is exact. -/
noncomputable instance abelianInverseImage_preservesFiniteLimits
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

/-- Inverse image of abelian sheaves on bounded below derived categories. -/
noncomputable def abelianPullback {X Y : TopCat.{u}} (f : X ⟶ Y) :
    DerivedCategory.Plus (TopCat.Sheaf AddCommGrpCat.{u} Y) ⥤
      DerivedCategory.Plus (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).rightDerivedFunctorPlus

/-- Exactness of inverse image identifies `abelianPullback` with degreewise inverse
image. -/
noncomputable def abelianPullbackComparison {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh ≅ DerivedCategory.Plus.Qh ⋙ abelianPullback f := by
  let η : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ abelianPullback f :=
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).rightDerivedFunctorPlusUnith
  letI : IsIso η := exactUnit_isIso (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)
  exact asIso η

/-- The comparison of `abelianPullback` with degreewise inverse image is the canonical
right-derived-functor unit. -/
theorem abelianPullbackComparison_hom_app {X Y : TopCat.{u}} (f : X ⟶ Y)
    (K : HomotopyCategory.Plus (TopCat.Sheaf AddCommGrpCat.{u} Y)) :
    (abelianPullbackComparison f).hom.app K =
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).rightDerivedFunctorPlusUnith.app K := rfl

/-- The underived base change map `g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian sheaves,
obtained by adjunction from the commuting square of direct images. -/
noncomputable def abelianSheafBaseChange {X X' S S' : TopCat.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{u} g ⟶
      TopCat.Sheaf.pullback AddCommGrpCat.{u} g' ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} f' :=
  mate (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g')
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u}) comm))

/-- **What the underived base change map does on sections: it carries the unit of the
`(g')^{-1} ⊣ g'_*` adjunction to the unit of the `g^{-1} ⊣ g_*` adjunction.** Transposing
`abelianSheafBaseChange` back across the adjunction of `g` returns `f_*` applied to the unit of
the adjunction of `g'`, up to the identification of `g'_* f_*` with `f'_* g_*` supplied by
commutativity of the square.

Since transposition across an adjunction is a bijection, this *determines*
`abelianSheafBaseChange`, and so it is what any identification of that map with a concretely
given one — a germwise computation, or the map of [Stacks, Tag 0D90] — has to compare against.
No hypothesis on the square beyond commutativity is used. -/
theorem abelianSheafBaseChange_unit {X X' S S' : TopCat.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map
          ((abelianSheafBaseChange f f' g g' comm).app F) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g').unit.app F) ≫
        (eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u}) comm)).hom.app
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj F) :=
  unit_comp_map_mate _ _ _ _ _ F

/-- `abelianSheafBaseChange_unit` read at one open `U` of `S`, which is the form a computation
on sections consumes: on the sections of `f_* F` over `U` — that is, on the sections of `F` over
`f⁻¹ U` — the base change map agrees with the unit of the adjunction of `g'` over `(f⁻¹ U)`. -/
theorem abelianSheafBaseChange_hom_app_unit {X X' S S' : TopCat.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : TopologicalSpace.Opens S) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)).hom.app (Opposite.op U) ≫
        ((abelianSheafBaseChange f f' g g' comm).app F).hom.app
          (Opposite.op ((TopologicalSpace.Opens.map g).obj U)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g').unit.app F).hom.app
          (Opposite.op ((TopologicalSpace.Opens.map f).obj U)) ≫
        ((eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u}) comm)).hom.app
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj F)).hom.app (Opposite.op U) :=
  congrArg (fun φ : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj F)) => φ.hom.app (Opposite.op U))
    (abelianSheafBaseChange_unit f f' g g' comm F)

/-- **Direct image along the identity is the identity functor.** This is Mathlib's
`TopCat.Presheaf.Pushforward.id` with the sheaf condition carried along: `Opens.map (𝟙 X)` is the
identity, so both the object and the morphism part are unchanged. -/
theorem pushforward_id (X : TopCat.{u}) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 X) = 𝟭 (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  rfl

/-- **The unit of the inverse-image/direct-image adjunction of the identity map is invertible**,
for abelian sheaves. Its right adjoint is the identity functor by `pushforward_id`, so
`isIso_unit_of_adj_id` applies. -/
theorem isIso_unit_pullbackPushforwardAdjunction_id (X : TopCat.{u}) :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (𝟙 X)).unit :=
  isIso_unit_of_adj_id (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (𝟙 X))

/-- **The underived base change map of a square whose horizontal arrows are identities is an
isomorphism**, for any continuous `f` and with no properness hypothesis: the square

```
X --𝟙--> X
|        |
f        f
v        v
Y --𝟙--> Y
```

is cartesian, and `g^{-1} f_* ⟶ f'_* (g')^{-1}` reads `f_* ⟶ f_*` up to the identifications of
`(𝟙)^{-1}` and `(𝟙)_*` with the identity functor.

This is proved from `unit_comp_map_mate` alone: transposing the mate across the adjunction of
`𝟙 Y` expresses `(𝟙 Y)_*` applied to it as a composite of the two adjunction units and the
comparison `e`, all three invertible here, and `(𝟙 Y)_*` reflects isomorphisms, being the
identity functor. No computation of a unit on sections is needed.

It is the degenerate case of the invertibility that
`Stacks.Cohomology.AbelianProperBaseChange.isIso_abelianSheafBaseChange_of_properMap` proves for
a general cartesian square with `f` proper, and it needs no properness. -/
theorem isIso_abelianSheafBaseChange_id {X Y : TopCat.{u}} (f : X ⟶ Y)
    (comm : 𝟙 X ≫ f = f ≫ 𝟙 Y) :
    IsIso (abelianSheafBaseChange f f (𝟙 Y) (𝟙 X) comm) := by
  have := isIso_unit_pullbackPushforwardAdjunction_id Y
  have := isIso_unit_pullbackPushforwardAdjunction_id X
  have : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 Y)).ReflectsIsomorphisms :=
    (inferInstance : (𝟭 (TopCat.Sheaf AddCommGrpCat.{u} Y)).ReflectsIsomorphisms)
  refine (NatTrans.isIso_iff_isIso_app _).2 fun F => ?_
  have : IsIso ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 Y)).map
      ((abelianSheafBaseChange f f (𝟙 Y) (𝟙 X) comm).app F)) :=
    IsIso.of_isIso_fac_left (unit_comp_map_mate
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (𝟙 Y))
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (𝟙 X))
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      (eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u}) comm)) F)
  exact isIso_of_reflects_iso _ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 Y))

/-- The base change map on bounded below complexes: the underived map applied degreewise,
followed by the derived-functor units of `R(g')^{-1}` and `Rf'_*`. -/
noncomputable def abelianBaseChangeOnHomotopyCategory {X X' S S' : TopCat.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh) ⋙ abelianPullback g ⟶
      DerivedCategory.Plus.Qh ⋙ (abelianPullback g' ⋙
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').rightDerivedFunctorPlus) :=
  onHomotopy (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g) (TopCat.Sheaf.pullback AddCommGrpCat.{u} g')
    (abelianSheafBaseChange f f' g g' comm) (abelianPullbackComparison g)

/-- The canonical base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` for a commutative square
of topological spaces, with coefficients in abelian sheaves. No hypothesis beyond
commutativity of the square is needed, because inverse image of abelian sheaves is exact. -/
noncomputable def abelianBaseChange {X X' S S' : TopCat.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerivedFunctorPlus ⋙
        abelianPullback g ⟶
      abelianPullback g' ⋙
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').rightDerivedFunctorPlus :=
  derived (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g) (TopCat.Sheaf.pullback AddCommGrpCat.{u} g')
    (abelianSheafBaseChange f f' g g' comm) (abelianPullbackComparison g)

/-- **The abelian base change map is the canonical one.** Precomposition with the
derived-functor unit of `Rf_*` recovers the explicit adjunction map on bounded below
complexes, which characterizes `abelianBaseChange`. -/
theorem abelianBaseChange_fac {X X' S S' : TopCat.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g) :
    Functor.whiskerRight
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerivedFunctorPlusUnith
        (abelianPullback g) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (abelianBaseChange f f' g g' comm) =
        abelianBaseChangeOnHomotopyCategory f f' g g' comm :=
  derived_fac (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g) (TopCat.Sheaf.pullback AddCommGrpCat.{u} g')
    (abelianSheafBaseChange f f' g g' comm) (abelianPullbackComparison g)

end Stacks.Cohomology.BaseChange
