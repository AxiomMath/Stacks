module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonInDegreeZero

/-!
# Relative Mayer--Vietoris

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `iU : U ⟶ X`, `iV : V ⟶ X` be open
immersions whose images cover `X`, with `iW : W ⟶ X` an open immersion cutting out their
intersection. Writing `a = iU ≫ f`, `b = iV ≫ f` and `c = iW ≫ f`, Stacks 01EC asserts that
for every `𝒪_X`-module `ℱ` the higher direct images fit into a long exact sequence

`0 ⟶ f_*ℱ ⟶ a_*(ℱ|_U) ⊕ b_*(ℱ|_V) ⟶ c_*(ℱ|_{U ∩ V}) ⟶ R¹f_*ℱ ⟶ ⋯`

functorially in `ℱ`. This file proves this for the `ℕ`-indexed higher direct images, and for
the `ℤ`-indexed higher direct images obtained from the bounded below derived functor of
pushforward, and constructs the `ℕ`-indexed sequence explicitly, with its degree-zero maps
identified.

## Main definitions

* `Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact`: exactness of two consecutive
  morphisms.
* `Stacks.Cohomology.RelativeMayerVietoris.RelativeMayerVietorisSequence`: the three natural
  maps in every degree and the exactness assertions which join them into a long exact
  sequence.
* `Stacks.Cohomology.RelativeMayerVietoris.higherDirectImagePlus`: the `ℤ`-indexed higher
  direct image `R ⁿ f_*`, obtained from the bounded below derived functor of pushforward.
* `Stacks.Cohomology.RelativeMayerVietoris.RelativeMayerVietorisSequencePlus`: the
  `ℤ`-indexed form of `RelativeMayerVietorisSequence`.
* `Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietorisSequence`: the relative
  Mayer--Vietoris sequence of a cover by two open immersions.
* `Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardToZero`: the degree-zero
  comparison between the pushed-forward restriction to the image of an open immersion and the
  restricted higher direct image.

## Main results

* `Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietoris`: the functorial relative
  Mayer--Vietoris sequence exists.
* `Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietorisPlus`: the same for the
  `ℤ`-indexed higher direct images.
* `Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietorisSequence_toCover_zero` and
  `Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietorisSequence_toIntersection_zero`:
  in degree zero the two maps of `relativeMayerVietorisSequence` are `pushforwardToCover` and
  `pushforwardToIntersection`, read through `CategoryTheory.Functor.toRightDerivedZero`.

## References

* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbsoluteMayerVietoris
  (evalBiprodIso evalBiprodIso_hom_lift evalBiprodIso_inv_desc)
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.RestrictionCover

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

/-! ### The shape of the statement -/

/-- The `n`-th higher direct image along a morphism of ringed spaces. -/
@[stacks 0715 "definition of R^i f_*"]
public noncomputable abbrev higherDirectImage {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (n : ℕ) :
    SheafOfModules (structureSheafRing X) ⥤ SheafOfModules (structureSheafRing Y) :=
  (modulePushforward f).rightDerived n

/-- Higher direct image after restricting a module along an open immersion. -/
public noncomputable abbrev restrictedHigherDirectImage
    {X Y U : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X) (n : ℕ) :
    SheafOfModules (structureSheafRing X) ⥤ SheafOfModules (structureSheafRing Y) :=
  modulePullback i ⋙ higherDirectImage (i ≫ f) n

/-- Two consecutive morphisms are exact if they form an exact short complex. -/
public def MorphismPairExact {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D : C} (p : A ⟶ B) (q : B ⟶ D) : Prop :=
  ∃ h : p ≫ q = 0, (ShortComplex.mk p q h).Exact

/-- Exactness of a pair of morphisms is invariant under conjugating by isomorphisms. -/
public theorem morphismPairExact_conjugate
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D A' B' D' : C} {p : A ⟶ B} {q : B ⟶ D}
    (eA : A' ≅ A) (eB : B' ≅ B) (eD : D' ≅ D)
    (h : MorphismPairExact p q) :
    MorphismPairExact (eA.hom ≫ p ≫ eB.inv) (eB.hom ≫ q ≫ eD.inv) := by
  obtain ⟨hpq, hexact⟩ := h
  exact ⟨by simp [reassoc_of% hpq], ShortComplex.exact_of_iso
    (ShortComplex.isoMk eA.symm eB.symm eD.symm (by simp) (by simp)) hexact⟩

section Statement

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

/-- A functorial relative Mayer--Vietoris long exact sequence.  Its maps in degree `n` are
`R^n f_* → R^n a_*|_U ⊕ R^n b_*|_V → R^n c_*|_{U∩V} → R^(n+1) f_*`.  The three exactness
fields state exactness at every term of this repeating pattern. -/
public structure RelativeMayerVietorisSequence
    {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)
    (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X) where
  /-- Restriction from `X` to the two members of the cover. -/
  toCover (n : ℕ) :
    higherDirectImage f n ⟶
      restrictedHigherDirectImage f iU n ⊞ restrictedHigherDirectImage f iV n
  /-- The difference of the two restrictions on the intersection. -/
  toIntersection (n : ℕ) :
    restrictedHigherDirectImage f iU n ⊞ restrictedHigherDirectImage f iV n ⟶
      restrictedHigherDirectImage f iW n
  /-- The connecting morphism. -/
  boundary (n : ℕ) :
    restrictedHigherDirectImage f iW n ⟶ higherDirectImage f (n + 1)
  /-- Exactness at the two-open term. -/
  exact_cover (n : ℕ) (F : SheafOfModules (structureSheafRing X)) :
    MorphismPairExact ((toCover n).app F) ((toIntersection n).app F)
  /-- Exactness at the intersection term. -/
  exact_intersection (n : ℕ) (F : SheafOfModules (structureSheafRing X)) :
    MorphismPairExact ((toIntersection n).app F) ((boundary n).app F)
  /-- Exactness at each positive-degree direct-image term. -/
  exact_base (n : ℕ) (F : SheafOfModules (structureSheafRing X)) :
    MorphismPairExact ((boundary n).app F) ((toCover (n + 1)).app F)
  /-- The sequence starts with `0 → f_* F`. -/
  mono_zero (F : SheafOfModules (structureSheafRing X)) : Mono ((toCover 0).app F)

end Statement

/-! ### Right derivation along a natural isomorphism -/

/-- Right derived functors of isomorphic functors are isomorphic. -/
public noncomputable def rightDerivedMapIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D]
    {G₁ G₂ : C ⥤ D} [G₁.Additive] [G₂.Additive] (e : G₁ ≅ G₂) (n : ℕ) :
    G₁.rightDerived n ≅ G₂.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-! ### The short complex of functors on `Y` -/

section Complex

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Restriction to an open subset `U` of `X`, pushed forward to `Y`. -/
public noncomputable abbrev restrictedPushforwardOpen (U : Opens X.carrier) :
    SheafOfModules (structureSheafRing X) ⥤ SheafOfModules (structureSheafRing Y) :=
  restrictPush (structureSheafRing X) U ⋙ modulePushforward f

/-- Restriction of a direct image to an open subset of the source. -/
public noncomputable def pushforwardCoverUnit (U : Opens X.carrier) :
    modulePushforward f ⟶ restrictedPushforwardOpen f U where
  app M := (modulePushforward f).map
    ((ExtensionByZeroModules.jStarAdjunction U (structureSheafRing X)).unit.app M)
  naturality A B g := by
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (modulePushforward f).map
      ((ExtensionByZeroModules.jStarAdjunction U (structureSheafRing X)).unit.naturality g)

/-- Further restriction of a direct image, from an open subset `U` to a smaller one `T`. -/
public noncomputable def pushforwardCoverTransition (T U : Opens X.carrier) (hTU : T ≤ U) :
    restrictedPushforwardOpen f U ⟶ restrictedPushforwardOpen f T where
  app M := (modulePushforward f).map
    ((restrictPushTransition (structureSheafRing X) T U hTU).app M)
  naturality A B g := by
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (modulePushforward f).map
      ((restrictPushTransition (structureSheafRing X) T U hTU).naturality g)

section

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

variable (U V : Opens X.carrier)

/-- The first map of the Mayer--Vietoris short complex of functors: restriction of a direct
image to the two members of the cover. -/
public noncomputable def pushforwardToCover :
    modulePushforward f ⟶
      restrictedPushforwardOpen f U ⊞ restrictedPushforwardOpen f V :=
  biprod.lift (pushforwardCoverUnit f U) (pushforwardCoverUnit f V)

/-- The second map of the Mayer--Vietoris short complex of functors: the difference of the two
further restrictions to the intersection. -/
public noncomputable def pushforwardToIntersection :
    restrictedPushforwardOpen f U ⊞ restrictedPushforwardOpen f V ⟶
      restrictedPushforwardOpen f (U ⊓ V) :=
  biprod.desc (pushforwardCoverTransition f (U ⊓ V) U inf_le_left)
    (-pushforwardCoverTransition f (U ⊓ V) V inf_le_right)

/-- The two maps of the Mayer--Vietoris short complex of functors compose to zero. -/
public theorem pushforwardToCover_comp_toIntersection :
    pushforwardToCover f U V ≫ pushforwardToIntersection f U V = 0 := by
  dsimp only [pushforwardToCover, pushforwardToIntersection]
  rw [biprod.lift_desc, Preadditive.comp_neg]
  refine NatTrans.ext (funext fun M => ?_)
  have key : ∀ (T : Opens X.carrier) (hT : U ⊓ V ≤ T),
      (pushforwardCoverUnit f T ≫ pushforwardCoverTransition f (U ⊓ V) T hT).app M =
      (modulePushforward f).map
        ((ExtensionByZeroModules.jStarAdjunction (U ⊓ V) (structureSheafRing X)).unit.app M) :=
    fun T hT => by
      show (modulePushforward f).map _ ≫ (modulePushforward f).map _ = _
      rw [← Functor.map_comp]
      exact congrArg (modulePushforward f).map
        (congrFun (congrArg NatTrans.app
          (restrictPushTransition_unit (structureSheafRing X) (U ⊓ V) T hT)) M)
  simp only [NatTrans.app_add, NatTrans.app_neg, NatTrans.app_zero, key U inf_le_left,
    key V inf_le_right,
    add_neg_cancel]

/-- The Mayer--Vietoris short complex of functors is short exact at every injective
module. -/
public theorem pushforward_shortExact_on_injectives (hUV : U ⊔ V = ⊤)
    (I : SheafOfModules (structureSheafRing X)) (hI : Injective I) :
    (NatTrans.appShortComplex (pushforwardToCover f U V)
      (pushforwardToIntersection f U V)
      (pushforwardToCover_comp_toIntersection f U V) I).ShortExact := by
  let O := structureSheafRing X
  let Gf := modulePushforward f
  let S : ShortComplex (SheafOfModules O) :=
    ShortComplex.mk ((restrictionCoverFirst O U V).app I)
      ((restrictionCoverSecond O U V).app I)
      (NatTrans.congr_app (restrictionCoverFirst_comp_second O U V) I)
  have hS : S.ShortExact := restrictionCoverShortExact_object O U V hUV I
  have hmono : Mono S.f := hS.mono_f
  let r : S.X₂ ⟶ S.X₁ := Injective.factorThru (𝟙 S.X₁) S.f
  have hr : S.f ≫ r = 𝟙 S.X₁ := Injective.comp_factorThru (𝟙 S.X₁) S.f
  let sp : S.Splitting :=
    ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hr hS.epi_g
  have hmapped : (S.map Gf).ShortExact :=
    { mono_f := (sp.map Gf).mono_f
      epi_g := (sp.map Gf).epi_g
      exact := (sp.map Gf).exact }
  let α : (S.map Gf).X₂ ≅
      (restrictedPushforwardOpen f U ⊞ restrictedPushforwardOpen f V).obj I :=
    Gf.mapBiprod ((restrictPush O U).obj I) ((restrictPush O V).obj I) ≪≫
      (evalBiprodIso (restrictedPushforwardOpen f U)
        (restrictedPushforwardOpen f V) I).symm
  let ev := evalBiprodIso (restrictedPushforwardOpen f U)
    (restrictedPushforwardOpen f V) I
  let mb := Gf.mapBiprod ((restrictPush O U).obj I) ((restrictPush O V).obj I)
  have h1 : Gf.map ((restrictionCoverFirst O U V).app I) ≫ mb.hom =
      biprod.lift ((pushforwardCoverUnit f U).app I)
        ((pushforwardCoverUnit f V).app I) :=
    biprod.map_lift_mapBiprod Gf _ _ _ _
  have h2 : (pushforwardToCover f U V).app I ≫ ev.hom =
      biprod.lift ((pushforwardCoverUnit f U).app I)
        ((pushforwardCoverUnit f V).app I) :=
    evalBiprodIso_hom_lift _ _ I
  have hcomm₁₂ : Gf.map ((restrictionCoverFirst O U V).app I) ≫ α.hom =
      (pushforwardToCover f U V).app I :=
    calc Gf.map ((restrictionCoverFirst O U V).app I) ≫ α.hom
        = (Gf.map ((restrictionCoverFirst O U V).app I) ≫ mb.hom) ≫ ev.inv :=
          (Category.assoc _ _ _).symm
      _ = ((pushforwardToCover f U V).app I ≫ ev.hom) ≫ ev.inv := by rw [h1, h2]
      _ = (pushforwardToCover f U V).app I := by simp
  have h3 : ev.inv ≫ (pushforwardToIntersection f U V).app I =
      biprod.desc (Gf.map ((restrictPushTransition O (U ⊓ V) U inf_le_left).app I))
        (-Gf.map ((restrictPushTransition O (U ⊓ V) V inf_le_right).app I)) :=
    evalBiprodIso_inv_desc _ _ I
  have h4 : mb.hom ≫
      biprod.desc (Gf.map ((restrictPushTransition O (U ⊓ V) U inf_le_left).app I))
        (-Gf.map ((restrictPushTransition O (U ⊓ V) V inf_le_right).app I)) =
      Gf.map ((restrictionCoverSecond O U V).app I) := by
    rw [← Gf.map_neg]
    exact biprod.mapBiprod_hom_desc Gf _ _ _ _
  have hcomm₂₃ : α.hom ≫ (pushforwardToIntersection f U V).app I =
      Gf.map ((restrictionCoverSecond O U V).app I) :=
    (Category.assoc mb.hom ev.inv _).trans
      ((congrArg (fun t => mb.hom ≫ t) h3).trans h4)
  have e : (S.map Gf) ≅
      NatTrans.appShortComplex (pushforwardToCover f U V)
        (pushforwardToIntersection f U V)
        (pushforwardToCover_comp_toIntersection f U V) I :=
    ShortComplex.isoMk (Iso.refl _) α (Iso.refl _)
      ((Category.id_comp _).trans hcomm₁₂.symm)
      (hcomm₂₃.trans (Category.comp_id _).symm)
  exact ShortComplex.shortExact_of_iso e hmapped

end

end Complex

/-! ### Identifying the terms -/

section Terms

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The pushed-forward restriction to the image of an open immersion is the
pullback-pushforward composite attached to the open immersion. -/
public noncomputable def restrictedPushforwardOpenIso
    {U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    restrictedPushforwardOpen f (immImage i) ≅
      modulePullback i ⋙ modulePushforward (i ≫ f) :=
  restrictedPushforwardIso f (immImage i) ≪≫
    restrictedPushforwardOpenImmersionIso i f

/-- The `n`-th right derived functor of the pushed-forward restriction to the image of an open
immersion is the restricted higher direct image. -/
public noncomputable def restrictedPushforwardRightDerivedIso
    {U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] (n : ℕ) :
    (restrictedPushforwardOpen f (immImage i)).rightDerived n ≅
      restrictedHigherDirectImage f i n := by
  have hhom : (modulePullback i).PreservesHomology :=
    Stacks.Cohomology.openImmersionModulePullback_preservesHomology i
  have : PreservesFiniteLimits (modulePullback i) :=
    (modulePullback i).preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits (modulePullback i) :=
    (modulePullback i).preservesFiniteColimits_of_preservesHomology
  have : (modulePullback i).PreservesInjectiveObjects :=
    modulePullback_preservesInjectiveObjects i
  exact rightDerivedMapIso (restrictedPushforwardOpenIso f i) n ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (modulePullback i)
      (modulePushforward (i ≫ f)) n

end Terms

/-! ### The long exact sequence -/

/-- Exactness of a pair of morphisms is invariant under conjugating by isomorphisms at all
three places. -/
public theorem morphismPairExact_conj
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D A' B' D' : C} {p : A ⟶ B} {q : B ⟶ D}
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D') (h : MorphismPairExact p q) :
    MorphismPairExact (eA.inv ≫ p ≫ eB.hom) (eB.inv ≫ q ≫ eD.hom) :=
  morphismPairExact_conjugate eA.symm eB.symm eD.symm h

/-- The three exactness assertions carried by an exact sequence of five composable arrows. -/
public theorem morphismPairExact_of_exact₅
    {C : Type*} [Category C] [Abelian C] {A₀ A₁ A₂ A₃ A₄ A₅ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄} {e : A₄ ⟶ A₅}
    (h : (ComposableArrows.mk₅ a b c d e).Exact) :
    MorphismPairExact a b ∧ MorphismPairExact b c ∧ MorphismPairExact c d :=
  ⟨⟨h.toIsComplex.zero' 0 1 2, h.exact 0⟩,
    ⟨h.toIsComplex.zero' 1 2 3, h.exact 1⟩,
    ⟨h.toIsComplex.zero' 2 3 4, h.exact 2⟩⟩

/-- The three exactness assertions of the long exact sequence of right derived functors of a
short complex of functors which is short exact on injectives. -/
private theorem morphismPairExact_rightDerived_chain {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasInjectiveResolutions A] {F G H : A ⥤ B}
    [F.Additive] [G.Additive] [H.Additive] (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0)
    (hinj : ∀ X : A, Injective X → (NatTrans.appShortComplex i q hiq X).ShortExact)
    (n : ℕ) (M : A) :
    MorphismPairExact ((NatTrans.rightDerived i n).app M) ((NatTrans.rightDerived q n).app M) ∧
      MorphismPairExact ((NatTrans.rightDerived q n).app M)
        ((CategoryTheory.rightDerivedDelta i q hiq hinj n).app M) ∧
      MorphismPairExact ((CategoryTheory.rightDerivedDelta i q hiq hinj n).app M)
        ((NatTrans.rightDerived i (n + 1)).app M) :=
  morphismPairExact_of_exact₅
    (CategoryTheory.exact_rightDerived_composableArrows₅ i q hiq hinj (injectiveResolution M) n)

/-- Conjugating a natural transformation by isomorphisms preserves monomorphisms at an
object. -/
private theorem mono_app_conj {C D : Type*} [Category C] [Category D] {F F' G G' : C ⥤ D}
    (e₁ : F ≅ F') (e₂ : G ≅ G') (a : F ⟶ G) (M : C) [Mono (a.app M)] :
    Mono ((e₁.inv ≫ a ≫ e₂.hom).app M) := by
  change Mono (e₁.inv.app M ≫ a.app M ≫ e₂.hom.app M)
  have : IsIso (e₁.inv.app M) := inferInstanceAs (IsIso (e₁.app M).inv)
  have : IsIso (e₂.hom.app M) := inferInstanceAs (IsIso (e₂.app M).hom)
  infer_instance

section Main

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- For a morphism `f : X → Y`, two open subspaces covering `X`, and their intersection, the
higher direct images of every module fit into a long exact Mayer--Vietoris sequence, naturally
in the module. -/
@[stacks 01EC]
public theorem relativeMayerVietoris
    (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
    [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
    [SheafedSpace.IsOpenImmersion iW]
    (cover : Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ)
    (intersection : Set.range iW.hom.base =
      Set.range iU.hom.base ∩ Set.range iV.hom.base) :
    Nonempty (RelativeMayerVietorisSequence f iU iV iW) := by
  obtain ⟨hcover, hinter⟩ :=
    openImmersionImages_cover_intersection iU iV iW cover intersection
  let i := pushforwardToCover f (immImage iU) (immImage iV)
  let q := pushforwardToIntersection f (immImage iU) (immImage iV)
  let hiq := pushforwardToCover_comp_toIntersection f (immImage iU) (immImage iV)
  have hinj : ∀ M : SheafOfModules (structureSheafRing X), Injective M →
      (NatTrans.appShortComplex i q hiq M).ShortExact :=
    fun M hM =>
      pushforward_shortExact_on_injectives f (immImage iU) (immImage iV) hcover M hM
  let δ := CategoryTheory.rightDerivedDelta i q hiq hinj
  let e0 (n : ℕ) : higherDirectImage f n ≅ higherDirectImage f n := Iso.refl _
  let eMid (n : ℕ) :
      (restrictedPushforwardOpen f (immImage iU) ⊞
        restrictedPushforwardOpen f (immImage iV)).rightDerived n ≅
          restrictedHigherDirectImage f iU n ⊞ restrictedHigherDirectImage f iV n :=
    Functor.rightDerivedBiprodIso (restrictedPushforwardOpen f (immImage iU))
        (restrictedPushforwardOpen f (immImage iV)) n ≪≫
      biprod.mapIso (restrictedPushforwardRightDerivedIso f iU n)
        (restrictedPushforwardRightDerivedIso f iV n)
  let eW (n : ℕ) :
      (restrictedPushforwardOpen f (immImage iU ⊓ immImage iV)).rightDerived n ≅
        restrictedHigherDirectImage f iW n :=
    rightDerivedMapIso
        (eqToIso (congrArg (restrictedPushforwardOpen f) hinter.symm)) n ≪≫
      restrictedPushforwardRightDerivedIso f iW n
  let p (n : ℕ) : higherDirectImage f n ⟶
      restrictedHigherDirectImage f iU n ⊞ restrictedHigherDirectImage f iV n :=
    (e0 n).inv ≫ NatTrans.rightDerived i n ≫ (eMid n).hom
  let r (n : ℕ) : restrictedHigherDirectImage f iU n ⊞ restrictedHigherDirectImage f iV n ⟶
      restrictedHigherDirectImage f iW n :=
    (eMid n).inv ≫ NatTrans.rightDerived q n ≫ (eW n).hom
  let d (n : ℕ) : restrictedHigherDirectImage f iW n ⟶ higherDirectImage f (n + 1) :=
    (eW n).inv ≫ δ n ≫ (e0 (n + 1)).hom
  have hchain := morphismPairExact_rightDerived_chain i q hiq hinj
  refine Nonempty.intro
    { toCover := p
      toIntersection := r
      boundary := d
      exact_cover := fun n M =>
        morphismPairExact_conj ((e0 n).app M) ((eMid n).app M) ((eW n).app M)
          (hchain n M).1
      exact_intersection := fun n M =>
        morphismPairExact_conj ((eMid n).app M) ((eW n).app M) ((e0 (n + 1)).app M)
          (hchain n M).2.1
      exact_base := fun n M =>
        morphismPairExact_conj ((eW n).app M) ((e0 (n + 1)).app M) ((eMid (n + 1)).app M)
          (hchain n M).2.2
      mono_zero := ?_ }
  intro M
  have h1 : Mono ((NatTrans.rightDerived i 0).app M) :=
    CategoryTheory.mono_rightDerived_zero_app i q hiq hinj M
  exact mono_app_conj (e0 0) (eMid 0) _ M

end Main

end Stacks.Cohomology.RelativeMayerVietoris

end

/-!
## Relative Mayer--Vietoris, indexed by the integers

The relative Mayer--Vietoris sequence for the `ℤ`-indexed higher direct images
`CategoryTheory.Functor.rightDerivedPlus` of pushforward, which vanish in negative degrees.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.RelativeMayerVietoris

/-! ### Degenerate exactness -/

/-- A biproduct of two zero objects is a zero object. -/
public theorem isZero_biprod {C : Type*} [Category C] [Preadditive C] {A B : C}
    [HasBinaryBiproduct A B] (hA : IsZero A) (hB : IsZero B) : IsZero (A ⊞ B) := by
  rw [IsZero.iff_id_eq_zero, ← biprod.total,
    hA.eq_of_tgt (biprod.fst : A ⊞ B ⟶ A) 0,
    hB.eq_of_tgt (biprod.snd : A ⊞ B ⟶ B) 0]
  simp

/-- A pair of morphisms through a zero object is exact. -/
public theorem morphismPairExact_of_isZero_mid {C : Type*} [Category C] [Abelian C]
    {A B D : C} (p : A ⟶ B) (q : B ⟶ D) (hB : IsZero B) : MorphismPairExact p q :=
  ⟨by rw [hB.eq_of_tgt p 0, zero_comp], ShortComplex.exact_of_isZero_X₂ _ hB⟩

/-- A pair of morphisms whose first has a zero source is exact exactly when the second is a
monomorphism. -/
public theorem morphismPairExact_of_isZero_src {C : Type*} [Category C] [Abelian C]
    {A B D : C} (p : A ⟶ B) (q : B ⟶ D) (hA : IsZero A) (hq : Mono q) :
    MorphismPairExact p q :=
  ⟨by rw [hA.eq_of_src p 0, zero_comp], (ShortComplex.exact_iff_mono _ (hA.eq_of_src p 0)).2 hq⟩

section

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

/-! ### The shape of the statement -/

/-- The `n`-th higher direct image along a morphism of ringed spaces, obtained from the bounded
below derived functor of pushforward and indexed by the integers. -/
public noncomputable abbrev higherDirectImagePlus {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (n : ℤ) : SheafOfModules (structureSheafRing X) ⥤ SheafOfModules (structureSheafRing Y) :=
  (modulePushforward f).rightDerivedPlus n

/-- Integer-indexed higher direct image after restricting a module along an open immersion. -/
public noncomputable abbrev restrictedHigherDirectImagePlus
    {X Y U : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X) (n : ℤ) :
    SheafOfModules (structureSheafRing X) ⥤ SheafOfModules (structureSheafRing Y) :=
  modulePullback i ⋙ higherDirectImagePlus (i ≫ f) n

/-- A functorial relative Mayer--Vietoris long exact sequence for integer-indexed bounded below
higher direct images.  Its maps in degree `n` are
`R ⁿ f_* → R ⁿ a_*|_U ⊕ R ⁿ b_*|_V → R ⁿ c_*|_{U∩V} → R ⁿ⁺¹ f_*`.  The three exactness fields
state exactness at every term of this repeating pattern. -/
public structure RelativeMayerVietorisSequencePlus
    {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)
    (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X) where
  /-- Restriction to the two open subspaces. -/
  toCover (n : ℤ) :
    higherDirectImagePlus f n ⟶
      restrictedHigherDirectImagePlus f iU n ⊞ restrictedHigherDirectImagePlus f iV n
  /-- Difference of the two restrictions to their intersection. -/
  toIntersection (n : ℤ) :
    restrictedHigherDirectImagePlus f iU n ⊞ restrictedHigherDirectImagePlus f iV n ⟶
      restrictedHigherDirectImagePlus f iW n
  /-- The connecting morphism. -/
  boundary (n : ℤ) :
    restrictedHigherDirectImagePlus f iW n ⟶ higherDirectImagePlus f (n + 1)
  /-- Exactness at the two-open term. -/
  exact_cover (n : ℤ) (F : SheafOfModules (structureSheafRing X)) :
    MorphismPairExact ((toCover n).app F) ((toIntersection n).app F)
  /-- Exactness at the intersection term. -/
  exact_intersection (n : ℤ) (F : SheafOfModules (structureSheafRing X)) :
    MorphismPairExact ((toIntersection n).app F) ((boundary n).app F)
  /-- Exactness at the direct-image term. -/
  exact_base (n : ℤ) (F : SheafOfModules (structureSheafRing X)) :
    MorphismPairExact ((boundary n).app F) ((toCover (n + 1)).app F)
  /-- The nonnegative sequence starts with an injection in degree zero. -/
  mono_zero (F : SheafOfModules (structureSheafRing X)) : Mono ((toCover 0).app F)

/-! ### Vanishing in negative degrees -/

section Vanishing

variable {X Y U : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Higher direct images vanish in negative degrees. -/
public theorem isZero_higherDirectImagePlus_obj (n : ℤ) (hn : n < 0)
    (F : SheafOfModules (structureSheafRing X)) : IsZero ((higherDirectImagePlus f n).obj F) :=
  Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ n hn F

/-- The negative-degree higher direct images are zero as functors. -/
public theorem isZero_higherDirectImagePlus (n : ℤ) (hn : n < 0) :
    IsZero (higherDirectImagePlus f n) :=
  (Functor.isZero_iff _).2 (isZero_higherDirectImagePlus_obj f n hn)

/-- The negative-degree restricted higher direct images vanish. -/
public theorem isZero_restrictedHigherDirectImagePlus_obj (i : U ⟶ X) (n : ℤ) (hn : n < 0)
    (F : SheafOfModules (structureSheafRing X)) :
    IsZero ((restrictedHigherDirectImagePlus f i n).obj F) :=
  Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ n hn _

/-- The negative-degree restricted higher direct images are zero as functors. -/
public theorem isZero_restrictedHigherDirectImagePlus (i : U ⟶ X) (n : ℤ) (hn : n < 0) :
    IsZero (restrictedHigherDirectImagePlus f i n) :=
  (Functor.isZero_iff _).2 (isZero_restrictedHigherDirectImagePlus_obj f i n hn)

end Vanishing

/-! ### Comparing the two indexings -/

section Comparison

variable {X Y U V : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The two indexings of the higher direct images agree in nonnegative degrees. -/
public noncomputable def higherDirectImagePlusIso (n : ℕ) :
    higherDirectImage f n ≅ higherDirectImagePlus f (n : ℤ) :=
  Stacks.DerivedIndexing.rightDerivedIso (modulePushforward f) n

/-- The two indexings of the restricted higher direct images agree in nonnegative degrees. -/
public noncomputable def restrictedHigherDirectImagePlusIso (i : U ⟶ X) (n : ℕ) :
    restrictedHigherDirectImage f i n ≅ restrictedHigherDirectImagePlus f i (n : ℤ) :=
  Functor.isoWhiskerLeft (modulePullback i)
    (Stacks.DerivedIndexing.rightDerivedIso (modulePushforward (i ≫ f)) n)

/-- The comparison at the middle, two-open term of the sequence. -/
public noncomputable def coverPlusIso (iU : U ⟶ X) (iV : V ⟶ X) (n : ℕ) :
    restrictedHigherDirectImage f iU n ⊞ restrictedHigherDirectImage f iV n ≅
      restrictedHigherDirectImagePlus f iU (n : ℤ) ⊞
        restrictedHigherDirectImagePlus f iV (n : ℤ) :=
  biprod.mapIso (restrictedHigherDirectImagePlusIso f iU n)
    (restrictedHigherDirectImagePlusIso f iV n)

end Comparison

/-! ### Transporting the sequence -/

section Transport

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)
  (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X) (s : RelativeMayerVietorisSequence f iU iV iW)

/-- The integer-indexed restriction map to the two members of the cover: in a nonnegative degree
the natural-number-indexed map conjugated by the comparison isomorphisms, and in a negative
degree the zero map, its source being a zero object. -/
public noncomputable def toCoverPlus : ∀ n : ℤ,
    higherDirectImagePlus f n ⟶
      restrictedHigherDirectImagePlus f iU n ⊞ restrictedHigherDirectImagePlus f iV n
  | Int.ofNat m =>
    (higherDirectImagePlusIso f m).inv ≫ s.toCover m ≫ (coverPlusIso f iU iV m).hom
  | Int.negSucc _ => 0

/-- The integer-indexed difference of the two restrictions to the intersection. -/
public noncomputable def toIntersectionPlus : ∀ n : ℤ,
    restrictedHigherDirectImagePlus f iU n ⊞ restrictedHigherDirectImagePlus f iV n ⟶
      restrictedHigherDirectImagePlus f iW n
  | Int.ofNat m =>
    (coverPlusIso f iU iV m).inv ≫ s.toIntersection m ≫
      (restrictedHigherDirectImagePlusIso f iW m).hom
  | Int.negSucc _ => 0

/-- The integer-indexed connecting morphism. -/
public noncomputable def boundaryPlus : ∀ n : ℤ,
    restrictedHigherDirectImagePlus f iW n ⟶ higherDirectImagePlus f (n + 1)
  | Int.ofNat m =>
    (restrictedHigherDirectImagePlusIso f iW m).inv ≫ s.boundary m ≫
      (higherDirectImagePlusIso f (m + 1)).hom
  | Int.negSucc _ => 0

include s in
/-- A natural-number-indexed relative Mayer--Vietoris sequence gives an integer-indexed
one. -/
public theorem nonempty_relativeMayerVietorisSequencePlus :
    Nonempty (RelativeMayerVietorisSequencePlus f iU iV iW) := by
  have hmono : ∀ (k : ℤ), k = 0 → ∀ F : SheafOfModules (structureSheafRing X),
      Mono ((toCoverPlus f iU iV iW s k).app F) := by
    rintro k rfl F
    have := s.mono_zero F
    exact mono_app_conj (higherDirectImagePlusIso f 0) (coverPlusIso f iU iV 0) _ F
  refine Nonempty.intro
    { toCover := toCoverPlus f iU iV iW s
      toIntersection := toIntersectionPlus f iU iV iW s
      boundary := boundaryPlus f iU iV iW s
      exact_cover := ?_
      exact_intersection := ?_
      exact_base := ?_
      mono_zero := hmono 0 rfl }
  · intro n F
    rcases lt_or_ge n 0 with hn | hn
    · exact morphismPairExact_of_isZero_mid _ _
        ((Functor.isZero_iff _).1
          (isZero_biprod (isZero_restrictedHigherDirectImagePlus f iU n hn)
            (isZero_restrictedHigherDirectImagePlus f iV n hn)) F)
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      exact morphismPairExact_conj ((higherDirectImagePlusIso f m).app F)
        ((coverPlusIso f iU iV m).app F)
        ((restrictedHigherDirectImagePlusIso f iW m).app F) (s.exact_cover m F)
  · intro n F
    rcases lt_or_ge n 0 with hn | hn
    · exact morphismPairExact_of_isZero_mid _ _
        (isZero_restrictedHigherDirectImagePlus_obj f iW n hn F)
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      exact morphismPairExact_conj ((coverPlusIso f iU iV m).app F)
        ((restrictedHigherDirectImagePlusIso f iW m).app F)
        ((higherDirectImagePlusIso f (m + 1)).app F) (s.exact_intersection m F)
  · intro n F
    rcases lt_or_ge (n + 1) 0 with hn | hn
    · exact morphismPairExact_of_isZero_mid _ _
        (isZero_higherDirectImagePlus_obj f (n + 1) hn F)
    · rcases lt_or_ge n 0 with hneg | hpos
      · exact morphismPairExact_of_isZero_src _ _
          (isZero_restrictedHigherDirectImagePlus_obj f iW n hneg F)
          (hmono (n + 1) (by omega) F)
      · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
        exact morphismPairExact_conj
          ((restrictedHigherDirectImagePlusIso f iW m).app F)
          ((higherDirectImagePlusIso f (m + 1)).app F)
          ((coverPlusIso f iU iV (m + 1)).app F) (s.exact_base m F)

end Transport

/-! ### The integer-indexed sequence -/

section Main

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The bounded below higher direct images of a module and of its restrictions to a two-open
cover and to the intersection form a functorial long exact sequence indexed by the integers. -/
@[stacks 01EC "bounded-below integer-indexed sequence"]
public theorem relativeMayerVietorisPlus
    (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
    [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
    [SheafedSpace.IsOpenImmersion iW]
    (cover : Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ)
    (intersection : Set.range iW.hom.base =
      Set.range iU.hom.base ∩ Set.range iV.hom.base) :
    Nonempty (RelativeMayerVietorisSequencePlus f iU iV iW) :=
  nonempty_relativeMayerVietorisSequencePlus f iU iV iW
    (Classical.choice (relativeMayerVietoris f iU iV iW cover intersection))

end Main

end

end Stacks.Cohomology.RelativeMayerVietoris

end

/-!
## The relative Mayer--Vietoris sequence as a term

The relative Mayer--Vietoris sequence of a cover by two open immersions, and its degree-zero
maps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.RestrictionCover

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

section Canonical

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The degree-zero comparison at a member of the cover: the pushed-forward restriction to the
image of an open immersion maps to the degree-zero restricted higher direct image. -/
public noncomputable def restrictedPushforwardToZero
    (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    restrictedPushforwardOpen f (immImage i) ⟶ restrictedHigherDirectImage f i 0 :=
  (restrictedPushforwardOpenIso f i).hom ≫
    Functor.whiskerLeft (modulePullback i) (modulePushforward (i ≫ f)).toRightDerivedZero

/-- The canonical map to the degree-zero right derived functor of the pushed-forward
restriction, followed by `restrictedPushforwardRightDerivedIso`, is
`restrictedPushforwardToZero`. -/
@[reassoc]
public theorem toRightDerivedZero_comp_restrictedPushforwardRightDerivedIso
    (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    (restrictedPushforwardOpen f (immImage i)).toRightDerivedZero ≫
        (restrictedPushforwardRightDerivedIso f i 0).hom =
      restrictedPushforwardToZero f i := by
  have hhom : (modulePullback i).PreservesHomology :=
    Stacks.Cohomology.openImmersionModulePullback_preservesHomology i
  have : PreservesFiniteLimits (modulePullback i) :=
    (modulePullback i).preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits (modulePullback i) :=
    (modulePullback i).preservesFiniteColimits_of_preservesHomology
  have : (modulePullback i).PreservesInjectiveObjects :=
    modulePullback_preservesInjectiveObjects i
  dsimp only [restrictedPushforwardRightDerivedIso, restrictedPushforwardToZero,
    rightDerivedMapIso, Iso.trans_hom]
  rw [← Category.assoc, ← ModuleSheafCohomology.toRightDerivedZero_naturality_functor
      (restrictedPushforwardOpenIso f i).hom, Category.assoc,
    Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_zero]

/-- The first component of the restriction map to the cover. -/
@[reassoc]
public theorem pushforwardToCover_comp_fst (A B : Opens X.carrier) :
    pushforwardToCover f A B ≫ biprod.fst = pushforwardCoverUnit f A :=
  biprod.lift_fst _ _

/-- The second component of the restriction map to the cover. -/
@[reassoc]
public theorem pushforwardToCover_comp_snd (A B : Opens X.carrier) :
    pushforwardToCover f A B ≫ biprod.snd = pushforwardCoverUnit f B :=
  biprod.lift_snd _ _

/-- `restrictedPushforwardToZero` followed by the inverse of
`restrictedPushforwardRightDerivedIso` is the canonical map to the degree-zero right derived
functor. -/
@[reassoc]
public theorem restrictedPushforwardToZero_comp_inv
    (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    restrictedPushforwardToZero f i ≫ (restrictedPushforwardRightDerivedIso f i 0).inv =
      (restrictedPushforwardOpen f (immImage i)).toRightDerivedZero := by
  rw [← toRightDerivedZero_comp_restrictedPushforwardRightDerivedIso f i, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

variable (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
  [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
  [SheafedSpace.IsOpenImmersion iW]

/-- The middle term of the long exact sequence of the Mayer--Vietoris short complex of functors,
identified with the biproduct of the two restricted higher direct images. -/
public noncomputable def coverRightDerivedIso (n : ℕ) :
    (restrictedPushforwardOpen f (immImage iU) ⊞
        restrictedPushforwardOpen f (immImage iV)).rightDerived n ≅
      restrictedHigherDirectImage f iU n ⊞ restrictedHigherDirectImage f iV n :=
  Functor.rightDerivedBiprodIso (restrictedPushforwardOpen f (immImage iU))
      (restrictedPushforwardOpen f (immImage iV)) n ≪≫
    biprod.mapIso (restrictedPushforwardRightDerivedIso f iU n)
      (restrictedPushforwardRightDerivedIso f iV n)

variable (cover : Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ)
  (intersection : Set.range iW.hom.base = Set.range iU.hom.base ∩ Set.range iV.hom.base)

/-- The last term of the long exact sequence, identified with the restricted higher direct image
along the open immersion cutting out the intersection. -/
public noncomputable def intersectionRightDerivedIso (n : ℕ) :
    (restrictedPushforwardOpen f (immImage iU ⊓ immImage iV)).rightDerived n ≅
      restrictedHigherDirectImage f iW n :=
  rightDerivedMapIso (eqToIso (congrArg (restrictedPushforwardOpen f)
      (openImmersionImages_cover_intersection iU iV iW cover intersection).2.symm)) n ≪≫
    restrictedPushforwardRightDerivedIso f iW n

/-- The degree-zero comparison at the intersection term. -/
public noncomputable def intersectionPushforwardToZero :
    restrictedPushforwardOpen f (immImage iU ⊓ immImage iV) ⟶
      restrictedHigherDirectImage f iW 0 :=
  (eqToIso (congrArg (restrictedPushforwardOpen f)
      (openImmersionImages_cover_intersection iU iV iW cover intersection).2.symm)).hom ≫
    restrictedPushforwardToZero f iW

/-- The canonical map to the degree-zero right derived functor of the pushed-forward
restriction to the intersection, followed by `intersectionRightDerivedIso`, is
`intersectionPushforwardToZero`. -/
@[reassoc]
public theorem toRightDerivedZero_comp_intersectionRightDerivedIso :
    (restrictedPushforwardOpen f (immImage iU ⊓ immImage iV)).toRightDerivedZero ≫
        (intersectionRightDerivedIso f iU iV iW cover intersection 0).hom =
      intersectionPushforwardToZero f iU iV iW cover intersection := by
  dsimp only [intersectionRightDerivedIso, intersectionPushforwardToZero, rightDerivedMapIso,
    Iso.trans_hom]
  rw [← Category.assoc, ← ModuleSheafCohomology.toRightDerivedZero_naturality_functor,
    Category.assoc, toRightDerivedZero_comp_restrictedPushforwardRightDerivedIso]

/-- The connecting morphism of the canonical relative Mayer--Vietoris sequence: the connecting
morphism of the long exact sequence of right derived functors of the Mayer--Vietoris short
complex of functors attached to the images of the two open immersions. -/
public noncomputable def relativeMayerVietorisBoundary (n : ℕ) :
    (restrictedPushforwardOpen f (immImage iU ⊓ immImage iV)).rightDerived n ⟶
      higherDirectImage f (n + 1) :=
  CategoryTheory.rightDerivedDelta (pushforwardToCover f (immImage iU) (immImage iV))
    (pushforwardToIntersection f (immImage iU) (immImage iV))
    (pushforwardToCover_comp_toIntersection f (immImage iU) (immImage iV))
    (fun M hM => pushforward_shortExact_on_injectives f (immImage iU) (immImage iV)
      (openImmersionImages_cover_intersection iU iV iW cover intersection).1 M hM) n

/-- The three exactness assertions of the long exact sequence of right derived functors of the
Mayer--Vietoris short complex of functors. -/
private theorem relativeMayerVietorisChain (n : ℕ) (M : SheafOfModules (structureSheafRing X)) :
    MorphismPairExact
        ((NatTrans.rightDerived
          (pushforwardToCover f (immImage iU) (immImage iV)) n).app M)
        ((NatTrans.rightDerived
          (pushforwardToIntersection f (immImage iU) (immImage iV)) n).app M) ∧
      MorphismPairExact
        ((NatTrans.rightDerived
          (pushforwardToIntersection f (immImage iU) (immImage iV)) n).app M)
        ((relativeMayerVietorisBoundary f iU iV iW cover intersection n).app M) ∧
      MorphismPairExact
        ((relativeMayerVietorisBoundary f iU iV iW cover intersection n).app M)
        ((NatTrans.rightDerived
          (pushforwardToCover f (immImage iU) (immImage iV)) (n + 1)).app M) :=
  morphismPairExact_rightDerived_chain _ _
    (pushforwardToCover_comp_toIntersection f (immImage iU) (immImage iV)) _ n M

/-- The relative Mayer--Vietoris sequence of a cover by two open immersions: its degree-`n`
maps are the right derived functors of the Mayer--Vietoris short complex of functors, read
through the identifications of the three terms. -/
public noncomputable def relativeMayerVietorisSequence :
    RelativeMayerVietorisSequence f iU iV iW where
  toCover n :=
    NatTrans.rightDerived (pushforwardToCover f (immImage iU) (immImage iV)) n ≫
      (coverRightDerivedIso f iU iV n).hom
  toIntersection n :=
    (coverRightDerivedIso f iU iV n).inv ≫
      NatTrans.rightDerived (pushforwardToIntersection f (immImage iU) (immImage iV)) n ≫
      (intersectionRightDerivedIso f iU iV iW cover intersection n).hom
  boundary n :=
    (intersectionRightDerivedIso f iU iV iW cover intersection n).inv ≫
      relativeMayerVietorisBoundary f iU iV iW cover intersection n
  exact_cover n M := by
    have h := morphismPairExact_conj (Iso.refl ((higherDirectImage f n).obj M))
      ((coverRightDerivedIso f iU iV n).app M)
      ((intersectionRightDerivedIso f iU iV iW cover intersection n).app M)
      (relativeMayerVietorisChain f iU iV iW cover intersection n M).1
    rwa [Iso.refl_inv, Category.id_comp] at h
  exact_intersection n M := by
    have h := morphismPairExact_conj ((coverRightDerivedIso f iU iV n).app M)
      ((intersectionRightDerivedIso f iU iV iW cover intersection n).app M)
      (Iso.refl ((higherDirectImage f (n + 1)).obj M))
      (relativeMayerVietorisChain f iU iV iW cover intersection n M).2.1
    rwa [Iso.refl_hom, Category.comp_id] at h
  exact_base n M := by
    have h := morphismPairExact_conj
      ((intersectionRightDerivedIso f iU iV iW cover intersection n).app M)
      (Iso.refl ((higherDirectImage f (n + 1)).obj M))
      ((coverRightDerivedIso f iU iV (n + 1)).app M)
      (relativeMayerVietorisChain f iU iV iW cover intersection n M).2.2
    rwa [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp] at h
  mono_zero M := by
    have h1 : Mono ((NatTrans.rightDerived
        (pushforwardToCover f (immImage iU) (immImage iV)) 0).app M) :=
      CategoryTheory.mono_rightDerived_zero_app _ _ _
        (fun N hN => pushforward_shortExact_on_injectives f (immImage iU) (immImage iV)
          (openImmersionImages_cover_intersection iU iV iW cover intersection).1 N hN) M
    have h2 : IsIso ((coverRightDerivedIso f iU iV 0).hom.app M) :=
      inferInstanceAs (IsIso ((coverRightDerivedIso f iU iV 0).app M).hom)
    change Mono ((NatTrans.rightDerived
      (pushforwardToCover f (immImage iU) (immImage iV)) 0).app M ≫
      (coverRightDerivedIso f iU iV 0).hom.app M)
    infer_instance

/-- The degree-zero restriction to the first member of the cover. -/
public theorem relativeMayerVietorisSequence_toCover_zero_comp_fst :
    (modulePushforward f).toRightDerivedZero ≫
        (relativeMayerVietorisSequence f iU iV iW cover intersection).toCover 0 ≫ biprod.fst =
      pushforwardCoverUnit f (immImage iU) ≫ restrictedPushforwardToZero f iU := by
  dsimp only [relativeMayerVietorisSequence, coverRightDerivedIso, Iso.trans_hom]
  rw [Functor.rightDerivedBiprodIso_hom]
  simp only [Category.assoc, biprod.mapIso_hom, biprod.map_fst, biprod.lift_fst_assoc]
  rw [← NatTrans.rightDerived_comp_assoc, pushforwardToCover_comp_fst, ← Category.assoc,
    ← ModuleSheafCohomology.toRightDerivedZero_naturality_functor, Category.assoc,
    toRightDerivedZero_comp_restrictedPushforwardRightDerivedIso]

/-- The degree-zero restriction to the second member of the cover. -/
public theorem relativeMayerVietorisSequence_toCover_zero_comp_snd :
    (modulePushforward f).toRightDerivedZero ≫
        (relativeMayerVietorisSequence f iU iV iW cover intersection).toCover 0 ≫ biprod.snd =
      pushforwardCoverUnit f (immImage iV) ≫ restrictedPushforwardToZero f iV := by
  dsimp only [relativeMayerVietorisSequence, coverRightDerivedIso, Iso.trans_hom]
  rw [Functor.rightDerivedBiprodIso_hom]
  simp only [Category.assoc, biprod.mapIso_hom, biprod.map_snd, biprod.lift_snd_assoc]
  rw [← NatTrans.rightDerived_comp_assoc, pushforwardToCover_comp_snd, ← Category.assoc,
    ← ModuleSheafCohomology.toRightDerivedZero_naturality_functor, Category.assoc,
    toRightDerivedZero_comp_restrictedPushforwardRightDerivedIso]

/-- The degree-zero restriction map of `relativeMayerVietorisSequence` is the
Mayer--Vietoris restriction of a direct image. -/
public theorem relativeMayerVietorisSequence_toCover_zero :
    (modulePushforward f).toRightDerivedZero ≫
        (relativeMayerVietorisSequence f iU iV iW cover intersection).toCover 0 =
      pushforwardToCover f (immImage iU) (immImage iV) ≫
        biprod.map (restrictedPushforwardToZero f iU) (restrictedPushforwardToZero f iV) := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, relativeMayerVietorisSequence_toCover_zero_comp_fst, Category.assoc,
      biprod.map_fst, pushforwardToCover_comp_fst_assoc]
  · rw [Category.assoc, relativeMayerVietorisSequence_toCover_zero_comp_snd, Category.assoc,
      biprod.map_snd, pushforwardToCover_comp_snd_assoc]

/-- The degree-zero difference map of `relativeMayerVietorisSequence` is the Mayer--Vietoris
difference of the two further restrictions to the intersection. -/
public theorem relativeMayerVietorisSequence_toIntersection_zero :
    biprod.map (restrictedPushforwardToZero f iU) (restrictedPushforwardToZero f iV) ≫
        (relativeMayerVietorisSequence f iU iV iW cover intersection).toIntersection 0 =
      pushforwardToIntersection f (immImage iU) (immImage iV) ≫
        intersectionPushforwardToZero f iU iV iW cover intersection := by
  dsimp only [relativeMayerVietorisSequence, coverRightDerivedIso, Iso.trans_inv]
  rw [Functor.rightDerivedBiprodIso_inv]
  refine biprod.hom_ext' _ _ ?_ ?_ <;>
  · simp only [Category.assoc, biprod.mapIso_inv, biprod.inl_map_assoc, biprod.inl_desc_assoc,
      biprod.inr_map_assoc, biprod.inr_desc_assoc]
    rw [restrictedPushforwardToZero_comp_inv_assoc, ← NatTrans.rightDerived_comp_assoc,
      ← Category.assoc, ← ModuleSheafCohomology.toRightDerivedZero_naturality_functor]
    simp only [Category.assoc]
    rw [toRightDerivedZero_comp_intersectionRightDerivedIso]

end Canonical

end Stacks.Cohomology.RelativeMayerVietoris

end
