module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# Mayer--Vietoris for the right-derived model of sheaf cohomology

Let `X` be a topological space, `O` a sheaf of rings on `X`, and `U`, `V` two opens with
`U ⊔ V = ⊤`.  For every sheaf of `O`-modules `F` this file produces the long exact sequence

`0 ⟶ H⁰(X,F) ⟶ H⁰(U,F) ⊞ H⁰(V,F) ⟶ H⁰(U ⊓ V,F) ⟶ H¹(X,F) ⟶ H¹(U,F) ⊞ H¹(V,F) ⟶ ⋯`

in the cohomology **`Hgroup`**, i.e. `H^n(W,F) = ((secF O W).rightDerived n).obj F` of
`StacksDraft.Ch20.Sec7.Tag01E3`, with all three maps natural in `F` and with the two
non-connecting maps *identified with the restriction maps* `Hrestrict` of that same file.

`Stacks.Cohomology.MayerVietoris.mayerVietorisInitialSequence_exact` already has Tag 01EB for
an abelian sheaf on a site, but in Mathlib's `Ext`-based `Sheaf.H'`; the only bridge to
`Hgroup` is an `IsZero` *iff* with no coherence in the open, across which a diagram chase
cannot be transported.  This file is the same theorem stated inside `Hgroup`.

## Main definitions

* `Stacks.Cohomology.AbsoluteMayerVietoris.restrictedSections`: restriction of a module to an
  open subset followed by an additive functor `P`.
* `Stacks.Cohomology.AbsoluteMayerVietoris.toCover` and
  `Stacks.Cohomology.AbsoluteMayerVietoris.toIntersection`: the two maps of the
  Mayer--Vietoris short complex of functors, for an arbitrary additive `P`.
* `Stacks.Cohomology.AbsoluteMayerVietoris.mvFirst`,
  `Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond` and
  `Stacks.Cohomology.AbsoluteMayerVietoris.mvDelta`: the three maps of the long exact sequence,
  as natural transformations between the cohomology functors `Hfunctor`.

## Main results

* `Stacks.Cohomology.AbsoluteMayerVietoris.shortExact_on_injectives`: the Mayer--Vietoris
  short complex of functors is short exact at every injective module, for *every* additive
  target functor `P`.
* `Stacks.Cohomology.AbsoluteMayerVietoris.restrictedSections_secF_top`: sections over the
  whole space of the restriction to `U` **are** sections over `U`, as an equality of functors.
* `Stacks.Cohomology.AbsoluteMayerVietoris.mayerVietoris_exact` and
  `Stacks.Cohomology.AbsoluteMayerVietoris.mono_mvFirst_zero`: **the long exact sequence.**
* `Stacks.Cohomology.AbsoluteMayerVietoris.mvFirst_eq` and
  `Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq`: the first map is the pair of
  restrictions `H^n(X,-) ⟶ H^n(U,-) ⊞ H^n(V,-)` and the second is the difference of the two
  restrictions to `U ⊓ V`, both spelled with `HrestrictNT`.

## Implementation notes

The input is the Mayer--Vietoris short complex of *endofunctors* of `Mod(O)`,
`Stacks.Cohomology.RestrictionCover.restrictionCoverShortExact_object`, which is short exact at
every injective sheaf of modules.  `shortExact_on_injectives` pushes that statement through an
arbitrary additive `P` by the splitting trick of
`Stacks.Cohomology.RelativeMayerVietoris.pushforward_shortExact_on_injectives`: the sequence on
`X` has an *injective* first term, hence splits, and a split short exact sequence survives any
additive functor.  Consequently **no exactness and no preservation of injectives by
`restrictPush` is needed anywhere**, and in particular the sections-level short exactness
proved inside `RestrictionCoverShortExact` is not used.

The long exact sequence is then
`CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives`, taken in the
`exact_rightDerived_composableArrows₅` form so that the connecting map is the named natural
transformation `CategoryTheory.rightDerivedDelta` rather than an existential witness.

What identifies the resulting sequence as *Mayer--Vietoris in `Hgroup`* is
`restrictedSections_secF_top`: `restrictPush O U ⋙ secF O W` is `secF O ((openIntersection U).obj
W)` **by `rfl`**, and `(openIntersection U).obj ⊤ = U`, so the `U`-term of the derived sequence
is `Hfunctor O U n` after `Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso` applied to
  `eqToIso` of an
equality of functors.  The middle term is split by
`CategoryTheory.Functor.rightDerivedBiprodIso`.

The equality `(openIntersection U).obj ⊤ = U` is not definitional, so the identification of the
maps with `HrestrictNT` has to move an `eqToHom` past the unit of restriction.  It is done by
generalising the open and substituting the equality (`coverUnit_comp_eqToHom` and
`coverTransition_conj`), after which both sides are the presheaf acting on a morphism of
`(Opens X)ᵒᵖ` and the homs there are subsingletons.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ExtensionByZeroModules
open Stacks.Cohomology.RestrictionCover

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Cohomology.AbsoluteMayerVietoris

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-! ### Biproducts of functors are pointwise -/

/-- The biproduct of two functors, evaluated at an object, is the biproduct of the values:
biproducts in a functor category are pointwise, so the evaluation functors preserve them. -/
public def evalBiprodIso {A B : Type*} [Category A] [Category B] [Abelian B]
    (R S : A ⥤ B) (M : A) : (R ⊞ S).obj M ≅ R.obj M ⊞ S.obj M :=
  ((evaluation A B).obj M).mapBiprod R S

/-- Evaluating a lift into a biproduct of functors. -/
public theorem evalBiprodIso_hom_lift {A B : Type*} [Category A] [Category B] [Abelian B]
    {Q R S : A ⥤ B} (a : Q ⟶ R) (b : Q ⟶ S) (M : A) :
    (biprod.lift a b).app M ≫ (evalBiprodIso R S M).hom =
      biprod.lift (a.app M) (b.app M) :=
  biprod.map_lift_mapBiprod ((evaluation A B).obj M) R S a b

/-- Evaluating a descent out of a biproduct of functors. -/
public theorem evalBiprodIso_inv_desc {A B : Type*} [Category A] [Category B] [Abelian B]
    {R S Q : A ⥤ B} (a : R ⟶ Q) (b : S ⟶ Q) (M : A) :
    (evalBiprodIso R S M).inv ≫ (biprod.desc a b).app M =
      biprod.desc (a.app M) (b.app M) :=
  biprod.mapBiprod_inv_map_desc ((evaluation A B).obj M) R S a b

/-! ### Right derivation of natural transformations is additive -/

/-- Right derivation of natural transformations commutes with negation.  Companion to
`CategoryTheory.NatTrans.rightDerived_zero` and
`CategoryTheory.NatTrans.rightDerived_add`. -/
public theorem natTrans_rightDerived_neg {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [Abelian C] [HasInjectiveResolutions C] [Abelian D] {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    NatTrans.rightDerived (-α) n = -NatTrans.rightDerived α n := by
  have h : NatTrans.rightDerived (-α) n + NatTrans.rightDerived α n = 0 := by
    rw [← NatTrans.rightDerived_add, neg_add_cancel, NatTrans.rightDerived_zero]
  exact eq_neg_of_add_eq_zero_left h

/-! ### The Mayer--Vietoris short complex of functors -/

section General

variable {B : Type*} [Category B] [Abelian B] (P : SheafOfModules.{u} O ⥤ B) [P.Additive]

/-- Restriction of a module to an open subset `U`, followed by `P`.  Its value at `M` is `P`
applied to the sheaf whose sections over `W` are the sections of `M` over `W ⊓ U`. -/
public abbrev restrictedSections (U : Opens X) : SheafOfModules.{u} O ⥤ B :=
  restrictPush O U ⋙ P

/-- `P` applied to the restriction map of a module to an open subset `U`. -/
public def coverUnit (U : Opens X) : P ⟶ restrictedSections O P U where
  app M := P.map ((jStarAdjunction U O).unit.app M)
  naturality A C g := by
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg P.map ((jStarAdjunction U O).unit.naturality g)

/-- `P` applied to the further restriction from an open subset `U` to a smaller one `T`. -/
public def coverTransition (T U : Opens X) (hTU : T ≤ U) :
    restrictedSections O P U ⟶ restrictedSections O P T where
  app M := P.map ((restrictPushTransition O T U hTU).app M)
  naturality A C g := by
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg P.map ((restrictPushTransition O T U hTU).naturality g)

variable (U V : Opens X)

/-- The first map of the Mayer--Vietoris short complex of functors: the pair of the
restrictions to the two members of the cover. -/
public def toCover : P ⟶ restrictedSections O P U ⊞ restrictedSections O P V :=
  biprod.lift (coverUnit O P U) (coverUnit O P V)

/-- The second map of the Mayer--Vietoris short complex of functors: the difference of the two
further restrictions to the intersection. -/
public def toIntersection :
    restrictedSections O P U ⊞ restrictedSections O P V ⟶ restrictedSections O P (U ⊓ V) :=
  biprod.desc (coverTransition O P (U ⊓ V) U inf_le_left)
    (-coverTransition O P (U ⊓ V) V inf_le_right)

omit [P.Additive] in
/-- The two maps of the short complex compose to zero: restricting to `U` and then to `U ⊓ V`
is restricting to `U ⊓ V`, as is the same through `V`, so their difference vanishes. -/
public theorem toCover_comp_toIntersection :
    toCover O P U V ≫ toIntersection O P U V = 0 := by
  dsimp only [toCover, toIntersection]
  rw [biprod.lift_desc, Preadditive.comp_neg]
  refine NatTrans.ext (funext fun M => ?_)
  have h (W : Opens X) (hW : U ⊓ V ≤ W) :
      (coverUnit O P W ≫ coverTransition O P (U ⊓ V) W hW).app M =
        P.map ((jStarAdjunction (U ⊓ V) O).unit.app M) := by
    show P.map _ ≫ P.map _ = _
    rw [← Functor.map_comp]
    exact congrArg P.map (congrFun (congrArg NatTrans.app
      (restrictPushTransition_unit O (U ⊓ V) W hW)) M)
  simp only [NatTrans.app_add, NatTrans.app_neg, NatTrans.app_zero, h U inf_le_left,
    h V inf_le_right, add_neg_cancel]

/-- **The Mayer--Vietoris short complex of functors is short exact at every injective
module**, for every additive target functor `P`.  The sequence of modules on `X` has an
injective first term, hence splits, and a split short exact sequence stays short exact under
any additive functor; so neither exactness nor preservation of injectives by `restrictPush` is
required. -/
public theorem shortExact_on_injectives (hUV : U ⊔ V = ⊤)
    (I : SheafOfModules.{u} O) (hI : Injective I) :
    (NatTrans.appShortComplex (toCover O P U V) (toIntersection O P U V)
      (toCover_comp_toIntersection O P U V) I).ShortExact := by
  have hI' : Injective I := hI
  let S : ShortComplex (SheafOfModules.{u} O) :=
    ShortComplex.mk ((restrictionCoverFirst O U V).app I)
      ((restrictionCoverSecond O U V).app I)
      (NatTrans.congr_app (restrictionCoverFirst_comp_second O U V) I)
  have hS : S.ShortExact := restrictionCoverShortExact_object O U V hUV I
  have hmono : Mono S.f := hS.mono_f
  let r : S.X₂ ⟶ S.X₁ := Injective.factorThru (𝟙 S.X₁) S.f
  have hr : S.f ≫ r = 𝟙 S.X₁ := Injective.comp_factorThru (𝟙 S.X₁) S.f
  let sp : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hr hS.epi_g
  have hmapped : (S.map P).ShortExact :=
    { mono_f := (sp.map P).mono_f
      epi_g := (sp.map P).epi_g
      exact := (sp.map P).exact }
  let ev := evalBiprodIso (restrictedSections O P U) (restrictedSections O P V) I
  let mb := P.mapBiprod ((restrictPush O U).obj I) ((restrictPush O V).obj I)
  let α : (S.map P).X₂ ≅ (restrictedSections O P U ⊞ restrictedSections O P V).obj I :=
    mb ≪≫ ev.symm
  have h1 : P.map ((restrictionCoverFirst O U V).app I) ≫ mb.hom =
      biprod.lift ((coverUnit O P U).app I) ((coverUnit O P V).app I) :=
    biprod.map_lift_mapBiprod P _ _ _ _
  have h2 : (toCover O P U V).app I ≫ ev.hom =
      biprod.lift ((coverUnit O P U).app I) ((coverUnit O P V).app I) :=
    evalBiprodIso_hom_lift _ _ I
  have hcomm₁₂ : P.map ((restrictionCoverFirst O U V).app I) ≫ α.hom =
      (toCover O P U V).app I :=
    calc P.map ((restrictionCoverFirst O U V).app I) ≫ α.hom
        = (P.map ((restrictionCoverFirst O U V).app I) ≫ mb.hom) ≫ ev.inv :=
          (Category.assoc _ _ _).symm
      _ = ((toCover O P U V).app I ≫ ev.hom) ≫ ev.inv := by rw [h1, h2]
      _ = (toCover O P U V).app I := by simp
  have h3 : ev.inv ≫ (toIntersection O P U V).app I =
      biprod.desc (P.map ((restrictPushTransition O (U ⊓ V) U inf_le_left).app I))
        (-P.map ((restrictPushTransition O (U ⊓ V) V inf_le_right).app I)) :=
    evalBiprodIso_inv_desc _ _ I
  have h4 : mb.hom ≫
      biprod.desc (P.map ((restrictPushTransition O (U ⊓ V) U inf_le_left).app I))
        (-P.map ((restrictPushTransition O (U ⊓ V) V inf_le_right).app I)) =
      P.map ((restrictionCoverSecond O U V).app I) := by
    rw [← P.map_neg]
    exact biprod.mapBiprod_hom_desc P _ _ _ _
  have hcomm₂₃ : α.hom ≫ (toIntersection O P U V).app I =
      P.map ((restrictionCoverSecond O U V).app I) :=
    (Category.assoc mb.hom ev.inv _).trans
      ((congrArg (fun t => mb.hom ≫ t) h3).trans h4)
  have e : (S.map P) ≅
      NatTrans.appShortComplex (toCover O P U V) (toIntersection O P U V)
        (toCover_comp_toIntersection O P U V) I :=
    ShortComplex.isoMk (Iso.refl _) α (Iso.refl _)
      ((Category.id_comp _).trans hcomm₁₂.symm)
      (hcomm₂₃.trans (Category.comp_id _).symm)
  exact ShortComplex.shortExact_of_iso e hmapped

end General

/-! ### Sections over the whole space of a restricted module -/

/-- Intersecting an open `U` with the whole space gives back `U`.  This equality is *not*
definitional, which is the only reason the identifications below need an `eqToHom`. -/
public theorem openIntersection_obj_top (U : Opens X) : (openIntersection U).obj ⊤ = U := by
  simp [openIntersection]

/-- **Sections over the whole space of the restriction to `U` are sections over `U`**, as an
equality of functors.  `restrictPush O U ⋙ secF O W` is `secF O ((openIntersection U).obj W)`
by `rfl`, and `(openIntersection U).obj ⊤ = U`. -/
public theorem restrictedSections_secF_top (U : Opens X) :
    restrictedSections O (secF O ⊤) U = secF O U :=
  congrArg (secF O) (openIntersection_obj_top U)

/-- The restriction map to `U` on sections over the whole space is the restriction map
`Γ(X,-) ⟶ Γ(U,-)`: both are the presheaf acting on the unique morphism `U ⟶ ⊤`.  Stated with
the open and the equality generalised, so that substituting the equality clears the
`eqToHom`. -/
public theorem coverUnit_comp_eqToHom (U W : Opens X) (h : (openIntersection U).obj ⊤ = W)
    (hW : W ≤ ⊤) :
    coverUnit O (secF O ⊤) U ≫ eqToHom (congrArg (secF O) h) = secRestrict O hW := by
  subst h
  refine NatTrans.ext (funext fun M => ?_)
  have hid : (secF O ⊤).map ((jStarAdjunction U O).unit.app M) ≫
      𝟙 ((secF O ((openIntersection U).obj ⊤)).obj M) =
      ((SheafOfModules.toSheaf O).obj M).obj.map
        (U.isOpenEmbedding.isOpenMap.adjunction.counit.app (⊤ : Opens X)).op :=
    Category.comp_id _
  refine hid.trans ?_
  exact congrArg ((SheafOfModules.toSheaf O).obj M).obj.map
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The restriction map to `U`, with the `U`-term of the derived sequence named `secF O U`. -/
public theorem coverUnit_secF_top (U : Opens X) :
    coverUnit O (secF O ⊤) U ≫ eqToHom (restrictedSections_secF_top O U) =
      secRestrict O (le_top : U ≤ ⊤) :=
  coverUnit_comp_eqToHom O U U (openIntersection_obj_top U) le_top

/-- The further restriction from `U` to `T ≤ U`, read on sections over the whole space, is the
restriction map `Γ(U,-) ⟶ Γ(T,-)`.  Both are the presheaf acting on the unique morphism
`T ⊓ ⊤ ⟶ U ⊓ ⊤`. -/
public theorem coverTransition_app_eq (T U : Opens X) (hTU : T ≤ U)
    (hW : (openIntersection T).obj ⊤ ≤ (openIntersection U).obj ⊤)
    (M : SheafOfModules.{u} O) :
    (secF O ⊤).map ((restrictPushTransition O T U hTU).app M) = (secRestrict O hW).app M := by
  ext x
  have h1 := restrictPushTransition_app_val_app O T U hTU M (op (⊤ : Opens X)) x
  have h2 : (openIntersectionToOpenIntersection T U hTU).app (⊤ : Opens X) = homOfLE hW :=
    Subsingleton.elim _ _
  rwa [h2] at h1

/-- `coverTransition` conjugated by the identifications of its source and target with sections
over the two opens.  Stated with both opens and both equalities generalised, so that
substituting them clears the two `eqToHom`s. -/
public theorem coverTransition_conj (T U W₁ W₂ : Opens X) (hTU : T ≤ U)
    (h₁ : (openIntersection U).obj ⊤ = W₁) (h₂ : (openIntersection T).obj ⊤ = W₂)
    (hW : W₂ ≤ W₁) :
    eqToHom (congrArg (secF O) h₁).symm ≫ coverTransition O (secF O ⊤) T U hTU ≫
        eqToHom (congrArg (secF O) h₂) = secRestrict O hW := by
  subst h₁ h₂
  refine NatTrans.ext (funext fun M => ?_)
  exact (Category.id_comp _).trans
    ((Category.comp_id _).trans (coverTransition_app_eq O T U hTU hW M))

/-- `coverTransition` conjugated by the identifications of `restrictedSections_secF_top`: the
spelling in which the identification is used below. -/
public theorem coverTransition_secF_top (T U : Opens X) (hTU : T ≤ U) :
    eqToHom (restrictedSections_secF_top O U).symm ≫ coverTransition O (secF O ⊤) T U hTU ≫
        eqToHom (restrictedSections_secF_top O T) = secRestrict O hTU :=
  coverTransition_conj O T U U T hTU (openIntersection_obj_top U)
    (openIntersection_obj_top T) hTU

/-! ### The Mayer--Vietoris long exact sequence of `Hgroup` -/

section Hgroup

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

/-- **The `U`-term of the derived sequence is `H^n(U, -)`.** -/
public def termIso (U : Opens X) (n : ℕ) :
    (restrictedSections O (secF O ⊤) U).rightDerived n ≅ Hfunctor O U n :=
  Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso (eqToIso (restrictedSections_secF_top O
    U)) n

/-- `termIso` is the right derivation of the identification of its source with `secF O U`. -/
public theorem termIso_hom (U : Opens X) (n : ℕ) :
    (termIso O U n).hom =
      NatTrans.rightDerived (eqToHom (restrictedSections_secF_top O U)) n := rfl

/-- The inverse of `termIso`, likewise. -/
public theorem termIso_inv (U : Opens X) (n : ℕ) :
    (termIso O U n).inv =
      NatTrans.rightDerived (eqToHom (restrictedSections_secF_top O U).symm) n := rfl

variable (U V : Opens X)

/-- **The middle term of the derived sequence is `H^n(U, -) ⊞ H^n(V, -)`**: right derivation
commutes with binary biproducts of functors. -/
public def midIso (n : ℕ) :
    (restrictedSections O (secF O ⊤) U ⊞ restrictedSections O (secF O ⊤) V).rightDerived n ≅
      Hfunctor O U n ⊞ Hfunctor O V n :=
  Functor.rightDerivedBiprodIso (restrictedSections O (secF O ⊤) U)
      (restrictedSections O (secF O ⊤) V) n ≪≫
    biprod.mapIso (termIso O U n) (termIso O V n)

/-- **The first map of the Mayer--Vietoris sequence**, `H^n(X,-) ⟶ H^n(U,-) ⊞ H^n(V,-)`. -/
public def mvFirst (n : ℕ) : Hfunctor O ⊤ n ⟶ Hfunctor O U n ⊞ Hfunctor O V n :=
  NatTrans.rightDerived (toCover O (secF O ⊤) U V) n ≫ (midIso O U V n).hom

/-- **The second map of the Mayer--Vietoris sequence**,
`H^n(U,-) ⊞ H^n(V,-) ⟶ H^n(U ⊓ V,-)`. -/
public def mvSecond (n : ℕ) : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O (U ⊓ V) n :=
  (midIso O U V n).inv ≫ NatTrans.rightDerived (toIntersection O (secF O ⊤) U V) n ≫
    (termIso O (U ⊓ V) n).hom

/-! ### The two outer maps are the restriction maps -/


/-- The first projection after `midIso` is the derived projection followed by `termIso`. -/
private theorem midIso_hom_comp_fst (n : ℕ) :
    (midIso O U V n).hom ≫ biprod.fst =
      NatTrans.rightDerived (biprod.fst : restrictedSections O (secF O ⊤) U ⊞
        restrictedSections O (secF O ⊤) V ⟶ restrictedSections O (secF O ⊤) U) n ≫
        (termIso O U n).hom := by
  rw [midIso, Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst,
    ← Category.assoc, Functor.rightDerivedBiprodIso_hom, biprod.lift_fst]

/-- The second projection after `midIso` is the derived projection followed by `termIso`. -/
private theorem midIso_hom_comp_snd (n : ℕ) :
    (midIso O U V n).hom ≫ biprod.snd =
      NatTrans.rightDerived (biprod.snd : restrictedSections O (secF O ⊤) U ⊞
        restrictedSections O (secF O ⊤) V ⟶ restrictedSections O (secF O ⊤) V) n ≫
        (termIso O V n).hom := by
  rw [midIso, Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_snd,
    ← Category.assoc, Functor.rightDerivedBiprodIso_hom, biprod.lift_snd]

/-- The first inclusion before `midIso.inv` is `termIso.inv` followed by the derived inclusion. -/
private theorem inl_comp_midIso_inv (n : ℕ) :
    (biprod.inl : Hfunctor O U n ⟶ Hfunctor O U n ⊞ Hfunctor O V n) ≫ (midIso O U V n).inv =
      (termIso O U n).inv ≫ NatTrans.rightDerived (biprod.inl :
        restrictedSections O (secF O ⊤) U ⟶ restrictedSections O (secF O ⊤) U ⊞
          restrictedSections O (secF O ⊤) V) n := by
  rw [midIso, Iso.trans_inv, biprod.mapIso_inv, ← Category.assoc, biprod.inl_map,
    Category.assoc, Functor.rightDerivedBiprodIso_inv, biprod.inl_desc]

/-- The second inclusion before `midIso.inv` is `termIso.inv` followed by the derived inclusion. -/
private theorem inr_comp_midIso_inv (n : ℕ) :
    (biprod.inr : Hfunctor O V n ⟶ Hfunctor O U n ⊞ Hfunctor O V n) ≫ (midIso O U V n).inv =
      (termIso O V n).inv ≫ NatTrans.rightDerived (biprod.inr :
        restrictedSections O (secF O ⊤) V ⟶ restrictedSections O (secF O ⊤) U ⊞
          restrictedSections O (secF O ⊤) V) n := by
  rw [midIso, Iso.trans_inv, biprod.mapIso_inv, ← Category.assoc, biprod.inr_map,
    Category.assoc, Functor.rightDerivedBiprodIso_inv, biprod.inr_desc]

/-- The first component of `mvFirst` is the restriction `H^n(X,-) ⟶ H^n(U,-)`. -/
public theorem mvFirst_comp_fst (n : ℕ) :
    mvFirst O U V n ≫ biprod.fst = HrestrictNT O (le_top : U ≤ ⊤) n := by
  rw [mvFirst, Category.assoc, midIso_hom_comp_fst, ← Category.assoc,
    ← NatTrans.rightDerived_comp, toCover, biprod.lift_fst, termIso_hom,
    ← NatTrans.rightDerived_comp, coverUnit_secF_top]
  rfl

/-- The second component of `mvFirst` is the restriction `H^n(X,-) ⟶ H^n(V,-)`. -/
public theorem mvFirst_comp_snd (n : ℕ) :
    mvFirst O U V n ≫ biprod.snd = HrestrictNT O (le_top : V ≤ ⊤) n := by
  rw [mvFirst, Category.assoc, midIso_hom_comp_snd, ← Category.assoc,
    ← NatTrans.rightDerived_comp, toCover, biprod.lift_snd, termIso_hom,
    ← NatTrans.rightDerived_comp, coverUnit_secF_top]
  rfl

/-- **The first map of the Mayer--Vietoris sequence is the pair of the two restriction maps.**
-/
public theorem mvFirst_eq (n : ℕ) :
    mvFirst O U V n =
      biprod.lift (HrestrictNT O (le_top : U ≤ ⊤) n) (HrestrictNT O (le_top : V ≤ ⊤) n) := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [biprod.lift_fst]; exact mvFirst_comp_fst O U V n
  · rw [biprod.lift_snd]; exact mvFirst_comp_snd O U V n


/-- The restriction of `mvSecond` to the `U`-summand is the restriction map
`H^n(U,-) ⟶ H^n(U ⊓ V,-)`. -/
public theorem inl_comp_mvSecond (n : ℕ) :
    (biprod.inl : Hfunctor O U n ⟶ Hfunctor O U n ⊞ Hfunctor O V n) ≫ mvSecond O U V n =
      HrestrictNT O (inf_le_left : U ⊓ V ≤ U) n := by
  rw [mvSecond, ← Category.assoc, inl_comp_midIso_inv, Category.assoc,
    ← Category.assoc (NatTrans.rightDerived _ n), ← NatTrans.rightDerived_comp,
    toIntersection, biprod.inl_desc, termIso_inv, termIso_hom, ← NatTrans.rightDerived_comp,
    ← NatTrans.rightDerived_comp, coverTransition_secF_top O (U ⊓ V) U inf_le_left]
  rfl

/-- The restriction of `mvSecond` to the `V`-summand is minus the restriction map
`H^n(V,-) ⟶ H^n(U ⊓ V,-)`. -/
public theorem inr_comp_mvSecond (n : ℕ) :
    (biprod.inr : Hfunctor O V n ⟶ Hfunctor O U n ⊞ Hfunctor O V n) ≫ mvSecond O U V n =
      -HrestrictNT O (inf_le_right : U ⊓ V ≤ V) n := by
  rw [mvSecond, ← Category.assoc, inr_comp_midIso_inv, Category.assoc,
    ← Category.assoc (NatTrans.rightDerived _ n), ← NatTrans.rightDerived_comp,
    toIntersection, biprod.inr_desc, termIso_inv, termIso_hom, natTrans_rightDerived_neg,
    Preadditive.neg_comp, Preadditive.comp_neg, ← NatTrans.rightDerived_comp,
    ← NatTrans.rightDerived_comp, coverTransition_secF_top O (U ⊓ V) V inf_le_right]
  rfl

/-- **The second map of the Mayer--Vietoris sequence is the difference of the two restriction
maps to the intersection.** -/
public theorem mvSecond_eq (n : ℕ) :
    mvSecond O U V n =
      biprod.desc (HrestrictNT O (inf_le_left : U ⊓ V ≤ U) n)
        (-HrestrictNT O (inf_le_right : U ⊓ V ≤ V) n) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_desc]; exact inl_comp_mvSecond O U V n
  · rw [biprod.inr_desc]; exact inr_comp_mvSecond O U V n

/-! ### Exactness -/

variable (hUV : U ⊔ V = ⊤)

include hUV

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)] in
/-- Short exactness at injectives of the Mayer--Vietoris complex of sections functors. -/
public theorem secF_shortExact_on_injectives (M : SheafOfModules.{u} O) (hM : Injective M) :
    (NatTrans.appShortComplex (toCover O (secF O ⊤) U V) (toIntersection O (secF O ⊤) U V)
      (toCover_comp_toIntersection O (secF O ⊤) U V) M).ShortExact :=
  shortExact_on_injectives O (secF O ⊤) U V hUV M hM

/-- The connecting morphism of the Mayer--Vietoris sequence, before the source is renamed. -/
public def rawDelta (n : ℕ) :
    (restrictedSections O (secF O ⊤) (U ⊓ V)).rightDerived n ⟶ Hfunctor O ⊤ (n + 1) :=
  CategoryTheory.rightDerivedDelta (toCover O (secF O ⊤) U V)
    (toIntersection O (secF O ⊤) U V) (toCover_comp_toIntersection O (secF O ⊤) U V)
    (fun M hM => secF_shortExact_on_injectives O U V hUV M hM) n

/-- **The connecting map of the Mayer--Vietoris sequence**,
`H^n(U ⊓ V,-) ⟶ H^{n+1}(X,-)`. -/
public def mvDelta (n : ℕ) : Hfunctor O (U ⊓ V) n ⟶ Hfunctor O ⊤ (n + 1) :=
  (termIso O (U ⊓ V) n).inv ≫ rawDelta O U V hUV n

/-- **Stacks Project, Tag 01EB (Mayer--Vietoris), in the right-derived model of cohomology.**
Every six-term window
`H^n(X,F) ⟶ H^n(U,F) ⊞ H^n(V,F) ⟶ H^n(U ⊓ V,F) ⟶ H^{n+1}(X,F) ⟶ H^{n+1}(U,F) ⊞ H^{n+1}(V,F)
⟶ H^{n+1}(U ⊓ V,F)` of the Mayer--Vietoris sequence is exact.  The two outer maps are the
restriction maps, by `mvFirst_eq` and `mvSecond_eq`. -/
@[stacks 01EB "in the right-derived model `Hgroup`"]
public theorem mayerVietoris_exact (n : ℕ) (F : SheafOfModules.{u} O) :
    (ComposableArrows.mk₅ ((mvFirst O U V n).app F) ((mvSecond O U V n).app F)
      ((mvDelta O U V hUV n).app F) ((mvFirst O U V (n + 1)).app F)
      ((mvSecond O U V (n + 1)).app F)).Exact := by
  have hraw := CategoryTheory.exact_rightDerived_composableArrows₅ (toCover O (secF O ⊤) U V)
      (toIntersection O (secF O ⊤) U V) (toCover_comp_toIntersection O (secF O ⊤) U V)
      (fun M hM => secF_shortExact_on_injectives O U V hUV M hM) (injectiveResolution F) n
  refine ComposableArrows.exact_of_iso ?_ hraw
  refine ComposableArrows.isoMk₅
    (Iso.refl _) ((midIso O U V n).app F) ((termIso O (U ⊓ V) n).app F)
    (Iso.refl _) ((midIso O U V (n + 1)).app F) ((termIso O (U ⊓ V) (n + 1)).app F)
    ?_ ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · show (NatTrans.rightDerived (toIntersection O (secF O ⊤) U V) n).app F ≫
        (termIso O (U ⊓ V) n).hom.app F =
      (midIso O U V n).hom.app F ≫ (midIso O U V n).inv.app F ≫
        (NatTrans.rightDerived (toIntersection O (secF O ⊤) U V) n).app F ≫
          (termIso O (U ⊓ V) n).hom.app F
    rw [← Category.assoc, (midIso O U V n).hom_inv_id_app, Category.id_comp]
  · refine (Category.comp_id _).trans ?_
    show (rawDelta O U V hUV n).app F =
      (termIso O (U ⊓ V) n).hom.app F ≫ (termIso O (U ⊓ V) n).inv.app F ≫
        (rawDelta O U V hUV n).app F
    rw [← Category.assoc, (termIso O (U ⊓ V) n).hom_inv_id_app, Category.id_comp]
  · exact (Category.id_comp _).symm
  · show (NatTrans.rightDerived (toIntersection O (secF O ⊤) U V) (n + 1)).app F ≫
        (termIso O (U ⊓ V) (n + 1)).hom.app F =
      (midIso O U V (n + 1)).hom.app F ≫ (midIso O U V (n + 1)).inv.app F ≫
        (NatTrans.rightDerived (toIntersection O (secF O ⊤) U V) (n + 1)).app F ≫
          (termIso O (U ⊓ V) (n + 1)).hom.app F
    rw [← Category.assoc, (midIso O U V (n + 1)).hom_inv_id_app, Category.id_comp]

/-- **The five-arrow row the five lemma consumes**, extracted from the Mayer--Vietoris
sequence: the four-arrow window
`H^n(X,F) ⟶ H^n(U,F) ⊞ H^n(V,F) ⟶ H^n(U ⊓ V,F) ⟶ H^{n+1}(X,F) ⟶ H^{n+1}(U,F) ⊞ H^{n+1}(V,F)`
is exact as a `CategoryTheory.ComposableArrows _ 4`, which is the shape
`CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono` (Stacks 05QB) takes. -/
public theorem mayerVietoris_exact_four (n : ℕ) (F : SheafOfModules.{u} O) :
    (ComposableArrows.mk₅ ((mvFirst O U V n).app F) ((mvSecond O U V n).app F)
      ((mvDelta O U V hUV n).app F) ((mvFirst O U V (n + 1)).app F)
      ((mvSecond O U V (n + 1)).app F)).δlast.Exact :=
  ((ComposableArrows.exact_iff_δlast _).1 (mayerVietoris_exact O U V hUV n F)).1

/-- **The Mayer--Vietoris sequence starts with a zero**: the pair of restriction maps
`H⁰(X,F) ⟶ H⁰(U,F) ⊞ H⁰(V,F)` is a monomorphism. -/
@[stacks 01EB "the leading zero, in the right-derived model `Hgroup`"]
public theorem mono_mvFirst_zero (F : SheafOfModules.{u} O) :
    Mono ((mvFirst O U V 0).app F) := by
  have h1 : Mono ((NatTrans.rightDerived (toCover O (secF O ⊤) U V) 0).app F) :=
    CategoryTheory.mono_rightDerived_zero_app (toCover O (secF O ⊤) U V)
      (toIntersection O (secF O ⊤) U V) (toCover_comp_toIntersection O (secF O ⊤) U V)
      (fun M hM => secF_shortExact_on_injectives O U V hUV M hM) F
  have h2 : IsIso ((midIso O U V 0).hom.app F) :=
    inferInstanceAs (IsIso ((midIso O U V 0).app F).hom)
  show Mono ((NatTrans.rightDerived (toCover O (secF O ⊤) U V) 0).app F ≫
    (midIso O U V 0).hom.app F)
  infer_instance

end Hgroup

end Stacks.Cohomology.AbsoluteMayerVietoris

end
