module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffective
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

/-!
# Glueing modules of finite presentation in a closed fibre

Let `s` be a closed point of a scheme `S` whose open complement `U = S \ {s}` has quasi-compact
inclusion, and write `V = Spec 𝒪_{S, s} ∖ {s}` for the punctured local scheme.  A module of
finite presentation on `S` restricts to one on `U`, to one on `Spec 𝒪_{S, s}`, and the two
restrictions to `V` are canonically identified.  This file proves that this assignment is an
equivalence onto the category of triples `(𝒢, ℋ, α)`.

The proof is by flat descent.  The open `U` and the morphism `Spec 𝒪_{S, s} ⟶ S` form a
quasi-compact flat covering of `S`, so quasi-coherent modules on `S` are the same thing as
quasi-coherent descent data for that two-member family; and because both members have
monomorphic structure morphism with pullback `V`, such a descent datum is exactly a pair of
modules together with an isomorphism of their restrictions to `V`.  Finite presentation descends
along a flat covering, which is what cuts the equivalence down to the modules of finite
presentation.

## Main definitions

* `AlgebraicGeometry.GlueingNearPoint.FinitePresentationModules`: the category of modules of
  finite presentation on a scheme.
* `AlgebraicGeometry.GlueingNearPoint.moduleOverlapIso`: the canonical identification of the two
  restrictions to `V` of a module on `S`.
* `AlgebraicGeometry.GlueingNearPoint.moduleGlueingDataNearPoint`: the category of triples
  `(𝒢, ℋ, α)`.
* `AlgebraicGeometry.GlueingNearPoint.moduleRestrictionFunctorAtPoint`: the canonical functor
  from modules of finite presentation on `S` to such triples.
* `AlgebraicGeometry.GlueingNearPoint.BinaryDescent.datum`: the descent datum for a two-member
  family with monomorphic structure morphisms attached to an isomorphism over their pullback.

## Main results

* `AlgebraicGeometry.GlueingNearPoint.moduleGlueingEquivalenceNearClosedPoint`: the equivalence
  of categories, with the canonical functor as its forward direction.

## References

* [Stacks Project, Tag 0F21](https://stacks.math.columbia.edu/tag/0F21)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe w z t v u

namespace AlgebraicGeometry.GlueingNearPoint

/-! ### Descent data for a two-member family with monomorphic structure morphisms -/

namespace BinaryDescent

variable {C : Type t} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, z}}

/-- Pulling back comparison morphisms is compatible with composition. -/
lemma pullHom_comp_pullHom {X₁ X₂ X₃ Y Y' : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {M₃ : F.obj (.mk (op X₃))} {a : Y ⟶ X₁} {b : Y ⟶ X₂} {c : Y ⟶ X₃}
    (φ : (F.map a.op.toLoc).toFunctor.obj M₁ ⟶ (F.map b.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map b.op.toLoc).toFunctor.obj M₂ ⟶ (F.map c.op.toLoc).toFunctor.obj M₃)
    (g : Y' ⟶ Y) (ga : Y' ⟶ X₁) (gb : Y' ⟶ X₂) (gc : Y' ⟶ X₃)
    (ha : g ≫ a = ga) (hb : g ≫ b = gb) (hc : g ≫ c = gc) :
    pullHom φ g ga gb ha hb ≫ pullHom ψ g gb gc hb hc =
      pullHom (φ ≫ ψ) g ga gc ha hc := by
  simp [pullHom, Functor.map_comp, Category.assoc]

/-- Pulling back an identity comparison morphism gives an identity. -/
lemma pullHom_id_eq {X Y Y' : C} {M : F.obj (.mk (op X))}
    {a : Y ⟶ X} (g : Y' ⟶ Y) (ga : Y' ⟶ X) (ha : g ≫ a = ga) :
    pullHom (𝟙 ((F.map a.op.toLoc).toFunctor.obj M)) g ga ga ha ha = 𝟙 _ := by
  simp [pullHom]

/-- A commuting square of comparison morphisms stays commuting after pullback. -/
lemma pullHom_comm {X₁ X₂ Y Y' : C}
    {M₁ N₁ : F.obj (.mk (op X₁))} {M₂ N₂ : F.obj (.mk (op X₂))}
    {a : Y ⟶ X₁} {b : Y ⟶ X₂}
    (φ : (F.map a.op.toLoc).toFunctor.obj M₁ ⟶ (F.map b.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map a.op.toLoc).toFunctor.obj N₁ ⟶ (F.map b.op.toLoc).toFunctor.obj N₂)
    (left : M₁ ⟶ N₁) (right : M₂ ⟶ N₂)
    (comm : (F.map a.op.toLoc).toFunctor.map left ≫ ψ =
      φ ≫ (F.map b.op.toLoc).toFunctor.map right)
    (g : Y' ⟶ Y) (ga : Y' ⟶ X₁) (gb : Y' ⟶ X₂)
    (ha : g ≫ a = ga) (hb : g ≫ b = gb) :
    (F.map ga.op.toLoc).toFunctor.map left ≫ pullHom ψ g ga gb ha hb =
      pullHom φ g ga gb ha hb ≫ (F.map gb.op.toLoc).toFunctor.map right := by
  simp only [pullHom, Category.assoc, F.mapComp'_hom_naturality_assoc,
    ← Functor.map_comp_assoc, comm, Functor.map_comp, F.mapComp'_inv_naturality]

/-- The two members of a two-member family. -/
abbrev pieces (U T : C) : Bool → C
  | false => U
  | true => T

/-- The two structure morphisms of a two-member family. -/
abbrev arrows {U T S : C} (fU : U ⟶ S) (fT : T ⟶ S) :
    ∀ index, pieces U T index ⟶ S
  | false => fU
  | true => fT

/-- A pair of objects, one over each member of a two-member family. -/
abbrev objects {U T : C} (M : F.obj (.mk (op U))) (N : F.obj (.mk (op T))) :
    ∀ index, F.obj (.mk (op (pieces U T index)))
  | false => M
  | true => N

/-- A pair of morphisms of descent data, read as a family indexed by the two members. -/
abbrev maps {S U T : C} {fU : U ⟶ S} {fT : T ⟶ S}
    {D E : F.DescentData (arrows fU fT)}
    (left : D.obj false ⟶ E.obj false) (right : D.obj true ⟶ E.obj true) :
    ∀ index, D.obj index ⟶ E.obj index
  | false => left
  | true => right

variable {U T S V : C} {fU : U ⟶ S} {fT : T ⟶ S} {j : V ⟶ U} {k : V ⟶ T}
  [Mono fU] [Mono fT] (square : IsPullback j k fU fT)
  {M : F.obj (.mk (op U))} {N : F.obj (.mk (op T))}
  (α : (F.map j.op.toLoc).toFunctor.obj M ≅ (F.map k.op.toLoc).toFunctor.obj N)

/-- Two morphisms into the same member of the family with the same composite to `S` are equal. -/
private lemma eq_of_comp_arrows_eq {Y : C} {index : Bool} {a b : Y ⟶ pieces U T index}
    (h : a ≫ arrows fU fT index = b ≫ arrows fU fT index) : a = b := by
  cases index
  exacts [(cancel_mono fU).mp h, (cancel_mono fT).mp h]

/-- A pair of morphisms commuting with the comparison over the pullback commutes with every
comparison of the descent data. -/
lemma descentHom_comm
    (D E : F.DescentData (arrows fU fT))
    (left : D.obj false ⟶ E.obj false) (right : D.obj true ⟶ E.obj true)
    (comm : (F.map j.op.toLoc).toFunctor.map left ≫
        E.hom (i₁ := false) (i₂ := true) (j ≫ fU) j k rfl square.w.symm =
      D.hom (i₁ := false) (i₂ := true) (j ≫ fU) j k rfl square.w.symm ≫
        (F.map k.op.toLoc).toFunctor.map right)
    {Y : C} (q : Y ⟶ S) {first second : Bool}
    (a : Y ⟶ pieces U T first) (b : Y ⟶ pieces U T second)
    (ha : a ≫ arrows fU fT first = q) (hb : b ≫ arrows fU fT second = q) :
    (F.map a.op.toLoc).toFunctor.map (maps left right first) ≫
      E.hom q a b ha hb =
    D.hom q a b ha hb ≫
      (F.map b.op.toLoc).toFunctor.map (maps left right second) := by
  cases first <;> cases second
  · obtain rfl := eq_of_comp_arrows_eq (ha.trans hb.symm)
    rw [E.hom_self (i := false) q a ha, D.hom_self (i := false) q a ha]
    simp
  · let lift := square.lift a b (ha.trans hb.symm)
    have hl : lift ≫ j = a := square.lift_fst ..
    have hr : lift ≫ k = b := square.lift_snd ..
    have hq : lift ≫ (j ≫ fU) = q := by rw [← Category.assoc, hl, ha]
    rw [← E.pullHom_hom (i₁ := false) (i₂ := true) lift (j ≫ fU) q hq j k rfl
        square.w.symm a b hl hr,
      ← D.pullHom_hom (i₁ := false) (i₂ := true) lift (j ≫ fU) q hq j k rfl
        square.w.symm a b hl hr]
    exact pullHom_comm _ _ left right comm lift a b hl hr
  · let lift := square.lift b a (hb.trans ha.symm)
    have hl : lift ≫ j = b := square.lift_fst ..
    have hr : lift ≫ k = a := square.lift_snd ..
    have hq : lift ≫ (j ≫ fU) = q := by rw [← Category.assoc, hl, hb]
    have reverse : (F.map k.op.toLoc).toFunctor.map right ≫
        E.hom (i₁ := true) (i₂ := false) (j ≫ fU) k j square.w.symm rfl =
      D.hom (i₁ := true) (i₂ := false) (j ≫ fU) k j square.w.symm rfl ≫
        (F.map j.op.toLoc).toFunctor.map left := by
      rw [← cancel_mono (E.hom (i₁ := false) (i₂ := true) (j ≫ fU) j k rfl square.w.symm)]
      rw [Category.assoc, E.hom_comp (i₁ := true) (i₂ := false) (i₃ := true)
          (j ≫ fU) k j k square.w.symm rfl square.w.symm,
        E.hom_self (i := true) (j ≫ fU) k square.w.symm, Category.comp_id,
        Category.assoc, comm, ← Category.assoc,
        D.hom_comp (i₁ := true) (i₂ := false) (i₃ := true)
          (j ≫ fU) k j k square.w.symm rfl square.w.symm,
        D.hom_self (i := true) (j ≫ fU) k square.w.symm, Category.id_comp]
    rw [← E.pullHom_hom (i₁ := true) (i₂ := false) lift (j ≫ fU) q hq k j square.w.symm rfl
        a b hr hl,
      ← D.pullHom_hom (i₁ := true) (i₂ := false) lift (j ≫ fU) q hq k j square.w.symm rfl
        a b hr hl]
    exact pullHom_comm _ _ right left reverse lift a b hr hl
  · obtain rfl := eq_of_comp_arrows_eq (ha.trans hb.symm)
    rw [E.hom_self (i := true) q a ha, D.hom_self (i := true) q a ha]
    simp

/-- The comparison morphisms of the descent datum built from a single isomorphism over the
pullback: over an object mapping to both members it is a pullback of that isomorphism, and over
an object mapping twice to the same member it is an identity. -/
noncomputable def transition {Y : C} (q : Y ⟶ S) {first second : Bool}
    (a : Y ⟶ pieces U T first) (b : Y ⟶ pieces U T second)
    (ha : a ≫ arrows fU fT first = q) (hb : b ≫ arrows fU fT second = q) :
    (F.map a.op.toLoc).toFunctor.obj (objects M N first) ⟶
      (F.map b.op.toLoc).toFunctor.obj (objects M N second) := by
  cases first <;> cases second
  · exact eqToHom (congrArg (fun morphism : Y ⟶ U =>
        (F.map morphism.op.toLoc).toFunctor.obj M) ((cancel_mono fU).mp (ha.trans hb.symm)))
  · exact pullHom α.hom (square.lift a b (ha.trans hb.symm)) a b
      (square.lift_fst ..) (square.lift_snd ..)
  · exact pullHom α.inv (square.lift b a (hb.trans ha.symm)) a b
      (square.lift_snd ..) (square.lift_fst ..)
  · exact eqToHom (congrArg (fun morphism : Y ⟶ T =>
        (F.map morphism.op.toLoc).toFunctor.obj N) ((cancel_mono fT).mp (ha.trans hb.symm)))

/-- Every comparison morphism of `transition` from a member to itself is an identity. -/
lemma transition_self {Y : C} (q : Y ⟶ S) {index : Bool}
    (a : Y ⟶ pieces U T index) (ha : a ≫ arrows fU fT index = q) :
    transition square α q a a ha ha = 𝟙 _ := by
  cases index <;> simp [transition]

/-- `transition` is compatible with further pullback. -/
lemma transition_pull {Y Y' : C} (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    (hq : g ≫ q = q') {first second : Bool}
    (a : Y ⟶ pieces U T first) (b : Y ⟶ pieces U T second)
    (ha : a ≫ arrows fU fT first = q) (hb : b ≫ arrows fU fT second = q)
    (ga : Y' ⟶ pieces U T first) (gb : Y' ⟶ pieces U T second)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb) :
    pullHom (transition square α q a b ha hb) g ga gb hga hgb =
      transition square α q' ga gb (by rw [← hga, Category.assoc, ha, hq])
        (by rw [← hgb, Category.assoc, hb, hq]) := by
  cases first <;> cases second
  all_goals try obtain rfl := eq_of_comp_arrows_eq (ha.trans hb.symm)
  all_goals try obtain rfl : ga = g ≫ a := hga.symm
  all_goals try obtain rfl : gb = g ≫ a := hgb.symm
  all_goals try
    simp only [transition, eqToHom_refl]
    exact pullHom_id_eq g (g ≫ a) rfl
  all_goals
    simp only [transition, pullHom_pullHom]
    congr 1
    apply square.hom_ext <;> simp [Category.assoc, hgb]

/-- `transition` satisfies the cocycle condition. -/
lemma transition_comp {Y : C} (q : Y ⟶ S) {first second third : Bool}
    (a : Y ⟶ pieces U T first) (b : Y ⟶ pieces U T second)
    (c : Y ⟶ pieces U T third)
    (ha : a ≫ arrows fU fT first = q) (hb : b ≫ arrows fU fT second = q)
    (hc : c ≫ arrows fU fT third = q) :
    transition square α q a b ha hb ≫ transition square α q b c hb hc =
      transition square α q a c ha hc := by
  cases first <;> cases second <;> cases third
  all_goals try obtain rfl := eq_of_comp_arrows_eq (ha.trans hb.symm)
  all_goals try obtain rfl := eq_of_comp_arrows_eq (hb.trans hc.symm)
  all_goals try obtain rfl := eq_of_comp_arrows_eq (ha.trans hc.symm)
  all_goals
    simp [transition, pullHom_comp_pullHom, pullHom_id_eq]

/-- The descent datum for a two-member family with monomorphic structure morphisms attached to
an isomorphism of the two restrictions to the pullback. -/
noncomputable def datum : F.DescentData (arrows fU fT) where
  obj := objects M N
  hom := fun {_} q {_ _} a b ha hb => transition square α q a b ha hb
  pullHom_hom := by
    intros
    apply transition_pull square α
    assumption
  hom_self := by
    intros
    apply transition_self square α
  hom_comp := by
    intros
    apply transition_comp square α

/-- The comparison morphism of `datum` over the pullback is the given isomorphism. -/
lemma datum_overlap :
    (datum square α).hom (i₁ := false) (i₂ := true) (j ≫ fU) j k rfl square.w.symm =
      α.hom := by
  dsimp only [datum, transition]
  have hlift : square.lift j k square.w = 𝟙 V := by
    apply square.hom_ext <;> simp
  simpa only [hlift] using (pullHom_id α.hom)

/-- A morphism of descent data for a two-member family with monomorphic structure morphisms,
built from a pair of morphisms commuting with the comparison over the pullback. -/
noncomputable def homMk (D E : F.DescentData (arrows fU fT))
    (left : D.obj false ⟶ E.obj false) (right : D.obj true ⟶ E.obj true)
    (comm : (F.map j.op.toLoc).toFunctor.map left ≫
        E.hom (i₁ := false) (i₂ := true) (j ≫ fU) j k rfl square.w.symm =
      D.hom (i₁ := false) (i₂ := true) (j ≫ fU) j k rfl square.w.symm ≫
        (F.map k.op.toLoc).toFunctor.map right) : D ⟶ E where
  hom := maps left right
  comm := by
    intros
    exact descentHom_comm square D E left right comm _ _ _ _ _

end BinaryDescent

open BinaryDescent

/-! ### Modules of finite presentation and their restrictions -/

/-- The category of modules of finite presentation on a scheme. -/
abbrev FinitePresentationModules (X : Scheme.{u}) :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).FullSubcategory

/-- Restriction of a module of finite presentation along a morphism of schemes, taking values in
all modules on the source. -/
noncomputable abbrev finitePresentationModuleRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FinitePresentationModules Y ⥤ X.Modules :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).ι ⋙ Scheme.Modules.pullback f

/-- Restriction of a module of finite presentation along a morphism of schemes. -/
noncomputable def finitePresentationModulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FinitePresentationModules Y ⥤ FinitePresentationModules X :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).lift
    (finitePresentationModuleRestriction f)
    fun M ↦ Stacks.Modules.isFinitePresentation_pullback f M.obj M.property

/-- A module of finite presentation is quasi-coherent, functorially. -/
noncomputable def finitePresentationToQuasicoherent (X : Scheme.{u}) :
    FinitePresentationModules X ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι
    fun M ↦ Stacks.Modules.isQuasicoherent_of_isFinitePresentation (h := M.property) M.obj

/-- The canonical identification of the two restrictions to `V = f⁻¹(U)` of a module on `S`:
restrict to `U` and then to `V`, or restrict along `f` and then to `V`. -/
noncomputable def moduleOverlapNatIso {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens) :
    Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (f ⁻¹ᵁ U).ι :=
  Scheme.Modules.pullbackComp (f ∣_ U) U.ι ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U) ≪≫
      (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).symm

/-- The canonical identification of the two restrictions to `V = f⁻¹(U)` of a module on `S`. -/
noncomputable def moduleOverlapIso {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens)
    (M : S.Modules) :
    (Scheme.Modules.pullback (f ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj M) ≅
      (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj M) :=
  (moduleOverlapNatIso f U).app M

/-- Glueing data for modules near a point: a module of finite presentation on `U`, one on
`Spec 𝒪_{S, s}`, and an isomorphism `α` of their restrictions to the punctured local scheme. -/
noncomputable abbrev moduleGlueingDataNearPoint (S : Scheme.{u}) (U : S.Opens) (s : S) :=
  IsoComma (finitePresentationModuleRestriction (S.fromSpecStalk s ∣_ U))
    (finitePresentationModuleRestriction ((S.fromSpecStalk s) ⁻¹ᵁ U).ι)

/-- The projection of a module glueing datum to its component on the open `U`. -/
noncomputable def moduleOpenComponent (S : Scheme.{u}) (U : S.Opens) (s : S) :
    moduleGlueingDataNearPoint S U s ⥤ FinitePresentationModules U.toScheme :=
  (show ObjectProperty (Comma (finitePresentationModuleRestriction (S.fromSpecStalk s ∣_ U))
      (finitePresentationModuleRestriction ((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) from
    fun X ↦ IsIso X.hom).ι ⋙ Comma.fst _ _

/-- The projection of a module glueing datum to its component on `Spec 𝒪_{S, s}`. -/
noncomputable def moduleLocalComponent (S : Scheme.{u}) (U : S.Opens) (s : S) :
    moduleGlueingDataNearPoint S U s ⥤
      FinitePresentationModules (Spec (S.presheaf.stalk s)) :=
  (show ObjectProperty (Comma (finitePresentationModuleRestriction (S.fromSpecStalk s ∣_ U))
      (finitePresentationModuleRestriction ((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) from
    fun X ↦ IsIso X.hom).ι ⋙ Comma.snd _ _

/-- **Stacks 0F21**, the canonical functor.  A module of finite presentation on `S` goes to its
restriction to `U`, its restriction to `Spec 𝒪_{S, s}`, and the canonical identification of the
two restrictions to the punctured local scheme. -/
@[stacks 0F21 "the canonical functor"]
noncomputable def moduleRestrictionFunctorAtPoint (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationModules S ⥤ moduleGlueingDataNearPoint S U s :=
  (show ObjectProperty (Comma (finitePresentationModuleRestriction (S.fromSpecStalk s ∣_ U))
      (finitePresentationModuleRestriction ((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) from
    fun X ↦ IsIso X.hom).lift
    { obj := fun M ↦ ⟨(finitePresentationModulePullback U.ι).obj M,
        (finitePresentationModulePullback (S.fromSpecStalk s)).obj M,
        (moduleOverlapNatIso (S.fromSpecStalk s) U).hom.app M.obj⟩
      map := fun φ ↦ ⟨(finitePresentationModulePullback U.ι).map φ,
        (finitePresentationModulePullback (S.fromSpecStalk s)).map φ,
        (moduleOverlapNatIso (S.fromSpecStalk s) U).hom.naturality φ.hom⟩
      map_id := by intro X; ext <;> simp
      map_comp := by intro X Y Z f g; ext <;> simp }
    fun M ↦ ((moduleOverlapNatIso (S.fromSpecStalk s) U).app M.obj).isIso_hom

/-- The component of the canonical functor on the open `U` is restriction to `U`. -/
theorem moduleOpenComponent_comp_moduleRestrictionFunctorAtPoint (S : Scheme.{u})
    (U : S.Opens) (s : S) :
    moduleRestrictionFunctorAtPoint S U s ⋙ moduleOpenComponent S U s =
      finitePresentationModulePullback U.ι :=
  rfl

/-- The component of the canonical functor on `Spec 𝒪_{S, s}` is restriction along
`Spec 𝒪_{S, s} ⟶ S`. -/
theorem moduleLocalComponent_comp_moduleRestrictionFunctorAtPoint (S : Scheme.{u})
    (U : S.Opens) (s : S) :
    moduleRestrictionFunctorAtPoint S U s ⋙ moduleLocalComponent S U s =
      finitePresentationModulePullback (S.fromSpecStalk s) :=
  rfl

/-- The comparison morphism of the glueing datum produced by the canonical functor is the
canonical identification of the two restrictions. -/
theorem moduleRestrictionFunctorAtPoint_obj_hom (S : Scheme.{u}) (U : S.Opens) (s : S)
    (M : FinitePresentationModules S) :
    ((moduleRestrictionFunctorAtPoint S U s).obj M).obj.hom =
      (moduleOverlapIso (S.fromSpecStalk s) U M.obj).hom :=
  rfl

/-! ### The canonical descent datum of a module, over the pullback -/

/-- Composing the canonical identification with the comparison for the second member of the
family gives the comparison for the first member. -/
theorem moduleOverlapIso_hom_comp {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens)
    (M : S.Modules) :
    (moduleOverlapIso f U M).hom ≫
        ((Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
          (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M).hom =
      Stacks.Descent.pullbackCompHom (f ∣_ U) U.ι ((f ∣_ U) ≫ U.ι) rfl M := by
  have hsymm : Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm =
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U)).symm := rfl
  have hrfl : Scheme.Modules.pullbackCongr (rfl : (f ∣_ U) ≫ U.ι = (f ∣_ U) ≫ U.ι) =
      Iso.refl (Scheme.Modules.pullback ((f ∣_ U) ≫ U.ι)) := rfl
  rw [Stacks.Descent.pullbackCompHom_eq_hom, hsymm, hrfl]
  simp [moduleOverlapIso, moduleOverlapNatIso]

/-- The comparison morphism of the canonical descent datum of `M`, over the pullback of the two
members of the family, is the canonical identification of the two restrictions. -/
theorem ofObj_hom_eq_moduleOverlapIso {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens)
    (M : S.Modules) :
    (Pseudofunctor.DescentData.ofObj (F := modulePullbackPseudofunctor)
        (f := arrows U.ι f) M).hom (i₁ := false) (i₂ := true)
        ((f ∣_ U) ≫ U.ι) (f ∣_ U) (f ⁻¹ᵁ U).ι rfl (morphismRestrict_ι f U).symm =
      (moduleOverlapIso f U M).hom := by
  have key := Stacks.Descent.ofObj_hom_comp_pullbackCompHom (f := arrows U.ι f) M
    ((f ∣_ U) ≫ U.ι) (i₁ := false) (i₂ := true) (f ∣_ U) (f ⁻¹ᵁ U).ι rfl
    (morphismRestrict_ι f U).symm
  exact (cancel_mono (((Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M).hom)).mp
      (key.trans (moduleOverlapIso_hom_comp f U M).symm)

/-- The comparison morphism of the canonical quasi-coherent descent datum of `M`, over the
pullback of the two members of the family. -/
theorem canonicalDescentFunctor_obj_hom_overlap {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens)
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    ((canonicalDescentFunctor (arrows U.ι f)).obj M).obj.hom (i₁ := false) (i₂ := true)
        ((f ∣_ U) ≫ U.ι) (f ∣_ U) (f ⁻¹ᵁ U).ι rfl (morphismRestrict_ι f U).symm =
      (moduleOverlapIso f U M.obj).hom :=
  ofObj_hom_eq_moduleOverlapIso f U M.obj

/-! ### The two-member flat covering of `S` -/

variable {S : Scheme.{u}} {s : S}

/-- `U = S \ {s}` together with `Spec 𝒪_{S, s} ⟶ S` is a quasi-compact flat covering of `S`. -/
noncomputable def puncturedCover (hs : IsClosed ({s} : Set S))
    [QuasiCompact (puncturedOpen hs).ι] : S.Cover.{0} Scheme.fpqcPrecoverage := by
  have : Flat (S.fromSpecStalk s) := flat_fromSpecStalk S s
  let cover : S.Cover.{0} (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers Bool (pieces (puncturedOpen hs).toScheme
        (Spec (S.presheaf.stalk s))) (arrows (puncturedOpen hs).ι (S.fromSpecStalk s))
      (fun x => by
        obtain rfl | hxs := eq_or_ne x s
        · exact ⟨true, IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
        · exact ⟨false, ⟨x, hxs⟩, rfl⟩)
      (fun index => by cases index <;> infer_instance)
  have : QuasiCompactCover cover.toPreZeroHypercover := by
    refine ⟨fun {W} hW => ?_⟩
    classical
    let localOpen : (Spec (S.presheaf.stalk s)).Opens := if s ∈ W then ⊤ else ⊥
    let opens : ∀ index,
        (pieces (puncturedOpen hs).toScheme (Spec (S.presheaf.stalk s)) index).Opens
      | false => (puncturedOpen hs).ι ⁻¹ᵁ W
      | true => localOpen
    apply IsCompactOpenCovered.of_finite (fun index : Bool => index) opens
    · rintro (_ | _)
      · exact hW.isCompact.preimage_of_isOpen (puncturedOpen hs).ι.isSpectralMap W.2
      · dsimp only [opens, localOpen]
        split
        · exact isCompact_univ
        · exact isCompact_empty
    · ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨index, y, hy, rfl⟩
        cases index
        · exact hy
        · have hsW : s ∈ W := by
            by_contra hsW
            simp [opens, localOpen, hsW] at hy
          have hmem : S.fromSpecStalk s y ∈ Set.range (S.fromSpecStalk s) := ⟨y, rfl⟩
          rw [Scheme.range_fromSpecStalk] at hmem
          exact hmem.mem_open W.2 hsW
      · intro hx
        obtain rfl | hxs := eq_or_ne x s
        · refine ⟨true, IsLocalRing.closedPoint _, ?_, Scheme.fromSpecStalk_closedPoint⟩
          simp only [opens, localOpen, ite_eq_left (show x ∈ W from hx)]
          trivial
        · exact ⟨false, ⟨x, hxs⟩, hx, rfl⟩
  exact cover.ofQuasiCompactCover

/-! ### Full faithfulness and essential surjectivity -/

/-- The quasi-coherent descent datum attached to a module glueing datum. -/
noncomputable def glueingDescentDatum (hs : IsClosed ({s} : Set S))
    (D : moduleGlueingDataNearPoint S (puncturedOpen hs) s) :
    QuasicoherentDescentData (arrows (puncturedOpen hs).ι (S.fromSpecStalk s)) :=
  ⟨datum (F := modulePullbackPseudofunctor)
      (isPullback_morphismRestrict (S.fromSpecStalk s) (puncturedOpen hs))
      (@asIso _ _ _ _ D.obj.hom D.property),
    fun index => by
      cases index
      · exact Stacks.Modules.isQuasicoherent_of_isFinitePresentation
          (h := D.obj.left.property) D.obj.left.obj
      · exact Stacks.Modules.isQuasicoherent_of_isFinitePresentation
          (h := D.obj.right.property) D.obj.right.obj⟩

/-- The comparison morphism of `glueingDescentDatum` over the pullback is the isomorphism `α` of
the glueing datum. -/
theorem glueingDescentDatum_overlap (hs : IsClosed ({s} : Set S))
    (D : moduleGlueingDataNearPoint S (puncturedOpen hs) s) :
    (glueingDescentDatum hs D).obj.hom (i₁ := false) (i₂ := true)
        ((S.fromSpecStalk s ∣_ puncturedOpen hs) ≫ (puncturedOpen hs).ι)
        (S.fromSpecStalk s ∣_ puncturedOpen hs)
        (S.fromSpecStalk s ⁻¹ᵁ puncturedOpen hs).ι rfl
        (morphismRestrict_ι (S.fromSpecStalk s) (puncturedOpen hs)).symm = D.obj.hom :=
  datum_overlap (F := modulePullbackPseudofunctor)
    (isPullback_morphismRestrict (S.fromSpecStalk s) (puncturedOpen hs))
    (@asIso _ _ _ _ D.obj.hom D.property)

/-- An isomorphism from the canonical descent datum of a quasi-coherent module to an arbitrary
quasi-coherent descent datum gives the compatibility square over the pullback.  The comparison
of the target datum is taken as a separate argument `α`. -/
theorem descentData_comparison_square {T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens)
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (E : QuasicoherentDescentData (arrows U.ι f))
    (α : (Scheme.Modules.pullback (f ∣_ U)).obj (E.obj.obj false) ⟶
      (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (E.obj.obj true))
    (hα : E.obj.hom (i₁ := false) (i₂ := true) ((f ∣_ U) ≫ U.ι) (f ∣_ U) (f ⁻¹ᵁ U).ι rfl
      (morphismRestrict_ι f U).symm = α)
    (cmp : (canonicalDescentFunctor (arrows U.ι f)).obj M ≅ E) :
    (Scheme.Modules.pullback (f ∣_ U)).map (cmp.hom.hom.hom false) ≫ α =
      (moduleOverlapIso f U M.obj).hom ≫
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map (cmp.hom.hom.hom true) := by
  have hcomm := cmp.hom.hom.comm (i₁ := false) (i₂ := true) ((f ∣_ U) ≫ U.ι) (f ∣_ U)
    (f ⁻¹ᵁ U).ι rfl (morphismRestrict_ι f U).symm
  rwa [hα, canonicalDescentFunctor_obj_hom_overlap] at hcomm

/-- A pair of morphisms of modules compatible with the canonical identifications on the overlap
is a morphism of the canonical descent data. -/
noncomputable def canonicalDescentHomOfGluing {T : Scheme.{u}}
    (f : T ⟶ S) [Mono f] (U : S.Opens)
    (M N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (left : (Scheme.Modules.pullback U.ι).obj M.obj ⟶
      (Scheme.Modules.pullback U.ι).obj N.obj)
    (right : (Scheme.Modules.pullback f).obj M.obj ⟶
      (Scheme.Modules.pullback f).obj N.obj)
    (comm : (Scheme.Modules.pullback (f ∣_ U)).map left ≫ (moduleOverlapIso f U N.obj).hom =
      (moduleOverlapIso f U M.obj).hom ≫
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map right) :
    (canonicalDescentFunctor (arrows U.ι f)).obj M ⟶
      (canonicalDescentFunctor (arrows U.ι f)).obj N := by
  refine ⟨homMk (isPullback_morphismRestrict f U) _ _ left right ?_⟩
  rwa [canonicalDescentFunctor_obj_hom_overlap f U N,
    canonicalDescentFunctor_obj_hom_overlap f U M]

/-- The lift of a morphism of module glueing data to a morphism of canonical descent data. -/
noncomputable def glueingDescentLift (hs : IsClosed ({s} : Set S))
    {M N : FinitePresentationModules S}
    (φ : (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).obj M ⟶
      (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).obj N) :
    (canonicalDescentFunctor (arrows (puncturedOpen hs).ι (S.fromSpecStalk s))).obj
        ((finitePresentationToQuasicoherent S).obj M) ⟶
      (canonicalDescentFunctor (arrows (puncturedOpen hs).ι (S.fromSpecStalk s))).obj
        ((finitePresentationToQuasicoherent S).obj N) :=
  canonicalDescentHomOfGluing (S.fromSpecStalk s) (puncturedOpen hs)
    ((finitePresentationToQuasicoherent S).obj M)
    ((finitePresentationToQuasicoherent S).obj N)
    φ.hom.left.hom φ.hom.right.hom φ.hom.w

/-- The canonical descent functor for the two-member covering is fully faithful. -/
noncomputable def puncturedDescentFullyFaithful (hs : IsClosed ({s} : Set S))
    [QuasiCompact (puncturedOpen hs).ι] :
    (canonicalDescentFunctor
      (arrows (puncturedOpen hs).ι (S.fromSpecStalk s))).FullyFaithful :=
  (QuasicoherentDescentData.nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage
    (puncturedCover hs).toPreZeroHypercover (puncturedCover hs).mem₀).some

/-- The canonical functor is fully faithful. -/
noncomputable def moduleRestrictionFunctorAtPoint_fullyFaithful
    (hs : IsClosed ({s} : Set S)) [QuasiCompact (puncturedOpen hs).ι] :
    (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).FullyFaithful := by
  let fullyFaithful := puncturedDescentFullyFaithful hs
  refine
    { preimage := fun φ => ⟨(fullyFaithful.preimage (glueingDescentLift hs φ)).hom⟩
      map_preimage := ?_
      preimage_map := ?_ }
  · intro M N φ
    have hmap := fullyFaithful.map_preimage (glueingDescentLift hs φ)
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> apply ObjectProperty.hom_ext
    · exact congrArg (fun ψ => ψ.hom.hom false) hmap
    · exact congrArg (fun ψ => ψ.hom.hom true) hmap
  · intro M N φ
    apply ObjectProperty.hom_ext
    have hlift : glueingDescentLift hs
        ((moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).map φ) =
          (canonicalDescentFunctor (arrows (puncturedOpen hs).ι (S.fromSpecStalk s))).map
            ((finitePresentationToQuasicoherent S).map φ) := by
      apply ObjectProperty.hom_ext
      apply Pseudofunctor.DescentData.hom_ext
      intro index
      cases index <;> rfl
    change (fullyFaithful.preimage (glueingDescentLift hs
      ((moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).map φ))).hom = φ.hom
    rw [hlift, fullyFaithful.preimage_map]
    rfl

/-- The canonical functor is essentially surjective. -/
lemma moduleRestrictionFunctorAtPoint_essSurj (hs : IsClosed ({s} : Set S))
    [QuasiCompact (puncturedOpen hs).ι] :
    (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).EssSurj := by
  refine ⟨fun D => ?_⟩
  obtain ⟨M, ⟨comparison⟩⟩ := QuasicoherentDescentData.isEffective_fpqcPrecoverage
    (puncturedCover hs).toPreZeroHypercover (puncturedCover hs).mem₀ (glueingDescentDatum hs D)
  have cmp : (canonicalDescentFunctor
      (arrows (puncturedOpen hs).ι (S.fromSpecStalk s))).obj M ≅ glueingDescentDatum hs D :=
    comparison
  let componentIso (index : Bool) :
      ((Scheme.Modules.pullback
          (arrows (puncturedOpen hs).ι (S.fromSpecStalk s) index)).obj M.obj) ≅
        (glueingDescentDatum hs D).obj.obj index :=
    { hom := cmp.hom.hom.hom index
      inv := cmp.inv.hom.hom index
      hom_inv_id := congrArg (fun ψ => ψ.hom.hom index) cmp.hom_inv_id
      inv_hom_id := congrArg (fun ψ => ψ.hom.hom index) cmp.inv_hom_id }
  have finitePresentation : M.obj.IsFinitePresentation :=
    isFinitePresentation_of_pullback_fpqcCover M.obj (puncturedCover hs) (by
      intro index
      cases index
      · exact (SheafOfModules.isFinitePresentation
          (puncturedOpen hs).toScheme.ringCatSheaf).prop_of_iso
            (componentIso false).symm D.obj.left.property
      · exact (SheafOfModules.isFinitePresentation (Spec (S.presheaf.stalk s)).ringCatSheaf)
          |>.prop_of_iso (componentIso true).symm D.obj.right.property)
  let ambient : FinitePresentationModules S := ⟨M.obj, finitePresentation⟩
  let leftIso : ((moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).obj
      ambient).obj.left ≅ D.obj.left :=
    ObjectProperty.isoMk
      (SheafOfModules.isFinitePresentation (puncturedOpen hs).toScheme.ringCatSheaf)
      (componentIso false)
  let rightIso : ((moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).obj
      ambient).obj.right ≅ D.obj.right :=
    ObjectProperty.isoMk
      (SheafOfModules.isFinitePresentation (Spec (S.presheaf.stalk s)).ringCatSheaf)
      (componentIso true)
  exact ⟨ambient, ⟨ObjectProperty.isoMk (fun X => IsIso X.hom)
    (Comma.isoMk leftIso rightIso
      (descentData_comparison_square (S.fromSpecStalk s) (puncturedOpen hs) M
        (glueingDescentDatum hs D) D.obj.hom (glueingDescentDatum_overlap hs D) cmp))⟩⟩

/-- **Stacks 0F21.** Let `s` be a closed point of a scheme `S` whose open complement
`U = S \ {s}` has quasi-compact inclusion, and let `V = Spec 𝒪_{S, s} ∖ {s}`.  Restricting a
module of finite presentation on `S` to `U` and to `Spec 𝒪_{S, s}`, together with the canonical
identification `α` of the two induced restrictions to `V`, is an equivalence onto the category
of triples `(𝒢, ℋ, α)`. -/
@[stacks 0F21]
noncomputable def moduleGlueingEquivalenceNearClosedPoint (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι) :
    FinitePresentationModules S ≌ moduleGlueingDataNearPoint S (puncturedOpen hs) s := by
  have := hqc
  have : (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).Full :=
    (moduleRestrictionFunctorAtPoint_fullyFaithful hs).full
  have : (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).Faithful :=
    (moduleRestrictionFunctorAtPoint_fullyFaithful hs).faithful
  have : (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).EssSurj :=
    moduleRestrictionFunctorAtPoint_essSurj hs
  have : (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).IsEquivalence := {}
  exact (moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s).asEquivalence

/-- The forward direction of the glueing equivalence is the canonical restriction functor. -/
theorem moduleGlueingEquivalenceNearClosedPoint_functor (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι) :
    (moduleGlueingEquivalenceNearClosedPoint S s hs hqc).functor =
      moduleRestrictionFunctorAtPoint S (puncturedOpen hs) s :=
  rfl

end AlgebraicGeometry.GlueingNearPoint

end
