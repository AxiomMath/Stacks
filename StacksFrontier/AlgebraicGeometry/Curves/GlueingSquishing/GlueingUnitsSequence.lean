module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingTwoPoints
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingTangentVector
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule
public import StacksFrontier.Topology.Sheaves.Sheaf.Abelian

/-!
# The sheaf of units of a glueing of two rational points

Let `k` be an algebraically closed field and let `f : X' ⟶ X` glue the two distinct rational
points `a` and `b` of an algebraic `k`-scheme `X'` to the point `x` of `X`, in the sense of
[Stacks, Tag 0C1J]. [Stacks, Tag 0C1M] reads its exact sequence of Picard groups off a short
exact sequence of *sheaves of units* on `X` followed by the low-degree cohomology sequence.
This file supplies that short exact sequence,

`1 ⟶ 𝒪_X^* ⟶ f_*𝒪_{X'}^* ⟶ (k^*)_x ⟶ 1`,

whose second map sends a unit `h` on `f ⁻¹ᵁ U` to the ratio `h(a) h(b)⁻¹` of its two values.

## Main definitions

* `Stacks.GlueSquishUnits.unitRatioAt` is the multiplicative ratio `h(a) h(b)⁻¹` of the values
  of a unit at two rational points.
* `Stacks.GlueSquishUnits.skyscraperUnitsSheaf` is the skyscraper sheaf with fibre `kˣ`, written
  additively, and `Stacks.GlueSquishUnits.skyscraperUnitsEval` identifies its sections over an
  open containing the point with that fibre.

## Main results

* `Stacks.GlueSquishUnits.isShortExact_units_of_isGlueingTwoPoints` — the short exact sequence
  of sheaves of units attached to a glueing of two rational points, together with the
  description of both of its maps on sections.

## Implementation notes

The units sheaf is `Stacks.Cohomology.Generators.unitsSheaf`, the structure sheaf composed with
the unit-group functor; its sections over `U` are therefore definitionally `Additive Γ(X, U)ˣ`,
and the whole sequence lives in the category of sheaves of *additive* commutative groups, where
`CategoryTheory.ShortComplex.ShortExact` is available. Both multiplicative groups — the units of
a ring and `kˣ` — are consequently written additively, through `Additive.ofMul`.

The quotient map is built from the stalk at the glued point by
`StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf`, which is how one produces a map to
a skyscraper sheaf: a section of the skyscraper over an open containing the point is an element
of the fibre, and over an open missing it there is nothing to say. Because
`skyscraperPresheaf` is defined by an `if`, that identification of the sections with the
fibre is an `eqToHom`; it is named `skyscraperUnitsEval`, and it is through it rather than
through a transported equality that the second map is pinned down on sections. Its two
properties — compatibility with restriction, and the computation of the map to the skyscraper —
are both read off `StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk`, which is the one
statement in Mathlib that relates sections of a skyscraper to the stalk without passing through
the `if`.

Exactness is checked on stalks, which for sheaves of abelian groups on a space is
`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`. This is packaged as
`TopCat.Sheaf.shortExact_of_local`, which reduces all three conditions to germ-local
statements of exactly the shape the three final clauses of `AlgebraicGeometry.IsGlueingTwoPoints`
provide. Away from the glued point `f` is an isomorphism on a neighbourhood, which settles all
three there.

Membership hypotheses are always carried in the spelling the consumer wants — `a(p) ∈ f ⁻¹ᵁ U`
for `AlgebraicGeometry.sectionAt` upstairs, `gluedPoint f a ∈ U` for the skyscraper and
`(a ≫ f)(p) ∈ U` for the clauses of `AlgebraicGeometry.IsGlueingTwoPoints` — and converted
between the three by `mem_preimage_left`, `mem_preimage_right` and `mem_comp`. The three are
definitionally equal, but a hypothesis of the wrong spelling makes the surrounding term fail to
typecheck at the `implicit` transparency level, which is the level `rw` uses; for the same
reason the proofs below use `Eq.trans` and `congrArg` where `rw` would be shorter, and the
glued point is named rather than written out.

Evaluation at a rational point is `AlgebraicGeometry.sectionAt` and the constant sections are
`constHom`, with `sectionAtHom` the bundled ring-homomorphism form of the former; that the value
of a constant section is that constant is the only place where
`k`-rationality of the glued points is used. The algebra of lifting a prescribed pair of values
is isolated in `exists_pair_values`, a statement about two evaluations on an abstract ring with
a common section for the constants.

## References

* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
* [Stacks Project, Tag 0C1M](https://stacks.math.columbia.edu/tag/0C1M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.GlueSquishUnits

open Stacks.Cohomology.Generators (unitsSheaf)

/-! ### The map from the units of the structure sheaf to the pushforward units -/

/-- The morphism of sheaves of rings from the structure sheaf of `X` to the pushforward of the
structure sheaf of `X'`, obtained from the comorphism of `f`. -/
def ringPushforwardMap {X' X : Scheme.{u}} (f : X' ⟶ X) :
    X.toLocallyRingedSpace.toRingedSpace.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
        X'.toLocallyRingedSpace.toRingedSpace.sheaf :=
  (TopCat.Sheaf.forget CommRingCat.{u} X.toLocallyRingedSpace.toRingedSpace).preimage
    f.toLRSHom.toHom.c

/-- **The first map of the short exact sequence**: pullback of units along `f`, as a morphism
from the units sheaf of `X` to the pushforward of the units sheaf of `X'`. -/
def unitsPushforwardMap {X' X : Scheme.{u}} (f : X' ⟶ X) :
    unitsSheaf X.toLocallyRingedSpace.toRingedSpace ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
        (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) :=
  (sheafCompose (Opens.grothendieckTopology X)
      commGroupAddCommGroupEquivalence.functor).map <|
    (sheafCompose (Opens.grothendieckTopology X) CommMonCat.units).map <|
      (sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat CommMonCat)).map (ringPushforwardMap f)

/-- On sections, `Stacks.GlueSquishUnits.unitsPushforwardMap` is `f.app U` on units. -/
theorem unitsPushforwardMap_app {X' X : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) (s : Γ(X, U)ˣ) :
    (unitsPushforwardMap f).hom.app (op U) (Additive.ofMul s) =
      Additive.ofMul (Units.map (f.app U).hom.toMonoidHom s) := by
  have hα : (ringPushforwardMap f).hom.app (op U) = f.app U := by
    have hm := (TopCat.Sheaf.forget CommRingCat.{u}
        X.toLocallyRingedSpace.toRingedSpace).map_preimage
      (X := X.toLocallyRingedSpace.toRingedSpace.sheaf)
      (Y := (TopCat.Sheaf.pushforward CommRingCat.{u}
        f.toLRSHom.toHom.base).obj X'.toLocallyRingedSpace.toRingedSpace.sheaf)
      f.toLRSHom.toHom.c
    convert congrArg (fun g => g.app (op U)) hm using 1
    all_goals rfl
  show Additive.ofMul
      (Units.map ((ringPushforwardMap f).hom.app (op U)).hom.toMonoidHom s) = _
  rw [hα]
  rfl

/-! ### The glued point and membership in the preimage of an open -/

/-- **The point of `X` to which `f` sends the rational point `a` of `X'`.** When `f` glues `a`
and `b` this is the glued point, and it is where the skyscraper quotient of the sequence sits.

It is given a name of its own because `AlgebraicGeometry.IsGlueingTwoPoints` spells it
`(a ≫ f).base (IsLocalRing.closedPoint k)`, and the closed point of `Spec k` is an element of
`PrimeSpectrum k` rather than of the carrier of the scheme `Spec k`: the two agree only after
unfolding `AlgebraicGeometry.Spec`, so a goal mentioning that spelling is not type-correct at
the `implicit` transparency level and `rw` refuses to act on it. A definition whose *declared*
type is already the carrier of `X` has no such defect. -/
def gluedPoint {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (a : Spec (.of k) ⟶ X') : X :=
  (a ≫ f).base (IsLocalRing.closedPoint k)

/-- `Stacks.GlueSquishUnits.gluedPoint` is the image of the closed point of `Spec k`. -/
theorem gluedPoint_eq {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (a : Spec (.of k) ⟶ X') :
    gluedPoint f a = (a ≫ f).base (IsLocalRing.closedPoint k) := rfl

/-- The spelling of membership that the clauses of `AlgebraicGeometry.IsGlueingTwoPoints`
consume. -/
private theorem mem_comp {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (a : Spec (.of k) ⟶ X') {U : X.Opens} (hz : gluedPoint f a ∈ U) :
    (a ≫ f).base (IsLocalRing.closedPoint k) ∈ U := hz

/-- The point of `a` lies in the preimage of `U` exactly when the glued point lies in `U`; this
is the spelling `AlgebraicGeometry.sectionAt` wants upstairs. -/
private theorem mem_preimage_left {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (a : Spec (.of k) ⟶ X') {U : X.Opens} (hz : gluedPoint f a ∈ U) :
    a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U := hz

/-- The companion of `Stacks.GlueSquishUnits.mem_preimage_left` for the second glued point. -/
private theorem mem_preimage_right {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    {a b : Spec (.of k) ⟶ X'} (hab : a ≫ f = b ≫ f) {U : X.Opens}
    (hz : gluedPoint f a ∈ U) :
    b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U := by
  have h : (a ≫ f).base (IsLocalRing.closedPoint k) ∈ U := hz
  rwa [hab] at h

/-! ### Constant sections and evaluation at a rational point -/

/-- Evaluation at a rational point is unchanged by restricting to a smaller open which still
contains the point. -/
private lemma sectionAt_res {k : Type u} [Field k] {X : Scheme.{u}}
    (a : Spec (.of k) ⟶ X) {U V : X.Opens} (i : V ⟶ U)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ V) (s : Γ(X, U)) :
    sectionAt a V ha (X.presheaf.map i.op s) = sectionAt a U (i.le ha) s :=
  congrArg (Scheme.stalkClosedPointTo a).hom (X.presheaf.germ_res_apply i _ ha s)

/-- Evaluation at a rational point depends only on the point, not on the chosen morphism
presenting it. -/
private theorem sectionAt_congr {k : Type u} [Field k] {X : Scheme.{u}}
    {g h : Spec (.of k) ⟶ X} (e : g = h) (U : X.Opens)
    (hg : g.base (IsLocalRing.closedPoint k) ∈ U)
    (hh : h.base (IsLocalRing.closedPoint k) ∈ U) (s : Γ(X, U)) :
    sectionAt g U hg s = sectionAt h U hh s := by
  cases e
  rfl

/-- Evaluating the pullback of a section of `𝒪_X` at a rational point of `X'` is the same as
evaluating the section itself at the image point. -/
private theorem sectionAt_pullback {k : Type u} [Field k] {X' X : Scheme.{u}}
    (f : X' ⟶ X) (a : Spec (.of k) ⟶ X') (U : X.Opens)
    (hx : (a ≫ f).base (IsLocalRing.closedPoint k) ∈ U)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    sectionAt a (f ⁻¹ᵁ U) ha (f.app U s) = sectionAt (a ≫ f) U hx s := by
  unfold sectionAt
  rw [Scheme.stalkClosedPointTo_comp]
  have h := Scheme.Hom.germ_stalkMap f U (a.base (IsLocalRing.closedPoint k)) ha
  have hp := congrArg (fun m : CommRingCat.Hom _ _ => m.hom s) h
  have hp' : (X'.presheaf.germ (f ⁻¹ᵁ U) _ ha).hom ((f.app U).hom s) =
      (Scheme.Hom.stalkMap f (a.base (IsLocalRing.closedPoint k))).hom
        ((X.presheaf.germ U _ ha).hom s) := by
    simpa only [ConcreteCategory.comp_apply] using hp.symm
  exact congrArg (Scheme.stalkClosedPointTo a).hom hp'

/-- Evaluation at a rational point depends only on the point, not on the chosen morphism
presenting it.

This is the form other modules use: `Stacks.GlueSquishUnits.sectionAt_congr` is private to this
file. -/
alias sectionAt_congr' := sectionAt_congr

/-- Evaluating the pullback of a section of `𝒪_X` at a rational point of `X'` is the same as
evaluating the section itself at the image point.

This is the form other modules use: `Stacks.GlueSquishUnits.sectionAt_pullback` is private to
this file. -/
alias sectionAt_pullback' := sectionAt_pullback

/-! ### Two facts about a morphism which is an isomorphism over an open -/

/-- If `f` restricts to an isomorphism over `W`, then `f.app U` is an isomorphism for every open
`U ≤ W`. -/
private lemma app_isIso_of_restrict {X' X : Scheme.{u}} (f : X' ⟶ X)
    (W : X.Opens) [IsIso (f ∣_ W)] (U : X.Opens) (hUW : U ≤ W) : IsIso (f.app U) := by
  have he : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    ext x
    show (∃ y : W.toScheme, y ∈ W.ι ⁻¹ᵁ U ∧ W.ι y = x) ↔ x ∈ U
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨⟨x, hUW hx⟩, hx, rfl⟩⟩
  have h1 : IsIso ((f ∣_ W).app (W.ι ⁻¹ᵁ U)) := inferInstance
  have hcomp : IsIso (f.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ≫
      X'.presheaf.map
        (eqToHom (image_morphismRestrict_preimage f W (W.ι ⁻¹ᵁ U))).op) := by
    rw [← morphismRestrict_app f W (W.ι ⁻¹ᵁ U)]
    exact h1
  have hpart : IsIso (f.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ U))) :=
    IsIso.of_isIso_comp_right _
      (X'.presheaf.map (eqToHom (image_morphismRestrict_preimage f W (W.ι ⁻¹ᵁ U))).op)
  exact he ▸ hpart

/-- Pullback of sections commutes with restriction. -/
private lemma pullback_res {X' X : Scheme.{u}} (f : X' ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(X, U)) :
    f.app V (X.presheaf.map i.op s) =
      X'.presheaf.map (homOfLE (f.preimage_mono i.le)).op (f.app U s) :=
  congrArg (fun g : CommRingCat.Hom _ _ => g.hom s) (f.naturality i.op)

/-- Restricting a section along `i` after identifying its restriction with a pullback `f.app V t`
is the pullback of the restriction of `t`. -/
private lemma pullback_res_of_eq {X' X : Scheme.{u}} (f : X' ⟶ X) {U V W : X.Opens}
    (hVU : V ≤ U) (i : W ⟶ V) (s : Γ(X', f ⁻¹ᵁ U)) (t : Γ(X, V))
    (hst : X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op s = f.app V t) :
    X'.presheaf.map (homOfLE (f.preimage_mono (i.le.trans hVU))).op s =
      f.app W (X.presheaf.map i.op t) := by
  rw [pullback_res, ← hst, ← Functor.map_comp_apply]
  rfl

/-- A local homomorphism reflects units: if the pullback of a section is a unit in the stalk
upstairs, the section is already a unit in the stalk downstairs. -/
private theorem pullback_germ_unit_reflect {X' X : Scheme.{u}}
    (f : X' ⟶ X) (y : X') (U : X.Opens) (hy : f y ∈ U) (t : Γ(X, U))
    (ht : IsUnit (X'.presheaf.germ (f ⁻¹ᵁ U) y hy ((f.app U).hom t))) :
    IsUnit (X.presheaf.germ U (f y) hy t) := by
  have hm : IsUnit ((f.toLRSHom.stalkMap y).hom (X.presheaf.germ U (f y) hy t)) := by
    rw [LocallyRingedSpace.stalkMap_germ_apply f.toLRSHom]
    exact ht
  exact (isUnit_map_iff (f.toLRSHom.stalkMap y).hom _).mp hm

/-! ### Sections of a skyscraper sheaf -/

/-- The sections of a skyscraper presheaf over an open containing the point are its fibre. -/
theorem skyscraperPresheaf_obj_eq {T : TopCat.{u}} (p : T)
    [∀ V : Opens T, Decidable (p ∈ V)] (A : AddCommGrpCat.{u}) {U : Opens T} (hp : p ∈ U) :
    (skyscraperPresheaf p A).obj (op U) = A := ite_eq_left hp

/-- A map to a skyscraper presheaf, read on sections over an open containing the point, is the
germ at that point followed by the map out of the stalk. This is
`StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk` combined with the fact that `fromStalk`
inverts `toSkyscraperPresheaf`. -/
private lemma toSkyscraperPresheaf_app_comp {T : TopCat.{u}} (p : T)
    [∀ V : Opens T, Decidable (p ∈ V)] {A : AddCommGrpCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} T} (ρ : F.stalk p ⟶ A)
    {U : Opens T} (hp : p ∈ U) :
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf p ρ).app (op U) ≫
        eqToHom (skyscraperPresheaf_obj_eq p A hp) = F.germ U p hp ≫ ρ := by
  rw [← StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk p _ U hp,
    StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper]

/-- Restriction of a skyscraper presheaf between two opens containing the point is the identity
on the fibre. -/
theorem skyscraperPresheaf_map_comp {T : TopCat.{u}} (p : T)
    [∀ V : Opens T, Decidable (p ∈ V)] (A : AddCommGrpCat.{u}) {U V : Opens T} (i : V ⟶ U)
    (hp : p ∈ V) :
    (skyscraperPresheaf p A).map i.op ≫ eqToHom (skyscraperPresheaf_obj_eq p A hp) =
      eqToHom (skyscraperPresheaf_obj_eq p A (i.le hp)) := by
  have key (W : Opens T) (hW : p ∈ W) :
      (skyscraperPresheaf p A).germ W p hW ≫
        StalkSkyscraperPresheafAdjunctionAuxs.fromStalk p
          (𝟙 (skyscraperPresheaf p A)) = eqToHom (skyscraperPresheaf_obj_eq p A hW) := by
    rw [StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk, NatTrans.id_app,
      Category.id_comp]
  rw [← key V hp, ← key U (i.le hp), ← Category.assoc,
    TopCat.Presheaf.germ_res (skyscraperPresheaf p A) i p hp]

/-- The skyscraper sheaf of the multiplicative group `kˣ`, written additively. -/
abbrev skyscraperUnitsSheaf {k : Type u} [Field k]
    (X : Scheme.{u}) (x : X) : TopCat.Sheaf AddCommGrpCat.{u} X := by
  classical
  exact skyscraperSheaf x (AddCommGrpCat.of (Additive kˣ))

/-- **The sections of the skyscraper sheaf of units over an open containing the point are the
fibre `kˣ`**, written additively. This is the isomorphism through which the second map of the
sequence is read on sections. -/
def skyscraperUnitsEval {k : Type u} [Field k]
    (X : Scheme.{u}) (x : X) {U : X.Opens} (hx : x ∈ U) :
    (skyscraperUnitsSheaf (k := k) X x).obj.obj (op U) ⟶
      AddCommGrpCat.of (Additive kˣ) := by
  classical
  exact eqToHom (skyscraperPresheaf_obj_eq x (AddCommGrpCat.of (Additive kˣ)) hx)

/-- `Stacks.GlueSquishUnits.skyscraperUnitsEval` is injective, being an isomorphism. -/
private lemma skyscraperUnitsEval_injective {k : Type u} [Field k]
    (X : Scheme.{u}) (x : X) {U : X.Opens} (hx : x ∈ U) :
    Function.Injective (skyscraperUnitsEval (k := k) X x hx) := by
  classical
  exact (ConcreteCategory.bijective_of_isIso
    (eqToHom (skyscraperPresheaf_obj_eq x (AddCommGrpCat.of (Additive kˣ)) hx))).1

/-- Evaluation of a section of the skyscraper sheaf of units is unchanged by restriction to a
smaller open still containing the point. -/
private lemma skyscraperUnitsEval_res {k : Type u} [Field k]
    (X : Scheme.{u}) (x : X) {U V : X.Opens} (i : V ⟶ U) (hx : x ∈ V)
    (s : (skyscraperUnitsSheaf (k := k) X x).obj.obj (op U)) :
    skyscraperUnitsEval X x hx ((skyscraperUnitsSheaf (k := k) X x).obj.map i.op s) =
      skyscraperUnitsEval X x (i.le hx) s := by
  classical
  exact congrArg (fun g : AddCommGrpCat.Hom _ _ => g.hom s)
    (skyscraperPresheaf_map_comp x (AddCommGrpCat.of (Additive kˣ)) i hx)

/-- The skyscraper sheaf of units has no sections beyond zero over an open missing the point. -/
private lemma skyscraper_subsingleton {k : Type u} [Field k]
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hx : x ∉ U) :
    Subsingleton ((skyscraperUnitsSheaf (k := k) X x).obj.obj (op U)) := by
  classical
  have he : (skyscraperUnitsSheaf (k := k) X x).obj.obj (op U) =
      ⊤_ AddCommGrpCat.{u} := by
    dsimp only [skyscraperUnitsSheaf, skyscraperSheaf, skyscraperPresheaf]
    simp [hx]
  rw [he]
  have := Concrete.uniqueOfTerminalOfPreserves (⊤_ AddCommGrpCat.{u})
    (terminalIsTerminal (C := AddCommGrpCat.{u}))
  infer_instance

/-! ### The ratio of the two values of a unit -/

/-- The multiplicative difference `h(a) h(b)⁻¹` of the values of a unit at two rational
points. -/
def unitRatioAt {k : Type u} [Field k] {X : Scheme.{u}}
    (a b : Spec (.of k) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ U) (h : Γ(X, U)ˣ) : kˣ :=
  Units.map (X.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo a).hom.toMonoidHom h *
    (Units.map
      (X.presheaf.germ U _ hb ≫ Scheme.stalkClosedPointTo b).hom.toMonoidHom h)⁻¹

/-- The ratio `h(a) h(b)⁻¹` of the values of a unit at two rational points, as a group
homomorphism; this is the form in which it is fed to the colimit defining the stalk. -/
def unitRatioMonoidHom {k : Type u} [Field k] {X : Scheme.{u}}
    (a b : Spec (.of k) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ U) :
    ((X.sheaf.obj.obj (op U))ˣ) →* kˣ :=
  Units.map (X.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo a).hom.toMonoidHom /
    Units.map (X.presheaf.germ U _ hb ≫ Scheme.stalkClosedPointTo b).hom.toMonoidHom

/-- `Stacks.GlueSquishUnits.unitRatioMonoidHom` computes
`Stacks.GlueSquishUnits.unitRatioAt`. -/
theorem unitRatioMonoidHom_apply {k : Type u} [Field k] {X : Scheme.{u}}
    (a b : Spec (.of k) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ U) (s : Γ(X, U)ˣ) :
    unitRatioMonoidHom a b U ha hb s = unitRatioAt a b U ha hb s := rfl

/-- The ratio of two evaluations is trivial exactly when the underlying ring-valued evaluations
agree. This is the bridge to the additive middle-exactness clause of
`AlgebraicGeometry.IsGlueingTwoPoints`. -/
theorem unitRatioAt_eq_one_iff {k : Type u} [Field k] {X : Scheme.{u}}
    (a b : Spec (.of k) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ U) (s : Γ(X, U)ˣ) :
    unitRatioAt a b U ha hb s = 1 ↔
      sectionAt a U ha (s : Γ(X, U)) = sectionAt b U hb (s : Γ(X, U)) := by
  show Units.map _ s * (Units.map _ s)⁻¹ = 1 ↔ _
  rw [mul_inv_eq_one]
  exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

/-- The preceding criterion in the additive form used by the conductor quotient in the
definition of glueing two points. -/
theorem unitRatioAt_eq_one_iff_sub_eq_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (a b : Spec (.of k) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ U) (s : Γ(X, U)ˣ) :
    unitRatioAt a b U ha hb s = 1 ↔
      sectionAt a U ha (s : Γ(X, U)) - sectionAt b U hb (s : Γ(X, U)) = 0 := by
  rw [sub_eq_zero]
  exact unitRatioAt_eq_one_iff a b U ha hb s

/-- **The ratio of the two values of a unit is unchanged by restriction.** -/
theorem unitRatioAt_restrict {k : Type u} [Field k] {X : Scheme.{u}}
    (a b : Spec (.of k) ⟶ X) {U V : X.Opens} (i : V ⟶ U)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ V)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ V) (s : Γ(X, U)ˣ) :
    unitRatioAt a b V ha hb (Units.map (X.presheaf.map i.op).hom.toMonoidHom s) =
      unitRatioAt a b U (i.le ha) (i.le hb) s := by
  have key (c : Spec (.of k) ⟶ X) (hc : c.base (IsLocalRing.closedPoint k) ∈ V) :
      Units.map (X.presheaf.germ V _ hc ≫ Scheme.stalkClosedPointTo c).hom.toMonoidHom
        (Units.map (X.presheaf.map i.op).hom.toMonoidHom s) =
      Units.map (X.presheaf.germ U _ (i.le hc) ≫
        Scheme.stalkClosedPointTo c).hom.toMonoidHom s :=
    Units.ext (sectionAt_res c i hc s)
  show Units.map _ _ * (Units.map _ _)⁻¹ = Units.map _ s * (Units.map _ s)⁻¹
  rw [key a ha, key b hb]

/-- The ratio of the two values of a *pulled back* unit is trivial, because the two points have
the same image. -/
private theorem unitRatioAt_pullback_eq_one {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (hab : a ≫ f = b ≫ f) (U : X.Opens) (hz : gluedPoint f a ∈ U)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    unitRatioAt a b (f ⁻¹ᵁ U) ha hb (Units.map (f.app U).hom.toMonoidHom s) = 1 := by
  apply (unitRatioAt_eq_one_iff (a := a) (b := b) (U := f ⁻¹ᵁ U) (ha := ha) (hb := hb)
    (s := Units.map (f.app U).hom.toMonoidHom s)).2
  have hx : (a ≫ f).base (IsLocalRing.closedPoint k) ∈ U := mem_comp f a hz
  have hxB : (b ≫ f).base (IsLocalRing.closedPoint k) ∈ U := by rwa [← hab]
  have hA : sectionAt a (f ⁻¹ᵁ U) ha (f.app U (s : Γ(X, U))) = sectionAt (a ≫ f) U hx s :=
    sectionAt_pullback f a U hx ha (s : Γ(X, U))
  have hB : sectionAt b (f ⁻¹ᵁ U) hb (f.app U (s : Γ(X, U))) = sectionAt (b ≫ f) U hxB s :=
    sectionAt_pullback f b U hxB hb (s : Γ(X, U))
  show sectionAt a (f ⁻¹ᵁ U) ha (f.app U (s : Γ(X, U))) =
    sectionAt b (f ⁻¹ᵁ U) hb (f.app U (s : Γ(X, U)))
  rw [hA, hB]
  exact sectionAt_congr hab U hx hxB (s : Γ(X, U))

/-! ### The quotient map of the sequence -/

/-- The pushforward of the units sheaf of `X'`, as a presheaf of abelian groups on `X`. -/
private abbrev pushforwardUnitsPresheaf {X' X : Scheme.{u}} (f : X' ⟶ X) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  (TopCat.Sheaf.forget AddCommGrpCat.{u} X).obj
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
      (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace))

/-- The cocone, over the neighbourhoods of the glued point, whose components send a unit to the
ratio of its two values. -/
private def unitsRatioCocone {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (hab : a ≫ f = b ≫ f) :
    Cocone ((OpenNhds.inclusion (gluedPoint f a)).op ⋙ pushforwardUnitsPresheaf f) where
  pt := AddCommGrpCat.of (Additive kˣ)
  ι :=
    { app := fun U => AddCommGrpCat.ofHom (MonoidHom.toAdditive
        (unitRatioMonoidHom a b (f ⁻¹ᵁ (OpenNhds.inclusion _).obj U.unop)
          (mem_preimage_left f a U.unop.2) (mem_preimage_right f hab U.unop.2)))
      naturality := fun U V i => by
        ext s
        exact congrArg Additive.ofMul (unitRatioAt_restrict a b
          (homOfLE (f.preimage_mono ((OpenNhds.inclusion _).map i.unop).le))
          (mem_preimage_left f a V.unop.2) (mem_preimage_right f hab V.unop.2) s.toMul) }

/-- The ratio of the two values, as a map out of the stalk of the pushforward units sheaf at the
glued point. -/
private def unitsRatioStalkHom {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (hab : a ≫ f = b ≫ f) :
    (pushforwardUnitsPresheaf f).stalk (gluedPoint f a) ⟶ AddCommGrpCat.of (Additive kˣ) :=
  colimit.desc ((OpenNhds.inclusion (gluedPoint f a)).op ⋙ pushforwardUnitsPresheaf f)
    (unitsRatioCocone f a b hab)

/-- The stalk map of the ratio, computed on a germ. -/
private theorem unitsRatioStalkHom_germ {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (hab : a ≫ f = b ≫ f) (U : X.Opens) (hz : gluedPoint f a ∈ U)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U) :
    (pushforwardUnitsPresheaf f).germ U (gluedPoint f a) hz ≫
        unitsRatioStalkHom f a b hab =
      AddCommGrpCat.ofHom (unitRatioMonoidHom a b (f ⁻¹ᵁ U) ha hb).toAdditive :=
  colimit.ι_desc _ _

/-- **The second map of the sequence**: the ratio of the two values, as a morphism from the
pushforward units sheaf to the skyscraper sheaf of units at the glued point. -/
private def unitsRatioPushforwardMap {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (hab : a ≫ f = b ≫ f) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
        (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) ⟶
      skyscraperUnitsSheaf (k := k) X (gluedPoint f a) := by
  classical
  exact ObjectProperty.homMk
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf (gluedPoint f a)
      (unitsRatioStalkHom f a b hab))

/-- **On sections over an open containing the glued point, the second map of the sequence is the
ratio of the two values of a unit.** -/
private lemma ratio_app_eval {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (hab : a ≫ f = b ≫ f) (U : X.Opens) (hz : gluedPoint f a ∈ U)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U) (s : Γ(X', f ⁻¹ᵁ U)ˣ) :
    skyscraperUnitsEval X (gluedPoint f a) hz
      ((unitsRatioPushforwardMap f a b hab).hom.app (op U) (Additive.ofMul s)) =
      Additive.ofMul (unitRatioAt a b (f ⁻¹ᵁ U) ha hb s) := by
  classical
  have he : (unitsRatioPushforwardMap f a b hab).hom.app (op U) ≫
      skyscraperUnitsEval X (gluedPoint f a) hz =
      AddCommGrpCat.ofHom (unitRatioMonoidHom a b (f ⁻¹ᵁ U) ha hb).toAdditive :=
    Eq.trans
      (toSkyscraperPresheaf_app_comp (gluedPoint f a) (unitsRatioStalkHom f a b hab) hz)
      (unitsRatioStalkHom_germ f a b hab U hz ha hb)
  exact congrArg (fun g : AddCommGrpCat.Hom _ _ => g.hom (Additive.ofMul s)) he

/-- `Stacks.GlueSquishUnits.skyscraperUnitsEval` sends the zero section to zero. -/
private lemma skyscraperUnitsEval_zero {k : Type u} [Field k] (X : Scheme.{u}) (x : X)
    {U : X.Opens} (hx : x ∈ U) :
    skyscraperUnitsEval (k := k) X x hx 0 = 0 := by
  classical
  exact map_zero _

/-- `Stacks.GlueSquishUnits.skyscraperUnitsEval` is a function: equal sections have equal
images. -/
private lemma skyscraperUnitsEval_congr {k : Type u} [Field k] (X : Scheme.{u}) (x : X)
    {U : X.Opens} (hx : x ∈ U)
    (s t : (skyscraperUnitsSheaf (k := k) X x).obj.obj (op U)) (hst : s = t) :
    skyscraperUnitsEval X x hx s = skyscraperUnitsEval X x hx t := by
  subst hst
  rfl

/-- A unit of `Γ(X, U)` whose pullback along `f` is `1` has `s - 1` in the kernel of `f.app U`;
this is the shape in which the injectivity clause of `AlgebraicGeometry.IsGlueingTwoPoints`
consumes it. -/
private lemma app_sub_one_eq_zero {X' X : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens)
    (su : Γ(X, U)ˣ) (hs : Units.map (f.app U).hom.toMonoidHom su = 1) :
    (f.app U).hom ((su : Γ(X, U)) - 1) = 0 := by
  have he : (f.app U).hom (su : Γ(X, U)) = 1 := congrArg Units.val hs
  simp only [map_sub, map_one, he, sub_self]

/-- Conversely, a unit whose restriction has `s - 1` in the kernel restricts to `1`. -/
private lemma units_res_eq_one {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U)
    (su : Γ(X, U)ˣ)
    (hv : (X.presheaf.map (homOfLE hVU).op).hom ((su : Γ(X, U)) - 1) = 0) :
    Units.map (X.presheaf.map (homOfLE hVU).op).hom.toMonoidHom su = 1 := by
  apply Units.ext
  show (X.presheaf.map (homOfLE hVU).op).hom (su : Γ(X, U)) = 1
  simpa only [map_sub, map_one, sub_eq_zero] using hv

/-- Equal sections of the pushforward units sheaf have equal images under the second map of
the sequence, read through `Stacks.GlueSquishUnits.skyscraperUnitsEval`. -/
private lemma ratio_eval_congr {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (hab : a ≫ f = b ≫ f) (U : X.Opens) (hz : gluedPoint f a ∈ U)
    (s t : ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
      (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace)).obj.obj (op U)) (hst : s = t) :
    skyscraperUnitsEval X (gluedPoint f a) hz
        ((unitsRatioPushforwardMap f a b hab).hom.app (op U) s) =
      skyscraperUnitsEval X (gluedPoint f a) hz
        ((unitsRatioPushforwardMap f a b hab).hom.app (op U) t) := by
  subst hst
  rfl

/-- The two maps of the sequence compose to zero: the two values of a pulled back unit
agree. -/
private lemma unitsPushforwardMap_comp_ratio {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (hab : a ≫ f = b ≫ f) :
    unitsPushforwardMap f ≫ unitsRatioPushforwardMap f a b hab = 0 := by
  classical
  apply Sheaf.hom_ext
  ext U s
  show (unitsRatioPushforwardMap f a b hab).hom.app (op U.unop)
    ((unitsPushforwardMap f).hom.app (op U.unop) s) = 0
  by_cases hz : gluedPoint f a ∈ U.unop
  · refine skyscraperUnitsEval_injective (k := k) X _ hz ?_
    refine Eq.trans ?_ (skyscraperUnitsEval_zero (k := k) X (gluedPoint f a) hz).symm
    refine Eq.trans (ratio_eval_congr f a b hab U.unop hz _ _
      (unitsPushforwardMap_app f U.unop s)) ?_
    refine Eq.trans (ratio_app_eval f a b hab U.unop hz (mem_preimage_left f a hz)
      (mem_preimage_right f hab hz)
      (Units.map (f.app U.unop).hom.toMonoidHom s)) ?_
    exact congrArg Additive.ofMul (unitRatioAt_pullback_eq_one f a b hab U.unop hz
      (mem_preimage_left f a hz) (mem_preimage_right f hab hz) s)
  · exact (skyscraper_subsingleton (k := k) X _ U.unop hz).elim _ _

/-! ### Lifting a prescribed pair of values -/

/-- **Two evaluations with a common section for the constants realize every prescribed pair of
values.** Given `A`, `B : R →+* k` and `C : k →+* R` with `A ∘ C = B ∘ C = id`, and a section
`s` whose two values differ by `c - 1`, this produces `t` with values `c` and `1` and a
companion `v` whose product with `t` has both values `1`. -/
theorem exists_pair_values {R k : Type u} [CommRing R] [Field k]
    (A B : R →+* k) (C : k →+* R) (hAC : ∀ d, A (C d) = d) (hBC : ∀ d, B (C d) = d)
    (s : R) (c : kˣ) (hs : A s - B s = (c : k) - 1) :
    ∃ t v : R, A t = (c : k) ∧ B t = 1 ∧ A (t * v) = 1 ∧ B (t * v) = 1 := by
  have hcc : (↑c⁻¹ : k) * (c : k) = 1 := c.inv_mul
  have hat : A (s + C (1 - B s)) = (c : k) := by
    rw [map_add, hAC]
    linear_combination hs
  have hbt : B (s + C (1 - B s)) = 1 := by
    rw [map_add, hBC]
    ring
  refine ⟨s + C (1 - B s),
    C ((↑c⁻¹ : k) + 1) - C (↑c⁻¹ : k) * (s + C (1 - B s)), hat, hbt, ?_, ?_⟩
  · rw [map_mul, hat, map_sub, map_mul, hAC, hAC, hat]
    linear_combination (1 - (c : k)) * hcc
  · rw [map_mul, hbt, map_sub, map_mul, hBC, hBC, hbt]
    ring

/-- A section on `f ⁻¹ᵁ U` taking the value `1` at both glued points descends to a section
downstairs with value `1`, hence is a unit after shrinking. -/
private lemma isUnit_restrict_of_values_one {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : IsGlueingTwoPoints f a b)
    (U : X.Opens) (hz : gluedPoint f a ∈ U)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
    (s : Γ(X', f ⁻¹ᵁ U))
    (hA : sectionAt a (f ⁻¹ᵁ U) ha s = 1)
    (hB : sectionAt b (f ⁻¹ᵁ U) hb s = 1) :
    ∃ (V : X.Opens) (hVU : V ≤ U) (_ : gluedPoint f a ∈ V),
      IsUnit (X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op s) := by
  obtain ⟨hab, -, -, -, hmid, -⟩ := h.2.2.2.2.2.2.2.2
  obtain ⟨V, hVU, hxV, t, hst⟩ :=
    hmid U (mem_comp f a hz) s (by rw [hA, hB]; exact sub_self 1)
  have hzV : gluedPoint f a ∈ V := hxV
  have hxV' : (a ≫ f).base (IsLocalRing.closedPoint k) ∈ V := hxV
  have haV : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ V := hxV
  have ht : sectionAt (a ≫ f) V hxV' t = 1 := by
    rwa [← sectionAt_pullback f a V hxV' haV t, ← hst, sectionAt_res]
  have hunit : IsUnit (X.presheaf.germ V _ hxV' t) := by
    apply (isUnit_map_iff (Scheme.stalkClosedPointTo (a ≫ f)).hom _).mp
    show IsUnit (sectionAt (a ≫ f) V hxV' t)
    exact ht ▸ isUnit_one
  obtain ⟨W, i, hxW, hu⟩ :=
    X.toLocallyRingedSpace.toRingedSpace.isUnit_res_of_isUnit_germ V t _ hxV' hunit
  refine ⟨W, i.le.trans hVU, hxW, ?_⟩
  rw [pullback_res_of_eq f hVU i s t hst]
  exact hu.map (f.app W).hom

/-- **Every scalar is the ratio of the two values of a unit, locally at the glued point.**
A section with the prescribed values is lifted additively using the surjectivity clause of
`AlgebraicGeometry.IsGlueingTwoPoints`; a companion with reciprocal values makes the product
descend to a unit, so the original lift is itself a unit after restriction. -/
private lemma exists_unit_ratio {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : IsGlueingTwoPoints f a b) (c : kˣ) :
    ∃ (U : X.Opens) (_ : gluedPoint f a ∈ U)
      (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
      (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
      (s : Γ(X', f ⁻¹ᵁ U)ˣ), unitRatioAt a b (f ⁻¹ᵁ U) ha hb s = c := by
  obtain ⟨hab, -, -, -, -, hsurj⟩ := h.2.2.2.2.2.2.2.2
  have haOver : a.IsOver (Spec (.of k)) := h.1
  have hbOver : b.IsOver (Spec (.of k)) := h.2.1
  obtain ⟨U, hx, s, hs⟩ := hsurj ((c : k) - 1)
  have hz : gluedPoint f a ∈ U := hx
  have ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U := hx
  have hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U := mem_preimage_right f hab hz
  have hle : (f ⁻¹ᵁ U) ≤ (X' ↘ Spec (.of k)) ⁻¹ᵁ ⊤ := by simp
  have hsa : sectionAtHom a (f ⁻¹ᵁ U) ha s - sectionAtHom b (f ⁻¹ᵁ U) hb s = (c : k) - 1 := hs
  obtain ⟨t, v, hat, hbt, hatv, hbtv⟩ := exists_pair_values
    (sectionAtHom a (f ⁻¹ᵁ U) ha) (sectionAtHom b (f ⁻¹ᵁ U) hb)
    (constHom X' (f ⁻¹ᵁ U) hle)
    (fun d => sectionAt_constHom a haOver _ ha hle d)
    (fun d => sectionAt_constHom b hbOver _ hb hle d) s c hsa
  obtain ⟨V, hVU, hzV, hu⟩ :=
    isUnit_restrict_of_values_one f a b h U hz ha hb (t * v) hatv hbtv
  rw [map_mul] at hu
  have haV : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ V := hzV
  have hbV : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ V := mem_preimage_right f hab hzV
  have ht' : ((isUnit_of_mul_isUnit_left hu).unit : Γ(X', f ⁻¹ᵁ V)) =
      X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op t :=
    (isUnit_of_mul_isUnit_left hu).unit_spec
  have hatt : sectionAt a (f ⁻¹ᵁ U) ha t = (c : k) := hat
  have hbtt : sectionAt b (f ⁻¹ᵁ U) hb t = 1 := hbt
  refine ⟨V, hzV, haV, hbV, (isUnit_of_mul_isUnit_left hu).unit, ?_⟩
  apply Units.ext
  simp only [unitRatioAt, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map]
  show sectionAt a (f ⁻¹ᵁ V) haV ((isUnit_of_mul_isUnit_left hu).unit : Γ(X', f ⁻¹ᵁ V)) *
    (sectionAt b (f ⁻¹ᵁ V) hbV
      ((isUnit_of_mul_isUnit_left hu).unit : Γ(X', f ⁻¹ᵁ V)))⁻¹ = (c : k)
  rw [ht', sectionAt_res a _ haV t, sectionAt_res b _ hbV t, hatt, hbtt, inv_one, mul_one]

/-- **A unit on `f ⁻¹ᵁ U` which descends to a section downstairs descends to a unit.** The
middle-exactness clause of `AlgebraicGeometry.IsGlueingTwoPoints` produces the section; that it
is itself a unit is because `f` is a local homomorphism on stalks. -/
private theorem unitPullback_local_surj {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (a : Spec (.of k) ⟶ X')
    (U : X.Opens) (s : Γ(X', f ⁻¹ᵁ U)ˣ)
    (hmid : ∃ (V : X.Opens) (hVU : V ≤ U)
        (_hxV : (a ≫ f).base (IsLocalRing.closedPoint k) ∈ V) (t : Γ(X, V)),
      X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op (s : Γ(X', f ⁻¹ᵁ U)) = f.app V t) :
    ∃ (V : X.Opens) (hVU : V ≤ U) (_hzV : gluedPoint f a ∈ V) (t : Γ(X, V)ˣ),
      Units.map (X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom.toMonoidHom s =
        Units.map (f.app V).hom.toMonoidHom t := by
  obtain ⟨V, hVU, hxV, t, hst⟩ := hmid
  have haV : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ V := hxV
  have hunitPull : IsUnit (X'.presheaf.germ (f ⁻¹ᵁ V)
      (a.base (IsLocalRing.closedPoint k)) haV ((f.app V).hom t)) := by
    rw [← hst]
    exact RingHom.isUnit_map _ (Units.isUnit (Units.map
      (X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom.toMonoidHom s))
  have hunitT : IsUnit (X.presheaf.germ V
      (f (a.base (IsLocalRing.closedPoint k))) haV t) :=
    pullback_germ_unit_reflect f (a.base (IsLocalRing.closedPoint k)) V haV t hunitPull
  obtain ⟨W, iWV, hxW, hunitW⟩ :=
    X.toLocallyRingedSpace.toRingedSpace.isUnit_res_of_isUnit_germ V t _ haV hunitT
  refine ⟨W, le_trans iWV.le hVU, hxW, hunitW.unit, ?_⟩
  apply Units.ext
  show X'.presheaf.map (homOfLE (f.preimage_mono (le_trans iWV.le hVU))).op
      (s : Γ(X', f ⁻¹ᵁ U)) = (f.app W).hom (hunitW.unit : Γ(X, W))
  rw [hunitW.unit_spec]
  exact pullback_res_of_eq f hVU iWV _ t hst

/-! ### The short exact sequence -/

/-- The sequence of units sheaves of a glueing of two points is short exact. All three
conditions are checked germ-locally through `TopCat.Sheaf.shortExact_of_local`: at a
point other than the glued one `f` is an isomorphism on a neighbourhood, and at the glued point
the three final clauses of `AlgebraicGeometry.IsGlueingTwoPoints` apply. -/
private lemma shortExact_units {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : IsGlueingTwoPoints f a b) (hab : a ≫ f = b ≫ f)
    (hzero : unitsPushforwardMap f ≫ unitsRatioPushforwardMap f a b hab = 0) :
    (ShortComplex.mk (unitsPushforwardMap f)
      (unitsRatioPushforwardMap f a b hab) hzero).ShortExact := by
  classical
  obtain ⟨hab', -, ⟨W, hW, hiW⟩, hinj, hmid, -⟩ := h.2.2.2.2.2.2.2.2
  have := hiW
  have hmemW (y : X) : y ∈ W ↔ y ≠ gluedPoint f a := by
    show y ∈ (W : Set X) ↔ _
    rw [hW]
    rfl
  apply TopCat.Sheaf.shortExact_of_local
  · intro U s hs y hy
    have hs' : Units.map (f.app U).hom.toMonoidHom s = 1 :=
      congrArg Additive.toMul ((unitsPushforwardMap_app f U s).symm.trans hs)
    have hzeroRing := app_sub_one_eq_zero f U s hs'
    suffices hsuf : ∃ (V : X.Opens) (hVU : V ≤ U) (_ : y ∈ V),
        (X.presheaf.map (homOfLE hVU).op).hom ((Units.val s : Γ(X, U)) - 1) = 0 by
      obtain ⟨V, hVU, hyV, hv⟩ := hsuf
      exact ⟨V, homOfLE hVU, hyV, congrArg Additive.ofMul (units_res_eq_one hVU s hv)⟩
    by_cases hyz : y = gluedPoint f a
    · subst y
      exact hinj U (mem_comp f a hy) ((Units.val s : Γ(X, U)) - 1)
        ⟨U, le_rfl, mem_comp f a hy, by simpa using hzeroRing⟩
    · have : IsIso (f.app (U ⊓ W)) := app_isIso_of_restrict f W (U ⊓ W) inf_le_right
      refine ⟨U ⊓ W, inf_le_left, ⟨hy, (hmemW y).2 hyz⟩, ?_⟩
      apply (ConcreteCategory.bijective_of_isIso (f.app (U ⊓ W))).1
      rw [map_zero, pullback_res, hzeroRing, map_zero]
  · intro U s hs y hy
    by_cases hyz : y = gluedPoint f a
    · subst y
      have ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U := mem_preimage_left f a hy
      have hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U := mem_preimage_right f hab hy
      have hr : unitRatioAt a b (f ⁻¹ᵁ U) ha hb s = 1 :=
        congrArg Additive.toMul
          (((ratio_app_eval f a b hab U hy ha hb s).symm.trans
            (skyscraperUnitsEval_congr X (gluedPoint f a) hy _ 0 hs)).trans
              (skyscraperUnitsEval_zero (k := k) X (gluedPoint f a) hy))
      obtain ⟨V, hVU, hzV, t, ht⟩ :=
        unitPullback_local_surj f a U s
          (hmid U (mem_comp f a hy) (Units.val s : Γ(X', f ⁻¹ᵁ U))
            ((unitRatioAt_eq_one_iff_sub_eq_zero a b (f ⁻¹ᵁ U) ha hb s).mp hr))
      exact ⟨V, homOfLE hVU, hzV, Additive.ofMul t,
        (unitsPushforwardMap_app f V t).trans (congrArg Additive.ofMul ht.symm)⟩
    · have : IsIso (f.app (U ⊓ W)) := app_isIso_of_restrict f W (U ⊓ W) inf_le_right
      refine ⟨U ⊓ W, homOfLE inf_le_left, ⟨hy, (hmemW y).2 hyz⟩,
        Additive.ofMul (Units.map (inv (f.app (U ⊓ W))).hom.toMonoidHom
          (Units.map (X'.presheaf.map (homOfLE
            (f.preimage_mono (inf_le_left : U ⊓ W ≤ U))).op).hom.toMonoidHom s)), ?_⟩
      refine (unitsPushforwardMap_app f (U ⊓ W) _).trans
        (congrArg Additive.ofMul (Units.ext ?_))
      exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (f.app (U ⊓ W))) _
  · intro U s y hy
    by_cases hyz : y = gluedPoint f a
    · subst y
      obtain ⟨V, hzV, haV, hbV, t, ht⟩ := exists_unit_ratio f a b h
        (skyscraperUnitsEval (k := k) X (gluedPoint f a) hy s).toMul
      have hzZ : gluedPoint f a ∈ V ⊓ U := ⟨hzV, hy⟩
      have haZ : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ (V ⊓ U) :=
        mem_preimage_left f a hzZ
      have hbZ : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ (V ⊓ U) :=
        mem_preimage_right f hab hzZ
      refine ⟨V ⊓ U, homOfLE inf_le_right, hzZ, Additive.ofMul (Units.map
        (X'.presheaf.map (homOfLE
          (f.preimage_mono (inf_le_left : V ⊓ U ≤ V))).op).hom.toMonoidHom t), ?_⟩
      refine skyscraperUnitsEval_injective (k := k) X _ hzZ ?_
      refine Eq.trans (ratio_app_eval f a b hab (V ⊓ U) hzZ haZ hbZ _) ?_
      refine Eq.trans (congrArg Additive.ofMul
        ((unitRatioAt_restrict a b
          (homOfLE (f.preimage_mono (inf_le_left : V ⊓ U ≤ V))) haZ hbZ t).trans ht)) ?_
      exact (skyscraperUnitsEval_res X (gluedPoint f a)
        (homOfLE (inf_le_right : V ⊓ U ≤ U)) hzZ s).symm
    · have hzV : gluedPoint f a ∉ U ⊓ W := fun hzV => ((hmemW _).1 hzV.2) rfl
      exact ⟨U ⊓ W, homOfLE inf_le_left, ⟨hy, (hmemW y).2 hyz⟩, 0,
        (skyscraper_subsingleton (k := k) X _ (U ⊓ W) hzV).elim _ _⟩

/-- **The short exact sequence of sheaves of units of a glueing of two rational points.**
If `f : X' ⟶ X` glues the distinct rational points `a` and `b` of `X'` to the point
`x = f(a) = f(b)` of `X`, then

`1 ⟶ 𝒪_X^* ⟶ f_*𝒪_{X'}^* ⟶ (k^*)_x ⟶ 1`

is a short exact sequence of sheaves of abelian groups on `X`, the first map being pullback of
units along `f` and the second the ratio `h ↦ h(a) h(b)⁻¹` of the two values of a unit. Both
maps are pinned down on sections, so the sequence is the one of [Stacks, Tag 0C1J] and not
merely some exact sequence with those terms.

This is the input from which [Stacks, Tag 0C1M] obtains the exact sequence
`k^* ⟶ Pic(X) ⟶ Pic(X') ⟶ 0`: the five-term low-degree cohomology sequence over `U = ⊤`,
`Stacks.Cohomology.AbelianColimit.H'longExactSequence_exact`, gives
`H⁰(X, f_*𝒪_{X'}^*) ⟶ k^* ⟶ H¹(X, 𝒪_X^*) ⟶ H¹(X, f_*𝒪_{X'}^*)`, and
`Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup` identifies the first cohomology of a
units sheaf with the Picard group. -/
@[stacks 0C1J "the units short exact sequence"]
theorem isShortExact_units_of_isGlueingTwoPoints {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : IsGlueingTwoPoints f a b) (hab : a ≫ f = b ≫ f) :
    ∃ (φ : unitsSheaf X.toLocallyRingedSpace.toRingedSpace ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
          (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace))
      (ψ : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
          (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) ⟶
        skyscraperUnitsSheaf (k := k) X (gluedPoint f a))
      (hzero : φ ≫ ψ = 0),
      (ShortComplex.mk φ ψ hzero).ShortExact ∧
      (∀ (U : X.Opens) (s : Γ(X, U)ˣ),
        φ.hom.app (op U) (Additive.ofMul s) =
          Additive.ofMul (Units.map (f.app U).hom.toMonoidHom s)) ∧
      (∀ (U : X.Opens) (hz : gluedPoint f a ∈ U)
        (ha : a.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U)
        (hb : b.base (IsLocalRing.closedPoint k) ∈ f ⁻¹ᵁ U) (s : Γ(X', f ⁻¹ᵁ U)ˣ),
        skyscraperUnitsEval X (gluedPoint f a) hz
            (ψ.hom.app (op U) (Additive.ofMul s)) =
          Additive.ofMul (unitRatioAt a b (f ⁻¹ᵁ U) ha hb s)) :=
  ⟨unitsPushforwardMap f, unitsRatioPushforwardMap f a b hab,
    unitsPushforwardMap_comp_ratio f a b hab,
    shortExact_units f a b h hab (unitsPushforwardMap_comp_ratio f a b hab),
    fun U s => unitsPushforwardMap_app f U s,
    fun U hz ha hb s => ratio_app_eval f a b hab U hz ha hb s⟩

end Stacks.GlueSquishUnits

end
