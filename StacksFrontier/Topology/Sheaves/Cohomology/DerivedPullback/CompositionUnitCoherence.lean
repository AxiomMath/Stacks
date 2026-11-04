module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.SingleUnitComposition
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# The structure-sheaf comparison in a shifted degree is pseudofunctorial

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (W, 𝒪_W)` be morphisms of ringed spaces.
`Stacks.RingedSpace.derivedPullbackShiftedUnitIso h p` is the identification
`ν_h : Lh^*(𝒪[-p]) ≅ 𝒪[-p]`, the comparison `Lh^*(𝒪[0]) ≅ 𝒪[0]` of [Stacks, Tag 01CD]
conjugated by the commutation of `Lh^*` with the shift of [Stacks, Tag 06YJ]. This file proves
that the family `ν` is compatible with the composition isomorphism
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` of [Stacks, Tag 0D5S],

`c_{f,g} ≫ ν_{f ≫ g} = Lf^*(ν_g) ≫ ν_f`,

and then that the four such comparisons attached to a commutative square of ringed spaces agree
across it. That last statement was the hypothesis `hcompat` of [Stacks, Tag 0G79], the last
thing that tag was waiting on; `shiftedUnitIso_square_left` is it in the spelling the tag
consumes, so [Stacks, Tag 0G79] is now unconditional.

## Main results

* `StacksDraft.UnitPullbackComposition.commShift_derivedPullbackCompComparisonCanonical`:
  **the comparison of [Stacks, Tag 0D5S] commutes with the shift.** Nothing in the development
  had a `CategoryTheory.NatTrans.CommShift` for it before.
* `StacksDraft.UnitPullbackComposition.derivedPullbackCompIsoCanonical_hom_app_shiftedUnit`:
  **the coherence**, in an arbitrary degree `p`.
* `StacksDraft.UnitPullbackComposition.shiftedUnitIso_square`: the coherence read around a
  commutative square.
* `StacksDraft.UnitPullbackComposition.shiftedUnitIso_square_left`: the same, with the
  composition isomorphism down the left read as
  `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`. **This is the hypothesis
  `hcompat` of [Stacks, Tag 0G79]**, which therefore no longer has one.

## Implementation notes

*Why the comparison's commutation with the shift needs the K-flat complexes.* The comparison of
Tag 0D5S is `CategoryTheory.Functor.leftDerivedLift` of
`Stacks.DerivedPullback.Composition.derivedPullbackCompCounit`, and the equation characterising
it has `derivedPullbackComparison (f ≫ g)` on the right, which is not monic. So the equation
determines the comparison only where that map is invertible — which is at the K-flat complexes,
by [Stacks, Tag 06YJ]. `commShift_of_isIso_comp` is the detection principle in that shape: the
condition is tested on a class of objects where the comparison is invertible, and the class is
asked to reach every object of the derived category only after localization. The K-flat objects
enter only as an index set for `CategoryTheory.NatTrans.ext_of_essSurj`, so no shift on them is
needed.

*Associators are not optional.* `derivedPullbackCompCounit` is a three-fold composite of
whiskerings written without associators; the two bracketings are definitionally equal functors
but `CategoryTheory.Functor.CommShift.comp` gives them *different* commutations with the shift,
so an instance for one is not an instance for the other.
`derivedPullbackCompCounitComposite` is the same transformation with the three associators
inserted, and its commutation with the shift is then found by synthesis.

*Why so many one-line lemmas with every object a variable.* The terms here are large enough
that the **kernel's** budget — per declaration, and not raisable without `set_option` — is
spent by about two identifications of this size. In this file, the identification
`(e₁ ≪≫ e₂).hom.app A = e₁.hom.app A ≫ e₂.hom.app A`
at `e₁ = derivedPullbackCompIsoCanonical i' f` exceeds the kernel's budget *on its own*, for
every proof of it tried — `rfl`, `simp`, a `rw` chain, and an application of an abstract lemma
alike — while the same identification performed first at the level of natural transformations,
where no object occurs (`derivedPullbackCompIsoLeft_hom`), and then evaluated at an object with
`CategoryTheory.NatTrans.comp_app`, is cheap. (It is the `Iso.trans` projection that is dear,
not the evaluation: with the composite already written as `e₁.hom ≫ e₂.hom`, the same
identification at `shiftedUnitObject X p` checks by `rfl`.) Every step below is accordingly an
application of a lemma in which each category, functor, object and morphism is a variable, never
a `rw` on a goal of the full size, and no declaration consumes more than two concrete facts.

*A conversion that is affordable only in one shape.* The last step is the fold between the two
spellings of the composition isomorphism down the left: `shiftedUnitIso_square` writes it as
`derivedPullbackCompIsoCanonical i' f ≪≫ eqToIso (congrArg (derivedPullback ·) sq.symm)`, while
[Stacks, Tag 0G79] writes it as
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft gr i' i f sq`. The two are
definitionally equal (`derivedPullbackCompIsoLeft_eq`, by `rfl`), so the step is a conversion
and no mathematics — but it is *not* obtainable by substituting `shiftedUnitObject X p` into a
lemma whose object is a variable. Concretely:

* `derivedPullbackCompIsoLeft_hom_app f i i' gr sq (shiftedUnitObject X p)`, alone in its own
  declaration with the resulting statement written out, is **over the kernel's budget** —
  although the statement it proves checks with `rfl` on either side on its own, and the lemma it
  instantiates checks at a variable object. Substituting `square_of_facts` at the same object
  fails the same way, with the two composition laws supplied, with one of them, and with
  neither.
* `derivedPullbackCompIsoLeft_hom_app_shiftedUnit`, **the very same statement**, proved instead
  by `CategoryTheory.NatTrans.congr_app` of the *transformation-level*
  `derivedPullbackCompIsoLeft_hom` at that object, **is cheap** — under a second, where the
  substitution exhausts the budget.

The two differ in what the kernel is left to reconcile. `congr_app` of a transformation-level
equation leaves it comparing a composite of transformations evaluated at an object with the
composite of their evaluations: a projection and a beta step. Substituting into the
object-variable lemma leaves it reconciling a *substituted* statement with the freshly
elaborated one written here, and those agree only after the terms underneath are unfolded. So
the rule this file follows for the *argument* — state it where every object is a variable —
inverts for the *conversion*: state the conversion where no object occurs at all, and read it
at the object once.

## References

* [Stacks Project, Tag 0G79](https://stacks.math.columbia.edu/tag/0G79)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical
  derivedPullbackCompComparisonCanonical pullbackOnHomotopyCompIso)
open Stacks.RingedSpace (shiftedUnitObject shiftedUnitShiftIso derivedPullbackShiftedUnitIso
  derivedPullbackSingleUnitIso)

universe u

namespace StacksDraft.UnitPullbackComposition

attribute [local instance] HasDerivedCategory.standard

/-! ### Detecting the shift compatibility behind a comparison invertible on a resolving class -/

section Detect

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {V : Type u₁} [Category.{v₁} V] {C : Type u₂} [Category.{v₂} C] {H : Type u₃}
  [Category.{v₃} H] {E : Type u₄} [Category.{v₄} E] {M : Type*} [AddMonoid M]
  [HasShift C M] [HasShift H M] [HasShift E M]

/-- **Commutation with the shift passes from a comparison to a transformation it determines.**
Let `η : F ⟶ G` be a transformation of functors on `H`, let `r : C ⥤ H` commute with the shift,
and suppose `η` is characterised by `η_{r(K)} ≫ β_K = γ_K` for two transformations `β` and `γ`
out of `r ⋙ G` and `r ⋙ F` which commute with the shift.  If `β` is invertible at every object
in the image of some `p : V ⥤ C` whose composite with `r` is essentially surjective, then `η`
commutes with the shift.

`CategoryTheory.NatTrans.commShift_of_whiskerLeft` is not enough here, because `β` need not be
monic: what the characterising equation determines is `η` only where `β` *is* invertible.

The equation for `η` at `r(p(Z))` is obtained by cancelling the invertible `β_{p(Z)}⟦a⟧` on the
right and the invertible `F(r_a)` on the left, where `r_a` is the component of the commutation
of `r` with the shift; what is left is the equation for `γ` on one side and, by naturality of
`η` at `r_a` followed by the equation for `β`, the equation for `γ` again on the other. -/
theorem commShift_of_isIso_comp (p : V ⥤ C) (r : C ⥤ H) [r.CommShift M] [(p ⋙ r).EssSurj]
    {F G : H ⥤ E} [F.CommShift M] [G.CommShift M] (η : F ⟶ G) {P : C ⥤ E} [P.CommShift M]
    (β : r ⋙ G ⟶ P) (γ : r ⋙ F ⟶ P)
    (hβc : NatTrans.CommShift β M) (hγc : NatTrans.CommShift γ M)
    (hc : ∀ K : C, η.app (r.obj K) ≫ β.app K = γ.app K)
    (hβ : ∀ Z : V, IsIso (β.app (p.obj Z))) :
    NatTrans.CommShift η M := by
  have := hβc
  have := hγc
  apply NatTrans.CommShift.of_core
  intro a
  constructor
  refine NatTrans.ext_of_essSurj (p ⋙ r) fun Z ↦ ?_
  have hβZ : IsIso (β.app (p.obj Z)) := hβ Z
  have hγ := NatTrans.shift_app_comm γ a (p.obj Z)
  have hβ' := NatTrans.shift_app_comm β a (p.obj Z)
  have hn := η.naturality ((r.commShiftIso a).hom.app (p.obj Z))
  rw [Functor.commShiftIso_comp_hom_app] at hγ hβ'
  simp only [Category.assoc] at hγ hβ'
  dsimp at hn ⊢
  rw [← cancel_mono ((shiftFunctor E a).map (β.app (p.obj Z))), Category.assoc, Category.assoc,
    ← Functor.map_comp, hc (p.obj Z),
    ← cancel_epi (F.map ((r.commShiftIso a).hom.app (p.obj Z))), hγ,
    ← Category.assoc (F.map ((r.commShiftIso a).hom.app (p.obj Z))), hn, Category.assoc, hβ',
    ← Category.assoc, hc ((shiftFunctor C a).obj (p.obj Z))]

end Detect

/-! ### The comparison of Tag 0D5S commutes with the shift -/

open Stacks.Cohomology.KFlatDerivedPullback (IsKFlat hasResolutions_isKFlat
  isIso_derivedPullbackComparison_app_of_isKFlat)

section CommShift

variable {X Y W : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ W)

/-- **The K-flat complexes, localized, reach every object of `D(𝒪_W)`.**  Every object of the
derived category is isomorphic to the image of a complex, by essential surjectivity of `Qh`,
and that complex receives a quasi-isomorphism from a K-flat one, which `Qh` inverts. -/
theorem essSurj_kFlat_comp_Qh (W : RingedSpace.{u, u}) :
    ((IsKFlat W).ι ⋙ DerivedCategory.Qh).EssSurj where
  mem_essImage Z := by
    obtain ⟨N, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh) Z
    obtain ⟨K, hK, s, hs⟩ := hasResolutions_isKFlat W N
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing W))
          (ComplexShape.up ℤ)) s hs
    exact ⟨⟨K, hK⟩, ⟨asIso (DerivedCategory.Qh.map s) ≪≫ e⟩⟩

/-- The comparison `Qh ⋙ (Lg^* ⋙ Lf^*) ⟶ K((f ≫ g)^*)` of
`Stacks.DerivedPullback.Composition.derivedPullbackCompCounit`, written as a composite of
whiskerings and associators.

The associators are what `derivedPullbackCompCounit` leaves implicit: the two bracketings of a
triple composite are definitionally equal functors but carry *different* commutations with the
shift, so an instance for one is not an instance for the other, and
`CategoryTheory.NatTrans.CommShift.associator` is the transformation that identifies them. -/
abbrev derivedPullbackCompCounitComposite :
    DerivedCategory.Qh ⋙ (derivedPullback g ⋙ derivedPullback f) ⟶
      pullbackOnHomotopy (f ≫ g) :=
  (Functor.associator DerivedCategory.Qh (derivedPullback g) (derivedPullback f)).inv ≫
    Functor.whiskerRight (derivedPullbackComparison g) (derivedPullback f) ≫
    (Functor.associator ((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (derivedPullback f)).hom ≫
    Functor.whiskerLeft ((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedPullbackComparison f) ≫
    (Functor.associator ((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh).inv ≫
    Functor.whiskerRight (pullbackOnHomotopyCompIso f g).hom DerivedCategory.Qh

/-- **The characterising equation of the comparison of Tag 0D5S**, with its right-hand side read
as the composite transformation above.  This is
`DerivedPushforwardComposition.derivedPullbackCompIsoCanonical_hom_app_comp_comparison`; the
associators contribute identities at every object. -/
theorem comparison_comp_eq_compCounitComposite
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ)) :
    (derivedPullbackCompComparisonCanonical f g).app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison (f ≫ g)).app K =
      (derivedPullbackCompCounitComposite f g).app K :=
  (open Stacks.Cohomology.DerivedPushforwardComposition in
    derivedPullbackCompIsoCanonical_hom_app_comp_comparison f g K).trans (by simp)

/-- **The comparison `Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*` of [Stacks, Tag 0D5S] commutes with the
shift.**

It is characterised by `comparison_comp_eq_compCounitComposite`, whose two other terms commute
with the shift; the comparison for `L(f ≫ g)^*` appearing there need not be monic, but it *is*
invertible at every K-flat complex, and the K-flat complexes reach every object of `D(𝒪_W)`
after localization.  That is the input of `commShift_of_isIso_comp`. -/
instance commShift_derivedPullbackCompComparisonCanonical :
    NatTrans.CommShift (derivedPullbackCompComparisonCanonical f g) ℤ := by
  have := essSurj_kFlat_comp_Qh W
  exact commShift_of_isIso_comp (IsKFlat W).ι DerivedCategory.Qh
    (derivedPullbackCompComparisonCanonical f g) (derivedPullbackComparison (f ≫ g))
    (derivedPullbackCompCounitComposite f g) inferInstance inferInstance
    (comparison_comp_eq_compCounitComposite f g)
    fun Z => isIso_derivedPullbackComparison_app_of_isKFlat (f ≫ g) Z.obj Z.property

/-- The composition isomorphism of [Stacks, Tag 0D5S] commutes with the shift. -/
instance commShift_derivedPullbackCompIsoCanonical_hom :
    NatTrans.CommShift (derivedPullbackCompIsoCanonical f g).hom ℤ :=
  commShift_derivedPullbackCompComparisonCanonical f g

end CommShift

/-! ### Pure category theory, with every object a variable

The lemmas of this section mention no ringed space.  They are stated with every category,
functor, object and morphism a variable so that a consumer pays one conversion check per
argument; see the implementation notes for why that matters here. -/

section General

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]

/-- **A composition law for maps out of a shifted object follows from the one in degree zero**,
as soon as the transformation `τ` relating the two sides commutes with the shift.

`sW`, `sY` and `sX` present three objects as shifts of three others, `ug`, `uf` and `ugf` are
maps out of the images of the unshifted ones, and `h` is the composition law between them.  The
conclusion is the composition law for the three conjugated maps. -/
theorem shiftIso_comp_of_comp (Fg : C₀ ⥤ C₁) (Ff : C₁ ⥤ C₂) (Fgf : C₀ ⥤ C₂)
    [Fg.CommShift ℤ] [Ff.CommShift ℤ] [Fgf.CommShift ℤ]
    (τ : Fg ⋙ Ff ⟶ Fgf) [NatTrans.CommShift τ ℤ] (n : ℤ)
    {w₀ w : C₀} {y₀ y : C₁} {x₀ x : C₂}
    (sW : (shiftFunctor C₀ n).obj w₀ ≅ w) (sY : (shiftFunctor C₁ n).obj y₀ ≅ y)
    (sX : (shiftFunctor C₂ n).obj x₀ ≅ x)
    (ug : Fg.obj w₀ ⟶ y₀) (uf : Ff.obj y₀ ⟶ x₀) (ugf : Fgf.obj w₀ ⟶ x₀)
    (h : τ.app w₀ ≫ ugf = Ff.map ug ≫ uf) :
    τ.app w ≫ Fgf.map sW.inv ≫ (Fgf.commShiftIso n).hom.app w₀ ≫
          (shiftFunctor C₂ n).map ugf ≫ sX.hom =
      Ff.map (Fg.map sW.inv ≫ (Fg.commShiftIso n).hom.app w₀ ≫
          (shiftFunctor C₁ n).map ug ≫ sY.hom) ≫
        Ff.map sY.inv ≫ (Ff.commShiftIso n).hom.app y₀ ≫
          (shiftFunctor C₂ n).map uf ≫ sX.hom := by
  have hn := τ.naturality sW.inv
  have hs := NatTrans.shift_app_comm τ n w₀
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hn, ← reassoc_of% hs, ← Functor.map_comp_assoc, h, Functor.map_comp,
    Functor.commShiftIso_comp_hom_app]
  simp only [Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality_assoc Ff ug n]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Cancelling a retraction in front of a composite. -/
theorem pre_cancel {D : Type*} [Category* D] {o₀ o₁ T : D} (a : o₀ ⟶ o₁) (a' : o₁ ⟶ o₀)
    (ha : a ≫ a' = 𝟙 o₀) (L : o₁ ⟶ T) (ν : o₀ ⟶ T) (hL : L = a' ≫ ν) : a ≫ L = ν := by
  rw [hL, ← Category.assoc, ha, Category.id_comp]

/-- Rewriting the first factor of a composite. -/
theorem rewrite_head {D : Type*} [Category* D] {o₁ o₂ T : D} {x y : o₁ ⟶ o₂} (hxy : x = y)
    (q : o₂ ⟶ T) (rhs : o₁ ⟶ T) (h : y ≫ q = rhs) : x ≫ q = rhs := by
  rwa [hxy]

/-- Rewriting the *second* factor of a composite, leaving the first factor and the tail alone.
`rewrite_head` with a morphism in front, bracketed so that a hypothesis already of the shape
`a ≫ (x₁ ≫ x₂) ≫ q = rhs` matches `h` syntactically, with no conversion. -/
theorem rewrite_mid {D : Type*} [Category* D] {o₀ o₁ o₂ T : D} (a : o₀ ⟶ o₁) {x y : o₁ ⟶ o₂}
    (hxy : x = y) (q : o₂ ⟶ T) (rhs : o₀ ⟶ T) (h : a ≫ y ≫ q = rhs) : a ≫ x ≫ q = rhs := by
  rwa [hxy]

/-- Reading a triangle `c₂ ≫ ν = m ≫ w` backwards through the invertible `c₂`. -/
theorem inv_app_comp {C D : Type*} [Category* C] [Category* D] {K H : C ⥤ D} (c₂ : K ≅ H)
    (A : C) {ob T : D} (m : K.obj A ⟶ ob) (ν : H.obj A ⟶ T) (w : ob ≅ T)
    (h : c₂.hom.app A ≫ ν = m ≫ w.hom) : c₂.inv.app A ≫ m = ν ≫ w.inv := by
  have hm : m = c₂.hom.app A ≫ ν ≫ w.inv := by
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hm, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- A functor carries `e.inv ≫ e.hom` to an identity. -/
theorem map_inv_hom_id {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {a b : C}
    (e : a ≅ b) : F.map e.inv ≫ F.map e.hom = 𝟙 (F.obj b) := by
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- Grafting a triangle onto the tail of a composite. -/
theorem glue_tail {D : Type*} [Category* D] {o₀ o₁ o₂ o₃ T ob : D} (a : o₀ ⟶ o₁) (L : o₁ ⟶ o₂)
    (ci : o₂ ⟶ o₃) (m : o₃ ⟶ ob) (ν : o₂ ⟶ T) (w : T ⟶ ob) (r : o₀ ⟶ T)
    (h₁ : a ≫ L ≫ ν = r) (h₂ : ci ≫ m = ν ≫ w) : a ≫ L ≫ ci ≫ m = r ≫ w := by
  rw [h₂, reassoc_of% h₁]

end General

/-! ### The coherence of the structure-sheaf comparison in degree `p` -/

section Coherence

variable {X Y W : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ W)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison `Lh^*(𝒪[-p]) ≅ 𝒪[-p]` of [Stacks, Tag 01CD] is pseudofunctorial**: the
composition isomorphism of [Stacks, Tag 0D5S] followed by the comparison for `f ≫ g` is the
derived pullback along `f` of the comparison for `g`, followed by the comparison for `f`.

The degree-`p` comparison is the degree-`0` one conjugated by the commutation of the derived
pullback with the shift, so this is
`derivedPullbackCompIsoCanonical_hom_app_singleUnit` together with
`commShift_derivedPullbackCompIsoCanonical_hom`, assembled by `shiftIso_comp_of_comp`. -/
theorem derivedPullbackCompIsoCanonical_hom_app_shiftedUnit (p : ℤ) :
    (derivedPullbackCompIsoCanonical f g).hom.app (shiftedUnitObject W p) ≫
        (derivedPullbackShiftedUnitIso (f ≫ g) p).hom =
      (derivedPullback f).map (derivedPullbackShiftedUnitIso g p).hom ≫
        (derivedPullbackShiftedUnitIso f p).hom :=
  shiftIso_comp_of_comp (derivedPullback g) (derivedPullback f) (derivedPullback (f ≫ g))
    (derivedPullbackCompIsoCanonical f g).hom (-p)
    (shiftedUnitShiftIso W p) (shiftedUnitShiftIso Y p) (shiftedUnitShiftIso X p)
    (derivedPullbackSingleUnitIso g).hom (derivedPullbackSingleUnitIso f).hom
    (derivedPullbackSingleUnitIso (f ≫ g)).hom
    (derivedPullbackCompIsoCanonical_hom_app_singleUnit f g)

end Coherence

/-! ### The coherence around a commutative square -/

section Square

variable {X X' Z Z' : RingedSpace.{u, u}}
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Z'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting the comparison `Lh^*(𝒪[-p]) ≅ 𝒪[-p]` along an equality of the morphism `h`. -/
theorem eqToIso_derivedPullback_hom_app_shiftedUnit (h h' : Z' ⟶ X) (e : h = h') (p : ℤ) :
    (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) e)).hom.app
          (shiftedUnitObject X p) ≫ (derivedPullbackShiftedUnitIso h' p).hom =
      (derivedPullbackShiftedUnitIso h p).hom := by
  subst e
  rw [eqToIso.hom, eqToHom_app, eqToHom_refl, Category.id_comp]

omit [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The composition isomorphism for the two legs `i'` and `f`, followed by the transport along
the square's commutativity, against the comparisons `Lh^*(𝒪[-p]) ≅ 𝒪[-p]`. -/
theorem comp_eqToIso_shiftedUnit (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (gr : Z' ⟶ Z)
    (sq : gr ≫ i = i' ≫ f) (p : ℤ) :
    (derivedPullbackCompIsoCanonical i' f).hom.app (shiftedUnitObject X p) ≫
        (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm)).hom.app
          (shiftedUnitObject X p) ≫ (derivedPullbackShiftedUnitIso (gr ≫ i) p).hom =
      (derivedPullback i').map (derivedPullbackShiftedUnitIso f p).hom ≫
        (derivedPullbackShiftedUnitIso i' p).hom :=
  (congrArg (fun t => (derivedPullbackCompIsoCanonical i' f).hom.app (shiftedUnitObject X p) ≫ t)
      (eqToIso_derivedPullback_hom_app_shiftedUnit (i' ≫ f) (gr ≫ i) sq.symm p)).trans
    (derivedPullbackCompIsoCanonical_hom_app_shiftedUnit i' f p)

omit [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `comp_eqToIso_shiftedUnit` with the two comparisons bracketed together, which is the shape
`derivedPullbackCompIsoLeft_hom_app` meets. -/
theorem comp_eqToIso_shiftedUnit_assoc (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (gr : Z' ⟶ Z)
    (sq : gr ≫ i = i' ≫ f) (p : ℤ) :
    ((derivedPullbackCompIsoCanonical i' f).hom.app (shiftedUnitObject X p) ≫
          (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm)).hom.app
            (shiftedUnitObject X p)) ≫ (derivedPullbackShiftedUnitIso (gr ≫ i) p).hom =
      (derivedPullback i').map (derivedPullbackShiftedUnitIso f p).hom ≫
        (derivedPullbackShiftedUnitIso i' p).hom :=
  (Category.assoc _ _ _).trans (comp_eqToIso_shiftedUnit f i i' gr sq p)

omit [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The comparison of [Stacks, Tag 0D5S] down the left of a commutative square is the
composition isomorphism for the two legs followed by the transport along the square's
commutativity.  One unfolding step, performed at the level of isomorphisms, where no object
occurs. -/
theorem derivedPullbackCompIsoLeft_eq (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X')
    (gr : Z' ⟶ Z) (sq : gr ≫ i = i' ≫ f) :
    Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft gr i' i f sq =
      derivedPullbackCompIsoCanonical i' f ≪≫
        eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm) :=
  rfl

omit [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `derivedPullbackCompIsoLeft_eq` on the underlying transformations.  Splitting the composite
here, where no object occurs, is what makes the next lemma affordable. -/
theorem derivedPullbackCompIsoLeft_hom (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X')
    (gr : Z' ⟶ Z) (sq : gr ≫ i = i' ≫ f) :
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft gr i' i f sq).hom =
      (derivedPullbackCompIsoCanonical i' f).hom ≫
        (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm)).hom :=
  congrArg Iso.hom (derivedPullbackCompIsoLeft_eq f i i' gr sq)

omit [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `derivedPullbackCompIsoLeft_hom` at an object. -/
theorem derivedPullbackCompIsoLeft_hom_app (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X')
    (gr : Z' ⟶ Z) (sq : gr ≫ i = i' ≫ f)
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft gr i' i f sq).hom.app A =
      (derivedPullbackCompIsoCanonical i' f).hom.app A ≫
        (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm)).hom.app A :=
  (congrArg (fun t => t.app A) (derivedPullbackCompIsoLeft_hom f i i' gr sq)).trans
    (NatTrans.comp_app _ _ A)

/-- **The square coherence, at an arbitrary object and for arbitrary comparisons.**  Given the
composition law for the two legs `i'`, `f` of the square (already transported along its
commutativity) and the one for the two legs `gr`, `i`, the two routes around the square agree.

The object `A` and the five comparisons are variables, and the one unfolding of
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is performed here.  This is
*not* how `shiftedUnitIso_square_left` is obtained: substituting the shifted structure sheaf
and the canonical comparisons into this statement is over the kernel's budget, which is why the
square is assembled there out of steps each written at the concrete object.  See the
implementation notes. -/
theorem square_of_facts (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (gr : Z' ⟶ Z)
    (sq : gr ≫ i = i' ≫ f) (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {bf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {bi : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))}
    {t : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z'))}
    (νf : (derivedPullback f).obj A ≅ bf) (νi' : (derivedPullback i').obj bf ⟶ t)
    (νi : (derivedPullback i).obj A ⟶ bi) (νgr : (derivedPullback gr).obj bi ≅ t)
    (νa : (derivedPullback (gr ≫ i)).obj A ⟶ t)
    (hL : ((derivedPullbackCompIsoCanonical i' f).hom.app A ≫
          (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm)).hom.app A) ≫ νa =
        (derivedPullback i').map νf.hom ≫ νi')
    (h₂ : (derivedPullbackCompIsoCanonical gr i).hom.app A ≫ νa =
        (derivedPullback gr).map νi ≫ νgr.hom) :
    (derivedPullback i').map νf.inv ≫
        (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft gr i' i f sq).hom.app A ≫
        (derivedPullbackCompIsoCanonical gr i).inv.app A ≫ (derivedPullback gr).map νi =
      νi' ≫ νgr.inv :=
  glue_tail _ _ _ _ _ _ _
    (pre_cancel _ _ (map_inv_hom_id (derivedPullback i') νf) _ _
      (rewrite_head (derivedPullbackCompIsoLeft_hom_app f i i' gr sq A) νa _ hL))
    (inv_app_comp _ A _ _ νgr h₂)

/-- The composition isomorphism along the top and down the right of the square, read backwards
against the comparisons `Lh^*(𝒪[-p]) ≅ 𝒪[-p]`. -/
theorem derivedPullbackCompIsoCanonical_inv_app_shiftedUnit (i : Z ⟶ X) (gr : Z' ⟶ Z) (p : ℤ) :
    (derivedPullbackCompIsoCanonical gr i).inv.app (shiftedUnitObject X p) ≫
        (derivedPullback gr).map (derivedPullbackShiftedUnitIso i p).hom =
      (derivedPullbackShiftedUnitIso (gr ≫ i) p).hom ≫
        (derivedPullbackShiftedUnitIso gr p).inv :=
  inv_app_comp _ (shiftedUnitObject X p) _ _ (derivedPullbackShiftedUnitIso gr p)
    (derivedPullbackCompIsoCanonical_hom_app_shiftedUnit gr i p)

omit [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `comp_eqToIso_shiftedUnit_assoc` with the comparison for `f` cancelled off in front. -/
theorem comp_eqToIso_shiftedUnit_cancel (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (gr : Z' ⟶ Z)
    (sq : gr ≫ i = i' ≫ f) (p : ℤ) :
    (derivedPullback i').map (derivedPullbackShiftedUnitIso f p).inv ≫
        (((derivedPullbackCompIsoCanonical i' f).hom.app (shiftedUnitObject X p) ≫
            (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm)).hom.app
              (shiftedUnitObject X p)) ≫ (derivedPullbackShiftedUnitIso (gr ≫ i) p).hom) =
      (derivedPullbackShiftedUnitIso i' p).hom :=
  pre_cancel _ _ (map_inv_hom_id (derivedPullback i') (derivedPullbackShiftedUnitIso f p)) _ _
    (comp_eqToIso_shiftedUnit_assoc f i i' gr sq p)

/-- **The four comparisons `Lh^*(𝒪[-p]) ≅ 𝒪[-p]` agree across a commutative square of ringed
spaces.**  The two routes `L(i')^*Lf^*(𝒪_X[-p]) ⟶ L(gr)^*(𝒪_Z[-p])` — one through the comparison
for `f` and the composition isomorphism down the left of the square, the other through the
comparisons for `i'` and for `gr` — are the same.

The composition isomorphism down the left is written here as `derivedPullbackCompIsoLeft_eq`
gives it, rather than as `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`
itself; `shiftedUnitIso_square_left` is the same statement in the latter spelling, which is the
one [Stacks, Tag 0G79] consumes. -/
theorem shiftedUnitIso_square (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (gr : Z' ⟶ Z)
    (sq : gr ≫ i = i' ≫ f) (p : ℤ) :
    (derivedPullback i').map (derivedPullbackShiftedUnitIso f p).inv ≫
        ((derivedPullbackCompIsoCanonical i' f).hom.app (shiftedUnitObject X p) ≫
          (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm)).hom.app
            (shiftedUnitObject X p)) ≫
        (derivedPullbackCompIsoCanonical gr i).inv.app (shiftedUnitObject X p) ≫
        (derivedPullback gr).map (derivedPullbackShiftedUnitIso i p).hom =
      (derivedPullbackShiftedUnitIso i' p).hom ≫
        (derivedPullbackShiftedUnitIso gr p).inv :=
  glue_tail _ _ _ _ _ _ _ (comp_eqToIso_shiftedUnit_cancel f i i' gr sq p)
    (derivedPullbackCompIsoCanonical_inv_app_shiftedUnit i gr p)

/-! #### The same square with the composition isomorphism down the left folded back in

`shiftedUnitIso_square` writes the composition isomorphism down the left out as
`derivedPullbackCompIsoLeft_eq` gives it; [Stacks, Tag 0G79] wants it folded back into
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`.  The two are definitionally
equal, and the fold at the shifted structure sheaf *is* affordable — but only through the
transformation-level `derivedPullbackCompIsoLeft_hom`, read at the object by
`CategoryTheory.NatTrans.congr_app`.  Substituting the object into
`derivedPullbackCompIsoLeft_hom_app`, which is the same equation with the object a variable, is
not: see the implementation notes. -/

omit [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The fold.**  `derivedPullbackCompIsoLeft_hom_app` at the shifted structure sheaf, read off
the transformation-level `derivedPullbackCompIsoLeft_hom` rather than obtained by substituting
the object into the object-variable form.  The remaining identification, between a composite of
transformations evaluated at an object and the composite of their evaluations, is free. -/
theorem derivedPullbackCompIsoLeft_hom_app_shiftedUnit (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X')
    (gr : Z' ⟶ Z) (sq : gr ≫ i = i' ≫ f) (p : ℤ) :
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft gr i' i f sq).hom.app
          (shiftedUnitObject X p) =
      (derivedPullbackCompIsoCanonical i' f).hom.app (shiftedUnitObject X p) ≫
        (eqToIso (congrArg (fun k : Z' ⟶ X => derivedPullback k) sq.symm)).hom.app
          (shiftedUnitObject X p) :=
  NatTrans.congr_app (derivedPullbackCompIsoLeft_hom f i i' gr sq) (shiftedUnitObject X p)

/-- **The four comparisons `Lh^*(𝒪[-p]) ≅ 𝒪[-p]` agree across a commutative square**, with the
composition isomorphism down the left read as
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` itself.

This is `shiftedUnitIso_square` with the fold applied to its middle factor, and it is the
hypothesis `hcompat` of
`Stacks.Cohomology.SupportedComplexes.forgetSupport_pullbackSupportedClass_preimage_shiftedUnit`,
[Stacks, Tag 0G79], which is therefore no longer a hypothesis there. -/
theorem shiftedUnitIso_square_left (f : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (gr : Z' ⟶ Z)
    (sq : gr ≫ i = i' ≫ f) (p : ℤ) :
    (derivedPullback i').map (derivedPullbackShiftedUnitIso f p).inv ≫
        (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft gr i' i f sq).hom.app
          (shiftedUnitObject X p) ≫
        (derivedPullbackCompIsoCanonical gr i).inv.app (shiftedUnitObject X p) ≫
        (derivedPullback gr).map (derivedPullbackShiftedUnitIso i p).hom =
      (derivedPullbackShiftedUnitIso i' p).hom ≫ (derivedPullbackShiftedUnitIso gr p).inv :=
  rewrite_mid _ (derivedPullbackCompIsoLeft_hom_app_shiftedUnit f i i' gr sq p) _ _
    (shiftedUnitIso_square f i i' gr sq p)

end Square

end StacksDraft.UnitPullbackComposition

end
