module

public import Mathlib.Data.Set.Finite.Range
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Groupoid.Basic

/-!
# Finite collections of arrows

Let `C` be a groupoid, presented as a septuple `(Ob, Arrows, s, t, c, e, i)`. In the vocabulary of
this development that presentation is a `Deformation.PointwiseGroupoid`: two sets, a source and a
target map, a composition law on composable pairs, and the assertion that these make the objects
into a groupoid whose morphisms from `x` to `y` are the arrows with source `x` and target `y`. The
unit `e` and the inverse `i` are then determined, and are named here.

Out of this data **Stacks 04RS** builds another groupoid `C_fin`:

* an object is a finite subset `Z ⊆ Arrows` with `s(Z) = {u}` a singleton and `e(u) ∈ Z`;
* an arrow is a pair `(Z, z)` with `Z` an object and `z ∈ Z`;
* the source of `(Z, z)` is `Z`, and its target is `{z' ∘ z⁻¹ : z' ∈ Z}`;
* the composition of `(Z₁, z₁)` with `(Z₂, z₂)`, when `Z₁` is the target of `(Z₂, z₂)`, is
  `(Z₂, z₁ ∘ z₂)`.

The Stacks project omits the verification that this is a groupoid; it is carried out here.

## Main definitions

* `Deformation.PointwiseGroupoid.identityArrow` and
  `Deformation.PointwiseGroupoid.inverseArrow`: the unit `e` and the inverse `i` determined by a
  septuple.
* `Deformation.PointwiseGroupoid.ofFaithful`: a septuple is a groupoid as soon as it maps to one
  by a pair of maps which is injective on arrows with a common source and which matches the unit,
  the composition and the inverse.
* `Deformation.PointwiseGroupoid.FiniteArrows.Obj`,
  `Deformation.PointwiseGroupoid.FiniteArrows.Arr`,
  `Deformation.PointwiseGroupoid.FiniteArrows.src`,
  `Deformation.PointwiseGroupoid.FiniteArrows.tgt`,
  `Deformation.PointwiseGroupoid.FiniteArrows.unit`,
  `Deformation.PointwiseGroupoid.FiniteArrows.inv` and
  `Deformation.PointwiseGroupoid.FiniteArrows.compose`: the septuple of `C_fin`.
* `Deformation.PointwiseGroupoid.finiteArrows`: **Stacks 04RS**, that septuple is a groupoid.

## Main results

* `Deformation.PointwiseGroupoid.comp_assoc`, `.comp_identityArrow_fst`,
  `.comp_identityArrow_snd`, `.comp_inverseArrow_fst`, `.comp_inverseArrow_snd` and the two
  cancellation laws `.comp_comp_inverseArrow`, `.comp_comp_inverseArrow'`: the groupoid laws read
  as equalities between arrows, which is the form in which the construction of `C_fin` uses them.
* `Deformation.PointwiseGroupoid.FiniteArrows.mem_tgt_iff`: an arrow lies in the target of
  `(Z, z)` exactly when composing it with `z` lands in `Z`. This characterization, rather than the
  defining image, is what the groupoid laws of `C_fin` are checked against.

## Implementation notes

An object of `C_fin` is recorded as a structure carrying `u`, the subset `Z`, its finiteness, the
condition `s(Z) = {u}` in the form "every element of `Z` has source `u`", and `e(u) ∈ Z`. Nothing
is carried twice: `u` is determined by `Z`, which is
`Deformation.PointwiseGroupoid.FiniteArrows.Obj.base_eq_of_arrows_eq`. Writing `s(Z) = {u}` as a
universally quantified equation together with `e(u) ∈ Z` is equivalent to the singleton condition,
since `e(u) ∈ Z` makes `Z` nonempty.

The target of `(Z, z)` is the range of a map defined on the subtype `↥Z`, not the image of a map
defined on all of `Arrows`: composing with `z⁻¹` needs the composability hypothesis, which is
available only for elements of `Z`. Finiteness of the range is then automatic.

The groupoid laws are not checked by hand on the subsets. Instead the pair of maps `(Z, z) ↦ z` on
arrows and `Z ↦ u` on objects is recorded as faithful, and
`Deformation.PointwiseGroupoid.ofFaithful` transports the laws from `C`. That reflection is what
`Deformation.PointwiseGroupoid.ofIndexing` cannot do here: the arrows of `C_fin` from `Z` to `Z'`
are only *some* of the arrows of `C` from `u` to `u'`, so the identification `ofIndexing` demands
is not available — as the Stacks project puts it, `C_fin` is a disjoint union of groupoids.

The morphisms of the groupoid carried by a septuple are reached through
`Deformation.PointwiseGroupoid.homOf`, which takes the two endpoint equations as arguments rather
than fixing them to be reflexivity, so that a law may be read at whichever endpoints its consumer
has. For the same reason every statement below takes the composability hypotheses of the
compositions it mentions as arguments; those hypotheses are propositions, so any proof of them
will do.

## References

* [Stacks Project, Tag 0018](https://stacks.math.columbia.edu/tag/0018)
* [Stacks Project, Tag 0230](https://stacks.math.columbia.edu/tag/0230)
* [Stacks Project, Tag 04RS](https://stacks.math.columbia.edu/tag/04RS)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open CategoryTheory

universe w

namespace Deformation.PointwiseGroupoid

variable {U R : Type w} {source target : R → U}
  {comp : { p : R × R // source p.1 = target p.2 } → R}

/-! ### Reading an arrow as a morphism -/

/-- The morphism of the groupoid carried by `P` from `x` to `y` represented by an arrow `a` whose
source is `x` and whose target is `y`. -/
def homOf (P : PointwiseGroupoid source target comp) {x y : U} (a : R)
    (hx : source a = x) (hy : target a = y) :
    @Quiver.Hom U P.groupoid.toCategory.toQuiver x y :=
  (P.arrowEquiv x y).symm ⟨a, hx, hy⟩

/-- The arrow represented by `P.homOf a hx hy` is `a`. -/
theorem arrowEquiv_homOf (P : PointwiseGroupoid source target comp) {x y : U} (a : R)
    (hx : source a = x) (hy : target a = y) :
    (P.arrowEquiv x y (P.homOf a hx hy)).1 = a :=
  congrArg Subtype.val (Equiv.apply_symm_apply (P.arrowEquiv x y) _)

/-- Two arrows with the same endpoints which represent the same morphism are equal. -/
theorem eq_of_homOf_eq (P : PointwiseGroupoid source target comp) {x y : U} {a b : R}
    {hax : source a = x} {hay : target a = y} {hbx : source b = x} {hby : target b = y}
    (h : P.homOf a hax hay = P.homOf b hbx hby) : a = b := by
  simpa only [arrowEquiv_homOf] using congrArg (fun k => (P.arrowEquiv x y k).1) h

/-- The morphism represented by an arrow does not depend on the chosen endpoint equations. -/
theorem homOf_congr (P : PointwiseGroupoid source target comp) {x y : U} {a b : R} (hab : a = b)
    (hax : source a = x) (hay : target a = y) (hbx : source b = x) (hby : target b = y) :
    P.homOf a hax hay = P.homOf b hbx hby := by
  subst hab
  rfl

/-- Composition of morphisms represented by arrows is the composition of the septuple. -/
theorem homOf_comp (P : PointwiseGroupoid source target comp) {x y z : U} (a b : R)
    (hab : source a = target b) (hbx : source b = x) (hby : target b = y)
    (hay : source a = y) (haz : target a = z)
    (hcx : source (comp ⟨(a, b), hab⟩) = x) (hcz : target (comp ⟨(a, b), hab⟩) = z) :
    @CategoryStruct.comp U P.groupoid.toCategory.toCategoryStruct x y z
        (P.homOf b hbx hby) (P.homOf a hay haz) =
      P.homOf (comp ⟨(a, b), hab⟩) hcx hcz := by
  refine (P.arrowEquiv x z).injective (Subtype.ext ?_)
  rw [arrowEquiv_homOf, P.comp_eq]
  exact congrArg comp (Subtype.ext (Prod.ext (arrowEquiv_homOf P a hay haz)
    (arrowEquiv_homOf P b hbx hby)))

/-! ### The unit and the inverse of a septuple -/

/-- The unit `e(x)`: the arrow representing the identity morphism at `x`. -/
def identityArrow (P : PointwiseGroupoid source target comp) (x : U) : R :=
  (P.arrowEquiv x x (@CategoryStruct.id U P.groupoid.toCategory.toCategoryStruct x)).1

/-- The unit at `x` has source `x`. -/
theorem source_identityArrow (P : PointwiseGroupoid source target comp) (x : U) :
    source (P.identityArrow x) = x :=
  (P.arrowEquiv x x (@CategoryStruct.id U P.groupoid.toCategory.toCategoryStruct x)).2.1

/-- The unit at `x` has target `x`. -/
theorem target_identityArrow (P : PointwiseGroupoid source target comp) (x : U) :
    target (P.identityArrow x) = x :=
  (P.arrowEquiv x x (@CategoryStruct.id U P.groupoid.toCategory.toCategoryStruct x)).2.2

/-- The unit at `x` represents the identity morphism at `x`. -/
theorem homOf_identityArrow (P : PointwiseGroupoid source target comp) {x : U}
    (hx : source (P.identityArrow x) = x) (hy : target (P.identityArrow x) = x) :
    P.homOf (P.identityArrow x) hx hy =
      @CategoryStruct.id U P.groupoid.toCategory.toCategoryStruct x := by
  refine (P.arrowEquiv x x).injective (Subtype.ext ?_)
  rw [arrowEquiv_homOf]
  rfl

/-- The inverse `i(a)`: the arrow representing the inverse of the morphism represented by `a`. -/
def inverseArrow (P : PointwiseGroupoid source target comp) (a : R) : R :=
  (P.arrowEquiv (target a) (source a)
    (@Groupoid.inv U P.groupoid (source a) (target a) (P.homOf a rfl rfl))).1

/-- The inverse of `a` has source the target of `a`. -/
theorem source_inverseArrow (P : PointwiseGroupoid source target comp) (a : R) :
    source (P.inverseArrow a) = target a :=
  (P.arrowEquiv (target a) (source a)
    (@Groupoid.inv U P.groupoid (source a) (target a) (P.homOf a rfl rfl))).2.1

/-- The inverse of `a` has target the source of `a`. -/
theorem target_inverseArrow (P : PointwiseGroupoid source target comp) (a : R) :
    target (P.inverseArrow a) = source a :=
  (P.arrowEquiv (target a) (source a)
    (@Groupoid.inv U P.groupoid (source a) (target a) (P.homOf a rfl rfl))).2.2

/-- The inverse of `a` represents the inverse of the morphism represented by `a`. -/
theorem homOf_inverseArrow (P : PointwiseGroupoid source target comp) {x y : U} (a : R)
    (hx : source a = x) (hy : target a = y)
    (hx' : source (P.inverseArrow a) = y) (hy' : target (P.inverseArrow a) = x) :
    P.homOf (P.inverseArrow a) hx' hy' =
      @Groupoid.inv U P.groupoid x y (P.homOf a hx hy) := by
  subst hx hy
  refine (P.arrowEquiv (target a) (source a)).injective (Subtype.ext ?_)
  rw [arrowEquiv_homOf]
  rfl

/-! ### The groupoid laws as equalities between arrows -/

/-- A composition depends only on the two arrows composed. -/
theorem comp_congr (_P : PointwiseGroupoid source target comp) {a b a' b' : R} (ha : a = a')
    (hb : b = b') (h : source a = target b) (h' : source a' = target b') :
    comp ⟨(a, b), h⟩ = comp ⟨(a', b'), h'⟩ := by
  subst ha hb
  rfl

/-- A composite of arrows equals `c` as soon as the composite of the represented morphisms is the
morphism represented by `c`. -/
private theorem comp_eq_of_homOf_comp_eq (P : PointwiseGroupoid source target comp) {x y z : U}
    (a b c : R) (hab : source a = target b) (hbx : source b = x) (hby : target b = y)
    (hay : source a = y) (haz : target a = z) (hcx : source c = x) (hcz : target c = z)
    (h : @CategoryStruct.comp U P.groupoid.toCategory.toCategoryStruct x y z
        (P.homOf b hbx hby) (P.homOf a hay haz) = P.homOf c hcx hcz) :
    comp ⟨(a, b), hab⟩ = c :=
  P.eq_of_homOf_eq
    ((P.homOf_comp a b hab hbx hby hay haz ((P.source_comp a b hab).trans hbx)
      ((P.target_comp a b hab).trans haz)).symm.trans h)

/-- Composing an arrow with the unit at its target on the left returns the arrow. -/
theorem comp_identityArrow_fst (P : PointwiseGroupoid source target comp) (a : R) (u : U)
    (hu : target a = u) (h : source (P.identityArrow u) = target a) :
    comp ⟨(P.identityArrow u, a), h⟩ = a := by
  subst hu
  have cg := congrArg (fun k => @CategoryStruct.comp U P.groupoid.toCategory.toCategoryStruct
      (source a) (target a) (target a) (P.homOf a rfl rfl) k)
    (P.homOf_identityArrow h (P.target_identityArrow (target a)))
  have idc := @Category.comp_id U P.groupoid.toCategory (source a) (target a)
    (P.homOf a rfl rfl)
  exact comp_eq_of_homOf_comp_eq P _ a a h rfl rfl h (P.target_identityArrow _) rfl rfl
    (cg.trans idc)

/-- Composing an arrow with the unit at its source on the right returns the arrow. -/
theorem comp_identityArrow_snd (P : PointwiseGroupoid source target comp) (a : R) (u : U)
    (hu : source a = u) (h : source a = target (P.identityArrow u)) :
    comp ⟨(a, P.identityArrow u), h⟩ = a := by
  subst hu
  have cg := congrArg (fun k => @CategoryStruct.comp U P.groupoid.toCategory.toCategoryStruct
      (source a) (source a) (target a) k (P.homOf a rfl rfl))
    (P.homOf_identityArrow (P.source_identityArrow (source a))
      (P.target_identityArrow (source a)))
  have idc := @Category.id_comp U P.groupoid.toCategory (source a) (target a)
    (P.homOf a rfl rfl)
  exact comp_eq_of_homOf_comp_eq P a _ a h (P.source_identityArrow _) (P.target_identityArrow _)
    rfl rfl rfl rfl (cg.trans idc)

/-- An arrow composed with its inverse on the left is the unit at the source of the arrow. -/
theorem comp_inverseArrow_fst (P : PointwiseGroupoid source target comp) (a : R)
    (h : source (P.inverseArrow a) = target a) :
    comp ⟨(P.inverseArrow a, a), h⟩ = P.identityArrow (source a) := by
  have cg := congrArg (fun k => @CategoryStruct.comp U P.groupoid.toCategory.toCategoryStruct
      (source a) (target a) (source a) (P.homOf a rfl rfl) k)
    (P.homOf_inverseArrow a rfl rfl h (P.target_inverseArrow a))
  have ci := @Groupoid.comp_inv U P.groupoid (source a) (target a) (P.homOf a rfl rfl)
  have hid := (P.homOf_identityArrow (P.source_identityArrow (source a))
    (P.target_identityArrow (source a))).symm
  exact comp_eq_of_homOf_comp_eq P _ a _ h rfl rfl h (P.target_inverseArrow a)
    (P.source_identityArrow _) (P.target_identityArrow _) (cg.trans (ci.trans hid))

/-- An arrow composed with its inverse on the right is the unit at the target of the arrow. -/
theorem comp_inverseArrow_snd (P : PointwiseGroupoid source target comp) (a : R)
    (h : source a = target (P.inverseArrow a)) :
    comp ⟨(a, P.inverseArrow a), h⟩ = P.identityArrow (target a) := by
  have cg := congrArg (fun k => @CategoryStruct.comp U P.groupoid.toCategory.toCategoryStruct
      (target a) (source a) (target a) k (P.homOf a rfl rfl))
    (P.homOf_inverseArrow a rfl rfl (P.source_inverseArrow a) (P.target_inverseArrow a))
  have ic := @Groupoid.inv_comp U P.groupoid (source a) (target a) (P.homOf a rfl rfl)
  have hid := (P.homOf_identityArrow (P.source_identityArrow (target a))
    (P.target_identityArrow (target a))).symm
  exact comp_eq_of_homOf_comp_eq P a _ _ h (P.source_inverseArrow a) (P.target_inverseArrow a)
    rfl rfl (P.source_identityArrow _) (P.target_identityArrow _) (cg.trans (ic.trans hid))

/-- Composition of arrows is associative. -/
theorem comp_assoc (P : PointwiseGroupoid source target comp) (a b d : R)
    (hab : source a = target b) (hbd : source b = target d)
    (h₁ : source (comp ⟨(a, b), hab⟩) = target d)
    (h₂ : source a = target (comp ⟨(b, d), hbd⟩)) :
    comp ⟨(comp ⟨(a, b), hab⟩, d), h₁⟩ = comp ⟨(a, comp ⟨(b, d), hbd⟩), h₂⟩ := by
  have e1 := P.homOf_comp b d hbd rfl rfl hbd rfl
    (P.source_comp b d hbd) (P.target_comp b d hbd)
  have e2 := P.homOf_comp a b hab hbd rfl hab rfl
    ((P.source_comp a b hab).trans hbd) (P.target_comp a b hab)
  have e4 := P.homOf_comp a (comp ⟨(b, d), hbd⟩) h₂ (P.source_comp b d hbd)
    (P.target_comp b d hbd) hab rfl
    ((P.source_comp a _ h₂).trans (P.source_comp b d hbd)) (P.target_comp a _ h₂)
  have c1 := congrArg (fun k => @CategoryStruct.comp U P.groupoid.toCategory.toCategoryStruct
      (source d) (target d) (target a) (P.homOf d rfl rfl) k) e2.symm
  have asc := (@Category.assoc U P.groupoid.toCategory (source d) (target d) (target b)
    (target a) (P.homOf d rfl rfl) (P.homOf b hbd rfl) (P.homOf a hab rfl)).symm
  have c2 := congrArg (fun k => @CategoryStruct.comp U P.groupoid.toCategory.toCategoryStruct
      (source d) (target b) (target a) k (P.homOf a hab rfl)) e1
  exact comp_eq_of_homOf_comp_eq P _ d _ h₁ rfl rfl h₁ (P.target_comp a b hab)
    ((P.source_comp a _ h₂).trans (P.source_comp b d hbd)) (P.target_comp a _ h₂)
    (c1.trans (asc.trans (c2.trans e4)))

/-- Composing `a ∘ b⁻¹` with `b` returns `a`, for arrows `a` and `b` with a common source. -/
theorem comp_comp_inverseArrow (P : PointwiseGroupoid source target comp) (a b : R)
    (hs : source a = source b) (h₀ : source a = target (P.inverseArrow b))
    (h₁ : source (comp ⟨(a, P.inverseArrow b), h₀⟩) = target b) :
    comp ⟨(comp ⟨(a, P.inverseArrow b), h₀⟩, b), h₁⟩ = a := by
  have hiv : source (P.inverseArrow b) = target b := P.source_inverseArrow b
  refine (P.comp_assoc a (P.inverseArrow b) b h₀ hiv h₁
    (h₀.trans (P.target_comp _ b hiv).symm)).trans ?_
  refine (P.comp_congr (a := a) (b := comp ⟨(P.inverseArrow b, b), hiv⟩) rfl
    (P.comp_inverseArrow_fst b hiv) _
    (hs.trans (P.target_identityArrow (source b)).symm)).trans ?_
  exact P.comp_identityArrow_snd a (source b) hs
    (hs.trans (P.target_identityArrow (source b)).symm)

/-- Composing `a ∘ b` with `b⁻¹` returns `a`, for arrows with the source of `a` the target
of `b`. -/
theorem comp_comp_inverseArrow' (P : PointwiseGroupoid source target comp) (a b : R)
    (hab : source a = target b)
    (h₁ : source (comp ⟨(a, b), hab⟩) = target (P.inverseArrow b)) :
    comp ⟨(comp ⟨(a, b), hab⟩, P.inverseArrow b), h₁⟩ = a := by
  have hiv : source b = target (P.inverseArrow b) := (P.target_inverseArrow b).symm
  refine (P.comp_assoc a b (P.inverseArrow b) hab hiv h₁
    (hab.trans (P.target_comp b _ hiv).symm)).trans ?_
  refine (P.comp_congr (a := a) (b := comp ⟨(b, P.inverseArrow b), hiv⟩) rfl
    (P.comp_inverseArrow_snd b hiv) _
    (hab.trans (P.target_identityArrow (target b)).symm)).trans ?_
  exact P.comp_identityArrow_snd a (target b) hab
    (hab.trans (P.target_identityArrow (target b)).symm)

/-! ### Reflecting a groupoid along a faithful pair of maps -/

/-- A septuple `(O, A, s', t', c', e', i')` is a groupoid as soon as it maps to a groupoid `P` by
a pair of maps `objMap`, `arrowMap` which is compatible with source and target, which matches the
unit, the composition and the inverse, and which is *faithful*: two arrows with the same source
and the same image are equal.

The groupoid structure produced has the arrows from `x` to `y` as its morphisms from `x` to `y`,
so nothing is chosen; each law is checked by mapping it into `P`, where it holds, and reading it
back through faithfulness. -/
def ofFaithful {O A : Type w} {s' t' : A → O}
    {c' : { p : A × A // s' p.1 = t' p.2 } → A}
    (P : PointwiseGroupoid source target comp)
    (objMap : O → U) (arrowMap : A → R)
    (hs : ∀ a, source (arrowMap a) = objMap (s' a))
    (ht : ∀ a, target (arrowMap a) = objMap (t' a))
    (hfaithful : ∀ a b : A, s' a = s' b → arrowMap a = arrowMap b → a = b)
    (unit : O → A) (unit_source : ∀ x, s' (unit x) = x) (unit_target : ∀ x, t' (unit x) = x)
    (unit_map : ∀ x, arrowMap (unit x) = P.identityArrow (objMap x))
    (comp_source : ∀ q, s' (c' q) = s' q.1.2) (comp_target : ∀ q, t' (c' q) = t' q.1.1)
    (comp_map : ∀ q : { p : A × A // s' p.1 = t' p.2 },
      arrowMap (c' q) = comp ⟨(arrowMap q.1.1, arrowMap q.1.2),
        (hs q.1.1).trans ((congrArg objMap q.2).trans (ht q.1.2).symm)⟩)
    (inv : A → A) (inv_source : ∀ a, s' (inv a) = t' a) (inv_target : ∀ a, t' (inv a) = s' a)
    (inv_map : ∀ a, arrowMap (inv a) = P.inverseArrow (arrowMap a)) :
    PointwiseGroupoid s' t' c' := by
  letI _inst : Groupoid.{w} U := P.groupoid
  let hom (x y : O) := { a : A // s' a = x ∧ t' a = y }
  let map {x y : O} (a : hom x y) : objMap x ⟶ objMap y :=
    P.homOf (arrowMap a.1) ((hs a.1).trans (congrArg objMap a.2.1))
      ((ht a.1).trans (congrArg objMap a.2.2))
  have map_inj {x y : O} (a b : hom x y) (h : map a = map b) : a = b :=
    Subtype.ext (hfaithful a.1 b.1 (a.2.1.trans b.2.1.symm) (P.eq_of_homOf_eq h))
  let id' (x : O) : hom x x := ⟨unit x, unit_source x, unit_target x⟩
  let comp'' {x y z : O} (a : hom x y) (b : hom y z) : hom x z :=
    ⟨c' ⟨(b.1, a.1), b.2.1.trans a.2.2.symm⟩,
      (comp_source _).trans a.2.1, (comp_target _).trans b.2.2⟩
  let inv' {x y : O} (a : hom x y) : hom y x :=
    ⟨inv a.1, (inv_source a.1).trans a.2.2, (inv_target a.1).trans a.2.1⟩
  have map_id (x : O) : map (id' x) = 𝟙 (objMap x) :=
    (P.homOf_congr (unit_map x) _ _ (P.source_identityArrow _)
      (P.target_identityArrow _)).trans
      (P.homOf_identityArrow (P.source_identityArrow _) (P.target_identityArrow _))
  have map_comp {x y z : O} (a : hom x y) (b : hom y z) :
      map (comp'' a b) = map a ≫ map b := by
    have hab : source (arrowMap b.1) = target (arrowMap a.1) :=
      (hs b.1).trans ((congrArg objMap (b.2.1.trans a.2.2.symm)).trans (ht a.1).symm)
    have hax : source (arrowMap a.1) = objMap x := (hs a.1).trans (congrArg objMap a.2.1)
    have hay : target (arrowMap a.1) = objMap y := (ht a.1).trans (congrArg objMap a.2.2)
    have hbx : source (arrowMap b.1) = objMap y := (hs b.1).trans (congrArg objMap b.2.1)
    have hby : target (arrowMap b.1) = objMap z := (ht b.1).trans (congrArg objMap b.2.2)
    exact (P.homOf_congr (comp_map ⟨(b.1, a.1), b.2.1.trans a.2.2.symm⟩) _ _
        ((P.source_comp _ _ hab).trans hax) ((P.target_comp _ _ hab).trans hby)).trans
      (P.homOf_comp (arrowMap b.1) (arrowMap a.1) hab hax hay hbx hby
        ((P.source_comp _ _ hab).trans hax) ((P.target_comp _ _ hab).trans hby)).symm
  have map_inv {x y : O} (a : hom x y) : map (inv' a) = Groupoid.inv (map a) := by
    have hax : source (arrowMap a.1) = objMap x := (hs a.1).trans (congrArg objMap a.2.1)
    have hay : target (arrowMap a.1) = objMap y := (ht a.1).trans (congrArg objMap a.2.2)
    exact (P.homOf_congr (inv_map a.1) _ _
        ((P.source_inverseArrow _).trans hay) ((P.target_inverseArrow _).trans hax)).trans
      (P.homOf_inverseArrow (arrowMap a.1) hax hay
        ((P.source_inverseArrow _).trans hay) ((P.target_inverseArrow _).trans hax))
  have hid_comp {x y : O} (a : hom x y) : comp'' (id' x) a = a := by
    refine map_inj _ _ ?_
    rw [map_comp, map_id, Category.id_comp]
  have hcomp_id {x y : O} (a : hom x y) : comp'' a (id' y) = a := by
    refine map_inj _ _ ?_
    rw [map_comp, map_id, Category.comp_id]
  have hassoc {w' x y z : O} (a : hom w' x) (b : hom x y) (d : hom y z) :
      comp'' (comp'' a b) d = comp'' a (comp'' b d) := by
    refine map_inj _ _ ?_
    rw [map_comp, map_comp, map_comp, map_comp, Category.assoc]
  let cat : Category.{w} O :=
    { Hom := hom
      id := id'
      comp := comp''
      id_comp := hid_comp
      comp_id := hcomp_id
      assoc := hassoc }
  letI := cat
  have hinv_comp {x y : O} (a : hom x y) : comp'' (inv' a) a = id' y := by
    refine map_inj _ _ ?_
    rw [map_comp, map_inv, map_id, Groupoid.inv_comp]
  have hcomp_inv {x y : O} (a : hom x y) : comp'' a (inv' a) = id' x := by
    refine map_inj _ _ ?_
    rw [map_comp, map_inv, map_id, Groupoid.comp_inv]
  exact
    { groupoid :=
        { __ := cat
          inv := inv'
          inv_comp := hinv_comp
          comp_inv := hcomp_inv }
      arrowEquiv := fun _ _ => Equiv.refl _
      comp_eq := fun _ _ => rfl }

/-! ### The septuple of finite collections of arrows -/

namespace FiniteArrows

/-- An object of `C_fin`: a finite subset `Z` of the arrows whose elements all have source `u`,
containing the unit at `u`.

The point `u` is determined by `Z`, by `Obj.base_eq_of_arrows_eq`. -/
structure Obj (P : PointwiseGroupoid source target comp) where
  /-- The common source `u` of the arrows in the collection. -/
  base : U
  /-- The collection `Z` of arrows. -/
  arrows : Set R
  /-- The collection is finite. -/
  finite : arrows.Finite
  /-- Every arrow in the collection has source `u`, which together with the next field says that
  the set of sources of the collection is the singleton `{u}`. -/
  source_eq : ∀ z ∈ arrows, source z = base
  /-- The unit at `u` belongs to the collection. -/
  identityArrow_mem : P.identityArrow base ∈ arrows

/-- An arrow of `C_fin`: an object together with one of its arrows. -/
structure Arr (P : PointwiseGroupoid source target comp) where
  /-- The collection `Z`. -/
  obj : Obj P
  /-- The chosen arrow `z` of the collection. -/
  arrow : R
  /-- The chosen arrow belongs to the collection. -/
  arrow_mem : arrow ∈ obj.arrows

variable (P : PointwiseGroupoid source target comp)

/-- Objects of `C_fin` with the same point and the same collection are equal. -/
theorem Obj.ext' {X Y : Obj P} (hbase : X.base = Y.base) (harrows : X.arrows = Y.arrows) :
    X = Y := by
  cases X
  cases Y
  subst hbase harrows
  rfl

/-- The point of an object of `C_fin` is determined by its collection. -/
theorem Obj.base_eq_of_arrows_eq {X Y : Obj P} (harrows : X.arrows = Y.arrows) :
    X.base = Y.base := by
  have h : P.identityArrow X.base ∈ Y.arrows := harrows ▸ X.identityArrow_mem
  exact (P.source_identityArrow X.base).symm.trans (Y.source_eq _ h)

/-- Arrows of `C_fin` with the same collection and the same chosen arrow are equal. -/
theorem Arr.ext' {a b : Arr P} (hobj : a.obj = b.obj) (harrow : a.arrow = b.arrow) : a = b := by
  cases a
  cases b
  subst hobj harrow
  rfl

/-- The chosen arrow of an arrow of `C_fin` has source the point of its collection. -/
theorem Arr.source_arrow (a : Arr P) : source a.arrow = a.obj.base :=
  a.obj.source_eq a.arrow a.arrow_mem

/-- The source `s'` of `C_fin`: the rule `(Z, z) ↦ Z`. -/
def src (a : Arr P) : Obj P := a.obj

/-- The composability datum used to translate the collection of `(Z, z)` by `z⁻¹`. -/
theorem translate_composable (a : Arr P) {z : R} (hz : z ∈ a.obj.arrows) :
    source z = target (P.inverseArrow a.arrow) :=
  ((a.obj.source_eq z hz).trans (Arr.source_arrow P a).symm).trans
    (P.target_inverseArrow a.arrow).symm

/-- The target `t'` of `C_fin`: the rule `(Z, z) ↦ {z' ∘ z⁻¹ : z' ∈ Z}`. -/
def tgt (a : Arr P) : Obj P where
  base := target a.arrow
  arrows := Set.range fun z : a.obj.arrows =>
    comp ⟨(z.1, P.inverseArrow a.arrow), translate_composable P a z.2⟩
  finite := by
    have : Finite a.obj.arrows := a.obj.finite.to_subtype
    exact Set.finite_range _
  source_eq := by
    rintro w ⟨z, rfl⟩
    exact (P.source_comp _ _ _).trans (P.source_inverseArrow a.arrow)
  identityArrow_mem :=
    ⟨⟨a.arrow, a.arrow_mem⟩,
      P.comp_inverseArrow_snd a.arrow (translate_composable P a a.arrow_mem)⟩

/-- An arrow in the target collection of `(Z, z)` has source the target of `z`. -/
theorem source_of_mem_tgt (a : Arr P) {w : R} (hw : w ∈ (tgt P a).arrows) :
    source w = target a.arrow :=
  (tgt P a).source_eq w hw

/-- An arrow lies in the target collection of `(Z, z)` exactly when composing it with `z` lands
in `Z`. -/
theorem mem_tgt_iff (a : Arr P) (w : R) (h : source w = target a.arrow) :
    w ∈ (tgt P a).arrows ↔ comp ⟨(w, a.arrow), h⟩ ∈ a.obj.arrows := by
  refine ⟨?_, fun hc => ⟨⟨comp ⟨(w, a.arrow), h⟩, hc⟩,
    P.comp_comp_inverseArrow' w a.arrow h (translate_composable P a hc)⟩⟩
  rintro ⟨z, hzz⟩
  have hsX : source (comp ⟨(z.1, P.inverseArrow a.arrow),
      translate_composable P a z.2⟩) = target a.arrow := (congrArg source hzz).trans h
  have heq : comp ⟨(w, a.arrow), h⟩ = z.1 :=
    (P.comp_congr hzz.symm rfl h hsX).trans <| P.comp_comp_inverseArrow z.1 a.arrow
      ((a.obj.source_eq z.1 z.2).trans (Arr.source_arrow P a).symm)
      (translate_composable P a z.2) hsX
  rw [heq]
  exact z.2

/-- The unit `e'` of `C_fin`: the rule `Z ↦ (Z, e(u))`. -/
def unit (X : Obj P) : Arr P where
  obj := X
  arrow := P.identityArrow X.base
  arrow_mem := X.identityArrow_mem

/-- The inverse `i'` of `C_fin`: the rule `(Z, z) ↦ (Z ∘ z⁻¹, z⁻¹)`. -/
def inv (a : Arr P) : Arr P where
  obj := tgt P a
  arrow := P.inverseArrow a.arrow
  arrow_mem := by
    refine (mem_tgt_iff P a _ (P.source_inverseArrow a.arrow)).2 ?_
    rw [P.comp_inverseArrow_fst a.arrow (P.source_inverseArrow a.arrow),
      Arr.source_arrow P a]
    exact a.obj.identityArrow_mem

/-- The composability datum of a composable pair of arrows of `C_fin`. -/
theorem compose_composable (q : { p : Arr P × Arr P // src P p.1 = tgt P p.2 }) :
    source q.1.1.arrow = target q.1.2.arrow :=
  (Arr.source_arrow P q.1.1).trans (congrArg Obj.base q.2)

/-- The composition `c'` of `C_fin`: the rule `((Z₁, z₁), (Z₂, z₂)) ↦ (Z₂, z₁ ∘ z₂)`. -/
def compose (q : { p : Arr P × Arr P // src P p.1 = tgt P p.2 }) : Arr P where
  obj := q.1.2.obj
  arrow := comp ⟨(q.1.1.arrow, q.1.2.arrow), compose_composable P q⟩
  arrow_mem := by
    have hq : q.1.1.obj = tgt P q.1.2 := q.2
    refine (mem_tgt_iff P q.1.2 q.1.1.arrow (compose_composable P q)).1 ?_
    rw [← hq]
    exact q.1.1.arrow_mem

/-- The target of the unit at `Z` is `Z`. -/
theorem tgt_unit (X : Obj P) : tgt P (unit P X) = X := by
  refine Obj.ext' P (P.target_identityArrow X.base) (Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩)
  · have hsrc : source w = target (P.identityArrow X.base) := source_of_mem_tgt P (unit P X) hw
    have hc : comp ⟨(w, P.identityArrow X.base), hsrc⟩ ∈ X.arrows :=
      (mem_tgt_iff P (unit P X) w hsrc).1 hw
    rwa [P.comp_identityArrow_snd w X.base
      (hsrc.trans (P.target_identityArrow X.base)) hsrc] at hc
  · have hsrc : source w = target (P.identityArrow X.base) :=
      (X.source_eq w hw).trans (P.target_identityArrow X.base).symm
    refine (mem_tgt_iff P (unit P X) w hsrc).2 ?_
    change comp ⟨(w, P.identityArrow X.base), hsrc⟩ ∈ X.arrows
    rwa [P.comp_identityArrow_snd w X.base
      (hsrc.trans (P.target_identityArrow X.base)) hsrc]

/-- The target of the inverse of `(Z, z)` is `Z`. -/
theorem tgt_inv (a : Arr P) : tgt P (inv P a) = src P a := by
  refine Obj.ext' P ((P.target_inverseArrow a.arrow).trans (Arr.source_arrow P a))
    (Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩)
  · have hsrc : source w = target (P.inverseArrow a.arrow) := source_of_mem_tgt P (inv P a) hw
    have hc : comp ⟨(w, P.inverseArrow a.arrow), hsrc⟩ ∈ (tgt P a).arrows :=
      (mem_tgt_iff P (inv P a) w hsrc).1 hw
    have h₁ : source (comp ⟨(w, P.inverseArrow a.arrow), hsrc⟩) = target a.arrow :=
      source_of_mem_tgt P a hc
    have h2 := (mem_tgt_iff P a _ h₁).1 hc
    rwa [P.comp_comp_inverseArrow w a.arrow (hsrc.trans (P.target_inverseArrow a.arrow)) hsrc
      h₁] at h2
  · have hsrc : source w = target (P.inverseArrow a.arrow) := translate_composable P a hw
    refine (mem_tgt_iff P (inv P a) w hsrc).2 ?_
    change comp ⟨(w, P.inverseArrow a.arrow), hsrc⟩ ∈ (tgt P a).arrows
    exact ⟨⟨w, hw⟩, rfl⟩

/-- The target of a composite is the target of its first factor. -/
theorem tgt_compose (q : { p : Arr P × Arr P // src P p.1 = tgt P p.2 }) :
    tgt P (compose P q) = tgt P q.1.1 := by
  have hab : source q.1.1.arrow = target q.1.2.arrow := compose_composable P q
  have hq : q.1.1.obj = tgt P q.1.2 := q.2
  refine Obj.ext' P (P.target_comp _ _ hab)
    (Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩)
  · have hsrc : source w = target (comp ⟨(q.1.1.arrow, q.1.2.arrow), hab⟩) :=
      source_of_mem_tgt P (compose P q) hw
    have hsrc1 : source w = target q.1.1.arrow := hsrc.trans (P.target_comp _ _ hab)
    have hc : comp ⟨(w, comp ⟨(q.1.1.arrow, q.1.2.arrow), hab⟩), hsrc⟩ ∈ q.1.2.obj.arrows :=
      (mem_tgt_iff P (compose P q) w hsrc).1 hw
    have h₁ : source (comp ⟨(w, q.1.1.arrow), hsrc1⟩) = target q.1.2.arrow :=
      (P.source_comp w q.1.1.arrow hsrc1).trans hab
    refine (mem_tgt_iff P q.1.1 w hsrc1).2 ?_
    rw [hq]
    refine (mem_tgt_iff P q.1.2 _ h₁).2 ?_
    rwa [P.comp_assoc w q.1.1.arrow q.1.2.arrow hsrc1 hab h₁ hsrc]
  · have hsrc1 : source w = target q.1.1.arrow := source_of_mem_tgt P q.1.1 hw
    have hsrc : source w = target (comp ⟨(q.1.1.arrow, q.1.2.arrow), hab⟩) :=
      hsrc1.trans (P.target_comp _ _ hab).symm
    have h₁ : source (comp ⟨(w, q.1.1.arrow), hsrc1⟩) = target q.1.2.arrow :=
      (P.source_comp w q.1.1.arrow hsrc1).trans hab
    have hc : comp ⟨(w, q.1.1.arrow), hsrc1⟩ ∈ q.1.1.obj.arrows :=
      (mem_tgt_iff P q.1.1 w hsrc1).1 hw
    rw [hq] at hc
    have h2 := (mem_tgt_iff P q.1.2 _ h₁).1 hc
    refine (mem_tgt_iff P (compose P q) w hsrc).2 ?_
    change comp ⟨(w, comp ⟨(q.1.1.arrow, q.1.2.arrow), hab⟩), hsrc⟩ ∈ q.1.2.obj.arrows
    rwa [← P.comp_assoc w q.1.1.arrow q.1.2.arrow hsrc1 hab h₁ hsrc]

end FiniteArrows

/-- **Stacks 04RS.** The septuple of finite collections of arrows of a groupoid is a groupoid:
its objects are the finite subsets `Z` of the arrows with `s(Z)` a singleton `{u}` and
`e(u) ∈ Z`, its arrows are the pairs `(Z, z)` with `z ∈ Z`, the source of `(Z, z)` is `Z`, its
target is `{z' ∘ z⁻¹ : z' ∈ Z}`, and the composite of `(Z₁, z₁)` with `(Z₂, z₂)` is
`(Z₂, z₁ ∘ z₂)`.

The verification is a reflection along the faithful pair of maps `Z ↦ u` and `(Z, z) ↦ z`, which
carries the unit, the composition and the inverse of `C_fin` to those of the original groupoid. -/
@[stacks 04RS "the groupoid of finite collections of arrows"]
def finiteArrows (P : PointwiseGroupoid source target comp) :
    PointwiseGroupoid (FiniteArrows.src P) (FiniteArrows.tgt P) (FiniteArrows.compose P) :=
  P.ofFaithful (fun X => X.base) (fun a => a.arrow)
    (fun a => FiniteArrows.Arr.source_arrow P a) (fun _ => rfl)
    (fun _ _ hobj harrow => FiniteArrows.Arr.ext' P hobj harrow)
    (FiniteArrows.unit P) (fun _ => rfl) (FiniteArrows.tgt_unit P) (fun _ => rfl)
    (fun _ => rfl) (FiniteArrows.tgt_compose P) (fun _ => rfl)
    (FiniteArrows.inv P) (fun _ => rfl) (FiniteArrows.tgt_inv P) (fun _ => rfl)

end Deformation.PointwiseGroupoid

end
