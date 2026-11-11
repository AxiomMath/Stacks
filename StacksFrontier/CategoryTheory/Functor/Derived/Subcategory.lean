module

public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.Biprod
public import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
import StacksFrontier.CategoryTheory.Triangulated.Localization
public import StacksFrontier.CategoryTheory.Triangulated.Quotient

/-!
# The right derived functor lives on a triangulated subcategory

Let `F : 𝒟 ⥤ 𝒟'` be an exact functor of pre-triangulated categories and let `S` be a saturated
multiplicative system in `𝒟` compatible with the triangulated structure (Situation 05S8). The
right derived functor `RF` is *defined at* an object `X` when the ind-object
$$ X/S ⟶ 𝒟', \qquad (s : X ⟶ X') ⟼ F(X'), $$
is essentially constant; its value is then `RF(X)` (Tag 05S9). Write `ℰ` for the full
subcategory of `𝒟` spanned by the objects at which `RF` is defined, and
`S_ℰ = Arrows(ℰ) ∩ S`. Then `ℰ` is a strictly full triangulated subcategory of `𝒟`, `RF` is an
exact functor `ℰ ⥤ 𝒟'`, every element of `S` with source *or* target in `ℰ` is a morphism of
`ℰ`, `S_ℰ` is a saturated multiplicative system in `ℰ` compatible with the triangulated
structure which `RF` inverts, the induced functor `S_ℰ^{-1}ℰ ⥤ S^{-1}𝒟` is fully faithful and
exact, `RF` factors through an exact functor `S_ℰ^{-1}ℰ ⥤ 𝒟'`, and `ℰ` is moreover saturated
(thick) as soon as `𝒟'` is Karoubian. So `RF` lives on a strictly full triangulated subcategory
of `S^{-1}𝒟` and is exact there.

## Main results

* `CategoryTheory.Functor.isTriangulated_and_exists_rightDerivedFunctor` (Tag 05SE): the eight
  assertions of the tag, as one conjunction over the subcategory `ℰ` and one right derived
  functor `RF` on it.
* `DerivedFunctorSubcategory.isSaturated_inverseImage_ι`,
  `DerivedFunctorSubcategory.isCompatibleWithTriangulation_inverseImage_ι`,
  `DerivedFunctorSubcategory.full_and_faithful_of_lifting_inverseImage_ι`: parts (5) and (6) for
  any subcategory closed along `W`, shared with the statement for `LF`
  (`CategoryTheory.Functor.isTriangulated_and_exists_leftDerivedFunctor`).

## Implementation notes

*Faithfulness.* (1) No hypothesis is dead. `hW` (Stacks 05Q8, i.e. MS1–MS4) is what makes `S_ℰ`
a multiplicative system and, with `W.IsCompatibleWithTriangulation` and exactness of `F`, is the
input of Tags 05SB, 05SC and 05SD used by every conjunct; `hE` is the definition of `ℰ`, so it
is used by all of them; `L` and its data occur in the conjunct that is the tag's part (6);
Karoubian-ness of `𝒟'` is carried by the conjunct that is part (8), not by the theorem, since
the other parts do not use it. (2) The data are the source's: one class `W` of morphisms of the
*source* category `C`, the index categories `X/W` of morphisms of `W` out of `X` with arbitrary
morphisms of `C` under `X` between them, and the ind-object valued in `H` through `F` — no
localization of `C` and no change of `W` anywhere in the definedness condition; the localization
`L : C ⥤ D` of `C` at `W` and the localization `LE` of `ℰ` at `S_ℰ` enter only in parts (6) and
(7), where the source has them. (3) The functor `RF` is pinned, not merely asserted to exist:
its value at `X` is required to be a value of `RF` at `X` in the sense of Tag 05S9, *at the
prescribed cocone* `ι X` — so `RF.obj X` comes with the coprojections `(ι X).app s : F(X') ⟶
RF(X)` — and `RF.map f` is required to satisfy the characterisation of Tag 05SA for every
commutative square `f ≫ b.hom = a.hom ≫ g` with `a ∈ X/W`, `b ∈ Y/W`, which determines it
uniquely. Likewise the two functors of parts (6) and (7) are not asserted to exist but pinned as
lifts through `LE`, and every lift is asserted to be fully faithful, resp. exact. (4) The
instantiation is not degenerate: for `W = MorphismProperty.isomorphisms C` the object `𝟙 X` is
initial in `X/W`, so `RF` is defined at every object with value `F(X)` (see Tag 05S9), `ℰ = ⊤`,
`S_ℰ = MorphismProperty.isomorphisms ℰ`, `RF ≅ F` and both localizations are equivalences; `L`
may be taken to be `W.Q`.

*The subcategory as a hypothesis.* The source's `ℰ` is the object property
`fun X ↦ ∃ c, F.IsRightDerivedValueAt W X c` (Tag 05S9 and the spelling of definedness used by
Tags 05SB, 05SC, 05SD and 05SV). It is introduced as a variable `E` together with `hE`, which
says exactly that, rather than substituted eight times: the conjuncts speak about
`E.FullSubcategory`, `E.ι` and `W.inverseImage E.ι`, and the abstraction keeps those readable
and keeps the instances that parts (2), (5), (6), (7) are stated over syntactically visible. It
is not a weakening: `hE` determines `E`.

*Strict fullness and the shape of part (1).* "Strictly full triangulated subcategory" is
`E.IsClosedUnderIsomorphisms` together with `ObjectProperty.IsTriangulated` (Mathlib does not
build closure under isomorphisms into the latter, since e.g. bounded-below complexes in a
homotopy category form a triangulated subcategory that is not strictly full). Fullness itself is
automatic: the subcategory is `E.FullSubcategory`. Both facts are `∃`-bound rather than
`∧`-conjoined because the later conjuncts are stated *over* them: the pre-triangulated structure
on `E.FullSubcategory`, hence exactness of `RF`, hence parts (2)–(7), only exist once `E` is a
triangulated subcategory. For the same reason part (5) is `∃`-bound before parts (6) and (7),
which are stated over the pre-triangulated structure on `S_ℰ^{-1}ℰ` that part (5) provides
through Tag 05R6.

*Values and the cocone.* A cocone with prescribed vertex is a natural transformation to a
constant functor, so the family `ι` gives `Cocone.mk (RF.obj X) (ι X)` with vertex exactly
`RF.obj X`; this is what lets the value condition of Tag 05S9 and the characterisation of Tag
05SA (which is not a named declaration in this project, and is written out here as in Tags 05SB,
05SC and 05SD) be stated about `RF` itself, with no transport along an equality of objects.

*Part (3).* "Elements of `S` with either source or target in `ℰ` are morphisms of `ℰ`" is the
statement that `W s` implies `E X ↔ E Y` for `s : X ⟶ Y`: given either endpoint in `ℰ`, both
are, and then `s` is a morphism of the full subcategory `ℰ`, indeed one of `S_ℰ`. This is Tag
05SB(1) for definedness; here it is part of the package because parts (5) and (6) rest on it.

*Parts (6) and (7).* `S^{-1}𝒟` and `S_ℰ^{-1}ℰ` are not chosen constructions: `L : C ⥤ D` is an
arbitrary localization functor for `W` and `LE` an arbitrary localization functor for `S_ℰ`,
each with the additive and shift data over which Tag 05R6 puts the pre-triangulated structure
`Triangulated.Localization.pretriangulated` on the target, so nothing has to be transported
afterwards. The two induced functors are quantified as lifts, `[Localization.Lifting …]`, the
convention of Tag 05R7 in this project; the quantification is not vacuous, because `E.ι ⋙ L` and
`RF` both invert `S_ℰ` (the latter is the conjunct that is part (4)), so `Localization.lift`
provides a lift, unique up to canonical isomorphism. Their commutation with the shift is the one
they inherit, `Functor.commShiftOfLocalization`, as in Tag 05R7. The witness of part (5) is
named, because being a saturated multiplicative system is what gives `S_ℰ` its calculus of left
fractions (Tag 05Q8), and that is what Tag 05R6 needs of `S_ℰ` before it can pre-triangulate
`S_ℰ^{-1}ℰ`; so parts (6) and (7) are stated only after that datum is in scope.

*Karoubian and saturated.* "Karoubian" is `IsIdempotentComplete`, and "saturated triangulated
subcategory" is `ObjectProperty.IsSaturated` (Tag 05RB): a direct summand of an object of `ℰ` is
again in `ℰ`. This conjunct is Tag 05SD(2) transported to `ℰ`.

*The dual statement for `LF`.* The source closes with "a similar result holds for `LF`", the
same eight assertions for the pro-object notion `IsLeftDerivedValueAt` of Tag 05S9. That
statement is `CategoryTheory.Functor.isTriangulated_and_exists_leftDerivedFunctor`, also
registered for Tag 05SE, in `StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedSubcategory`;
the two assertions about a subcategory closed along `W` that both statements use (parts (5) and
(6)) are the public lemmas `DerivedFunctorSubcategory.isSaturated_inverseImage_ι`,
`DerivedFunctorSubcategory.isCompatibleWithTriangulation_inverseImage_ι` and
`DerivedFunctorSubcategory.full_and_faithful_of_lifting_inverseImage_ι` of this file.

## Proof outline

# The right derived functor lives on a strictly full triangulated subcategory

Let `F : C ⥤ H` be an exact functor of pre-triangulated categories and let `W` be a saturated
multiplicative system in `C` (Stacks 05Q8) compatible with the triangulation. The right derived
functor `RF` is *defined at* `X` when the ind-object
`X/W ⟶ H`, `(s : X ⟶ X') ↦ F(X')` is essentially constant, its value being `RF(X)`
(Stacks 05S9); `E` is the full subcategory of objects at which `RF` is defined.

The proof of Stacks 05SE runs as in the source. Since `W` is saturated it contains every
isomorphism, so `E` is closed under isomorphisms by Stacks 05SB(1); it contains the zero objects
because the ind-object at a zero object is essentially constant with value `F(0)`; it is stable
under the shift because `X⟦1⟧` is the third object of the rotation of the contractible triangle
at `X`, whose second object is a zero object, so Stacks 05SC applies (this is how the source's
Stacks 05SU enters, and it is the only use made of it here); and it is closed under the
two-out-of-three property for distinguished triangles by Stacks 05SC. That is part (1). Part (3)
is Stacks 05SB(1), part (4) its second half, and part (8) is Stacks 05SD(2). The functor `RF` is
built from a chosen value at each object of `E` together with the morphism of Stacks 05SA, which
is unique because a value cocone is a colimit cocone; parts (6) and (7) are Stacks 05R7 applied
to the localizations of Stacks 05R6.

## Implementation notes

A value cocone is a colimit cocone (`nonempty_isColimit_of_isRightDerivedValueAt`), so a morphism
out of it
is determined by its composites with the coprojections. That is what makes the morphism of Stacks
05SA unique, hence what makes `RF` a functor: `IsDerivedMap` is the characterisation
of that morphism, `exists_isDerivedMap` its existence and
`eq_of_isDerivedMap` its uniqueness.

The composite `F(X') ⟶ F(Y') ⟶ RF(Y)` attached to a commutative square is independent of the
square (`map_comp_ι_app_eq`) and, over a fixed square at a larger index, is computed
by transport along the morphism of index categories (`map_comp_ι_app_eq_of_hom`);
those two are the whole content of Stacks 05SA, and both existence and functoriality of the
morphism reduce to them. The source of a coprojection of the ind-object is `F(X')` only after
unfolding a composite of forgetful functors, so `rw` and `simp` do not reassociate such a
composite in place; `comp_assoc_of_comp_eq` is therefore stated for abstract
morphisms of `H`.

Stacks 05SU is not formalized as a statement in this project, and only its definedness half for
`n = 1` is used here; it is obtained from Stacks 05SC and the contractible triangle rather than by
transporting essential constancy along the shift of index categories, which is the source's argument
(`mem_shift_iff`).

## References

* [StacksProject 05SE](https://stacks.math.columbia.edu/tag/05SE), Proposition 13.14.6; the
  situation is Tag 05S8, saturated multiplicative systems are Tag 05Q8, definedness and values
  are Tag 05S9, the map `RF(f)` is Tag 05SA, the inputs are Tags 05SB, 05SC, 05SU and 05SD, the
  localization of a pre-triangulated category is Tag 05R6, the factorization is Tag 05R7, and
  saturated subcategories are Tag 05RB.
-/

-- The pretriangulated structure on the categories, the exactness of `F` and the compatibility
-- of `W` with the triangulation are part of the mathematical setup of Stacks 05S8; several of
-- the bookkeeping lemmas below do not literally consume all of them, so the
-- unused-section-variable linter is silenced, as in the other files of this section.
set_option linter.unusedSectionVars false

@[expose] public section

open CategoryTheory Limits Pretriangulated Localization ZeroObject

namespace DerivedFunctorSubcategory

open DerivedFunctorValues (underShift underShift_full)

open DerivedFunctorBiprodComputes (mem_of_isIso)

open _root_.DerivedFunctorValues

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-! ### Values of the right derived functor -/

section Values

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (F : C ⥤ H) (W : MorphismProperty C)

/-- A morphism out of a value of `RF` at `X` is determined by its composites with the
coprojections. -/
private lemma hom_ext_of_value {X : C} {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    (hc : F.IsRightDerivedValueAt W X c) {V : H} {u u' : c.pt ⟶ V}
    (h : ∀ s, c.ι.app s ≫ u = c.ι.app s ≫ u') : u = u' := by
  obtain ⟨hcol⟩ := nonempty_isColimit_of_isRightDerivedValueAt F W hc
  exact hcol.hom_ext h

/-- `RF` is defined at every zero object, with value `F(0)`: the ind-object at a zero object `Z`
takes its values in the zero object `F(Z)` of `H`, so all of its transition morphisms and all of
the coprojections of the constant cocone at `F(Z)` agree. -/
private lemma exists_value_of_isZero [W.ContainsIdentities] {Z : C} (hZ : IsZero Z)
    (hFZ : IsZero (F.obj Z)) : ∃ c, F.IsRightDerivedValueAt W Z c := by
  refine ⟨Cocone.mk (F.obj Z)
    { app := fun _ => hFZ.from_ _
      naturality := fun _ _ _ => hFZ.eq_of_tgt _ _ },
    MorphismProperty.Under.mk ⊤ (𝟙 Z) (W.id_mem Z), hFZ.from_ _, hFZ.eq_of_tgt _ _, fun s => ?_⟩
  exact ⟨MorphismProperty.Under.mk ⊤ (𝟙 Z) (W.id_mem Z),
    MorphismProperty.Under.homMk (hZ.from_ s.right) (hZ.eq_of_tgt _ _) trivial, 𝟙 _,
    hFZ.eq_of_tgt _ _⟩

end Values

/-! ### The morphism of Stacks 05SA -/

section DerivedMap

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (F : C ⥤ H) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]


/-- The composite `F(X') ⟶ F(Y') ⟶ d.pt` attached to a square over an index `s` of `X/W` is
computed at any index `k` that `s` maps to: it is `F` of the morphism `s ⟶ k`, followed by the
composite attached to a square over `k`. This is `map_comp_ι_app_eq` with the two
applications of `F.map_comp` folded in. -/
private lemma map_comp_ι_app_eq_of_hom {X Y : C} (f : X ⟶ Y)
    {d : Cocone (DerivedFunctorValues.indDiagram F W Y)}
    {s k : W.Under ⊤ X} (α : s ⟶ k) {t tk : W.Under ⊤ Y} {f' : s.right ⟶ t.right}
    {fk : k.right ⟶ tk.right} (hsq : f ≫ t.hom = s.hom ≫ f')
    (hsqk : f ≫ tk.hom = k.hom ≫ fk) :
    F.map f' ≫ d.ι.app t = F.map α.right ≫ F.map fk ≫ d.ι.app tk :=
  (map_comp_ι_app_eq F W f s t tk f' (α.right ≫ fk) hsq
    (by rw [hsqk, ← MorphismProperty.Under.w α, Category.assoc])).trans
      (F.map_comp_assoc α.right fk _)

/-- Postcomposing a factorisation `b = A ≫ r ≫ p` with an abstract tail `w`. It is stated for
abstract morphisms of `H` for the same reason as `comp_assoc_of_comp_eq`. -/
private lemma comp_comp_eq_of_eq {P Q R S T : H} {A : P ⟶ Q} {r : Q ⟶ R} {p : R ⟶ S} {b : P ⟶ S}
    (h : b = A ≫ r ≫ p) (w : S ⟶ T) : A ≫ r ≫ p ≫ w = b ≫ w := by
  rw [h]; simp only [Category.assoc]

/-- Splicing two commuting squares: from `A ≫ u = B ≫ b` and `b ≫ v = D` follows
`A ≫ u ≫ v = B ≫ D`. It is stated for abstract morphisms of `H` because the composites it is
applied to end in a coprojection of a cocone on the ind-object, whose source is `F(X')` only
after unfolding the composite of forgetful functors; neither `rw` nor `simp` reassociates such a
composite in place. -/
private lemma comp_assoc_of_comp_eq {P Q R S T : H} {A : P ⟶ Q} {u : Q ⟶ R} {v : R ⟶ S}
    {B : P ⟶ T} {b : T ⟶ R} {D : T ⟶ S} (h₁ : A ≫ u = B ≫ b) (h₂ : b ≫ v = D) :
    A ≫ u ≫ v = B ≫ D := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

variable {F W}

/-- **Stacks 05SA.** The characterisation of the morphism `RF(f) : c.pt ⟶ d.pt` induced by
`f : X ⟶ Y` between a cocone `c` on the ind-object at `X` and a cocone `d` on the ind-object at
`Y`: compatibility with the coprojections along every commutative square `f ≫ t = s ≫ f'` whose
vertical sides are indices of `X/W` and of `Y/W`. -/
private def IsDerivedMap {X Y : C} (f : X ⟶ Y) {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    {d : Cocone (DerivedFunctorValues.indDiagram F W Y)} (u : c.pt ⟶ d.pt) : Prop :=
  ∀ (s : W.Under ⊤ X) (t : W.Under ⊤ Y) (f' : s.right ⟶ t.right),
    f ≫ t.hom = s.hom ≫ f' → c.ι.app s ≫ u = F.map f' ≫ d.ι.app t

/-- **Stacks 05SA**, existence. If `RF` is defined at `X` with value `c`, then `f : X ⟶ Y`
induces a morphism `c.pt ⟶ d.pt` to the vertex of any cocone `d` on the ind-object at `Y`
satisfying the characterisation `IsDerivedMap`. -/
private lemma exists_isDerivedMap {X Y : C} (f : X ⟶ Y)
    {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    (hc : F.IsRightDerivedValueAt W X c) (d : Cocone (DerivedFunctorValues.indDiagram F W Y)) :
    ∃ u : c.pt ⟶ d.pt, IsDerivedMap f u := by
  obtain ⟨s₀, r, hr, hcof⟩ := hc
  obtain ⟨t₀, f₀, hsq₀⟩ := exists_leftSquare_under W f s₀
  refine ⟨r ≫ F.map f₀ ≫ d.ι.app t₀, fun s t f' hsq => ?_⟩
  obtain ⟨k, β, α, hk⟩ := hcof s
  obtain ⟨tk, fk, hsqk⟩ := exists_leftSquare_under W f k
  rw [map_comp_ι_app_eq_of_hom F W f α hsq₀ hsqk, map_comp_ι_app_eq_of_hom F W f β hsq hsqk]
  exact comp_comp_eq_of_eq hk _

/-- **Stacks 05SA**, uniqueness. -/
private lemma eq_of_isDerivedMap {X Y : C} (f : X ⟶ Y)
    {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    (hc : F.IsRightDerivedValueAt W X c) {d : Cocone (DerivedFunctorValues.indDiagram F W Y)}
    {u u' : c.pt ⟶ d.pt}
    (hu : IsDerivedMap f u) (hu' : IsDerivedMap f u') : u = u' := by
  refine hom_ext_of_value F W hc fun s => ?_
  obtain ⟨t, f', hsq⟩ := exists_leftSquare_under W f s
  rw [hu s t f' hsq, hu' s t f' hsq]

/-- The characterisation of Stacks 05SA is compatible with composition. -/
private lemma IsDerivedMap.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    {d : Cocone (DerivedFunctorValues.indDiagram F W Y)}
    {e : Cocone (DerivedFunctorValues.indDiagram F W Z)} {u : c.pt ⟶ d.pt} {v : d.pt ⟶ e.pt}
    (hu : IsDerivedMap f u) (hv : IsDerivedMap g v) : IsDerivedMap (f ≫ g) (u ≫ v) := by
  intro s r h hsq
  obtain ⟨t, f', hsq'⟩ := exists_leftSquare_under W f s
  obtain ⟨r', g', hsq''⟩ := exists_leftSquare_under W g t
  rw [map_comp_ι_app_eq F W (f ≫ g) s r r' h (f' ≫ g') hsq
      (by rw [Category.assoc, hsq'', ← Category.assoc, hsq', Category.assoc]),
    comp_assoc_of_comp_eq (hu s t f' hsq') (hv t r' g' hsq'')]
  exact (F.map_comp_assoc f' g' _).symm

omit [W.HasLeftCalculusOfFractions] in
/-- The characterisation of Stacks 05SA for a morphism that is the identity. -/
private lemma isDerivedMap_of_eq_id {X : C} {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    {f : X ⟶ X}
    (hf : f = 𝟙 X) : IsDerivedMap f (𝟙 c.pt) := by
  subst hf; exact DerivedFunctorBiprod.isDerivedMap_id W F c

/-- The characterisation of Stacks 05SA for a morphism that is a composite. -/
private lemma IsDerivedMap.comp_of_eq {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    {d : Cocone (DerivedFunctorValues.indDiagram F W Y)}
    {e : Cocone (DerivedFunctorValues.indDiagram F W Z)} {u : c.pt ⟶ d.pt} {v : d.pt ⟶ e.pt}
    (hu : IsDerivedMap f u) (hv : IsDerivedMap g v) (hh : h = f ≫ g) :
    IsDerivedMap h (u ≫ v) := by
  subst hh; exact hu.comp hv

end DerivedMap

/-! ### Saturated multiplicative systems contain the isomorphisms -/

section Saturation

variable {C : Type u₁} [Category.{v₁} C]


end Saturation

/-! ### The subcategory of objects at which `RF` is defined -/

section Defined

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
  (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]
  (E : ObjectProperty C)

/-- **Stacks 05SE(3)**, which is the first half of Stacks 05SB: an element of `W` with either
source or target in `ℰ` has both in `ℰ`, hence is a morphism of `ℰ`. -/
private lemma prop_iff_of_mem (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) {X Y : C} {s : X ⟶ Y} (hs : W s) :
    E X ↔ E Y := by
  let := hW.hasLeftCalculusOfFractions
  rw [hE X, hE Y]
  exact (F.exists_isRightDerivedValueAt_iff_and_isIso_of_mem W hs).1

/-- `ℰ` is strictly full: a saturated multiplicative system contains every isomorphism, so this
is `prop_iff_of_mem`, i.e. Stacks 05SB, applied to an isomorphism. -/
private lemma isClosedUnderIsomorphisms (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) : E.IsClosedUnderIsomorphisms := by
  refine ⟨fun {X Y} e hX => ?_⟩
  exact (prop_iff_of_mem F W E hW hE (mem_of_isIso hW e.hom)).1 hX

/-- `RF` is defined at the zero object, with value `F(0)`. -/
private lemma prop_zero (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) : E (0 : C) := by
  let := hW.isMultiplicative
  exact (hE 0).2 (exists_value_of_isZero F W (isZero_zero C)
    (Functor.map_isZero _ (isZero_zero C)))

/-- `ℰ` contains the zero objects. -/
private lemma containsZero (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) : E.ContainsZero :=
  ⟨0, isZero_zero C, prop_zero F W E hW hE⟩

/-- **Stacks 05SU** for `n = 1`, in its definedness half: `RF` is defined at `X⟦1⟧` if and only
if it is defined at `X`. This is Stacks 05SC applied to the rotation `(X, 0, X⟦1⟧)` of the
contractible triangle at `X`, whose second object is a zero object; it replaces the source's
transport of essential constancy along the shift of the index categories. -/
private lemma prop_shift_iff (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) (X : C) :
    E (X⟦(1 : ℤ)⟧) ↔ E X := by
  obtain ⟨h₁₂₃, h₂₃₁, -⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
      W hW _ (rot_of_distTriang _ (contractible_distinguished X))).1
  have hz := (hE (0 : C)).1 (prop_zero F W E hW hE)
  exact ⟨fun h => (hE X).2 (h₂₃₁ hz ((hE _).1 h)), fun h => (hE _).2 (h₁₂₃ ((hE X).1 h) hz)⟩

/-- Two of three: `ℰ` is closed under extensions, by Stacks 05SC. -/
private lemma isTriangulatedClosed₂ (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) : E.IsTriangulatedClosed₂ := by
  let := isClosedUnderIsomorphisms F W E hW hE
  refine ObjectProperty.IsTriangulatedClosed₂.mk' fun T hT h₁ h₃ => (hE _).2 ?_
  exact (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
    W hW T hT).1.2.2.1 ((hE _).1 h₃) ((hE _).1 h₁)

/-- **Stacks 05SU**, definedness half: `RF` is defined at `X⟦n⟧` if and only if it is defined at
`X`, for every `n : ℤ`. The case `n = 1` is `prop_shift_iff`, and the induction on
`n` runs along the isomorphisms `X⟦n + 1⟧ ≅ (X⟦n⟧)⟦1⟧` of
`CategoryTheory.shiftFunctorAdd'`. -/
private lemma prop_shift_iff_int (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) (n : ℤ) (X : C) :
    E (X⟦n⟧) ↔ E X := by
  let := isClosedUnderIsomorphisms F W E hW hE
  induction n using Int.induction_on with
  | zero => exact E.prop_iff_of_iso ((shiftFunctorZero C ℤ).app X)
  | succ n ih =>
    refine Iff.trans (E.prop_iff_of_iso
      ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) rfl).app X)) (Iff.trans ?_ ih)
    exact prop_shift_iff F W E hW hE (X⟦(n : ℤ)⟧)
  | pred n ih =>
    refine Iff.trans (Iff.trans (prop_shift_iff F W E hW hE (X⟦(-(n : ℤ) - 1)⟧)).symm ?_) ih
    exact (E.prop_iff_of_iso
      ((shiftFunctorAdd' C (-(n : ℤ) - 1) 1 (-(n : ℤ)) (by omega)).app X)).symm

/-- **Stacks 05SU**, definedness half: `ℰ` is stable under every shift. -/
private lemma isStableUnderShift (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) : E.IsStableUnderShift ℤ :=
  ⟨fun n => ⟨fun X hX => (prop_shift_iff_int F W E hW hE n X).2 hX⟩⟩

/-- **Stacks 05SE(1)**: `ℰ` is a triangulated subcategory of `C`. -/
private lemma isTriangulated (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) : E.IsTriangulated := by
  let := containsZero F W E hW hE
  let := isStableUnderShift F W E hW hE
  let := isTriangulatedClosed₂ F W E hW hE
  constructor

/-- **Stacks 05SE(8)**: over a Karoubian target, `ℰ` is a saturated (thick) subcategory. This is
Stacks 05SD(2) — a direct summand of an object at which `RF` is defined is again one — together
with strict fullness, which identifies `E.isoClosure` with `E`. -/
private lemma isSaturated_of_isIdempotentComplete (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) (hH : IsIdempotentComplete H) :
    E.IsSaturated := by
  let := isClosedUnderIsomorphisms F W E hW hE
  have hself : ∀ Z : C, E.isoClosure Z → E Z := fun Z hZ => by
    rwa [E.isoClosure_eq_self] at hZ
  have key : ∀ X Y : C, E (X ⊞ Y) → E X ∧ E Y := fun X Y h => by
    obtain ⟨hX, hY⟩ := (F.exists_isDerivedValueAt_biprod_and_isIso_biprod_lift W hW X
      Y).2.2.1 hH ((hE _).1 h)
    exact ⟨(hE X).2 hX, (hE Y).2 hY⟩
  constructor
  · intro X Y _ h
    exact E.le_isoClosure _ (key X Y (hself _ h)).1
  · intro X Y _ h
    exact E.le_isoClosure _ (key X Y (hself _ h)).2

end Defined

/-! ### The right derived functor on `ℰ` -/

section Derived

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (F : C ⥤ H) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (E : ObjectProperty C)
  (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c)

/-- A value of `RF` at an object of `ℰ`, chosen once and for all (Stacks 05S9). -/
private noncomputable def valueCocone (X : E.FullSubcategory) :
    Cocone (DerivedFunctorValues.indDiagram F W X.obj) :=
  ((hE X.obj).1 X.property).choose

private lemma isRightDerivedValueAt_valueCocone (X : E.FullSubcategory) :
    F.IsRightDerivedValueAt W X.obj (valueCocone F W E hE X) :=
  ((hE X.obj).1 X.property).choose_spec

/-- The morphism of Stacks 05SA between the chosen values, i.e. `RF(f)`. -/
private noncomputable def derivedMap {X Y : E.FullSubcategory} (f : X ⟶ Y) :
    (valueCocone F W E hE X).pt ⟶ (valueCocone F W E hE Y).pt :=
  (exists_isDerivedMap f.hom (isRightDerivedValueAt_valueCocone F W E hE X)
    (valueCocone F W E hE Y)).choose

private lemma isDerivedMap_derivedMap {X Y : E.FullSubcategory} (f : X ⟶ Y) :
    IsDerivedMap f.hom (derivedMap F W E hE f) :=
  (exists_isDerivedMap f.hom (isRightDerivedValueAt_valueCocone F W E hE X)
    (valueCocone F W E hE Y)).choose_spec

private lemma derivedMap_eq {X Y : E.FullSubcategory} (f : X ⟶ Y)
    {u : (valueCocone F W E hE X).pt ⟶ (valueCocone F W E hE Y).pt}
    (hu : IsDerivedMap f.hom u) : derivedMap F W E hE f = u :=
  eq_of_isDerivedMap _ (isRightDerivedValueAt_valueCocone F W E hE X)
    (isDerivedMap_derivedMap F W E hE f) hu

/-- **Stacks 05SE(2)**, as a functor: the right derived functor `RF : ℰ ⥤ 𝒟'`, sending an object
of `ℰ` to the vertex of its chosen value and a morphism to the map of Stacks 05SA, which is
unique, so that functoriality is `DerivedFunctorBiprod.isDerivedMap_id` and
`IsDerivedMap.comp`. -/
private noncomputable def rightDerived : E.FullSubcategory ⥤ H where
  obj X := (valueCocone F W E hE X).pt
  map f := derivedMap F W E hE f
  map_id X := derivedMap_eq F W E hE (𝟙 X) (isDerivedMap_of_eq_id (by simp))
  map_comp f g := derivedMap_eq F W E hE (f ≫ g)
    ((isDerivedMap_derivedMap F W E hE f).comp_of_eq (isDerivedMap_derivedMap F W E hE g) (by simp))

@[local simp]
private lemma rightDerived_obj (X : E.FullSubcategory) :
    (rightDerived F W E hE).obj X = (valueCocone F W E hE X).pt := rfl

@[local simp]
private lemma rightDerived_map {X Y : E.FullSubcategory} (f : X ⟶ Y) :
    (rightDerived F W E hE).map f = derivedMap F W E hE f := rfl

/-- **Stacks 05SE(4)**: `RF` maps every element of `S_ℰ` to an isomorphism. This is the second
half of Stacks 05SB, together with the uniqueness of the map of Stacks 05SA. -/
private lemma isInvertedBy :
    (W.inverseImage E.ι).IsInvertedBy (rightDerived F W E hE) := by
  intro X Y s hs
  obtain ⟨φ, hφ, hiso⟩ := (F.exists_isRightDerivedValueAt_iff_and_isIso_of_mem W
    (s := s.hom) (by simpa using hs)).2 (isRightDerivedValueAt_valueCocone F W E hE X)
    (isRightDerivedValueAt_valueCocone F W E hE Y)
  rw [rightDerived_map, derivedMap_eq F W E hE s (fun a b f h => hφ a b f h.symm)]
  exact hiso

end Derived

/-! ### The multiplicative system of a subcategory closed along `W` -/

section Closed

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C) (E : ObjectProperty C)

/-- Let `W` be a saturated multiplicative system in `C` (Stacks 05Q8) and `E` a full subcategory
such that an element of `W` with source or target in `E` has both in `E`. Then
`S_E = Arrows(E) ∩ W` is a saturated multiplicative system in `E`: the object produced by the Ore
condition MS2, resp. by the cancellation MS3, in `C` is joined to an object of `E` by a morphism
of `W`, so it lies in `E`. This is the content of Stacks 05SE(5), first half, for `RF` and for
`LF` alike. -/
public lemma isSaturated_inverseImage_ι (hW : W.IsSaturated)
    (hEW : ∀ {X Y : C} (s : X ⟶ Y), W s → (E X ↔ E Y)) :
    (W.inverseImage E.ι).IsSaturated := by
  have hmul : (W.inverseImage E.ι).IsMultiplicative :=
    { id_mem := fun X => by simpa using hW.isMultiplicative.id_mem X.obj
      comp_mem := fun f g hf hg => by
        simpa using hW.isMultiplicative.comp_mem (E.ι.map f) (E.ι.map g) hf hg }
  have hleft : (W.inverseImage E.ι).HasLeftCalculusOfFractions := by
    let := hW.hasLeftCalculusOfFractions
    constructor
    · intro X Y φ
      obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk (W := W) φ.s.hom
        (by simpa using φ.hs) φ.f.hom).exists_leftFraction
      refine ⟨MorphismProperty.LeftFraction.mk (W := W.inverseImage E.ι)
        (Y' := ⟨ψ.Y', (hEW _ ψ.hs).1 Y.property⟩) ⟨ψ.f⟩ ⟨ψ.s⟩
        (by simpa using ψ.hs), ?_⟩
      apply E.ι.map_injective
      simpa using hψ
    · intro X' X Y f₁ f₂ s hs h
      obtain ⟨Y', t, ht, hft⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        (W := W) f₁.hom f₂.hom s.hom (by simpa using hs) (by simpa using E.ι.congr_map h)
      refine ⟨⟨Y', (hEW _ ht).1 Y.property⟩, ⟨t⟩, by simpa using ht, ?_⟩
      apply E.ι.map_injective
      simpa using hft
  have hright : (W.inverseImage E.ι).HasRightCalculusOfFractions := by
    let := hW.hasRightCalculusOfFractions
    constructor
    · intro X Y φ
      obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk (W := W) φ.f.hom φ.s.hom
        (by simpa using φ.hs)).exists_rightFraction
      refine ⟨MorphismProperty.RightFraction.mk (W := W.inverseImage E.ι)
        (X' := ⟨ψ.X', (hEW _ ψ.hs).2 X.property⟩) ⟨ψ.s⟩
        (by simpa using ψ.hs) ⟨ψ.f⟩, ?_⟩
      apply E.ι.map_injective
      simpa using hψ
    · intro X Y Y' f₁ f₂ s hs h
      obtain ⟨X', t, ht, hft⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
        (W := W) f₁.hom f₂.hom s.hom (by simpa using hs) (by simpa using E.ι.congr_map h)
      refine ⟨⟨X', (hEW _ ht).2 X.property⟩, ⟨t⟩, by simpa using ht, ?_⟩
      apply E.ι.map_injective
      simpa using hft
  exact
    { hasLeftCalculusOfFractions := hleft
      hasRightCalculusOfFractions := hright
      mem_of_comp_mem_comp := fun f g h hfg hgh =>
        hW.mem_of_comp_mem_comp (E.ι.map f) (E.ι.map g) (E.ι.map h)
          (by simpa using hfg) (by simpa using hgh) }

end Closed

/-! ### The multiplicative system of `ℰ` -/

section System

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
  (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]
  (E : ObjectProperty C)

/-- `S_ℰ = Arrows(ℰ) ∩ S` is multiplicative, because `W` is. -/
private lemma inverseImage_isMultiplicative (hW : W.IsSaturated) :
    (W.inverseImage E.ι).IsMultiplicative where
  id_mem X := by simpa using hW.isMultiplicative.id_mem X.obj
  comp_mem f g hf hg := by
    simpa using hW.isMultiplicative.comp_mem (E.ι.map f) (E.ι.map g) hf hg

/-- **Stacks 05SE(5)**, first half: `S_ℰ` has a calculus of left fractions. The object produced
by the Ore condition MS2, resp. by the cancellation MS3, in `𝒟` receives a morphism of `S` from
an object of `ℰ`, so it lies in `ℰ` by part (3), i.e. by `prop_iff_of_mem`. -/
private lemma inverseImage_hasLeftCalculusOfFractions (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) :
    (W.inverseImage E.ι).HasLeftCalculusOfFractions :=
  (isSaturated_inverseImage_ι W E hW fun _ hs =>
    prop_iff_of_mem F W E hW hE hs).hasLeftCalculusOfFractions

/-- **Stacks 05SE(5)**, first half: `S_ℰ` has a calculus of right fractions. Dually to
`inverseImage_hasLeftCalculusOfFractions`, the object produced maps into an object
of `ℰ` by a morphism of `S`, so part (3) puts it in `ℰ`. -/
private lemma inverseImage_hasRightCalculusOfFractions (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) :
    (W.inverseImage E.ι).HasRightCalculusOfFractions :=
  (isSaturated_inverseImage_ι W E hW fun _ hs =>
    prop_iff_of_mem F W E hW hE hs).hasRightCalculusOfFractions

/-- **Stacks 05SE(5)**: `S_ℰ` is a saturated multiplicative system in `ℰ`. Saturation (MS4) is
`W`'s, the two calculi of fractions are
`inverseImage_hasLeftCalculusOfFractions` and
`inverseImage_hasRightCalculusOfFractions`. -/
private lemma inverseImage_isSaturated (hW : W.IsSaturated)
    (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c) :
    (W.inverseImage E.ι).IsSaturated :=
  isSaturated_inverseImage_ι W E hW fun _ hs => prop_iff_of_mem F W E hW hE hs

end System

/-! ### The multiplicative system of `ℰ` is compatible with the triangulation -/

section Compatible

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]
  (E : ObjectProperty C) [E.IsTriangulated]

/-- `S_ℰ` is compatible with the shift, because `W` is and `E.ι` commutes with the shift. -/
private lemma inverseImage_isCompatibleWithShift (hW : W.IsSaturated) :
    (W.inverseImage E.ι).IsCompatibleWithShift ℤ where
  condition a := by
    let := hW.isMultiplicative
    let : W.RespectsIso :=
      MorphismProperty.respectsIso_of_isStableUnderComposition (isomorphisms_le_of_isSaturated hW)
    ext X Y f
    have h : W ((shiftFunctor E.FullSubcategory a ⋙ E.ι).map f) ↔
        W ((E.ι ⋙ shiftFunctor C a).map f) :=
      W.arrow_mk_iso_iff (Arrow.isoOfNatIso (E.ι.commShiftIso a) (Arrow.mk f))
    change W (E.ι.map ((shiftFunctor E.FullSubcategory a).map f)) ↔ W (E.ι.map f)
    exact h.trans (MorphismProperty.IsCompatibleWithShift.iff W (E.ι.map f) a)

/-- Let `W` be a saturated multiplicative system in `C` compatible with the triangulation and
`E` a triangulated subcategory. Then `S_E = Arrows(E) ∩ W` is compatible with the triangulated
structure of `E`: the third morphism produced by `W`'s compatibility in `C` is a morphism of `E`
because `E.ι` is full, and lies in `S_E` because it lies in `W`. This is Stacks 05SE(5), second
half, for `RF` and for `LF` alike. -/
public lemma isCompatibleWithTriangulation_inverseImage_ι (hW : W.IsSaturated) :
    (W.inverseImage E.ι).IsCompatibleWithTriangulation := by
  let := inverseImage_isCompatibleWithShift W E hW
  constructor
  intro T₁ T₂ hT₁ hT₂ a b ha hb comm
  obtain ⟨c, hc, hc₂, hc₃⟩ := MorphismProperty.compatible_with_triangulation
    (W := W) (E.ι.mapTriangle.obj T₁) (E.ι.mapTriangle.obj T₂) hT₁ hT₂ (E.ι.map a) (E.ι.map b)
    ha hb (show E.ι.map T₁.mor₁ ≫ E.ι.map b = E.ι.map a ≫ E.ι.map T₂.mor₁ by
      simpa using E.ι.congr_map comm)
  refine ⟨E.homMk c, hc, E.ι.map_injective (by rwa [E.ι.map_comp, E.ι.map_comp]), ?_⟩
  apply E.ι.map_injective
  rw [E.ι.map_comp, E.ι.map_comp, ← cancel_mono ((E.ι.commShiftIso (1 : ℤ)).hom.app T₂.obj₁),
    Category.assoc, Category.assoc, E.ι.commShiftIso_hom_naturality, ← Category.assoc]
  exact hc₃

/-- **Stacks 05SE(5)**, second half: `S_ℰ` is compatible with the triangulated structure of `ℰ`.
A triangle of `ℰ` is distinguished when its image under `E.ι` is, so the third morphism is the
one `W`'s own compatibility produces in `𝒟`; it is a morphism of `ℰ` because `E.ι` is full, and
it lies in `S_ℰ` because it lies in `W`. Compatibility with the shift is
`inverseImage_isCompatibleWithShift`. -/
private lemma inverseImage_isCompatibleWithTriangulation (hW : W.IsSaturated) :
    (W.inverseImage E.ι).IsCompatibleWithTriangulation :=
  isCompatibleWithTriangulation_inverseImage_ι W E hW

end Compatible

/-! ### The localization of `ℰ` sits fully faithfully in the localization of `𝒟` -/

section FullyFaithful

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C)
  [W.HasLeftCalculusOfFractions] (E : ObjectProperty C)

/-- Let `W` have a left calculus of fractions and let `E` be a full subcategory such that an
element of `W` with source or target in `E` has both in `E`, and such that `S_E = Arrows(E) ∩ W`
has a left calculus of fractions. Then any lift `S_E⁻¹E ⥤ W⁻¹C` of `E.ι` through localization
functors is fully faithful: every left fraction of `C` between objects of `E` is one of `E`, and
two morphisms of `E` identified in `W⁻¹C` are already identified in `S_E⁻¹E`. This is the fully
faithfulness of Stacks 05SE(6), for `RF` and for `LF` alike. -/
public lemma full_and_faithful_of_lifting_inverseImage_ι
    (hSE : (W.inverseImage E.ι).HasLeftCalculusOfFractions)
    (hEW : ∀ {X Y : C} (s : X ⟶ Y), W s → (E X ↔ E Y))
    {D : Type u₃} [Category.{v₃} D] (L : C ⥤ D) [L.IsLocalization W]
    (EL : Type u₄) [Category.{v₄} EL] (LE : E.FullSubcategory ⥤ EL)
    [LE.IsLocalization (W.inverseImage E.ι)] (Φ : EL ⥤ D)
    [Localization.Lifting LE (W.inverseImage E.ι) (E.ι ⋙ L) Φ] :
    Φ.Full ∧ Φ.Faithful := by
  let := hSE
  let := Localization.essSurj LE (W.inverseImage E.ι)
  let e : LE ⋙ Φ ≅ E.ι ⋙ L := Localization.Lifting.iso LE (W.inverseImage E.ι) (E.ι ⋙ L) Φ
  have hmap : ∀ {A B : E.FullSubcategory} (u : A ⟶ B),
      Φ.map (LE.map u) = e.hom.app A ≫ L.map (E.ι.map u) ≫ e.inv.app B :=
    fun u => (NatIso.naturality_2 e u).symm
  refine ⟨Φ.full_of_comp_essSurj LE fun {X₁ X₂} φ => ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction L W
      (e.inv.app X₁ ≫ φ ≫ e.hom.app X₂)
    let g : (W.inverseImage E.ι).LeftFraction X₁ X₂ :=
      { Y' := ⟨ψ.Y', (hEW ψ.s ψ.hs).1 X₂.property⟩
        f := E.homMk ψ.f
        s := E.homMk ψ.s
        hs := ψ.hs }
    let := Localization.inverts LE (W.inverseImage E.ι) _ g.hs
    refine ⟨g.map LE (Localization.inverts LE (W.inverseImage E.ι)), ?_⟩
    rw [← cancel_mono (Φ.map (LE.map g.s)), ← Functor.map_comp,
      MorphismProperty.LeftFraction.map_comp_map_s, hmap, hmap]
    change e.hom.app X₁ ≫ L.map ψ.f ≫ _ = _
    rw [← MorphismProperty.LeftFraction.map_comp_map_s ψ L (Localization.inverts L W), ← hψ]
    change _ = φ ≫ e.hom.app X₂ ≫ L.map ψ.s ≫ _
    simp
  · refine Functor.faithful_of_comp_of_hasLeftCalculusOfFractions (L := LE)
      (W := W.inverseImage E.ι) (F := Φ) fun {X₁ X₂} f g hfg => ?_
    have hfg' : L.map (E.ι.map f) = L.map (E.ι.map g) := by
      have h₁ := NatIso.naturality_1 e f
      have h₂ := NatIso.naturality_1 e g
      simp only [Functor.comp_map] at h₁ h₂
      rw [← h₁, ← h₂, hfg]
    rw [MorphismProperty.map_eq_iff_postcomp L W] at hfg'
    obtain ⟨Z, s, hs, fac⟩ := hfg'
    refine (MorphismProperty.map_eq_iff_postcomp LE (W.inverseImage E.ι) f g).2
      ⟨⟨Z, (hEW s hs).1 X₂.property⟩, E.homMk s, hs, E.ι.map_injective ?_⟩
    simpa using fac

/-- **Stacks 05SE(6)**, fully faithfulness: `S_ℰ^{-1}ℰ ⟶ S^{-1}𝒟` is fully faithful. Both
categories have their morphisms computed by left fractions, and part (3) — the hypothesis `hEW`,
that a morphism of `W` with source in `ℰ` has its target in `ℰ` — says that every left fraction
of `𝒟` between objects of `ℰ` is a left fraction of `ℰ`, and that two morphisms of `ℰ`
identified in `S^{-1}𝒟` are already identified in `S_ℰ^{-1}ℰ`. -/
private lemma full_and_faithful_of_lifting
    (hSE : (W.inverseImage E.ι).HasLeftCalculusOfFractions)
    (hEW : ∀ {X Y : C} (s : X ⟶ Y), W s → (E X ↔ E Y))
    {D : Type u₃} [Category.{v₃} D] (L : C ⥤ D) [L.IsLocalization W]
    (EL : Type u₄) [Category.{v₄} EL] (LE : E.FullSubcategory ⥤ EL)
    [LE.IsLocalization (W.inverseImage E.ι)] (Φ : EL ⥤ D)
    [Localization.Lifting LE (W.inverseImage E.ι) (E.ι ⋙ L) Φ] :
    Φ.Full ∧ Φ.Faithful :=
  full_and_faithful_of_lifting_inverseImage_ι W E hSE hEW L EL LE Φ

end FullyFaithful

/-! ### The shift on the index categories -/

-- An index of `X/W` and its shift are the same object under two spellings, and the shift sections
-- cross between them constantly. These are the one-line alias and structure literal the
-- crossings go through; Mathlib marks `Under.forget`, the analogous `CategoryTheory.Under.mk`
-- and `Under` itself `@[implicit_reducible]` but has not marked these two, so we do it here.
attribute [local implicit_reducible] MorphismProperty.Under.mk
  MorphismProperty.Comma.forget

section ShiftIndex

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] (W : MorphismProperty C)
  [W.IsMultiplicative] [W.IsCompatibleWithShift ℤ]


@[local simp]
private lemma shiftUnder_obj_right (n : ℤ) (X : C) (s : W.Under ⊤ X) :
    ((underShift W X n).obj s).right = s.right⟦n⟧ := rfl

@[local simp]
private lemma shiftUnder_obj_hom (n : ℤ) (X : C) (s : W.Under ⊤ X) :
    ((underShift W X n).obj s).hom = s.hom⟦n⟧' := rfl

@[local simp]
private lemma shiftUnder_map_right (n : ℤ) (X : C) {s t : W.Under ⊤ X} (u : s ⟶ t) :
    ((underShift W X n).map u).right = u.right⟦n⟧' := rfl

/-- The shift on index categories is faithful, because the shift of `C` is. -/
private lemma faithful_shiftUnder (n : ℤ) (X : C) : (underShift W X n).Faithful where
  map_injective {s t} u v h := by
    ext
    apply (shiftFunctor C n).map_injective
    have h2 : ((underShift W X n).map u).right = ((underShift W X n).map v).right := by rw [h]
    simpa using h2



/-- **The index categories of `X` and of `X⟦n⟧` are equivalent**, by the shift by `n`. This is
the input of the source's Stacks 05SU: the ind-object at `X⟦n⟧` restricted along the shift of
index categories is the ind-object at `X` followed by the shift of the target, up to
`F.commShiftIso n`, and the equivalence is what carries a cocone on the restriction back to a
cocone on the ind-object at `X⟦n⟧`. -/
private lemma isEquivalence_shiftUnder (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ)
    (X : C) : (underShift W X n).IsEquivalence :=
  have := faithful_shiftUnder W n X
  have := underShift_full W X n
  have := MorphismProperty.respectsIso_of_isStableUnderComposition hiso
  have := underShift_essSurj W X n
  { }

/-- Every index of `X⟦n⟧/W` maps to the shift of an index of `X/W`, compatibly with the
structure morphisms. -/
private lemma exists_hom_underShift (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ) {X : C}
    (t : W.Under ⊤ (X⟦n⟧)) :
    ∃ (σ : W.Under ⊤ X) (g : t ⟶ (underShift W X n).obj σ), t.hom ≫ g.right = σ.hom⟦n⟧' := by
  have := MorphismProperty.respectsIso_of_isStableUnderComposition hiso
  have := underShift_essSurj W X n
  exact ⟨_, ((underShift W X n).objObjPreimageIso t).inv, MorphismProperty.Under.w _⟩

end ShiftIndex

/-! ### The value of `RF` at a shifted object -/

section ShiftValue

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] {H : Type u₂} [Category.{v₂} H]
  [HasShift H ℤ] (F : C ⥤ H) [F.CommShift ℤ] (W : MorphismProperty C) [W.IsMultiplicative]
  [W.IsCompatibleWithShift ℤ]

/-- A transition morphism of the ind-object is `F` of its component in `C`. -/
private lemma indDiagram_map {X : C} {s t : W.Under ⊤ X} (u : s ⟶ t) :
    (DerivedFunctorValues.indDiagram F W X).map u = F.map u.right := rfl


/-- The cocone on the ind-object at `X⟦n⟧` restricted along `underShift W X n`, with vertex
`c.pt⟦n⟧`, obtained from a cocone `c` on the ind-object at `X` by shifting and transporting along
`indDiagramShiftIso`. -/
@[implicit_reducible]
private def preShiftCocone (n : ℤ) {X : C} (c : Cocone (DerivedFunctorValues.indDiagram F W X)) :
    Cocone (underShift W X n ⋙ DerivedFunctorValues.indDiagram F W (X⟦n⟧)) where
  pt := c.pt⟦n⟧
  ι :=
    { app := fun s => (F.commShiftIso n).hom.app s.right ≫ (c.ι.app s)⟦n⟧'
      naturality := fun s t u => by
        have hw : (F.map u.right)⟦n⟧' ≫ (c.ι.app t)⟦n⟧' = (c.ι.app s)⟦n⟧' :=
          ((shiftFunctor H n).map_comp (F.map u.right) (c.ι.app t)).symm.trans
            (congrArg (shiftFunctor H n).map (c.w u))
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        rw [Functor.comp_map, indDiagram_map, shiftUnder_map_right, ← Category.assoc,
          F.commShiftIso_hom_naturality u.right n, Category.assoc, hw] }

/-- The value of `RF` at `X⟦n⟧` attached to a cocone `c` on the ind-object at `X`: the cocone with
vertex `c.pt⟦n⟧` extended from `preShiftCocone` along the equivalence
`shiftUnderEquiv` of index categories. -/
@[implicit_reducible]
private noncomputable def shiftCocone (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ) {X : C}
    (c : Cocone (DerivedFunctorValues.indDiagram F W X)) :
    Cocone (DerivedFunctorValues.indDiagram F W (X⟦n⟧)) where
  pt := c.pt⟦n⟧
  ι :=
    haveI := isEquivalence_shiftUnder W hiso n X
    (Functor.Final.extendCocone.obj (preShiftCocone F W n c)).ι

/-- The coprojections of `shiftCocone`: at an index `t` of `X⟦n⟧/W` admitting *any*
morphism `g` to the shift of an index `s` of `X/W`, the coprojection is `F(g)` followed by
`F.commShiftIso n` and the shift of the coprojection of `c` at `s`. -/
private lemma shiftCocone_ι_app (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ) {X : C}
    (c : Cocone (DerivedFunctorValues.indDiagram F W X)) (t : W.Under ⊤ (X⟦n⟧)) (s : W.Under ⊤ X)
    (g : t ⟶ (underShift W X n).obj s) :
    (shiftCocone F W hiso n c).ι.app t
      = F.map g.right ≫ (F.commShiftIso n).hom.app s.right ≫ (c.ι.app s)⟦n⟧' := by
  have := isEquivalence_shiftUnder W hiso n X
  exact Functor.Final.extendCocone_obj_ι_app' (preShiftCocone F W n c) g

/-- The coprojection of `shiftCocone` at the shift of an index of `X/W`. -/
private lemma shiftCocone_ι_app_shift (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ) {X : C}
    (c : Cocone (DerivedFunctorValues.indDiagram F W X)) (s : W.Under ⊤ X) :
    (shiftCocone F W hiso n c).ι.app ((underShift W X n).obj s)
      = (F.commShiftIso n).hom.app s.right ≫ (c.ι.app s)⟦n⟧' := by
  rw [shiftCocone_ι_app F W hiso n c _ s (𝟙 _)]
  simp

/-- **Stacks 05SU**, value half. If `c` is a value of `RF` at `X` (Stacks 05S9), then `c.pt⟦n⟧`
is a value of `RF` at `X⟦n⟧`, at the cocone `shiftCocone`: the index `s₀` of `c`
shifts to an index of `X⟦n⟧/W`, the section `r` shifts to one there through `F.commShiftIso n`,
and the factorisation of a transition morphism at an index `t` of `X⟦n⟧/W` is the factorisation at
the index of `X/W` that `t` is the shift of, up to the isomorphism of essential surjectivity. -/
private lemma isRightDerivedValueAt_shiftCocone (hiso : MorphismProperty.isomorphisms C ≤ W)
    (n : ℤ) {X : C} {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    (hc : F.IsRightDerivedValueAt W X c) :
    F.IsRightDerivedValueAt W (X⟦n⟧) (shiftCocone F W hiso n c) := by
  have := isEquivalence_shiftUnder W hiso n X
  obtain ⟨s₀, r, hr, hcof⟩ := hc
  refine ⟨(underShift W X n).obj s₀, r⟦n⟧' ≫ (F.commShiftIso n).inv.app s₀.right, ?_, fun t => ?_⟩
  · have h₂ : r⟦n⟧' ≫ (c.ι.app s₀)⟦n⟧' = 𝟙 (c.pt⟦n⟧) :=
      ((shiftFunctor H n).map_comp r (c.ι.app s₀)).symm.trans
        (by rw [hr]; exact (shiftFunctor H n).map_id c.pt)
    rw [shiftCocone_ι_app_shift F W hiso n c s₀, Category.assoc,
      ← Category.assoc ((F.commShiftIso n).inv.app s₀.right), Iso.inv_hom_id_app,
      Category.id_comp]
    exact h₂
  · obtain ⟨σ, e, -⟩ := exists_hom_underShift W hiso n t
    obtain ⟨t₀, u₀, v₀, hu₀⟩ := hcof σ
    refine ⟨(underShift W X n).obj t₀, e ≫ (underShift W X n).map u₀,
      (underShift W X n).map v₀, ?_⟩
    have hnat : (F.commShiftIso n).inv.app s₀.right ≫ F.map (v₀.right⟦n⟧')
        = (F.map v₀.right)⟦n⟧' ≫ (F.commShiftIso n).inv.app t₀.right :=
      (F.commShiftIso_inv_naturality v₀.right n).symm
    have hnat' : F.map (u₀.right⟦n⟧') ≫ (F.commShiftIso n).hom.app t₀.right
        = (F.commShiftIso n).hom.app σ.right ≫ (F.map u₀.right)⟦n⟧' :=
      F.commShiftIso_hom_naturality u₀.right n
    have hshift₀ : (c.ι.app σ)⟦n⟧' ≫ r⟦n⟧' ≫ (F.map v₀.right)⟦n⟧'
        = (F.map u₀.right)⟦n⟧' :=
      (congrArg (fun x => (c.ι.app σ)⟦n⟧' ≫ x)
          ((shiftFunctor H n).map_comp r (F.map v₀.right)).symm).trans
        (((shiftFunctor H n).map_comp (c.ι.app σ) (r ≫ F.map v₀.right)).symm.trans
          (congrArg (shiftFunctor H n).map hu₀).symm)
    have hshift : ∀ {V : H} (w : (F.obj t₀.right)⟦n⟧ ⟶ V),
        (c.ι.app σ)⟦n⟧' ≫ r⟦n⟧' ≫ (F.map v₀.right)⟦n⟧' ≫ w
          = (F.map u₀.right)⟦n⟧' ≫ w := by
      intro V w
      rw [← hshift₀]
      simp only [Category.assoc]
    have hL : F.map ((e ≫ (underShift W X n).map u₀).right)
        = F.map e.right ≫ F.map (u₀.right⟦n⟧') := F.map_comp _ _
    have hL2 : F.map (u₀.right⟦n⟧')
        = (F.commShiftIso n).hom.app σ.right ≫ (F.map u₀.right)⟦n⟧'
            ≫ (F.commShiftIso n).inv.app t₀.right := by
      rw [← Category.assoc, ← hnat', Category.assoc, Iso.hom_inv_id_app]
      simp
    rw [shiftCocone_ι_app F W hiso n c t σ e, hL, hL2, shiftUnder_map_right]
    simp only [Category.assoc, hnat]
    rw [hshift]

end ShiftValue

/-! ### Derived maps and the shift -/

section ShiftDerivedMap

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] {H : Type u₂} [Category.{v₂} H]
  [HasShift H ℤ] (F : C ⥤ H) [F.CommShift ℤ] (W : MorphismProperty C)
  [W.IsCompatibleWithShift ℤ] [W.HasLeftCalculusOfFractions]

/-- `F` of the inverse and then of the forward component of an isomorphism of endofunctors cancels
in front of any tail. -/
private lemma map_inv_app_map_hom_app_comp {G G' : C ⥤ C} (e : G ≅ G') (X : C) {V : H}
    (w : F.obj (G'.obj X) ⟶ V) : F.map (e.inv.app X) ≫ F.map (e.hom.app X) ≫ w = w := by
  rw [← Category.assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id, Category.id_comp]

/-- One square per index suffices in the characterisation of Stacks 05SA: for a fixed index of
`X/W` the composite `F(X') ⟶ F(Y') ⟶ d.pt` does not depend on the chosen square, by
`map_comp_ι_app_eq`. -/
private lemma isDerivedMap_of_forall_exists {X Y : C} (g : X ⟶ Y)
    {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    {d : Cocone (DerivedFunctorValues.indDiagram F W Y)} {u : c.pt ⟶ d.pt}
    (h : ∀ s : W.Under ⊤ X, ∃ (t : W.Under ⊤ Y) (f' : s.right ⟶ t.right),
      g ≫ t.hom = s.hom ≫ f' ∧ c.ι.app s ≫ u = F.map f' ≫ d.ι.app t) :
    IsDerivedMap g u := by
  intro s t₂ f₂ hsq₂
  obtain ⟨t, f', hsq, he⟩ := h s
  rw [he, map_comp_ι_app_eq F W g s t t₂ f' f₂ hsq hsq₂]

/-- The shift of the map of Stacks 05SA attached to `g` is the map of Stacks 05SA attached to
`g⟦n⟧'`, between the cocones of `shiftCocone`. -/
private lemma isDerivedMap_shift (hiso : MorphismProperty.isomorphisms C ≤ W) (n : ℤ)
    {X Y : C} {g : X ⟶ Y} {c : Cocone (DerivedFunctorValues.indDiagram F W X)}
    {d : Cocone (DerivedFunctorValues.indDiagram F W Y)}
    {u : c.pt ⟶ d.pt} (hu : IsDerivedMap g u) :
    IsDerivedMap (c := shiftCocone F W hiso n c) (d := shiftCocone F W hiso n d)
      (g⟦n⟧') (u⟦n⟧') := by
  refine isDerivedMap_of_forall_exists F W _ fun s => ?_
  obtain ⟨σ, e, h1⟩ := exists_hom_underShift W hiso n s
  obtain ⟨τ, k, hk⟩ := exists_leftSquare_under W g σ
  refine ⟨(underShift W Y n).obj τ, e.right ≫ k⟦n⟧', ?_, ?_⟩
  · rw [shiftUnder_obj_hom, ← Category.assoc s.hom e.right (k⟦n⟧'), h1, ← Functor.map_comp,
      ← Functor.map_comp, hk]
  · have hshift : (c.ι.app σ)⟦n⟧' ≫ u⟦n⟧' = (F.map k)⟦n⟧' ≫ (d.ι.app τ)⟦n⟧' :=
      ((shiftFunctor H n).map_comp (c.ι.app σ) u).symm.trans
        ((congrArg (shiftFunctor H n).map (hu σ τ k hk)).trans
          ((shiftFunctor H n).map_comp (F.map k) (d.ι.app τ)))
    have key : (F.commShiftIso n).hom.app σ.right ≫ (F.map k)⟦n⟧' ≫ (d.ι.app τ)⟦n⟧'
        = F.map (k⟦n⟧') ≫ (F.commShiftIso n).hom.app τ.right ≫ (d.ι.app τ)⟦n⟧' := by
      rw [← Category.assoc, ← F.commShiftIso_hom_naturality k n, Category.assoc]
    rw [shiftCocone_ι_app F W hiso n c s σ e, shiftCocone_ι_app_shift F W hiso n d τ,
      F.map_comp]
    simp only [Category.assoc]
    rw [hshift, key]

/-- A morphism into the vertex of `shiftCocone` is the map of Stacks 05SA as soon as
it is compatible with the coprojections at the *shifted* indices — the form in which the third
clause of Stacks 05SC produces it. -/
private lemma isDerivedMap_shiftCocone_of_forall (hiso : MorphismProperty.isomorphisms C ≤ W)
    (n : ℤ) {Y X : C} (g : Y ⟶ X⟦n⟧) {c : Cocone (DerivedFunctorValues.indDiagram F W Y)}
    {d : Cocone (DerivedFunctorValues.indDiagram F W X)} {u : c.pt ⟶ d.pt⟦n⟧}
    (h : ∀ (r : W.Under ⊤ Y) (s : W.Under ⊤ X) (h' : r.right ⟶ s.right⟦n⟧),
      g ≫ s.hom⟦n⟧' = r.hom ≫ h' →
        c.ι.app r ≫ u = F.map h' ≫ (F.commShiftIso n).hom.app s.right ≫ (d.ι.app s)⟦n⟧') :
    IsDerivedMap (c := c) (d := shiftCocone F W hiso n d) g u := by
  refine isDerivedMap_of_forall_exists F W _ fun r => ?_
  obtain ⟨t, f', hsq⟩ := exists_leftSquare_under W g r
  obtain ⟨σ, e, hw⟩ := exists_hom_underShift W hiso n t
  have hsq' : g ≫ σ.hom⟦n⟧' = r.hom ≫ f' ≫ e.right := by
    rw [← hw, ← Category.assoc g t.hom e.right, hsq, Category.assoc r.hom f' e.right]
  refine ⟨(underShift W X n).obj σ, f' ≫ e.right, hsq', ?_⟩
  rw [shiftCocone_ι_app_shift F W hiso n d σ]
  exact h r σ (f' ≫ e.right) hsq'

/-- The unitor of the shift is the map of Stacks 05SA between a value and its zeroth shift. -/
private lemma isDerivedMap_shiftFunctorZero_inv (hiso : MorphismProperty.isomorphisms C ≤ W)
    {X : C} (c : Cocone (DerivedFunctorValues.indDiagram F W X)) :
    IsDerivedMap (c := c) (d := shiftCocone F W hiso 0 c)
      ((shiftFunctorZero C ℤ).inv.app X) ((shiftFunctorZero H ℤ).inv.app c.pt) := by
  refine isDerivedMap_of_forall_exists F W _ fun s => ?_
  refine ⟨(underShift W X 0).obj s, (shiftFunctorZero C ℤ).inv.app s.right, ?_, ?_⟩
  · exact ((shiftFunctorZero C ℤ).inv.naturality s.hom).symm
  · have h2 : (shiftFunctorZero H ℤ).inv.app (F.obj s.right) ≫ (c.ι.app s)⟦(0 : ℤ)⟧'
        = c.ι.app s ≫ (shiftFunctorZero H ℤ).inv.app c.pt :=
      ((shiftFunctorZero H ℤ).inv.naturality (c.ι.app s)).symm
    rw [shiftCocone_ι_app_shift F W hiso 0 c s, F.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app]
    simp only [Category.assoc]
    rw [map_inv_app_map_hom_app_comp]
    exact h2.symm

/-- The associator of the shift is the map of Stacks 05SA between the twice-shifted and the
once-shifted cocones of `shiftCocone`. -/
private lemma isDerivedMap_shiftFunctorAdd_inv (hiso : MorphismProperty.isomorphisms C ≤ W)
    (a b : ℤ) {X : C} (c : Cocone (DerivedFunctorValues.indDiagram F W X)) :
    IsDerivedMap (c := shiftCocone F W hiso b (shiftCocone F W hiso a c))
      (d := shiftCocone F W hiso (a + b) c)
      ((shiftFunctorAdd C a b).inv.app X) ((shiftFunctorAdd H a b).inv.app c.pt) := by
  refine isDerivedMap_of_forall_exists F W _ fun s => ?_
  obtain ⟨σ, ε, h1⟩ := exists_hom_underShift W hiso b s
  obtain ⟨ρ, δ, h2⟩ := exists_hom_underShift W hiso a σ
  refine ⟨(underShift W X (a + b)).obj ρ,
    ε.right ≫ δ.right⟦b⟧' ≫ (shiftFunctorAdd C a b).inv.app ρ.right, ?_, ?_⟩
  · have h3 : σ.hom⟦b⟧' ≫ δ.right⟦b⟧' = (ρ.hom⟦a⟧')⟦b⟧' :=
      ((shiftFunctor C b).map_comp σ.hom δ.right).symm.trans
        (congrArg (shiftFunctor C b).map h2)
    have h4 : (shiftFunctorAdd C a b).inv.app X ≫ ρ.hom⟦a + b⟧'
        = ((ρ.hom⟦a⟧')⟦b⟧') ≫ (shiftFunctorAdd C a b).inv.app ρ.right :=
      ((shiftFunctorAdd C a b).inv.naturality ρ.hom).symm
    rw [shiftUnder_obj_hom, h4, ← h3, ← h1, Category.assoc, Category.assoc]
  · have e2 : ∀ {V : H} (w : (F.obj (ρ.right⟦a⟧))⟦b⟧ ⟶ V),
        F.map (δ.right⟦b⟧') ≫ (F.commShiftIso b).hom.app (ρ.right⟦a⟧) ≫ w
          = (F.commShiftIso b).hom.app σ.right ≫ (F.map δ.right)⟦b⟧' ≫ w :=
      fun w => F.commShiftIso_hom_naturality_assoc δ.right b w
    have e3 : (shiftFunctorAdd H a b).inv.app (F.obj ρ.right) ≫ (c.ι.app ρ)⟦a + b⟧'
        = ((c.ι.app ρ)⟦a⟧')⟦b⟧' ≫ (shiftFunctorAdd H a b).inv.app c.pt :=
      ((shiftFunctorAdd H a b).inv.naturality (c.ι.app ρ)).symm
    rw [shiftCocone_ι_app F W hiso b (shiftCocone F W hiso a c) s σ ε,
      shiftCocone_ι_app F W hiso a c σ ρ δ,
      shiftCocone_ι_app_shift F W hiso (a + b) c ρ, F.commShiftIso_add a b,
      Functor.CommShift.isoAdd_hom_app]
    simp only [F.map_comp, Functor.map_comp, Category.assoc]
    rw [map_inv_app_map_hom_app_comp, e2, e3]

end ShiftDerivedMap

/-! ### The right derived functor commutes with the shift -/

section Exact

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
  (W : MorphismProperty C) [W.IsCompatibleWithTriangulation] [W.HasLeftCalculusOfFractions]
  (E : ObjectProperty C) [E.IsClosedUnderIsomorphisms] [E.IsTriangulated]
  (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c)

/-- The comparison morphism `RF(X⟦n⟧) ⟶ RF(X)⟦n⟧`: the map of Stacks 05SA along the isomorphism
`ι(X⟦n⟧) ≅ ι(X)⟦n⟧`, from the chosen value at `X⟦n⟧` to the value at `ι(X)⟦n⟧` provided by
Stacks 05SU (`isRightDerivedValueAt_shiftCocone`). -/
private noncomputable def shiftComparison (hW : W.IsSaturated) (n : ℤ) (X : E.FullSubcategory) :
    (rightDerived F W E hE).obj (X⟦n⟧) ⟶ ((rightDerived F W E hE).obj X)⟦n⟧ :=
  (exists_isDerivedMap ((E.ι.commShiftIso n).hom.app X)
    (isRightDerivedValueAt_valueCocone F W E hE (X⟦n⟧))
    (shiftCocone F W (isomorphisms_le_of_isSaturated hW) n (valueCocone F W E hE X))).choose

private lemma isDerivedMap_shiftComparison (hW : W.IsSaturated) (n : ℤ) (X : E.FullSubcategory) :
    IsDerivedMap (c := valueCocone F W E hE (X⟦n⟧))
      (d := shiftCocone F W (isomorphisms_le_of_isSaturated hW) n (valueCocone F W E hE X))
      ((E.ι.commShiftIso n).hom.app X) (shiftComparison F W E hE hW n X) :=
  (exists_isDerivedMap ((E.ι.commShiftIso n).hom.app X)
    (isRightDerivedValueAt_valueCocone F W E hE (X⟦n⟧))
    (shiftCocone F W (isomorphisms_le_of_isSaturated hW) n (valueCocone F W E hE X))).choose_spec

/-- The comparison morphism is an isomorphism: it is the map of Stacks 05SA along a morphism of
`W`, so this is the second half of Stacks 05SB. -/
private lemma isIso_shiftComparison (hW : W.IsSaturated) (n : ℤ) (X : E.FullSubcategory) :
    IsIso (shiftComparison F W E hE hW n X) := by
  obtain ⟨φ, hφ, hiso⟩ := (F.exists_isRightDerivedValueAt_iff_and_isIso_of_mem W
    (s := (E.ι.commShiftIso n).hom.app X) (mem_of_isIso hW _)).2
    (isRightDerivedValueAt_valueCocone F W E hE (X⟦n⟧))
    (isRightDerivedValueAt_shiftCocone F W (isomorphisms_le_of_isSaturated hW) n
      (isRightDerivedValueAt_valueCocone F W E hE X))
  have he : shiftComparison F W E hE hW n X = φ :=
    eq_of_isDerivedMap _ (isRightDerivedValueAt_valueCocone F W E hE (X⟦n⟧))
      (isDerivedMap_shiftComparison F W E hE hW n X) (fun A B g h => hφ A B g h.symm)
  rw [he]
  exact hiso

/-- The natural isomorphism `RF(-⟦n⟧) ≅ RF(-)⟦n⟧`, natural because both sides are the map of
Stacks 05SA along the two sides of the naturality square of `E.ι.commShiftIso n`. -/
private noncomputable def shiftIso (hW : W.IsSaturated) (n : ℤ) :
    shiftFunctor E.FullSubcategory n ⋙ rightDerived F W E hE ≅
      rightDerived F W E hE ⋙ shiftFunctor H n :=
  haveI := fun (m : ℤ) (Y : E.FullSubcategory) => isIso_shiftComparison F W E hE hW m Y
  NatIso.ofComponents (fun X => asIso (shiftComparison F W E hE hW n X)) fun {X Y} f =>
    eq_of_isDerivedMap _ (isRightDerivedValueAt_valueCocone F W E hE (X⟦n⟧))
      ((isDerivedMap_derivedMap F W E hE ((shiftFunctor E.FullSubcategory n).map f)).comp_of_eq
        (isDerivedMap_shiftComparison F W E hE hW n Y) rfl)
      ((isDerivedMap_shiftComparison F W E hE hW n X).comp_of_eq
        (isDerivedMap_shift F W (isomorphisms_le_of_isSaturated hW) n
          (isDerivedMap_derivedMap F W E hE f))
        (by simpa using E.ι.commShiftIso_hom_naturality f n))

@[local simp]
private lemma shiftIso_hom_app (hW : W.IsSaturated) (n : ℤ) (X : E.FullSubcategory) :
    (shiftIso F W E hE hW n).hom.app X = shiftComparison F W E hE hW n X := rfl

/-- **Stacks 05SU**, value half: the right derived functor commutes with the shift. The
isomorphisms are `shiftIso`; the two coherence axioms hold because each side is the
map of Stacks 05SA along the corresponding structural morphism of `C`, and that map is unique. -/
@[instance_reducible]
private noncomputable def rightDerivedCommShift (hW : W.IsSaturated) :
    (rightDerived F W E hE).CommShift ℤ where
  commShiftIso n := shiftIso F W E hE hW n
  commShiftIso_zero := by
    ext X
    rw [shiftIso_hom_app, Functor.CommShift.isoZero_hom_app]
    refine eq_of_isDerivedMap _ (isRightDerivedValueAt_valueCocone F W E hE (X⟦(0 : ℤ)⟧))
      (isDerivedMap_shiftComparison F W E hE hW 0 X)
      ((isDerivedMap_derivedMap F W E hE
        ((shiftFunctorZero E.FullSubcategory ℤ).hom.app X)).comp_of_eq
        (isDerivedMap_shiftFunctorZero_inv F W (isomorphisms_le_of_isSaturated hW)
          (valueCocone F W E hE X)) ?_)
    rw [E.ι.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
    rfl
  commShiftIso_add a b := by
    ext X
    rw [shiftIso_hom_app, Functor.CommShift.isoAdd_hom_app, shiftIso_hom_app, shiftIso_hom_app]
    refine eq_of_isDerivedMap _ (isRightDerivedValueAt_valueCocone F W E hE (X⟦a + b⟧))
      (isDerivedMap_shiftComparison F W E hE hW (a + b) X)
      ((isDerivedMap_derivedMap F W E hE
        ((shiftFunctorAdd E.FullSubcategory a b).hom.app X)).comp_of_eq
        ((isDerivedMap_shiftComparison F W E hE hW b (X⟦a⟧)).comp_of_eq
          ((isDerivedMap_shift F W (isomorphisms_le_of_isSaturated hW) b
            (isDerivedMap_shiftComparison F W E hE hW a X)).comp_of_eq
            (isDerivedMap_shiftFunctorAdd_inv F W (isomorphisms_le_of_isSaturated hW) a b
              (valueCocone F W E hE X)) rfl) rfl) ?_)
    rw [E.ι.commShiftIso_add a b, Functor.CommShift.isoAdd_hom_app]
    rfl

/-- **Stacks 05SE(2)**: `RF : ℰ ⥤ 𝒟'` is exact. This is the last conjunct of Stacks 05SC applied
to the image of a distinguished triangle of `ℰ` in `𝒟`, at the chosen values: the three morphisms
it produces are the maps of Stacks 05SA along the three morphisms of the triangle, hence, by
uniqueness, are `RF` of them — the third after the isomorphism of
`rightDerivedCommShift`. -/
private lemma rightDerived_isTriangulated (hW : W.IsSaturated) :
    letI := rightDerivedCommShift F W E hE hW
    (rightDerived F W E hE).IsTriangulated := by
  let := rightDerivedCommShift F W E hE hW
  constructor
  intro T hT
  obtain ⟨u, v, w, hdist, hu, hv, hw⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished W hW
        (E.ι.mapTriangle.obj T) (E.ι.map_distinguished T hT)).1.2.2.2
      (valueCocone F W E hE T.obj₁) (isRightDerivedValueAt_valueCocone F W E hE T.obj₁)
      (valueCocone F W E hE T.obj₂) (isRightDerivedValueAt_valueCocone F W E hE T.obj₂)
      (valueCocone F W E hE T.obj₃) (isRightDerivedValueAt_valueCocone F W E hE T.obj₃)
  have hcs : ((rightDerived F W E hE).commShiftIso (1 : ℤ)).hom.app T.obj₁
      = shiftComparison F W E hE hW 1 T.obj₁ := rfl
  have heu : u = (rightDerived F W E hE).map T.mor₁ :=
    eq_of_isDerivedMap _ (isRightDerivedValueAt_valueCocone F W E hE T.obj₁) hu
      (isDerivedMap_derivedMap F W E hE T.mor₁)
  have hev : v = (rightDerived F W E hE).map T.mor₂ :=
    eq_of_isDerivedMap _ (isRightDerivedValueAt_valueCocone F W E hE T.obj₂) hv
      (isDerivedMap_derivedMap F W E hE T.mor₂)
  have hew : w = (rightDerived F W E hE).map T.mor₃ ≫
      ((rightDerived F W E hE).commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
    rw [hcs]
    exact eq_of_isDerivedMap _ (isRightDerivedValueAt_valueCocone F W E hE T.obj₃)
      (isDerivedMap_shiftCocone_of_forall F W (isomorphisms_le_of_isSaturated hW) 1 _ hw)
      ((isDerivedMap_derivedMap F W E hE T.mor₃).comp_of_eq
        (isDerivedMap_shiftComparison F W E hE hW 1 T.obj₁) rfl)
  have hmk : Pretriangulated.Triangle.mk u v w = (rightDerived F W E hE).mapTriangle.obj T := by
    rw [heu, hev, hew]
    exact (Functor.mapTriangle_obj (rightDerived F W E hE) T).symm
  exact hmk ▸ hdist

end Exact

/-! ### Tag 05SE -/

section Solution

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  {D : Type u₃} [Category.{v₃} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

end Solution

end DerivedFunctorSubcategory

namespace CategoryTheory.Functor

open DerivedFunctorSubcategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  {D : Type u₃} [Category.{v₃} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

/-- **Stacks 05SE**. Let `F : C ⥤ H` be an exact functor of pre-triangulated categories, let `W`
be a saturated multiplicative system in `C` (Stacks 05Q8) compatible with the triangulation, and
let `E` be the full subcategory of `C` spanned by the objects at which the right derived functor
`RF` is defined, i.e. at which the ind-object `(s : X ⟶ X') ↦ F(X')` on `X/W` has a value in the
sense of Stacks 05S9. Let `L : C ⥤ D` be a localization functor for `W`, so that `D` is a model
of `W⁻¹C`, pre-triangulated by Stacks 05R6. Then, writing `S_E = W.inverseImage E.ι` for the
morphisms of `E` lying in `W`:

1. `E` is a strictly full triangulated subcategory of `C`;
2. `RF` is an exact functor `E ⥤ H`;
3. an element of `W` with source or target in `E` has both in `E`, hence is a morphism of `E`;
4. `RF` inverts every element of `S_E`;
5. `S_E` is a saturated multiplicative system in `E` compatible with the triangulation;
6. the induced functor `S_E⁻¹E ⥤ W⁻¹C` is fully faithful and exact;
7. `RF` factors through an exact functor `S_E⁻¹E ⥤ H`;
8. if `H` is Karoubian, `E` is a saturated (thick) triangulated subcategory of `C`.

The functor `RF` is pinned by its values: `RF.obj X` is the vertex of a value cocone `ι X` of
the ind-object at `X` (Stacks 05S9), and `RF.map f` is the unique map compatible with the
coprojections along every commutative square with sides in `W` (Stacks 05SA). The functors of
(6) and (7) are pinned as lifts through a localization functor `LE` of `E` at `S_E`. The
similar result for `LF` with which the source closes is
`isTriangulated_and_exists_leftDerivedFunctor`. -/
@[stacks 05SE "RF: items (1)-(8) for the subcategory on which the right derived functor is \
  defined; the LF statement is isTriangulated_and_exists_leftDerivedFunctor"]
public theorem isTriangulated_and_exists_rightDerivedFunctor
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (E : ObjectProperty C) (hE : ∀ X, E X ↔ ∃ c, F.IsRightDerivedValueAt W X c)
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.Additive] :
    letI := hW.hasLeftCalculusOfFractions
    letI := Triangulated.Localization.pretriangulated L W
    -- (1) `E` is a strictly full triangulated subcategory of `C`
    ∃ (_ : E.IsClosedUnderIsomorphisms) (_ : E.IsTriangulated),
      -- (3) an element of `W` with source or target in `E` has both in `E`
      (∀ {X Y : C} (s : X ⟶ Y), W s → (E X ↔ E Y)) ∧
      -- (8) over a Karoubian target, `E` is saturated
      (IsIdempotentComplete H → E.IsSaturated) ∧
      -- (5) `S_E` is a saturated multiplicative system compatible with the triangulation
      ∃ (hSE : (W.inverseImage E.ι).IsSaturated)
        (_ : (W.inverseImage E.ι).IsCompatibleWithTriangulation)
        (RF : E.FullSubcategory ⥤ H) (_ : RF.CommShift ℤ)
        (ι : ∀ X : E.FullSubcategory, MorphismProperty.Under.forget W ⊤ X.obj ⋙
          Under.forget X.obj ⋙ F ⟶ (Functor.const (W.Under ⊤ X.obj)).obj (RF.obj X)),
        -- (2) `RF : E ⥤ H` is exact
        RF.IsTriangulated ∧
        -- its value at `X` is a value of `RF` at `X` (Stacks 05S9)
        (∀ X : E.FullSubcategory,
          F.IsRightDerivedValueAt W X.obj (Cocone.mk (RF.obj X) (ι X))) ∧
        -- and its action on morphisms is the map of Stacks 05SA
        (∀ {X Y : E.FullSubcategory} (f : X ⟶ Y) (a : W.Under ⊤ X.obj) (b : W.Under ⊤ Y.obj)
          (g : a.right ⟶ b.right), E.ι.map f ≫ b.hom = a.hom ≫ g →
            (ι X).app a ≫ RF.map f = F.map g ≫ (ι Y).app b) ∧
        -- (4) `RF` inverts `S_E`
        (W.inverseImage E.ι).IsInvertedBy RF ∧
        letI := hSE.hasLeftCalculusOfFractions
        ∀ (EL : Type u₄) [Category.{v₄} EL] [HasZeroObject EL] [HasShift EL ℤ] [Preadditive EL]
          [∀ n : ℤ, (shiftFunctor EL n).Additive] (LE : E.FullSubcategory ⥤ EL)
          [LE.IsLocalization (W.inverseImage E.ι)] [LE.CommShift ℤ] [LE.Additive],
          letI := Triangulated.Localization.pretriangulated LE (W.inverseImage E.ι)
          -- (6) `S_E⁻¹E ⥤ W⁻¹C` is fully faithful and exact
          (∀ (Φ : EL ⥤ D) [Lifting LE (W.inverseImage E.ι) (E.ι ⋙ L) Φ],
            Φ.Full ∧ Φ.Faithful ∧
              (letI := Functor.commShiftOfLocalization LE (W.inverseImage E.ι) ℤ (E.ι ⋙ L) Φ;
                Φ.IsTriangulated)) ∧
            -- (7) `RF` factors through an exact functor `S_E⁻¹E ⥤ H`
            ∀ (RF' : EL ⥤ H) [Lifting LE (W.inverseImage E.ι) RF RF'],
              letI := Functor.commShiftOfLocalization LE (W.inverseImage E.ι) ℤ RF RF';
              RF'.IsTriangulated := by
  let := hW.hasLeftCalculusOfFractions
  let := Triangulated.Localization.pretriangulated L W
  let := isClosedUnderIsomorphisms F W E hW hE
  let := isTriangulated F W E hW hE
  let := rightDerivedCommShift F W E hE hW
  let := rightDerived_isTriangulated F W E hE hW
  refine ⟨inferInstance, inferInstance, fun {X Y} s hs => prop_iff_of_mem F W E hW hE hs,
    fun hH => isSaturated_of_isIdempotentComplete F W E hW hE hH,
    inverseImage_isSaturated F W E hW hE,
    inverseImage_isCompatibleWithTriangulation W E hW,
    DerivedFunctorSubcategory.rightDerived F W E hE, inferInstance,
    fun X => (valueCocone F W E hE X).ι, inferInstance,
    isRightDerivedValueAt_valueCocone F W E hE,
    fun {X Y} f a b g h => isDerivedMap_derivedMap F W E hE f a b g (by simpa using h),
    isInvertedBy F W E hE, ?_⟩
  intro EL _ _ _ _ _ LE _ _ _
  let := (inverseImage_isSaturated F W E hW hE).hasLeftCalculusOfFractions
  let := inverseImage_isCompatibleWithTriangulation W E hW
  let := Triangulated.Localization.pretriangulated LE (W.inverseImage E.ι)
  let := Localization.essSurj_mapArrow LE (W.inverseImage E.ι)
  let := (Triangulated.Localization.existsUnique_pretriangulated_and_isTriangulated LE
    (W.inverseImage E.ι)).1
  refine ⟨fun Φ _ => ⟨(full_and_faithful_of_lifting W E
      (inverseImage_isSaturated F W E hW hE).hasLeftCalculusOfFractions
      (fun s hs => prop_iff_of_mem F W E hW hE hs) L EL LE Φ).1,
    (full_and_faithful_of_lifting W E
      (inverseImage_isSaturated F W E hW hE).hasLeftCalculusOfFractions
      (fun s hs => prop_iff_of_mem F W E hW hE hs) L EL LE Φ).2,
    Functor.isTriangulated_of_localization LE (W.inverseImage E.ι) (E.ι ⋙ L) Φ⟩,
    fun RF' _ => Functor.isTriangulated_of_localization LE (W.inverseImage E.ι)
      (DerivedFunctorSubcategory.rightDerived F W E hE) RF'⟩

end CategoryTheory.Functor

end
