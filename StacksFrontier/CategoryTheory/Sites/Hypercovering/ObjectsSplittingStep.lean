module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectsSplittingIndex

/-!
# Hypercoverings by objects in a prescribed collection

Let `C` be a site with fibre products given by a pretopology `J`, let `X : C` and let `B ⊂ Ob(C)`
be a collection of objects which covers every object of `C` and for which a covering by objects of
`B` stays a covering after one more morphism out of an object of `B` is adjoined. Then `X` admits a
hypercovering all of whose summands have their underlying object in `B`. That is
[Stacks, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV), and it is proved here.

The proof is an induction on the truncation level:
`Stacks.CategoryTheory.Hypercovering.exists_hypercovering_of_objects_in_of_extensionData` runs it
granted an auxiliary invariant `Q`, and `exists_isTruncatedHypercoveringOver_succ_of_splitting`
performs the induction step when `Q` is *splitness* in the sense of
[Stacks, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU). The invariant propagates because the
one-step extension of a split truncated hypercovering is split again.

## The shape of the propagation

Let `Y` be a split `M`-truncated hypercovering with nondegenerate parts `N`, and let
`u : P ⟶ (cosk_M sk_M Y)_{M + 1}` be the covering of the matching object through which the
degenerate part maps. The extension's nondegenerate part in degree `M + 1` is the part of `P` that
the covering half of Tag 0DAV *adjoins*, i.e. the complement of the degenerate part inside `P`. So
what the propagation needs is a refinement of
`Stacks.CategoryTheory.Hypercovering.exists_isCoveringOver_objects_in` which exhibits `P` as a
coproduct of a new piece `Z'` and the nondegenerate parts along the epimorphisms out of `⦋M + 1⦌`,
with the degenerate part mapping in as the second family of injections. That is
`exists_isCoveringOver_objects_in_cofan`, and it is proved from the same two hypotheses on `B`,
through the same construction, by reading off the index type of the covering it builds.

Granted that, the splitting of the extension is assembled degreewise. In degrees at most `M` the
extension *is* `Y`, and the indices out of a simplex of dimension at most `M` are the same at
truncation level `M` and `M + 1` (`EpiOut.equivSucc`), so the colimit condition is the one carried
by `Y`. In degree `M + 1` the indices are the identity together with the indices at level `M`
(`EpiOut.equivSuccTop`), and the colimit condition is exactly the coproduct decomposition of `P`:
the leg at the identity is the inclusion of `Z'`, and the leg at an index `j` is the `j`-th
injection of the degenerate part followed by the factorization, because a degeneracy of a split
simplicial object acts on indices by precomposition (`Splitting.ι_comp_degenEpi`).

## Main definitions

* `CategoryTheory.Limits.Cofan.cons`: a cofan on a family extended by one more member, indexed by
  `Option`. This is the shape of the degree-`M + 1` coproduct decomposition.
* `CategoryTheory.Limits.FormalCoproduct.isColimitCofanOfBijective`: a cofan of formal coproducts
  whose index maps are jointly bijective and whose components are isomorphisms is a coproduct. This
  is the criterion by which the covering built by `exists_isCoveringOver_objects_in_cofan` is
  recognised as a coproduct, generalising `FormalCoproduct.isColimitCofanOfType`.
* `CategoryTheory.SimplicialObject.Truncated.EpiOut.raise`, `EpiOut.lowerOf`,
  `EpiOut.equivSucc`, `EpiOut.equivSuccTop`: the comparison of the index types of
  `CategoryTheory.SimplicialObject.Truncated.Splitting` at two consecutive truncation levels.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.extN` and `Splitting.extι`: the
  nondegenerate parts of a one-step extension and their inclusions.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.extSplittingOfData`: the resulting splitting
  of the extension.

## Main results

* `CategoryTheory.Limits.Cofan.isColimitOfReindex`: a colimit cofan stays one after reindexing
  along an equivalence, identifying the summands and the vertex.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.ι_comp_degenEpi`: the degeneracy of a
  splitting along the epimorphism of an index carries the nondegenerate part to the corresponding
  summand of the degenerate part.
* `Stacks.CategoryTheory.Hypercovering.exists_isCoveringOver_objects_in_cofan`: the covering half
  of the one-step extension, refined so that the covering is a coproduct of a new piece by objects
  of `B` and the given family.
* `Stacks.CategoryTheory.Hypercovering.exists_hypercovering_with_objects_in`: **Tag 0DAV.**

## Implementation notes

**One spelling per statement.** `ExtensionData.obj` is a dependent `if`, so the degree-`a` term of
an extension is only *equal* to the corresponding term of `Y`; and
`ExtensionData.extend.obj (op x)` is `ExtensionData.obj x` by definition but not syntactically. A
composite mixing the two spellings elaborates and is then not type-correct at `implicit`
transparency, after which `Category.assoc` silently fails to fire. Hence
`ExtensionData.extend_obj_of_le` and its three relatives, which are the existing lemmas restated
through `extend` and proved by `:=`; every statement below uses the `extend` spelling throughout.

**`B` is not closed under isomorphism**, so the refined covering lemma has to produce the new
nondegenerate part on the nose rather than up to isomorphism. It is taken to be the restriction of
the covering to the indices the first hypothesis on `B` contributes, so that its summands are
literally those of the covering.

**Bijectivity rather than an explicit equivalence.** The index type of the covering is a sigma type
over the indices of the matching object of a sum, and the index type of the degree-`M + 1` cofan is
a sigma type over `Option`. Writing down an equivalence between them means transporting a
dependent second component along an equality of first components; instead
`isColimitCofanOfBijective` asks only for joint bijectivity, injectivity is proved by exhibiting a
left inverse, and both directions then need no transport.

**Universes.** `A : Type u` with `[Category.{v} A]` for the simplicial material, `C : Type u` with
`[Category.{v} C]` and a free index universe `w` for the formal coproducts, as in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectsSplittingIndex`. The index type
`EpiOut M S` is a `Type`, which is why the degree-`M + 1` coproduct is taken in the explicitly
indexed form `FormalCoproduct.cofanOfType`. No universe is narrowed.

## References

* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
* [Stacks Project, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 01G3](https://stacks.math.columbia.edu/tag/01G3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject

universe w v u

namespace CategoryTheory.Limits

section Cofan

variable {A : Type u} [Category.{v} A]

/-- **A colimit cofan stays a colimit after reindexing.** The index type is moved along an
equivalence, the summands are identified one by one and the vertex is identified, and the legs are
required to correspond. -/
def Cofan.isColimitOfReindex {ι ι' : Type*} (ε : ι ≃ ι') {g : ι → A} {g' : ι' → A}
    {P P' : A} (hP : P = P') (hg : ∀ i, g' (ε i) = g i)
    {c : ∀ i, g i ⟶ P} {c' : ∀ i', g' i' ⟶ P'}
    (hc : ∀ i, c' (ε i) = eqToHom (hg i) ≫ c i ≫ eqToHom hP)
    (h : IsColimit (Cofan.mk P c)) : IsColimit (Cofan.mk P' c') := by
  subst hP
  simp only [eqToHom_refl, Category.comp_id] at hc
  have hfac : ∀ (T : A) (k : ∀ i, g i ⟶ T) (i : ι),
      c i ≫ Cofan.IsColimit.desc h k = k i := fun T k i ↦ Cofan.IsColimit.fac h k i
  have hext : ∀ (T : A) (p q : P ⟶ T), (∀ i, c i ≫ p = c i ≫ q) → p = q :=
    fun T p q hpq ↦ Cofan.IsColimit.hom_ext h p q hpq
  refine Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc h (fun i ↦ eqToHom (hg i).symm ≫ t.inj (ε i)))
    (fun t i' ↦ ?_) (fun t m hm ↦ ?_)
  · obtain ⟨i, rfl⟩ := ε.surjective i'
    change c' (ε i) ≫ _ = _
    rw [hc i, Category.assoc, hfac, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
  · refine hext _ _ _ fun i ↦ ?_
    rw [hfac]
    have h2 := hm (ε i)
    change c' (ε i) ≫ m = _ at h2
    rw [hc i, Category.assoc] at h2
    rw [← h2, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- A cofan on a family extended by one more member at `none`. This is the shape of the
degree-`M + 1` coproduct decomposition of a one-step extension: a new nondegenerate part together
with the degenerate summands. -/
def Cofan.cons {𝒜 : Type} (Z : A) (g : 𝒜 → A) {P : A} (z : Z ⟶ P) (σ : ∀ a, g a ⟶ P) :
    Cofan (Option.elim' Z g) :=
  Cofan.mk P fun o ↦ o.rec z σ

/-- The vertex of `Cofan.cons Z g z σ` is `P`. -/
@[simp]
theorem Cofan.cons_pt {𝒜 : Type} (Z : A) (g : 𝒜 → A) {P : A} (z : Z ⟶ P) (σ : ∀ a, g a ⟶ P) :
    (Cofan.cons Z g z σ).pt = P := rfl

end Cofan

namespace FormalCoproduct

variable {D : Type u} [Category.{v} D] {𝒜 : Type} {g : 𝒜 → FormalCoproduct.{w} D}

/-- **A cofan of formal coproducts with jointly bijective index maps and isomorphism components is
a coproduct.** This generalises `FormalCoproduct.isColimitCofanOfType`, which is the special case
where the index map is the tautological one; it is how a coproduct decomposition of a concretely
built semi-representable object is recognised. -/
noncomputable def isColimitCofanOfBijective (t : Cofan g)
    (hbij : Function.Bijective fun p : (a : 𝒜) × (g a).I ↦ (t.inj p.1).f p.2)
    (hiso : ∀ (a : 𝒜) (k : (g a).I), IsIso ((t.inj a).φ k)) : IsColimit t := by
  refine IsColimit.ofIsoColimit (isColimitCofanOfType g)
    (Cocone.ext (isoOfComponents (Equiv.ofBijective _ hbij)
      (fun p ↦ @asIso _ _ _ _ _ (hiso p.1 p.2))) ?_)
  rintro ⟨a⟩
  refine hom_ext (funext fun k ↦ rfl) fun k ↦ ?_
  have h : (𝟙 ((g a).obj k) ≫ (t.inj a).φ k) ≫ 𝟙 (t.pt.obj ((t.inj a).f k))
      = (t.inj a).φ k := by
    rw [Category.id_comp, Category.comp_id]
  exact h

end FormalCoproduct

end CategoryTheory.Limits

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] {M : ℕ}

/-- An index out of a simplex, read one truncation level higher. -/
def EpiOut.raise {S : SimplexCategory} (j : EpiOut M S) : EpiOut (M + 1) S :=
  ⟨⟨j.target.obj, j.target.property.trans (Nat.le_succ M)⟩, j.hom, j.2.2⟩

/-- An index whose target is `M`-truncated, read one truncation level lower. -/
def EpiOut.lowerOf {S : SimplexCategory} (j : EpiOut (M + 1) S) (h : j.target.obj.len ≤ M) :
    EpiOut M S := ⟨⟨j.target.obj, h⟩, j.hom, j.2.2⟩

/-- **For a simplex of dimension at most `M` the indices out of it do not depend on whether the
ambient truncation level is `M` or `M + 1`**, because an epimorphism cannot raise the dimension. -/
def EpiOut.equivSucc {S : SimplexCategory} (hS : S.len ≤ M) : EpiOut M S ≃ EpiOut (M + 1) S where
  toFun := EpiOut.raise
  invFun j := j.lowerOf ((SimplexCategory.len_le_of_epi j.hom).trans hS)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The indices out of `⦋M + 1⦌` at truncation level `M + 1` are the identity together with the
indices at level `M`.** An index whose target has dimension `M + 1` is the identity, its
epimorphism being an isomorphism of `SimplexCategory` and hence an identity. -/
def EpiOut.equivSuccTop :
    Option (EpiOut M ⦋M + 1⦌) ≃ EpiOut (M + 1) (⦋M + 1⦌ : SimplexCategory) where
  toFun o := o.elim (EpiOut.id (M + 1) ⟨⦋M + 1⦌, le_rfl⟩) EpiOut.raise
  invFun j := if h : j.target.obj.len ≤ M then some (j.lowerOf h) else none
  left_inv o := by
    rcases o with _ | j
    · exact dite_eq_right (by change ¬ M + 1 ≤ M; omega)
    · exact dite_eq_left j.target.property
  right_inv j := by
    dsimp only
    by_cases h : j.target.obj.len ≤ M
    · rw [dite_eq_left h]
      rfl
    · rw [dite_eq_right h]
      obtain ⟨t, e, he⟩ := j
      obtain rfl : t = ⟨⦋M + 1⦌, le_rfl⟩ :=
        ObjectProperty.FullSubcategory.ext (SimplexCategory.Truncated.obj_eq_mk_of_not_le h)
      obtain rfl : e = 𝟙 _ := SimplexCategory.eq_id_of_epi e
      rfl

/-- Composing an index with the identity index at its target gives it back. -/
theorem EpiOut.comp_epiOutId {S : SimplexCategory} (j : EpiOut M S) :
    EpiOut.comp j.hom (EpiOut.id M j.target) = j :=
  congrArg (fun q : { e : S ⟶ j.target.obj // Epi e } ↦ (⟨j.target, q⟩ : EpiOut M S))
    (Subtype.ext (Category.comp_id j.hom))

/-- A functor on truncated simplices sends the identity morphism to the identity. -/
private theorem map_homMk_id {n : ℕ} (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ A)
    (x : SimplexCategory.Truncated n) :
    F.map (ObjectProperty.homMk (X := x) (Y := x) (𝟙 x.obj)).op = 𝟙 (F.obj (op x)) :=
  F.map_id (op x)

namespace ExtensionData

variable {Y : SimplicialObject.Truncated A M} (D : ExtensionData Y)

/-- `ExtensionData.obj_of_le`, spelled through `ExtensionData.extend`. -/
theorem extend_obj_of_le {x : SimplexCategory.Truncated (M + 1)} (h : x.obj.len ≤ M) :
    D.extend.obj (op x) = Y.obj (op ⟨x.obj, h⟩) := D.obj_of_le h

/-- `ExtensionData.obj_of_not_le`, spelled through `ExtensionData.extend`. -/
theorem extend_obj_of_not_le {x : SimplexCategory.Truncated (M + 1)} (h : ¬ x.obj.len ≤ M) :
    D.extend.obj (op x) = D.pt := D.obj_of_not_le h

/-- `ExtensionData.map_of_le_le`, spelled through `ExtensionData.extend`. -/
theorem extend_map_of_le_le {a b : SimplexCategory.Truncated (M + 1)} (f : a.obj ⟶ b.obj)
    (ha : a.obj.len ≤ M) (hb : b.obj.len ≤ M) :
    D.extend.map (ObjectProperty.homMk (X := a) (Y := b) f).op
      = eqToHom (D.extend_obj_of_le hb)
        ≫ Y.map (ObjectProperty.homMk (X := (⟨a.obj, ha⟩ : SimplexCategory.Truncated M))
            (Y := ⟨b.obj, hb⟩) f).op
        ≫ eqToHom (D.extend_obj_of_le ha).symm := D.map_of_le_le a b f ha hb

/-- `ExtensionData.map_of_not_le_le`, spelled through `ExtensionData.extend`. -/
theorem extend_map_of_not_le_le {a b : SimplexCategory.Truncated (M + 1)} (f : a.obj ⟶ b.obj)
    (ha : ¬ a.obj.len ≤ M) (hb : b.obj.len ≤ M) :
    D.extend.map (ObjectProperty.homMk (X := a) (Y := b) f).op
      = eqToHom (D.extend_obj_of_le hb)
        ≫ D.degen ⟨b.obj, hb⟩
            (eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le ha).symm ≫ f)
        ≫ eqToHom (D.extend_obj_of_not_le ha).symm := D.map_of_not_le_le a b f ha hb

/-- The extension acts as the identity on the identity of a degree. -/
theorem extend_map_id (x : SimplexCategory.Truncated (M + 1)) :
    D.extend.map (ObjectProperty.homMk (X := x) (Y := x) (𝟙 x.obj)).op
      = 𝟙 (D.extend.obj (op x)) :=
  map_homMk_id D.extend x

end ExtensionData

namespace EpiExtensionData

/-- Along an epimorphism the reconstructed degeneracy family is the prescribed one. -/
theorem degen_of_epi {Y : SimplicialObject.Truncated A M} (D : EpiExtensionData Y)
    (x : SimplexCategory.Truncated M) (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] :
    D.degen x e = D.degenEpi x e := by
  rw [D.degen_eq_of_fac x.property e (𝟙 x.obj) (Category.comp_id e), map_homMk_id Y x]
  exact Category.id_comp _

end EpiExtensionData

namespace Splitting

variable {Y : SimplicialObject.Truncated A M} (S : Splitting Y)

/-- **The nondegenerate parts of a one-step extension**: those of `Y` in the degrees of dimension
at most `M`, and a prescribed object `Z'` in degree `M + 1`. -/
def extN (Z' : A) (x : SimplexCategory.Truncated (M + 1)) : A :=
  if h : x.obj.len ≤ M then S.N ⟨x.obj, h⟩ else Z'

/-- In a degree of dimension at most `M`, `extN Z'` is the nondegenerate part of `Y`. -/
theorem extN_of_le (Z' : A) {x : SimplexCategory.Truncated (M + 1)} (h : x.obj.len ≤ M) :
    S.extN Z' x = S.N ⟨x.obj, h⟩ := dite_eq_left h

/-- In degree `M + 1`, `extN Z'` is `Z'`. -/
theorem extN_of_not_le (Z' : A) {x : SimplexCategory.Truncated (M + 1)} (h : ¬ x.obj.len ≤ M) :
    S.extN Z' x = Z' := dite_eq_right h

/-- At the target of a raised index, `extN Z'` is the nondegenerate part of `Y` at the target of
the original index. -/
theorem extN_raise (Z' : A) {T : SimplexCategory} (j : EpiOut M T) :
    S.extN Z' (EpiOut.raise j).target = S.N j.target :=
  S.extN_of_le Z' (x := (EpiOut.raise j).target) j.target.property

/-- **The inclusions of the nondegenerate parts of a one-step extension.** -/
noncomputable def extι (D : ExtensionData Y) {Z' : A} (z' : Z' ⟶ D.pt)
    (x : SimplexCategory.Truncated (M + 1)) : S.extN Z' x ⟶ D.extend.obj (op x) :=
  if h : x.obj.len ≤ M then
    eqToHom (S.extN_of_le Z' h) ≫ S.ι ⟨x.obj, h⟩ ≫ eqToHom (D.extend_obj_of_le h).symm
  else
    eqToHom (S.extN_of_not_le Z' h) ≫ z' ≫ eqToHom (D.extend_obj_of_not_le h).symm

/-- In a degree of dimension at most `M`, `extι` is the inclusion `S.ι` of the nondegenerate part
of `Y`, up to the identifications of source and target. -/
@[reassoc]
theorem extι_of_le (D : ExtensionData Y) {Z' : A} (z' : Z' ⟶ D.pt)
    {x : SimplexCategory.Truncated (M + 1)} (h : x.obj.len ≤ M) :
    S.extι D z' x
      = eqToHom (S.extN_of_le Z' h) ≫ S.ι ⟨x.obj, h⟩
        ≫ eqToHom (D.extend_obj_of_le h).symm :=
  dite_eq_left h

/-- In degree `M + 1`, `extι` is `z'`, up to the identifications of source and target. -/
theorem extι_of_not_le (D : ExtensionData Y) {Z' : A} (z' : Z' ⟶ D.pt)
    {x : SimplexCategory.Truncated (M + 1)} (h : ¬ x.obj.len ≤ M) :
    S.extι D z' x
      = eqToHom (S.extN_of_not_le Z' h) ≫ z'
        ≫ eqToHom (D.extend_obj_of_not_le h).symm :=
  dite_eq_right h

/-- In a degree of dimension at most `M` the legs of the extension's splitting are those of `Y`. -/
theorem extι_leg_of_le (D : ExtensionData Y) {Z' : A} (z' : Z' ⟶ D.pt)
    {x : SimplexCategory.Truncated (M + 1)} (h : x.obj.len ≤ M) (j : EpiOut M x.obj) :
    S.extι D z' (EpiOut.raise j).target
        ≫ D.extend.map (ObjectProperty.homMk (EpiOut.raise j).hom).op
      = eqToHom (S.extN_raise Z' j)
        ≫ (S.ι j.target ≫ Y.map (ObjectProperty.homMk j.hom).op)
        ≫ eqToHom (D.extend_obj_of_le h).symm := by
  rw [S.extι_of_le_assoc D z' (x := (EpiOut.raise j).target) j.target.property,
    D.extend_map_of_le_le (EpiOut.raise j).hom h j.target.property,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- In degree `M + 1` the leg of the extension's splitting at the identity index is the inclusion
of the new nondegenerate part. -/
theorem extι_leg_top_none (D : ExtensionData Y) {Z' : A} (z' : Z' ⟶ D.pt)
    (hnot : ¬ (⟨⦋M + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (M + 1)).obj.len ≤ M) :
    S.extι D z' ⟨⦋M + 1⦌, le_rfl⟩
        ≫ D.extend.map (ObjectProperty.homMk
            (X := (⟨⦋M + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (M + 1)))
            (Y := ⟨⦋M + 1⦌, le_rfl⟩) (𝟙 ⦋M + 1⦌)).op
      = eqToHom (S.extN_of_not_le Z' hnot) ≫ z'
        ≫ eqToHom (D.extend_obj_of_not_le hnot).symm := by
  rw [D.extend_map_id, Category.comp_id, S.extι_of_not_le D z' hnot]

/-- In degree `M + 1` the leg of the extension's splitting at an index of level `M` is the
degeneracy of the extension along that index. -/
theorem extι_leg_top_raise (D : ExtensionData Y) {Z' : A} (z' : Z' ⟶ D.pt)
    (hnot : ¬ (⟨⦋M + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (M + 1)).obj.len ≤ M)
    (j : EpiOut M ⦋M + 1⦌) :
    S.extι D z' (EpiOut.raise j).target
        ≫ D.extend.map (ObjectProperty.homMk
            (X := (⟨⦋M + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (M + 1)))
            (Y := (EpiOut.raise j).target) (EpiOut.raise j).hom).op
      = eqToHom (S.extN_raise Z' j) ≫ (S.ι j.target ≫ D.degen j.target j.hom)
        ≫ eqToHom (D.extend_obj_of_not_le hnot).symm := by
  rw [S.extι_of_le_assoc D z' (x := (EpiOut.raise j).target) j.target.property,
    D.extend_map_of_not_le_le (EpiOut.raise j).hom hnot j.target.property, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [eqToHom_refl, Category.id_comp]
  rfl

section Extend

/-- **A degeneracy of a split simplicial object acts on indices by precomposition**, read at the
identity index: the nondegenerate part of the target of an index goes to the summand of the
degenerate part at that index. -/
theorem ι_comp_degenEpi [HasCoproduct S.degenFamily] (j : EpiOut M ⦋M + 1⦌) :
    S.ι j.target ≫ S.degenEpi j.target j.hom = Sigma.ι S.degenFamily j := by
  have h := S.inj_comp_degenEpi j.target j.hom (EpiOut.id M j.target)
  rw [S.inj_epiOutId, ← Sigma.eqToHom_comp_ι _ (EpiOut.comp_epiOutId j), eqToHom_refl,
    Category.id_comp] at h
  exact h

/-- **The one-step extension of a split truncated simplicial object is split again**, as soon as
its degree-`M + 1` object is the coproduct of a new piece `Z'` and the nondegenerate parts along
the epimorphisms out of `⦋M + 1⦌`, the latter legs computing the degeneracies.

In the degrees of dimension at most `M` the extension is `Y` and the index types agree, so the
colimit condition is the one `S` carries; in degree `M + 1` it is the assumed decomposition. -/
noncomputable def extSplittingOfData (D : ExtensionData Y) {Z' : A} (z' : Z' ⟶ D.pt)
    (σ : ∀ j : EpiOut M ⦋M + 1⦌, S.N j.target ⟶ D.pt)
    (hσ : ∀ j : EpiOut M ⦋M + 1⦌, S.ι j.target ≫ D.degen j.target j.hom = σ j)
    (hcol : IsColimit (Cofan.cons Z' S.degenFamily z' σ)) : Splitting D.extend where
  N := S.extN Z'
  ι := S.extι D z'
  isColimit x := by
    by_cases h : x.obj.len ≤ M
    · exact Cofan.isColimitOfReindex (EpiOut.equivSucc h) (D.extend_obj_of_le h).symm
        (fun j ↦ S.extN_raise Z' j) (fun j ↦ S.extι_leg_of_le D z' h j)
        (S.isColimit ⟨x.obj, h⟩)
    · obtain rfl : x = ⟨⦋M + 1⦌, le_rfl⟩ :=
        ObjectProperty.FullSubcategory.ext (SimplexCategory.Truncated.obj_eq_mk_of_not_le h)
      refine Cofan.isColimitOfReindex EpiOut.equivSuccTop
        (D.extend_obj_of_not_le h).symm ?_ ?_ hcol
      · rintro (_ | j)
        · exact S.extN_of_not_le Z' h
        · exact S.extN_raise Z' j
      · rintro (_ | j)
        · exact S.extι_leg_top_none D z' h
        · refine (S.extι_leg_top_raise D z' h j).trans ?_
          rw [hσ j]
          rfl

variable [∀ F : (SimplexCategory.Truncated M)ᵒᵖ ⥤ A,
  (SimplexCategory.Truncated.inclusion M).op.HasPointwiseRightKanExtension F]
  [HasCoproduct S.degenFamily] {P : A} (u : P ⟶ matchingObj Y) (s : S.degenPart ⟶ P)
  (hsu : s ≫ u = S.degenToMatching)

/-- The degeneracies of the extension data transported along a factorization are the summand
inclusions of the degenerate part followed by that factorization. -/
theorem ι_comp_degen_ofFac (j : EpiOut M ⦋M + 1⦌) :
    S.ι j.target
        ≫ (S.coskExtensionData.ofFac s u hsu).toEpiExtensionData.toExtensionData.degen
            j.target j.hom
      = Sigma.ι S.degenFamily j ≫ s := by
  rw [show (S.coskExtensionData.ofFac s u hsu).toEpiExtensionData.toExtensionData.degen
      j.target j.hom
      = (S.coskExtensionData.ofFac s u hsu).toEpiExtensionData.degen j.target j.hom from rfl,
    EpiExtensionData.degen_of_epi]
  change S.ι j.target ≫ S.degenEpi j.target j.hom ≫ s = _
  rw [← Category.assoc, S.ι_comp_degenEpi j]

end Extend

end Splitting

end CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialObject.Truncated CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- **The covering half of the one-step extension of Tag 0DAV, with the covering exhibited as a
coproduct.** Let `g` be a family of semi-representable objects over `X` with all summands in `B`,
and let `v` be a morphism from their coproduct to `W` with injective index map. Then `W` admits a
covering `u : P ⟶ W` by objects of `B` through which `v` factors, and `P` is the coproduct of the
`g a` and of one further semi-representable object `Z'` whose summands also lie in `B`.

This refines `exists_isCoveringOver_objects_in` by the coproduct decomposition, which is what the
propagation of splitness through the induction of Tag 0DAV needs: `Z'` becomes the nondegenerate
part of the extension in degree `M + 1`. Both hypotheses on `B` are used exactly as there, the
second one at the at most one summand of `g` lying over a given summand of `W`. -/
theorem exists_isCoveringOver_objects_in_cofan (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (A : ι → C) (a : ∀ i, A i ⟶ U),
      (∀ i, A i ∈ B) ∧ Presieve.ofArrows A a ∈ J U)
    (hadjoin : ∀ {ι : Type w} (A : ι → C) {U : C} (a : ∀ i, A i ⟶ U),
      (∀ i, A i ∈ B) → Presieve.ofArrows A a ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ b : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows A a h ∨ Presieve.singleton b h) ∈ J U)
    {X : C} (W : FormalCoproduct.{w} (Over X)) {𝒜 : Type}
    (g : 𝒜 → FormalCoproduct.{w} (Over X))
    (hg : ∀ (aa : 𝒜) (k : (g aa).I), ((g aa).obj k).left ∈ B)
    (v : (cofanOfType g).pt ⟶ W) (hv : Function.Injective v.f) :
    ∃ (Z' P : FormalCoproduct.{w} (Over X)) (u : P ⟶ W) (z' : Z' ⟶ P)
      (s : (cofanOfType g).pt ⟶ P),
      (∀ k : P.I, (P.obj k).left ∈ B) ∧ (∀ k : Z'.I, (Z'.obj k).left ∈ B) ∧
        IsCoveringOver J u ∧ s ≫ u = v ∧
        Nonempty (IsColimit (Cofan.cons Z' g z' fun aa ↦ (cofanOfType g).inj aa ≫ s)) := by
  classical
  have hsub : ∀ i : W.I, Subsingleton { k : (cofanOfType g).pt.I // v.f k = i } :=
    fun i ↦ ⟨fun k k' ↦ Subtype.ext (hv (k.2.trans k'.2.symm))⟩
  choose ι A a hAB hAJ using fun i : W.I ↦
    exists_ofArrows_sum_mem J B hcover hadjoin (hsub i)
      (fun k : { k : (cofanOfType g).pt.I // v.f k = i } ↦ ((cofanOfType g).pt.obj k.1).left)
      (fun k ↦ (v.φ k.1).left ≫ eqToHom (congrArg (fun m ↦ (W.obj m).left) k.2))
      (fun k ↦ hg k.1.1 k.1.2)
  have hdex : ∃ d : ∀ (i : W.I)
        (m : ι i ⊕ { k : (cofanOfType g).pt.I // v.f k = i }),
        Sum.elim (A i)
            (fun k : { k : (cofanOfType g).pt.I // v.f k = i } ↦
              ((cofanOfType g).pt.obj k.1).left) m ⟶ (W.obj i).left,
      (∀ i, Presieve.ofArrows (Sum.elim (A i)
          (fun k : { k : (cofanOfType g).pt.I // v.f k = i } ↦
            ((cofanOfType g).pt.obj k.1).left)) (d i) ∈ J (W.obj i).left) ∧
      (∀ (i : W.I) (k : { k : (cofanOfType g).pt.I // v.f k = i }), d i (Sum.inr k)
        = (v.φ k.1).left ≫ eqToHom (congrArg (fun m ↦ (W.obj m).left) k.2)) := by
    refine ⟨fun i ↦ Sum.rec (a i)
      (fun k ↦ (v.φ k.1).left ≫ eqToHom (congrArg (fun m ↦ (W.obj m).left) k.2)),
      fun i ↦ ?_, fun _ _ ↦ rfl⟩
    refine mem_coverings_of_eq (congrArg (Presieve.ofArrows _) ?_) (hAJ i)
    funext z
    cases z <;> rfl
  obtain ⟨d, hdJ, hdr⟩ := hdex
  have hwk : ∀ k : (cofanOfType g).pt.I, d (v.f k) (Sum.inr ⟨k, rfl⟩) ≫ (W.obj (v.f k)).hom
      = ((cofanOfType g).pt.obj k).hom := by
    intro k
    rw [hdr]
    simp only [eqToHom_refl, Category.comp_id]
    exact Over.w (v.φ k)
  have hisoOver : ∀ {Q R : Over X} (f : Q ⟶ R), IsIso f.left → IsIso f := by
    intro Q R f hf
    have h : IsIso ((Over.forget X).map f) := hf
    exact isIso_of_reflects_iso f (Over.forget X)
  refine ⟨⟨(i : W.I) × ι i, fun z ↦ Over.mk (d z.1 (Sum.inl z.2) ≫ (W.obj z.1).hom)⟩,
    ⟨(i : W.I) × (ι i ⊕ { k : (cofanOfType g).pt.I // v.f k = i }),
      fun z ↦ Over.mk (d z.1 z.2 ≫ (W.obj z.1).hom)⟩,
    ⟨fun z ↦ z.1, fun z ↦ Over.homMk (d z.1 z.2)⟩,
    ⟨fun z ↦ ⟨z.1, Sum.inl z.2⟩, fun _ ↦ 𝟙 _⟩,
    ⟨fun k ↦ ⟨v.f k, Sum.inr ⟨k, rfl⟩⟩,
      fun k ↦ Over.homMk (𝟙 _) ((Category.id_comp _).trans (hwk k))⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, m | k⟩
    · exact hAB i m
    · exact hg k.1.1 k.1.2
  · rintro ⟨i, m⟩
    exact hAB i m
  · exact isCoveringOver_sigma J W (fun i ↦ ι i ⊕ { k : (cofanOfType g).pt.I // v.f k = i })
      (fun i ↦ Sum.elim (A i) (fun k ↦ ((cofanOfType g).pt.obj k.1).left)) d hdJ
  · refine FormalCoproduct.hom_ext rfl fun k ↦ ?_
    rw [eqToHom_refl, Category.comp_id]
    refine Over.OverMorphism.ext ?_
    simp only [FormalCoproduct.category_comp_φ, Over.comp_left, hdr, eqToHom_refl,
      Category.comp_id]
    exact Category.id_comp _
  · refine ⟨isColimitCofanOfBijective _ ?_ ?_⟩
    · constructor
      · refine Function.LeftInverse.injective (g := fun q ↦
          Sum.elim (fun m ↦ ⟨none, ⟨q.1, m⟩⟩) (fun k ↦ ⟨some k.1.1, k.1.2⟩) q.2) ?_
        rintro ⟨_ | aa, k⟩ <;> rfl
      · rintro ⟨i, m | k⟩
        · exact ⟨⟨none, ⟨i, m⟩⟩, rfl⟩
        · obtain ⟨kk, hkk⟩ := k
          subst hkk
          exact ⟨⟨some kk.1, kk.2⟩, rfl⟩
    · rintro (_ | aa) k
      · change IsIso (𝟙 _)
        infer_instance
      · refine hisoOver _ ?_
        change IsIso (𝟙 ((g aa).obj k).left ≫ 𝟙 ((g aa).obj k).left)
        infer_instance

end Stacks.CategoryTheory.Hypercovering

end
