module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Presheaf

/-!
# The finite part of a base change

Let `X' = X ×_Y Y'` be a cartesian square of algebraic spaces over `S`, with vertical
morphisms `g' : X' ⟶ Y'` and `f : X ⟶ Y`. A morphism `a : T ⟶ Y'` identifies `T ×_{Y'} X'`
with `T ×_Y X`, so a pair of Stacks 04PC for `g'` over `T` becomes one for `f` over `T`, with
base morphism `a ≫ g`. This rule is natural in `T` and exhibits the square whose top edge is
the induced morphism `(X'/Y')_fin ⟶ (X/Y)_fin`, whose vertical edges are the projections to
`Y'` and to `Y`, and whose bottom edge is `g`, as a fibre product square of presheaves on the
big fppf site of `S`: that is, `(X'/Y')_fin = Y' ×_Y (X/Y)_fin`.

## Main definitions

* `AlgebraicGeometry.Space.FiniteOpenSubspace.ofPullbackSquare`: the pair of Stacks 04PC for
  `f` obtained from one for `g'`.
* `AlgebraicGeometry.Space.FinitePartPresheaf.mapOfPullbackSquare`: the induced morphism of
  finite parts `(X'/Y')_fin ⟶ (X/Y)_fin`.

## Main results

* `AlgebraicGeometry.Space.FiniteOpenSubspace.ofPullbackSquare_spec`: the transported pair has
  base morphism `a ≫ g`, and its open subspace is identified with the original one compatibly
  with the projections to `T` and to `X`.
* `AlgebraicGeometry.Space.FinitePartPresheaf.isPullback_mapOfPullbackSquare`: **Stacks
  04QF**, the square of finite parts is a fibre product square.

## Implementation notes

The statement is proved for an arbitrary pair of presheaves presenting the two finite parts,
not only for `AlgebraicGeometry.Space.finiteOpenSubspacePresheaf`, because the proof uses
nothing about them beyond the data of `AlgebraicGeometry.Space.FinitePartPresheaf`: the
identification of sections with pairs, the formula for the projection to the base, and the
base-change description of the restriction maps.

The open subspace of the transported pair is the preimage of the given one under the
identification of ambient fibre products, so the two are isomorphic rather than equal; the
open-subspace condition and the finiteness of the projection are transported along that
isomorphism. Injectivity and surjectivity of the transport on pairs with a prescribed base
morphism come from the fact that taking preimages along an isomorphism and along its inverse
are mutually inverse operations on subfunctors.

Cartesianness is checked sectionwise, by `CategoryTheory.IsPullback.of_forall_isPullback_app`
and the explicit criterion `CategoryTheory.Limits.Types.isPullback_iff` for squares of types.

## References

* [Stacks Project, Tag 04QF](https://stacks.math.columbia.edu/tag/04QF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-- For a cartesian square `X' = X ×_Y Y'` and a morphism `a : T ⟶ Y'`, the canonical
identification of the ambient fibre products `T ×_{Y'} X'` and `T ×_Y X`. -/
noncomputable def ambientIsoOfIsPullback {C : Type v} [Category.{u, v} C] [HasPullbacks C]
    {X' X Y' Y T : C} {f' : X' ⟶ X} {g' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h : IsPullback f' g' f g) (a : T ⟶ Y') : pullback a g' ≅ pullback (a ≫ g) f :=
  ((IsPullback.of_hasPullback a g').flip.paste_horiz h).flip.isoPullback

/-- An isomorphism of presheaves identifies a subfunctor of its source with the preimage of
that subfunctor in its target. -/
noncomputable def subfunctorIsoPreimage {C : Type v} [Category.{u, v} C]
    {F G : Cᵒᵖ ⥤ Type u} (e : F ≅ G) (Z : Subfunctor F) :
    Z.toFunctor ≅ (Z.preimage e.inv).toFunctor := by
  have hf : Subfunctor.range (Z.ι ≫ e.hom) ≤ Z.preimage e.inv := by
    rintro U y ⟨x, rfl⟩
    change e.inv.app U (e.hom.app U ((Z.ι.app U) x)) ∈ Z.obj U
    simp
  refine ⟨Subfunctor.lift (Z.ι ≫ e.hom) hf, Subfunctor.fromPreimage Z e.inv, ?_, ?_⟩
  · ext U x
    apply Subtype.ext
    change e.inv.app U (e.hom.app U x.val) = x.val
    simp
  · ext U x
    apply Subtype.ext
    change e.hom.app U (e.inv.app U x.val) = x.val
    simp

/-- The identification of a subfunctor with its preimage is compatible with the two
inclusions. -/
lemma subfunctorIsoPreimage_hom_ι {C : Type v} [Category.{u, v} C] {F G : Cᵒᵖ ⥤ Type u}
    (e : F ≅ G) (Z : Subfunctor F) :
    (subfunctorIsoPreimage e Z).hom ≫ (Z.preimage e.inv).ι = Z.ι ≫ e.hom := by
  dsimp only [subfunctorIsoPreimage]
  exact Subfunctor.lift_ι _ _

/-- Composing the identification of a subfunctor with its preimage and the inclusion of the
preimage with a morphism `m`, whose composite with the isomorphism is `n`, gives the inclusion
of the subfunctor followed by `n`. -/
private lemma subfunctorIsoPreimage_hom_ι_comp {C : Type v} [Category.{u, v} C]
    {F G H : Cᵒᵖ ⥤ Type u} (e : F ≅ G) (Z : Subfunctor F) (m : G ⟶ H) (n : F ⟶ H)
    (h : e.hom ≫ m = n) :
    (subfunctorIsoPreimage e Z).hom ≫ (Z.preimage e.inv).ι ≫ m = Z.ι ≫ n := by
  rw [← Category.assoc, subfunctorIsoPreimage_hom_ι, Category.assoc, h]

/-- A morphism between subfunctors of the same presheaf, compatible with the inclusions, shows
that the first is contained in the second. -/
private lemma subfunctor_le_of_comp_ι_eq {C : Type v} [Category.{u, v} C] {F : Cᵒᵖ ⥤ Type u}
    {Z W : Subfunctor F} (k : Z.toFunctor ⟶ W.toFunctor) (h : k ≫ W.ι = Z.ι) : Z ≤ W :=
  calc Z = Subfunctor.range Z.ι := (Subfunctor.range_ι Z).symm
    _ = Subfunctor.range (k ≫ W.ι) := by rw [h]
    _ ≤ Subfunctor.range W.ι := Subfunctor.range_comp_le _ _
    _ = W := Subfunctor.range_ι W

/-- Taking preimages along an isomorphism and along its inverse are mutually inverse. -/
private lemma preimage_hom_preimage_inv {C : Type v} [Category.{u, v} C] {F G : Cᵒᵖ ⥤ Type u}
    (e : F ≅ G) (Z : Subfunctor G) : (Z.preimage e.hom).preimage e.inv = Z := by
  rw [← Subfunctor.preimage_comp, e.inv_hom_id]
  exact Subfunctor.preimage_id Z

/-- Finiteness of a morphism of algebraic spaces transports along an isomorphism of its
source. -/
lemma isFinite_of_sourceIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) (a : F ⟶ H) (b : G ⟶ H)
    (w : e.hom ≫ b = a) (ha : IsFinite B S hS a) : IsFinite B S hS b := by
  intro U hU ξ
  obtain ⟨V, p, i, hV, hp, hi⟩ := ha U hU ξ
  refine ⟨V, p, i ≫ e.hom, hV, hp, ?_⟩
  exact hi.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simpa using w.symm) (by simp)

namespace FiniteOpenSubspace

/-- A pair of Stacks 04PC for a morphism `f₁ : X₁ ⟶ Y₁`, built from a pair `p` for a morphism
`f : X ⟶ Y`, a morphism `a : T ⟶ Y₁`, and an identification of `T ×_Y X` with `T ×_{Y₁} X₁`
over `T`: its open subspace is the preimage of that of `p`. -/
noncomputable def ofAmbientIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y X₁ Y₁ T : AlgebraicSpaces B S hS} {f : X ⟶ Y} {f₁ : X₁ ⟶ Y₁}
    (p : FiniteOpenSubspace B S hS f T) (a : T ⟶ Y₁)
    (e : pullback p.toBase.hom f.hom ≅ pullback a.hom f₁.hom)
    (he : e.hom ≫ pullback.fst a.hom f₁.hom = pullback.fst p.toBase.hom f.hom) :
    FiniteOpenSubspace B S hS f₁ T where
  toBase := a
  subspace := p.subspace.preimage e.inv
  isOpen := isOpenSubspace_preimage B S hS e.inv p.subspace
    (isAlgebraicSpace_pullback B S hS p.toBase.hom f.hom T.property X.property Y.property)
    (isAlgebraicSpace_pullback B S hS a.hom f₁.hom T.property X₁.property Y₁.property)
    p.isOpen
  finite_projection := isFinite_of_sourceIso B S hS (subfunctorIsoPreimage e p.subspace)
    _ _ (by rw [← Category.assoc, subfunctorIsoPreimage_hom_ι, Category.assoc, he])
    p.finite_projection

/-- For a cartesian square `X' = X ×_Y Y'` with vertical morphisms `g' : X' ⟶ Y'` and
`f : X ⟶ Y`, the pair of Stacks 04PC for `f` over `T` obtained from a pair `p` for `g'` over
`T`: its base morphism is `p.toBase ≫ g`, and its open subspace is that of `p` read through
the identification of `T ×_{Y'} X'` with `T ×_Y X`. -/
noncomputable def ofPullbackSquare (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y' Y T : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (h : IsPullback f' g' f g) (p : FiniteOpenSubspace B S hS g' T) :
    FiniteOpenSubspace B S hS f T :=
  ofAmbientIso B S hS p (p.toBase ≫ g)
    (ambientIsoOfIsPullback (AlgebraicSpaces.isPullback_hom B S hS h) p.toBase.hom)
    (IsPullback.isoPullback_hom_fst _)

/-- The transported pair has base morphism `p.toBase ≫ g`, and its open subspace is
isomorphic to that of `p` compatibly with the projections to `T` and to `X`. -/
theorem ofPullbackSquare_spec (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y' Y T : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (h : IsPullback f' g' f g) (p : FiniteOpenSubspace B S hS g' T) :
    let q := ofPullbackSquare B S hS f' g' f g h p
    (q.toBase.hom = p.toBase.hom ≫ g.hom) ∧
      ∃ i : p.subspace.toFunctor ≅ q.subspace.toFunctor,
        (i.hom ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom =
          p.subspace.ι ≫ pullback.fst p.toBase.hom g'.hom) ∧
        (i.hom ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
          p.subspace.ι ≫ pullback.snd p.toBase.hom g'.hom ≫ f'.hom) := by
  let e := ambientIsoOfIsPullback (AlgebraicSpaces.isPullback_hom B S hS h) p.toBase.hom
  refine ⟨rfl, subfunctorIsoPreimage e p.subspace, ?_, ?_⟩
  · exact subfunctorIsoPreimage_hom_ι_comp e _ _ _ (IsPullback.isoPullback_hom_fst _)
  · exact subfunctorIsoPreimage_hom_ι_comp e _ _ _ (IsPullback.isoPullback_hom_snd _)

/-- Two pairs of Stacks 04PC agree as soon as their base morphisms agree and their open
subspaces are isomorphic over both projections of the ambient fibre product. -/
theorem ext_of_iso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y} {p q : FiniteOpenSubspace B S hS f T}
    (ha : p.toBase.hom = q.toBase.hom) (e : p.subspace.toFunctor ≅ q.subspace.toFunctor)
    (hfst : e.hom ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom =
      p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom)
    (hsnd : e.hom ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
      p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom) : p = q := by
  obtain ⟨a, Z, ho, hf⟩ := p
  obtain ⟨b, W, ho', hf'⟩ := q
  obtain rfl : a = b := ObjectProperty.hom_ext _ ha
  have he : e.hom ≫ W.ι = Z.ι := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simpa only [Category.assoc] using hsnd
  have hZW : Z = W := le_antisymm (subfunctor_le_of_comp_ι_eq e.hom he)
    (subfunctor_le_of_comp_ι_eq e.inv (by rw [Iso.inv_comp_eq, he]))
  subst W
  rfl

/-- Transport along a cartesian square is injective on pairs with a prescribed base
morphism. -/
theorem ofPullbackSquare_injective (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y' Y T : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (h : IsPullback f' g' f g) {p q : FiniteOpenSubspace B S hS g' T}
    (ha : p.toBase.hom = q.toBase.hom)
    (he : ofPullbackSquare B S hS f' g' f g h p = ofPullbackSquare B S hS f' g' f g h q) :
    p = q := by
  obtain ⟨a, Z, ho, hf⟩ := p
  obtain ⟨b, W, ho', hf'⟩ := q
  obtain rfl : a = b := ObjectProperty.hom_ext _ ha
  let e := ambientIsoOfIsPullback (AlgebraicSpaces.isPullback_hom B S hS h) a.hom
  have hZW : Z.preimage e.inv = W.preimage e.inv := by injection he
  have hz := congrArg (fun V : Subfunctor _ => V.preimage e.hom) hZW
  replace hz := (preimage_hom_preimage_inv e.symm Z).symm.trans
    (hz.trans (preimage_hom_preimage_inv e.symm W))
  subst W
  rfl

/-- Every pair of Stacks 04PC for `f` whose base morphism factors through `g` is a transport
along the cartesian square, with the prescribed factorization as its base morphism. -/
theorem exists_ofPullbackSquare_eq (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y' Y T : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (h : IsPullback f' g' f g) (q : FiniteOpenSubspace B S hS f T) (a : T ⟶ Y')
    (ha : q.toBase.hom = a.hom ≫ g.hom) :
    ∃ p : FiniteOpenSubspace B S hS g' T,
      ofPullbackSquare B S hS f' g' f g h p = q ∧ p.toBase = a := by
  obtain ⟨b, Z, ho, hf⟩ := q
  obtain rfl : b = a ≫ g := ObjectProperty.hom_ext _ ha
  let e := ambientIsoOfIsPullback (AlgebraicSpaces.isPullback_hom B S hS h) a.hom
  refine ⟨ofAmbientIso B S hS (f₁ := g')
    (⟨a ≫ g, Z, ho, hf⟩ : FiniteOpenSubspace B S hS f T) a e.symm
    (IsPullback.isoPullback_inv_fst _), ?_, rfl⟩
  change FiniteOpenSubspace.mk (a ≫ g) ((Z.preimage e.hom).preimage e.inv) _ _ =
    ⟨a ≫ g, Z, ho, hf⟩
  congr 1
  exact preimage_hom_preimage_inv e Z

namespace IsBaseChange

/-- A base change of a pair of Stacks 04PC along a morphism of the site is unique. -/
theorem unique (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {T T' : BigFppfOver B S hS} {k : T' ⟶ T}
    {p : FiniteOpenSubspace B S hS f (schemeSpace T)}
    {q r : FiniteOpenSubspace B S hS f (schemeSpace T')}
    (hq : IsBaseChange B S hS f k p q) (hr : IsBaseChange B S hS f k p r) : q = r := by
  obtain ⟨ha, j, hj, hjx⟩ := hq
  obtain ⟨hb, l, hl, hlx⟩ := hr
  refine ext_of_iso B S hS (ha.trans hb.symm) (hj.isoIsPullback _ _ hl)
    (hj.isoIsPullback_hom_fst _ _ hl) ?_
  rwa [← hlx, ← Category.assoc, ← Category.assoc, hj.isoIsPullback_hom_snd _ _ hl]

/-- Transport along a cartesian square commutes with base change along a morphism of the
site. -/
theorem ofPullbackSquare (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y' Y : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (h : IsPullback f' g' f g) {T T' : BigFppfOver B S hS} {k : T' ⟶ T}
    {p : FiniteOpenSubspace B S hS g' (schemeSpace T)}
    {q : FiniteOpenSubspace B S hS g' (schemeSpace T')}
    (hq : IsBaseChange B S hS g' k p q) :
    IsBaseChange B S hS f k
      (FiniteOpenSubspace.ofPullbackSquare B S hS f' g' f g h p)
      (FiniteOpenSubspace.ofPullbackSquare B S hS f' g' f g h q) := by
  obtain ⟨ha, l, hl, hlx⟩ := hq
  obtain ⟨hpbase, i, hit, hix⟩ :=
    FiniteOpenSubspace.ofPullbackSquare_spec B S hS f' g' f g h p
  obtain ⟨hqbase, j, hjt, hjx⟩ :=
    FiniteOpenSubspace.ofPullbackSquare_spec B S hS f' g' f g h q
  refine ⟨?_, j.inv ≫ l ≫ i.hom, ?_, ?_⟩
  · rw [hqbase, hpbase]
    exact (congrArg (fun m => m ≫ g.hom) ha).trans (Category.assoc _ _ _)
  · exact hl.of_iso j (Iso.refl _) i (Iso.refl _) (by exact hjt.symm) (by simp)
      (by exact (Category.comp_id _).trans (Category.id_comp _).symm) (by exact hit.symm)
  · apply (cancel_epi j.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hix, hjx]
    simpa only [Category.assoc] using congrArg (fun m => m ≫ f'.hom) hlx

end IsBaseChange

end FiniteOpenSubspace

namespace FinitePartPresheaf

/-- For a cartesian square `X' = X ×_Y Y'` with vertical morphisms `g' : X' ⟶ Y'` and
`f : X ⟶ Y`, the morphism of finite parts `(X'/Y')_fin ⟶ (X/Y)_fin` given on sections by
`AlgebraicGeometry.Space.FiniteOpenSubspace.ofPullbackSquare`. -/
noncomputable def mapOfPullbackSquare (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X' X Y' Y : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback f' g' f g) (P : FinitePartPresheaf B S hS g')
    (Q : FinitePartPresheaf B S hS f) : P.toFunctor ⟶ Q.toFunctor where
  app T := ↾fun p => (Q.sections T.unop).symm
    (FiniteOpenSubspace.ofPullbackSquare B S hS f' g' f g h (P.sections T.unop p))
  naturality := by
    intro T T' k
    ext p
    apply (Q.sections T'.unop).injective
    dsimp
    simp only [Equiv.apply_symm_apply]
    apply FiniteOpenSubspace.IsBaseChange.unique B S hS
      (FiniteOpenSubspace.IsBaseChange.ofPullbackSquare B S hS f' g' f g h
        (P.map_isBaseChange k.unop p))
    simpa only [Equiv.apply_symm_apply, Quiver.Hom.op_unop] using
      Q.map_isBaseChange k.unop ((Q.sections T.unop).symm
        (FiniteOpenSubspace.ofPullbackSquare B S hS f' g' f g h (P.sections T.unop p)))

/-- On sections, the morphism of finite parts is the transport of pairs along the cartesian
square. -/
theorem sections_mapOfPullbackSquare (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X' X Y' Y : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback f' g' f g) (P : FinitePartPresheaf B S hS g')
    (Q : FinitePartPresheaf B S hS f) (T : BigFppfOver B S hS)
    (p : P.toFunctor.obj (op T)) :
    Q.sections T ((mapOfPullbackSquare B S hS f' g' f g h P Q).app (op T) p) =
      FiniteOpenSubspace.ofPullbackSquare B S hS f' g' f g h (P.sections T p) :=
  Equiv.apply_symm_apply _ _

/-- The morphism of finite parts is compatible with the projections to `Y'` and to `Y`. -/
theorem mapOfPullbackSquare_baseMap (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X' X Y' Y : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback f' g' f g) (P : FinitePartPresheaf B S hS g')
    (Q : FinitePartPresheaf B S hS f) :
    mapOfPullbackSquare B S hS f' g' f g h P Q ≫ Q.baseMap = P.baseMap ≫ g.hom := by
  ext T p
  apply yonedaEquiv.symm.injective
  change yonedaEquiv.symm
      (Q.baseMap.app T ((mapOfPullbackSquare B S hS f' g' f g h P Q).app T p)) =
    yonedaEquiv.symm (g.hom.app T (P.baseMap.app T p))
  rw [Q.baseMap_spec, sections_mapOfPullbackSquare, ← yonedaEquiv_symm_naturality_right,
    P.baseMap_spec]
  exact (FiniteOpenSubspace.ofPullbackSquare_spec B S hS f' g' f g h _).1

/-- **Stacks 04QF.** Let `S` be a scheme and let a square `X' → X`, `X' → Y'`, `X → Y`,
`Y' → Y` be a fibre product square of algebraic spaces over `S`. Then the square
`(X'/Y')_fin → (X/Y)_fin`, `(X'/Y')_fin → Y'`, `(X/Y)_fin → Y`, `Y' → Y` is a fibre product
square of sheaves on the big fppf site of `S`. -/
@[stacks 04QF]
theorem isPullback_mapOfPullbackSquare (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X' X Y' Y : AlgebraicSpaces B S hS} (f' : X' ⟶ X) (g' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback f' g' f g) (P : FinitePartPresheaf B S hS g')
    (Q : FinitePartPresheaf B S hS f) :
    IsPullback (mapOfPullbackSquare B S hS f' g' f g h P Q) P.baseMap Q.baseMap g.hom := by
  classical
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (mapOfPullbackSquare_baseMap B S hS f' g' f g h P Q) T, ?_, ?_⟩
  · intro p q hpq
    apply (P.sections T.unop).injective
    apply FiniteOpenSubspace.ofPullbackSquare_injective B S hS f' g' f g h
    · rw [← P.baseMap_spec, ← P.baseMap_spec, hpq.2]
    · rw [← sections_mapOfPullbackSquare, ← sections_mapOfPullbackSquare, hpq.1]
  · intro q a ha
    let b : schemeSpace T.unop ⟶ Y' := ObjectProperty.homMk (yonedaEquiv.symm a)
    have hb : (Q.sections T.unop q).toBase.hom = b.hom ≫ g.hom := by
      rw [← Q.baseMap_spec]
      change yonedaEquiv.symm _ = yonedaEquiv.symm a ≫ g.hom
      rw [yonedaEquiv_symm_naturality_right, ha]
    obtain ⟨r, hr, hb'⟩ := FiniteOpenSubspace.exists_ofPullbackSquare_eq B S hS f' g' f g h
      (Q.sections T.unop q) b hb
    refine ⟨(P.sections T.unop).symm r, ?_, ?_⟩
    · apply (Q.sections T.unop).injective
      rw [sections_mapOfPullbackSquare, Equiv.apply_symm_apply, hr]
    · apply yonedaEquiv.symm.injective
      rw [P.baseMap_spec, Equiv.apply_symm_apply, hb']
      rfl

end FinitePartPresheaf

end AlgebraicGeometry.Space

end
