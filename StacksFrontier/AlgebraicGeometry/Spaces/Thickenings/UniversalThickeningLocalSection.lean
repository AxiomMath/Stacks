module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningOfFormallyUnramified

/-!
# An étale-local section of the canonical morphism of universal first-order thickenings

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be formally unramified morphisms of algebraic spaces over a
scheme `S` sitting in a commutative triangle `i ≫ g = j` with `g : X ⟶ Y`, let `Z ⊂ Z'` be a
universal first-order thickening of `Z` over `X` and `Z ⊂ Z''` one of `Z` over `Y`, and let
`k : Z' ⟶ Z''` be the canonical morphism between them.  If `g` is formally smooth, then `k`
admits a section over every affine étale chart of `Z''`, and hence over a covering family of
affine étale charts of any étale chart of `Z''`.

## Main definitions

* `AlgebraicGeometry.Space.universalThickeningSourceMap`: the identification of the smaller
  space of `Z ⊂ Z'` with that of `Z ⊂ Z''`, obtained from the two identifications with `Z`.
* `AlgebraicGeometry.Space.universalThickeningComparison`: the canonical morphism
  `k : Z' ⟶ Z''` of the triangle, that is the morphism of Stacks 060A for the square built
  from `g` and that identification.

## Main results

* `AlgebraicGeometry.Space.universalThickeningSourceMap_comm`: the square built from `g` and
  the identification of the two smaller spaces commutes, which is what makes the canonical
  morphism available.
* `AlgebraicGeometry.Space.exists_lift_yoneda_of_formallySmooth'`: formal smoothness of
  Stacks 049S part (1), read on transformations out of representable presheaves rather than on
  sections.  This is the shape in which every consumer of the lifting property on an affine
  étale chart uses it, and it is stated here because this is the first file that needs it.
* `AlgebraicGeometry.Space.exists_local_section_of_formallySmooth`: over an affine étale chart
  of `Z''` the canonical morphism `k` has a section which restricts to the inclusion
  `Z ⟶ Z'` on the induced chart of `Z`.
* `AlgebraicGeometry.Space.exists_local_section_cover_of_formallySmooth`: every étale chart of
  `Z''` is covered by affine étale charts carrying such a section.

## Implementation notes

The argument is the one of Stacks 06BK.  On an affine étale chart `V ⟶ Z''` the inclusion
`Z ⊂ Z''` restricts to a square-zero closed immersion `U ⟶ V` of affine objects of the site,
by `AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`, so formal
smoothness of `g` produces `h : V ⟶ X` agreeing with `i` on `U` and lying over the restriction
of `Z'' ⟶ Y`.  The universal property of `Z ⊂ Z'` turns `h` into a morphism `s : V ⟶ Z'`, and
the uniqueness half of the universal property of `Z ⊂ Z''` — applied to the two morphisms
`s ≫ k` and `V ⟶ Z''`, which solve the same lifting problem — identifies `s ≫ k` with the
chart itself.  So `s` is a section of `k` over `V`.

The lifting problem fed to the universal property of `Z ⊂ Z'` is set up on the inverse image
`Z ×_{Z''} V ⊂ V` rather than on `U ⊂ V`: the universal property speaks of first-order
thickenings of algebraic spaces given by subfunctors, and the inverse image is one by
`AlgebraicGeometry.Space.isFirstOrderThickening_preimage`.  The two descriptions of the chart
of `Z` are identified by the isomorphism of the two cartesian squares over the cospan
`(V ⟶ Z'', Z ⊂ Z'')`, one of which is `CategoryTheory.Subfunctor.isPullback_preimage`.

## References

* [Stacks Project, Tag 06BK](https://stacks.math.columbia.edu/tag/06BK)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The canonical morphism of the two universal thickenings of one source -/

/-- For two universal first-order thickenings `Z ⊂ Z'` and `Z ⊂ Z''` of the same algebraic
space `Z`, the identification of their smaller spaces obtained by composing the two
identifications with `Z`. -/
def universalThickeningSourceMap {i : Z ⟶ X} {j : Z ⟶ Y}
    (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    ti.sub.toFunctor ⟶ tj.sub.toFunctor :=
  ti.sourceIso.inv ≫ tj.sourceIso.hom

/-- Taking underlying morphisms of an equation between a composite and a morphism. -/
private theorem hom_comp_eq_hom {P Q R : AlgebraicSpaces B S hS} {f : P ⟶ Q} {g : Q ⟶ R}
    {h : P ⟶ R} (e : f ≫ g = h) : f.hom ≫ g.hom = h.hom :=
  congrArg (fun m : P ⟶ R => m.hom) e

/-- The identification of the two smaller spaces is the inverse of the first identification
with `Z` followed by the second.  This is the defining equation, stated so that consumers may
rewrite with it rather than unfold the definition. -/
theorem universalThickeningSourceMap_eq {i : Z ⟶ X} {j : Z ⟶ Y}
    (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    universalThickeningSourceMap B S hS ti tj = ti.sourceIso.inv ≫ tj.sourceIso.hom :=
  rfl

/-- For a commutative triangle `i ≫ g = j`, the square of Stacks 060A built from `g` and the
identification of the smaller space of a universal first-order thickening of `i` with that of
one of `j` commutes: both composites are `Z ⟶ X ⟶ Y` read through the identifications. -/
theorem universalThickeningSourceMap_comm (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    ti.sub.ι ≫ ti.toBase.hom ≫ g.hom =
      universalThickeningSourceMap B S hS ti tj ≫ tj.sub.ι ≫ tj.toBase.hom := by
  rw [universalThickeningSourceMap_eq, Category.assoc, tj.sourceIso_ι_toBase,
    ← hom_comp_eq_hom B S hS hij,
    ← ti.sourceIso_ι_toBase]
  simp

/-- **Stacks 06BK, the canonical morphism `Z' ⟶ Z''`.** For a commutative triangle
`i ≫ g = j` and universal first-order thickenings `Z ⊂ Z'` of `Z` over `X` and `Z ⊂ Z''` of
`Z` over `Y`, the morphism of Stacks 060A for the square built from `g` and the identification
of the two smaller spaces. -/
noncomputable def universalThickeningComparison (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    ti.ambient ⟶ tj.ambient :=
  universalThickeningMap B S hS g (universalThickeningSourceMap B S hS ti tj)
    ti.isUniversal tj.isUniversal (universalThickeningSourceMap_comm B S hS g hij ti tj)

/-- The canonical morphism `Z' ⟶ Z''` restricts on the smaller spaces to the identification
of the smaller space of `Z ⊂ Z'` with that of `Z ⊂ Z''`. -/
theorem universalThickeningComparison_restrict (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    ti.sub.ι ≫ (universalThickeningComparison B S hS g hij ti tj).hom =
      universalThickeningSourceMap B S hS ti tj ≫ tj.sub.ι :=
  universalThickeningMap_restrict B S hS g (universalThickeningSourceMap B S hS ti tj)
    ti.isUniversal tj.isUniversal (universalThickeningSourceMap_comm B S hS g hij ti tj)

/-- The canonical morphism `Z' ⟶ Z''` lies over `Y`: composing it with `Z'' ⟶ Y` gives
`Z' ⟶ X ⟶ Y`. -/
theorem universalThickeningComparison_over (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    universalThickeningComparison B S hS g hij ti tj ≫ tj.toBase = ti.toBase ≫ g :=
  universalThickeningMap_over B S hS g (universalThickeningSourceMap B S hS ti tj)
    ti.isUniversal tj.isUniversal (universalThickeningSourceMap_comm B S hS g hij ti tj)

/-! ### Lifting across a square-zero closed immersion of affine charts -/

/-- Formal smoothness, read on morphisms out of representable presheaves: a commutative square
over a square-zero closed immersion of affine objects of the site admits a dotted arrow.

This is the definition of Stacks 049S part (1) transported along `CategoryTheory.yonedaEquiv`,
and it is the shape in which the lifting property is applied on an affine étale chart. -/
theorem exists_lift_yoneda_of_formallySmooth'
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G} (ha : FormallySmooth a)
    {P Q : BigFppfOver B S hS} {t : P ⟶ Q} (ht : IsSquareZeroClosedImmersion B S hS t)
    (hP : IsAffine ((BigFppfOver.toScheme B S hS).obj P))
    (hQ : IsAffine ((BigFppfOver.toScheme B S hS).obj Q))
    (x : yoneda.obj P ⟶ F) (y : yoneda.obj Q ⟶ G) (hsq : x ≫ a = yoneda.map t ≫ y) :
    ∃ z : yoneda.obj Q ⟶ F, yoneda.map t ≫ z = x ∧ z ≫ a = y := by
  obtain ⟨z, hz₁, hz₂⟩ := ha P Q hP hQ t ht (yonedaEquiv x) (yonedaEquiv y)
    (calc a.app (op P) (yonedaEquiv x) = yonedaEquiv (x ≫ a) := (yonedaEquiv_comp _ _).symm
      _ = yonedaEquiv (yoneda.map t ≫ y) := congrArg _ hsq
      _ = G.map t.op (yonedaEquiv y) := (yonedaEquiv_naturality _ _).symm)
  refine ⟨yonedaEquiv.symm z, ?_, ?_⟩
  · rw [yonedaEquiv_symm_naturality_left, hz₁, Equiv.symm_apply_apply]
  · rw [yonedaEquiv_symm_naturality_right, hz₂, Equiv.symm_apply_apply]

/-- The private form of `exists_lift_yoneda_of_formallySmooth'`. -/
private alias exists_lift_yoneda_of_formallySmooth := exists_lift_yoneda_of_formallySmooth'

/-! ### The étale-local section -/

/-- **Stacks 06BK: formal smoothness gives an étale-local section of the canonical morphism of
universal first-order thickenings.** Let `i : Z ⟶ X` and `j : Z ⟶ Y` sit in a commutative
triangle `i ≫ g = j` with `g` formally smooth, let `Z ⊂ Z'` be a universal first-order
thickening of `Z` over `X` and `Z ⊂ Z''` one of `Z` over `Y`, and let `V ⟶ Z''` be an étale
chart with `V` affine.  Then there is `s : V ⟶ Z'` which restricts on `Z ×_{Z''} V` to the
inclusion `Z ⟶ Z'` and satisfies `s ≫ k = (V ⟶ Z'')` for the canonical morphism `k`.

Formal smoothness of `g` lifts the chart of `Z` to `h : V ⟶ X` over `Z'' ⟶ Y`, the universal
property of `Z ⊂ Z'` turns `h` into `s`, and the uniqueness half of the universal property of
`Z ⊂ Z''` identifies `s ≫ k` with the chart. -/
theorem exists_local_section_of_formallySmooth (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) (hg : FormallySmooth g.hom)
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ tj.ambient.obj) (hv : IsEtale B S hS v)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    ∃ s : yoneda.obj V ⟶ ti.ambient.obj,
      (tj.sub.preimage v).ι ≫ s =
          tj.sub.fromPreimage v ≫ tj.sourceIso.inv ≫ ti.sourceIso.hom ≫ ti.sub.ι ∧
        s ≫ (universalThickeningComparison B S hS g hij ti tj).hom = v := by
  -- The chart of `Z ⊂ Z''` over `V`: a square-zero closed immersion of affine objects.
  obtain ⟨U, t, u, hpb, hUaff, -, ht⟩ :=
    exists_squareZeroChart_of_isFirstOrderThickening B S hS tj.isUniversal.firstOrder V v hv hV
  have hij' := hom_comp_eq_hom B S hS hij
  have hj : tj.sourceIso.inv ≫ j.hom = tj.sub.ι ≫ tj.toBase.hom := by
    rw [← tj.sourceIso_ι_toBase, Iso.inv_hom_id_assoc]
  -- Formal smoothness of `g` lifts the chart of `Z` to `X`.
  obtain ⟨h, hh₁, hh₂⟩ := exists_lift_yoneda_of_formallySmooth' B S hS hg ht hUaff hV
    (u ≫ tj.sourceIso.inv ≫ i.hom) (v ≫ tj.toBase.hom)
    (by simp only [Category.assoc, hij', hj, reassoc_of% hpb.w])
  -- The chart of `Z` as the inverse image of `Z` in `V`, a first-order thickening of `V`.
  have halg : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hthick : IsFirstOrderThickening B S hS
      (⟨yoneda.obj V, halg⟩ : AlgebraicSpaces B S hS) (tj.sub.preimage v) :=
    isFirstOrderThickening_preimage B S hS tj.sub
      (ObjectProperty.homMk v : (⟨yoneda.obj V, halg⟩ : AlgebraicSpaces B S hS) ⟶ tj.ambient)
      tj.isUniversal.firstOrder
  -- The two descriptions of that chart agree.
  have hpre : IsPullback (tj.sub.preimage v).ι (tj.sub.fromPreimage v) v tj.sub.ι :=
    (Subfunctor.isPullback_preimage v tj.sub).flip
  obtain ⟨e, he₁, he₂⟩ : ∃ e : (tj.sub.preimage v).toFunctor ≅ yoneda.obj U,
      e.hom ≫ yoneda.map t = (tj.sub.preimage v).ι ∧
        e.hom ≫ u = tj.sub.fromPreimage v :=
    ⟨hpre.isoIsPullback _ _ hpb, hpre.isoIsPullback_hom_fst _ _ hpb,
      hpre.isoIsPullback_hom_snd _ _ hpb⟩
  -- The universal property of `Z ⊂ Z'` turns the lift into a morphism `V ⟶ Z'`.
  have hb : (tj.sub.preimage v).ι ≫ h =
      (tj.sub.fromPreimage v ≫ tj.sourceIso.inv ≫ ti.sourceIso.hom) ≫
        ti.sub.ι ≫ ti.toBase.hom := by
    rw [← he₁, ← he₂]
    simp only [Category.assoc, hh₁, ti.sourceIso_ι_toBase]
  obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ := ti.isUniversal.existsUnique_lift
    (T' := (⟨yoneda.obj V, halg⟩ : AlgebraicSpaces B S hS)) (tj.sub.preimage v) hthick
    (tj.sub.fromPreimage v ≫ tj.sourceIso.inv ≫ ti.sourceIso.hom) h hb
  -- The uniqueness half of the universal property of `Z ⊂ Z''` identifies `s ≫ k` with `v`.
  obtain ⟨c, -, huniq⟩ := tj.isUniversal.existsUnique_lift
    (T' := (⟨yoneda.obj V, halg⟩ : AlgebraicSpaces B S hS)) (tj.sub.preimage v) hthick
    (tj.sub.fromPreimage v) (v ≫ tj.toBase.hom)
    (by rw [← Category.assoc, ← Category.assoc, Subfunctor.fromPreimage_ι])
  have hover : (universalThickeningComparison B S hS g hij ti tj).hom ≫ tj.toBase.hom =
      ti.toBase.hom ≫ g.hom :=
    hom_comp_eq_hom B S hS (universalThickeningComparison_over B S hS g hij ti tj)
  refine ⟨s, by simp only [hs₁, Category.assoc], (huniq _ ⟨?_, ?_⟩).trans
    (huniq v ⟨(Subfunctor.fromPreimage_ι tj.sub v).symm, rfl⟩).symm⟩
  · rw [← Category.assoc, hs₁]
    simp only [Category.assoc, universalThickeningComparison_restrict,
      universalThickeningSourceMap_eq, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, hover, ← Category.assoc, hs₂, hh₂]

/-- **Stacks 06BK, in a covering form.** Under the hypotheses of
`AlgebraicGeometry.Space.exists_local_section_of_formallySmooth`, an arbitrary étale chart
`V ⟶ Z''` is covered by affine étale charts over each of which the canonical morphism
`k : Z' ⟶ Z''` admits a section restricting to `Z ⟶ Z'`.

The covering family is the one of
`AlgebraicGeometry.Space.exists_squareZeroChart_cover_of_isFirstOrderThickening`, and the
affine case applies to each of its members. -/
theorem exists_local_section_cover_of_formallySmooth (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) (hg : FormallySmooth g.hom)
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ tj.ambient.obj) (hv : IsEtale B S hS v) :
    ∃ (I : Type u) (V' : I → BigFppfOver B S hS) (π : ∀ k, V' k ⟶ V)
        (s : ∀ k, yoneda.obj (V' k) ⟶ ti.ambient.obj),
      Sieve.generate (Presieve.ofArrows V' π) ∈ BigFppfOver.topology B S hS V ∧
        (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (V' k))) ∧
        (∀ k, (tj.sub.preimage (yoneda.map (π k) ≫ v)).ι ≫ s k =
            tj.sub.fromPreimage (yoneda.map (π k) ≫ v) ≫ tj.sourceIso.inv ≫
              ti.sourceIso.hom ≫ ti.sub.ι) ∧
          ∀ k, s k ≫ (universalThickeningComparison B S hS g hij ti tj).hom =
            yoneda.map (π k) ≫ v := by
  obtain ⟨I, V', π, -, -, -, hcov, hV'aff, -, hchart, -, -, -⟩ :=
    exists_squareZeroChart_cover_of_isFirstOrderThickening B S hS tj.isUniversal.firstOrder V v hv
  choose s hs₁ hs₂ using fun k => exists_local_section_of_formallySmooth B S hS g hij ti tj hg
    (V' k) (yoneda.map (π k) ≫ v) (hchart k) (hV'aff k)
  exact ⟨I, V', π, s, hcov, hV'aff, hs₁, hs₂⟩

end AlgebraicGeometry.Space

end
