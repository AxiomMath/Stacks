module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectEssSurj

/-!
# Essential surjectivity of the comparison of Stacks Tag 0EXC, from the corner compatibility

Let `p` be a prime, let `A` be a ring in characteristic `p`, let `f ∈ A` and let `J ⊆ A` be an
ideal annihilated by `f ^ n`, so that the spectra of

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

form the almost blowup square of More on Flatness, Example 0EVG. The comparison functor of
Stacks Tag 0EXC

`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`

is `AlgebraicGeometry.colimVectComparison`; it is fully faithful by
`AlgebraicGeometry.colimVectComparison_faithful` and
`AlgebraicGeometry.colimVectComparison_full`. This file **reduces its essential surjectivity to
one equation between morphisms of vector bundles on the exceptional corner.**

That equation — the hypothesis of
`AlgebraicGeometry.colimVectComparison_essSurj_of_corner_compat` — says that the two
restrictions to the exceptional corner of the vector bundle
`AlgebraicGeometry.OneGeneratorSquare.betaGluedVect` glued from a finite projective
`A ⧸ (J ∩ fA)`-module `L`, compared by
`AlgebraicGeometry.OneGeneratorSquare.squareVectIso`, agree with the structural isomorphism of
the compatible pair attached to `L` by the canonical comparison of Stacks Tag 0D2J, after the
two `N`-th Frobenius twists of
`AlgebraicGeometry.OneGeneratorSquare.betaGluedVectCentreTwistIso` and
`…betaGluedVectModificationTwistIso` are pushed into the corner by
`AlgebraicGeometry.OneGeneratorSquare.ctrCornerSquareIter` and `…modCornerSquareIter`.

## Main definitions

* `AlgebraicGeometry.OneGeneratorSquare.vectOfFinProjCentre` and
  `…vectOfFinProjModification`: the two reductions of a finite projective `A ⧸ (J ∩ fA)`-module,
  read as vector bundles on the centre and on the modification.
* `AlgebraicGeometry.OneGeneratorSquare.finProjCornerIso`: the structural isomorphism over the
  exceptional corner which the compatible pair attached to such a module carries.

## Main results

* `CategoryTheory.EndoColim.objShiftIso_hom_naturality`: **the iterated stage shift of Stacks
  Tag 0EXA is natural.**
* `CategoryTheory.EndoColim.map_stageHomOf`: **the induced functor between colimit categories
  sends a morphism placed at a stage to its image placed at the same stage.**
* `CategoryTheory.EndoColim.chainCompatPure`: **two chains of stage shifts in one colimit
  category agree**, given the two identifications of their ingredients.
* `CategoryTheory.EndoColim.stageChainCompat`: the same comparison for the two chains obtained
  by transporting along two functors commuting with the endofunctors.
* `AlgebraicGeometry.colimVectComparison_essSurj_of_corner_compat`: **the comparison functor of
  Stacks Tag 0EXC is essentially surjective** as soon as the corner compatibility holds.

## Implementation notes

The witness is the object `(β^*(L^~), m + (m + k) + N)` of `colim_F Vect(Spec A)`, where `m` and
`k` are the stage and the level produced by
`AlgebraicGeometry.exists_presented_compatible_pair`, `L` is the finite projective
`A ⧸ (J ∩ fA)`-module produced by `AlgebraicGeometry.exists_finProj_of_vect_pair` for the
compatible pair so obtained, and `β` is the Frobenius factorisation. The isomorphism onto the
given object of the categorical pullback is built in two steps — first onto the compatible pair
placed at the stage `m`, then onto the given object — so that the categorical pullback's own
composition carries the associativity, and the two compatibility conditions stay short.

`CategoryTheory.EndoColim.chainCompatPure` is stated for morphisms of the colimit category with
all the objects left variable, and `CategoryTheory.EndoColim.stageChainCompat` is deduced from
it by one definitional check. The split is forced: in the transported form some object arguments
of the composites are spelled `(map F F' Φ α).obj (E, n)` and others `(Φ.obj E, n)`, and while
the two are definitionally equal, neither `rw` nor `simp` can match the associativity of
composition across such a junction. For the same reason the parenthesisation of
`CategoryTheory.EndoColim.chainCompatPure` is the one which
`CategoryTheory.EndoColim.map_stageHomOf` and
`CategoryTheory.EndoColim.map_objShiftIso_hom` produce, and the final assembly uses the
isomorphism `ϑ` of the compatible pair at the stage `m` introduced with its own spelling of the
two objects rather than the image of the restriction functor.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe v u u₂ u₃

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C']

/-! ### Naturality of the iterated stage shift -/

/-- **The iterated stage shift is natural.** The isomorphism `(F^k E, n + k) ≅ (E, n)` of Stacks
Tag 0EXA is natural in `E`, by `CategoryTheory.EndoColim.shiftStepHom_naturality'` at every
step. -/
lemma objShiftIso_hom_naturality (F : C ⥤ C) (n : ℕ) :
    ∀ (k : ℕ) {E G : C} (g : E ⟶ G),
      stageHomOf F (n + k) ((F.endoIter k).map g) ≫ (objShiftIso F n k G).hom =
        (objShiftIso F n k E).hom ≫ stageHomOf F n g
  | 0, E, G, g => by
      show stageHomOf F n g ≫ 𝟙 _ = 𝟙 _ ≫ stageHomOf F n g
      rw [Category.comp_id, Category.id_comp]
  | k + 1, E, G, g => by
      have ih := objShiftIso_hom_naturality F n k g
      have hstep := shiftStepHom_naturality' F (n + k) ((F.endoIter k).map g)
      rw [objShiftIso_succ, Iso.trans_hom, shiftStepIso_hom, objShiftIso_succ, Iso.trans_hom,
        shiftStepIso_hom]
      show stageHomOf F (n + k + 1) (F.map ((F.endoIter k).map g)) ≫
            shiftStepHom F (n + k) ((F.endoIter k).obj G) ≫ (objShiftIso F n k G).hom =
          (shiftStepHom F (n + k) ((F.endoIter k).obj E) ≫ (objShiftIso F n k E).hom) ≫
            stageHomOf F n g
      rw [← Category.assoc, hstep, Category.assoc, ih, Category.assoc]

/-! ### The induced functor on a morphism placed at a stage -/

/-- **The induced functor between the colimit categories sends a morphism placed at a stage to
its image placed at the same stage.** This is `CategoryTheory.EndoColim.map_map_of` at level
`0`, where the conjugation by the iterated comparison is undone by the naturality
`CategoryTheory.EndoColim.squareIter_hom_naturality` of that comparison. -/
lemma map_stageHomOf (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F') (n : ℕ)
    {E G : C} (g : E ⟶ G) :
    (map F F' Φ α).map (stageHomOf F n g) = stageHomOf F' n (Φ.map g) := by
  rw [stageHomOf, map_map_of F F' Φ α n 0 ((F.endoIter (n + 0)).map g), stageHomOf]
  refine congrArg (Hom.of 0) ?_
  rw [transportHom, ← Category.assoc, ← squareIter_hom_naturality F F' Φ α (n + 0) g,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### Two chains of stage shifts -/

/-- The stage functor on a composite of two morphisms of `C`, with a trailing morphism of
`colim_F C`. -/
lemma stageHomOf_comp_assoc (F : C ⥤ C) (n : ℕ) {E G H : C} (g : E ⟶ G) (h : G ⟶ H)
    {T : EndoColim F} (z : (⟨H, n⟩ : EndoColim F) ⟶ T) :
    stageHomOf F n g ≫ stageHomOf F n h ≫ z = stageHomOf F n (g ≫ h) ≫ z := by
  rw [← Category.assoc, ← stageHomOf_comp]

/-- **Two chains of stage shifts in a colimit category agree.** Each chain places two morphisms
of `C` at the stages `m + (m + k) + N` and `m + (m + k)` and then shifts the stage down by `N`
and by `m + k`; the two are compared by the morphism `hh` presented at the level `k`. The
hypotheses are the two identifications in `C` which make that comparison work: `H1` over the
higher stage, after `N` applications of `F₃`, and `H2` over the lower one. -/
theorem chainCompatPure {C₃ : Type u₃} [Category.{v} C₃] (F₃ : C₃ ⥤ C₃) (m k N : ℕ)
    {X P₀ P P₂ P' Z Q₀ Q Q₂ Q' : C₃}
    (a₁ : X ⟶ P₀) (a₂ : P₀ ⟶ (F₃.endoIter N).obj P)
    (d₁ : P ⟶ P₂) (d₂ : P₂ ⟶ (F₃.endoIter (m + k)).obj P')
    (hh : (F₃.endoIter (m + k)).obj P' ⟶ (F₃.endoIter (m + k)).obj Q')
    (sqv : X ⟶ Z) (b₁ : Z ⟶ Q₀) (b₂ : Q₀ ⟶ (F₃.endoIter N).obj Q)
    (e₁ : Q ⟶ Q₂) (e₂ : Q₂ ⟶ (F₃.endoIter (m + k)).obj Q') (ϑ : P ⟶ Q)
    (H1 : (a₁ ≫ a₂) ≫ (F₃.endoIter N).map ϑ = sqv ≫ b₁ ≫ b₂)
    (H2 : (d₁ ≫ d₂) ≫ hh = ϑ ≫ e₁ ≫ e₂) :
    (stageHomOf F₃ (m + (m + k) + N) a₁ ≫
          (stageHomOf F₃ (m + (m + k) + N) a₂ ≫
            (objShiftIso F₃ (m + (m + k)) N P).hom) ≫
            stageHomOf F₃ (m + (m + k)) d₁ ≫
              stageHomOf F₃ (m + (m + k)) d₂ ≫ (objShiftIso F₃ m (m + k) P').hom) ≫
        Hom.of k hh =
      stageHomOf F₃ (m + (m + k) + N) sqv ≫
        stageHomOf F₃ (m + (m + k) + N) b₁ ≫
          (stageHomOf F₃ (m + (m + k) + N) b₂ ≫
            (objShiftIso F₃ (m + (m + k)) N Q).hom) ≫
            stageHomOf F₃ (m + (m + k)) e₁ ≫
              stageHomOf F₃ (m + (m + k)) e₂ ≫ (objShiftIso F₃ m (m + k) Q').hom := by
  have t1 : (objShiftIso F₃ m (m + k) P').hom ≫ Hom.of k hh =
      stageHomOf F₃ (m + (m + k)) hh ≫ (objShiftIso F₃ m (m + k) Q').hom := by
    rw [← objShiftIso_conj F₃ m k hh, Iso.hom_inv_id_assoc]
  have t2 : (objShiftIso F₃ (m + (m + k)) N P).hom ≫ stageHomOf F₃ (m + (m + k)) ϑ =
      stageHomOf F₃ (m + (m + k) + N) ((F₃.endoIter N).map ϑ) ≫
        (objShiftIso F₃ (m + (m + k)) N Q).hom :=
    (objShiftIso_hom_naturality F₃ (m + (m + k)) N ϑ).symm
  simp only [Category.assoc]
  rw [t1, stageHomOf_comp_assoc, stageHomOf_comp_assoc, stageHomOf_comp_assoc, H2]
  simp only [stageHomOf_comp, Category.assoc]
  rw [reassoc_of% t2, stageHomOf_comp_assoc, stageHomOf_comp_assoc, H1]
  simp only [stageHomOf_comp, Category.assoc]

/-- **Two chains of stage shifts transported along two functors commuting with the
endofunctors.** The two chains live in `colim_{F₁} C₁` and in `colim_{F₂} C₂`; they are
transported into `colim_{F₃} C₃` by `CategoryTheory.EndoColim.map`, and are compared by the
morphism presented at the level `k` by the isomorphism `u` of `C₃`, conjugated by the iterated
comparisons `CategoryTheory.EndoColim.squareIter`. The two hypotheses are an identification over
the higher stage — which is where the comparison `θ` of the two objects of `C₃` enters — and one
over the lower stage. -/
theorem stageChainCompat {C₁ : Type u} [Category.{v} C₁] {C₂ : Type u₂} [Category.{v} C₂]
    {C₃ : Type u₃} [Category.{v} C₃]
    (F₁ : C₁ ⥤ C₁) (F₂ : C₂ ⥤ C₂) (F₃ : C₃ ⥤ C₃) (Φ₁ : C₁ ⥤ C₃) (Φ₂ : C₂ ⥤ C₃)
    (α₁ : F₁ ⋙ Φ₁ ≅ Φ₁ ⋙ F₃) (α₂ : F₂ ⋙ Φ₂ ≅ Φ₂ ⋙ F₃) (m k N : ℕ)
    {X₁ Zv E₁ : C₁} {X₂ Mv E₂ : C₂}
    (aT : X₁ ⟶ (F₁.endoIter N).obj Zv) (ε₂ : Zv ⟶ (F₁.endoIter (m + k)).obj E₁)
    (bT : X₂ ⟶ (F₂.endoIter N).obj Mv) (ε₁ : Mv ⟶ (F₂.endoIter (m + k)).obj E₂)
    (u : Φ₁.obj ((F₁.endoIter (m + k)).obj E₁) ≅ Φ₂.obj ((F₂.endoIter (m + k)).obj E₂))
    (θ : Φ₂.obj Mv ≅ Φ₁.obj Zv) (sqv : Φ₁.obj X₁ ⟶ Φ₂.obj X₂)
    (hw : Φ₁.map ε₂ ≫ u.hom = θ.inv ≫ Φ₂.map ε₁)
    (hfin : Φ₁.map aT ≫ (squareIter F₁ F₃ Φ₁ α₁ N Zv).inv ≫ (F₃.endoIter N).map θ.inv =
      sqv ≫ Φ₂.map bT ≫ (squareIter F₂ F₃ Φ₂ α₂ N Mv).inv) :
    ((map F₁ F₃ Φ₁ α₁).map (stageHomOf F₁ (m + (m + k) + N) aT ≫
              (objShiftIso F₁ (m + (m + k)) N Zv).hom ≫
                stageHomOf F₁ (m + (m + k)) ε₂ ≫ (objShiftIso F₁ m (m + k) E₁).hom) :
            (⟨Φ₁.obj X₁, m + (m + k) + N⟩ : EndoColim F₃) ⟶ ⟨Φ₁.obj E₁, m⟩) ≫
        (Hom.of k ((squareIter F₁ F₃ Φ₁ α₁ (m + k) E₁).hom ≫ u.hom ≫
            (squareIter F₂ F₃ Φ₂ α₂ (m + k) E₂).inv) :
          (⟨Φ₁.obj E₁, m⟩ : EndoColim F₃) ⟶ ⟨Φ₂.obj E₂, m⟩) =
      stageHomOf F₃ (m + (m + k) + N) sqv ≫
        ((map F₂ F₃ Φ₂ α₂).map (stageHomOf F₂ (m + (m + k) + N) bT ≫
            (objShiftIso F₂ (m + (m + k)) N Mv).hom ≫
              stageHomOf F₂ (m + (m + k)) ε₁ ≫ (objShiftIso F₂ m (m + k) E₂).hom) :
          (⟨Φ₂.obj X₂, m + (m + k) + N⟩ : EndoColim F₃) ⟶ ⟨Φ₂.obj E₂, m⟩) := by
  have H1 : (Φ₁.map aT ≫ (squareIter F₁ F₃ Φ₁ α₁ N Zv).inv) ≫ (F₃.endoIter N).map θ.inv =
      sqv ≫ Φ₂.map bT ≫ (squareIter F₂ F₃ Φ₂ α₂ N Mv).inv :=
    (Category.assoc _ _ _).trans hfin
  have H2 : (Φ₁.map ε₂ ≫ (squareIter F₁ F₃ Φ₁ α₁ (m + k) E₁).inv) ≫
        ((squareIter F₁ F₃ Φ₁ α₁ (m + k) E₁).hom ≫ u.hom ≫
          (squareIter F₂ F₃ Φ₂ α₂ (m + k) E₂).inv) =
      θ.inv ≫ Φ₂.map ε₁ ≫ (squareIter F₂ F₃ Φ₂ α₂ (m + k) E₂).inv := by
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hw, Category.assoc]
  simp only [CategoryTheory.Functor.map_comp, map_stageHomOf, map_objShiftIso_hom]
  exact chainCompatPure F₃ m k N (Φ₁.map aT) (squareIter F₁ F₃ Φ₁ α₁ N Zv).inv
    (Φ₁.map ε₂) (squareIter F₁ F₃ Φ₁ α₁ (m + k) E₁).inv
    ((squareIter F₁ F₃ Φ₁ α₁ (m + k) E₁).hom ≫ u.hom ≫
      (squareIter F₂ F₃ Φ₂ α₂ (m + k) E₂).inv)
    sqv (Φ₂.map bT) (squareIter F₂ F₃ Φ₂ α₂ N Mv).inv (Φ₂.map ε₁)
    (squareIter F₂ F₃ Φ₂ α₂ (m + k) E₂).inv θ.inv H1 H2

end CategoryTheory.EndoColim

namespace AlgebraicGeometry.OneGeneratorSquare

/-! ### The two reductions of a finite projective module -/

/-- The reduction to the centre of a finite projective `A ⧸ (J ∩ fA)`-module, as a vector bundle
on the centre `Spec (A ⧸ fA)`. -/
abbrev vectOfFinProjCentre (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))) :
    (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect :=
  (tildeVect (CommRingCat.of (A ⧸ Ideal.span {f}))).obj
    ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
      (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).obj L)

/-- The reduction to the modification of a finite projective `A ⧸ (J ∩ fA)`-module, as a vector
bundle on the modification `Spec (A ⧸ J)`. -/
abbrev vectOfFinProjModification (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))) :
    (Spec (CommRingCat.of (A ⧸ J))).Vect :=
  (tildeVect (CommRingCat.of (A ⧸ J))).obj
    ((FinProj.extendScalars (CommRingCat.ofHom (Ideal.Quotient.factor
      (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).obj L)

/-- **The structural isomorphism over the exceptional corner carried by the compatible pair
attached to a finite projective `A ⧸ (J ∩ fA)`-module**, namely the one of the canonical
comparison `MilnorPatching.OneGeneratorFrobenius.finProjComparison` of Stacks Tag 0D2J read on
vector bundles through the affine comparison. -/
abbrev finProjCornerIso (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))) :
    (vectModExc A f J).obj (vectOfFinProjModification A f J L) ≅
      (vectCtrExc A f J).obj (vectOfFinProjCentre A f J L) :=
  ((CategoricalPullback.mapCospan (tildeCornerCospanTransform A f J)).obj
    ((MilnorPatching.OneGeneratorFrobenius.finProjComparison A f J).obj L)).iso

end AlgebraicGeometry.OneGeneratorSquare

namespace AlgebraicGeometry

open OneGeneratorSquare

/-! ### Essential surjectivity -/

/-- **The comparison functor of Stacks Tag 0EXC is essentially surjective**, granted the
compatibility over the exceptional corner of the two restrictions of the vector bundle glued
from a finite projective `A ⧸ (J ∩ fA)`-module.

Given an object of the categorical pullback,
`AlgebraicGeometry.exists_presented_compatible_pair` presents it by a compatible pair of vector
bundles over the exceptional corner at a common stage `m` and a finite level `k`;
`AlgebraicGeometry.exists_finProj_of_vect_pair` produces a finite projective
`A ⧸ (J ∩ fA)`-module `L` whose attached compatible pair is isomorphic to it *in the categorical
pullback*; and `AlgebraicGeometry.OneGeneratorSquare.betaGluedVect` glues `L` to a vector bundle
on `Spec A` whose two restrictions are the `N`-th Frobenius twists of the two reductions of `L`.
The witness is that vector bundle placed at the stage `m + (m + k) + N`, and the hypothesis is
exactly what identifies the comparison of its two restrictions to the exceptional corner with
the structural isomorphism of the compatible pair. -/
theorem colimVectComparison_essSurj_of_corner_compat
    (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N)
    (hcompat : ∀ L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))),
      (vectCtrExc A f J).map (betaGluedVectCentreTwistIso A f J n hann p hp N hN L).hom ≫
          (ctrCornerSquareIter A f J p hp N (vectOfFinProjCentre A f J L)).inv =
        (squareVectIso A f J).inv.app (betaGluedVect A f J n hann p hp N hN L) ≫
          (vectModExc A f J).map
              (betaGluedVectModificationTwistIso A f J n hann p hp N hN L).hom ≫
            (modCornerSquareIter A f J p hp N (vectOfFinProjModification A f J L)).inv ≫
              ((frobExc A f J p hp).endoIter N).map (finProjCornerIso A f J L).hom) :
    (colimVectComparison A f J p hp).EssSurj where
  mem_essImage Y := by
    obtain ⟨m, k, E₁, E₂, σ₁, σ₂, u, hu⟩ := exists_presented_compatible_pair A f J p hp Y
    obtain ⟨L, ⟨e⟩⟩ := exists_finProj_of_vect_pair A f J
      { fst := ((frobMod A J p hp).endoIter (m + k)).obj E₂
        snd := ((frobCtr A f p hp).endoIter (m + k)).obj E₁
        iso := u.symm }
    obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : vectOfFinProjModification A f J L ≅
        ((frobMod A J p hp).endoIter (m + k)).obj E₂, ε₁.hom = e.hom.fst :=
      ⟨(CategoricalPullback.π₁ _ _).mapIso e, rfl⟩
    obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : vectOfFinProjCentre A f J L ≅
        ((frobCtr A f p hp).endoIter (m + k)).obj E₁, ε₂.hom = e.hom.snd :=
      ⟨(CategoricalPullback.π₂ _ _).mapIso e, rfl⟩
    have hw : (vectModExc A f J).map ε₁.hom ≫ u.inv =
        (finProjCornerIso A f J L).hom ≫ (vectCtrExc A f J).map ε₂.hom := by
      rw [hε₁, hε₂]; exact e.hom.w
    have hw' : (vectCtrExc A f J).map ε₂.hom ≫ u.hom =
        (finProjCornerIso A f J L).inv ≫ (vectModExc A f J).map ε₁.hom := by
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hw, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    have hfin' : (vectCtrExc A f J).map
            (betaGluedVectCentreTwistIso A f J n hann p hp N hN L).hom ≫
          (ctrCornerSquareIter A f J p hp N (vectOfFinProjCentre A f J L)).inv ≫
            ((frobExc A f J p hp).endoIter N).map (finProjCornerIso A f J L).inv =
        (squareVectIso A f J).inv.app (betaGluedVect A f J n hann p hp N hN L) ≫
          (vectModExc A f J).map
              (betaGluedVectModificationTwistIso A f J n hann p hp N hN L).hom ≫
            (modCornerSquareIter A f J p hp N (vectOfFinProjModification A f J L)).inv := by
      rw [← Category.assoc, hcompat L, Category.assoc, Category.assoc, Category.assoc,
        ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.comp_id]
    have key := EndoColim.stageChainCompat (frobCtr A f p hp) (frobMod A J p hp)
      (frobExc A f J p hp) (vectCtrExc A f J) (vectModExc A f J)
      (frobVectIsoCtrExc A f J p hp) (frobVectIsoModExc A f J p hp) m k N
      (betaGluedVectCentreTwistIso A f J n hann p hp N hN L).hom ε₂.hom
      (betaGluedVectModificationTwistIso A f J n hann p hp N hN L).hom ε₁.hom u
      (finProjCornerIso A f J L)
      ((squareVectIso A f J).inv.app (betaGluedVect A f J n hann p hp N hN L)) hw' hfin'
    have hXiso : ((colimVectComparison A f J p hp).obj
          ⟨betaGluedVect A f J n hann p hp N hN L, m + (m + k) + N⟩).iso.hom =
        EndoColim.stageHomOf (frobExc A f J p hp) (m + (m + k) + N)
          ((squareVectIso A f J).inv.app (betaGluedVect A f J n hann p hp N hN L)) :=
      squareColimVectIso_hom_app A f J p hp (betaGluedVect A f J n hann p hp N hN L)
        (m + (m + k) + N)
    obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : (centreToExceptional A f J p hp).obj
          (⟨E₁, m⟩ : colimVectCentre A f p hp) ≅
        (modificationToExceptional A f J p hp).obj (⟨E₂, m⟩ : colimVectModification A J p hp),
        ϑ.hom = EndoColim.Hom.of k ((ctrCornerSquareIter A f J p hp (m + k) E₁).hom ≫ u.hom ≫
          (modCornerSquareIter A f J p hp (m + k) E₂).inv) :=
      ⟨(centreToExceptional A f J p hp).mapIso σ₁ ≪≫ Y.iso ≪≫
        ((modificationToExceptional A f J p hp).mapIso σ₂).symm, hu⟩
    have hu' : (centreToExceptional A f J p hp).map σ₁.hom ≫ Y.iso.hom =
        ϑ.hom ≫ (modificationToExceptional A f J p hp).map σ₂.hom :=
      (Iso.comp_inv_eq ((modificationToExceptional A f J p hp).mapIso σ₂)).mp
        ((Category.assoc _ _ _).trans (hu.trans hϑ.symm))
    refine ⟨⟨betaGluedVect A f J n hann p hp N hN L, m + (m + k) + N⟩,
      ⟨CategoricalPullback.mkIso
          (y := { fst := (⟨E₁, m⟩ : colimVectCentre A f p hp)
                  snd := (⟨E₂, m⟩ : colimVectModification A J p hp)
                  iso := ϑ })
          ((EndoColim.stageFunctor (frobCtr A f p hp) (m + (m + k) + N)).mapIso
                (betaGluedVectCentreTwistIso A f J n hann p hp N hN L) ≪≫
              EndoColim.objShiftIso (frobCtr A f p hp) (m + (m + k)) N
                  (vectOfFinProjCentre A f J L) ≪≫
                (EndoColim.stageFunctor (frobCtr A f p hp) (m + (m + k))).mapIso ε₂ ≪≫
                  EndoColim.objShiftIso (frobCtr A f p hp) m (m + k) E₁)
          ((EndoColim.stageFunctor (frobMod A J p hp) (m + (m + k) + N)).mapIso
                (betaGluedVectModificationTwistIso A f J n hann p hp N hN L) ≪≫
              EndoColim.objShiftIso (frobMod A J p hp) (m + (m + k)) N
                  (vectOfFinProjModification A f J L) ≪≫
                (EndoColim.stageFunctor (frobMod A J p hp) (m + (m + k))).mapIso ε₁ ≪≫
                  EndoColim.objShiftIso (frobMod A J p hp) m (m + k) E₂) ?_ ≪≫
        CategoricalPullback.mkIso
          (x := { fst := (⟨E₁, m⟩ : colimVectCentre A f p hp)
                  snd := (⟨E₂, m⟩ : colimVectModification A J p hp)
                  iso := ϑ }) σ₁ σ₂ hu'⟩⟩
    rw [hϑ, hXiso]
    exact key

end AlgebraicGeometry

end
