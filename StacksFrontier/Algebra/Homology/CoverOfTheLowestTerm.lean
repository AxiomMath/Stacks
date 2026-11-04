module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import StacksFrontier.Algebra.Homology.HomologyOfADegreewiseEpi

/-!
# Replacing one term of a complex by a cover of it

Let `K` be a homological complex in an abelian category, let `n` be a degree into which the
differential of `K` vanishes, and let `q : A ⟶ K^n` be any morphism. This file builds the complex

`… ⟶ 0 ⟶ A ⟶ K^{n+1} ⟶ K^{n+2} ⟶ …`

which agrees with `K` away from degree `n`, carries `A` in degree `n`, and comes with a morphism
to `K` which is the identity away from degree `n` and `q` in degree `n`.

The construction is a pullback, which is what makes the differentials and the morphism to `K`
come for free. The vanishing of the differential into degree `n` makes the projection of `K` onto
its degree-`n` term a morphism of complexes `π : K ⟶ K^n[-n]` to the single complex on `K^n`;
`q` is a morphism of single complexes `A[-n] ⟶ K^n[-n]`; and the complex above is the pullback of
`π` along it, computed degreewise because the evaluation functors preserve limits. In the degrees
`i ≠ n` the single complexes vanish, so the projection to `K` is an isomorphism there, and in
degree `n` the morphism `π` is invertible, so the projection to the single complex `A[-n]` is an
isomorphism and the projection to `K` is `q`.

When `q` is an epimorphism, the resulting morphism of complexes is a degreewise epimorphism which
is invertible away from degree `n`; its effect on cohomology is read off with the three statements
of `StacksFrontier.Algebra.Homology.HomologyOfADegreewiseEpi`.

The use this is made for is the last step of the inductive proof of the first assertion of
Stacks 0FPV: a complex approximating an object of `D(O)` from a degree `n` is strictly perfect in
every degree but `n`, where it is only finitely generated, and a surjection onto its degree-`n`
term from a finite free module turns it into a strictly perfect complex with the same
approximation property.

## Main definitions

* `HomologicalComplex.toBottomSingle`: the projection `K ⟶ K^n[-n]`.
* `HomologicalComplex.bottomCover`: the complex above.
* `HomologicalComplex.bottomCoverι`: its morphism to `K`.
* `HomologicalComplex.bottomCoverXIsoOfNe` and `HomologicalComplex.bottomCoverXIsoSelf`: its
  degree-`i` term is `K^i` for `i ≠ n`, and `A` in degree `n`.

## Main results

* `HomologicalComplex.isIso_bottomCoverι_f`: the morphism to `K` is invertible away from degree
  `n`.
* `HomologicalComplex.epi_bottomCoverι_f`: in degree `n` it is an epimorphism as soon as `q` is.
* `HomologicalComplex.isIso_homologyMap_bottomCoverι` and
  `HomologicalComplex.epi_homologyMap_bottomCoverι`: it is an isomorphism on cohomology in every
  degree `i` with `i ≠ n` and `c.next i ≠ n`, and an epimorphism on cohomology whenever only
  `c.next i ≠ n`.

## Implementation notes

The complex is a pullback in the category of complexes rather than a complex assembled by hand
from a case distinction on the degree. The two carry the same information, but the pullback needs
no `eqToHom` to transport a term along `i = n` and no three-way case distinction to check
`d ≫ d = 0`: both come from the universal property. The price is one isomorphism per degree,
`HomologicalComplex.bottomCoverXIso`, which is Mathlib's
`CategoryTheory.Limits.PreservesPullback.iso` for the evaluation functor; the degreewise
statements are read through it.

No hypothesis of boundedness or of vanishing below `n` is needed, and `q` is not assumed to be an
epimorphism except where that is stated: the vanishing `hd` of the differential into degree `n`
is the only hypothesis the construction has, and it is exactly what makes the projection onto the
degree-`n` term a morphism of complexes.
-/

@[expose] public noncomputable section

open CategoryTheory Category CategoryTheory.Limits

namespace HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} [DecidableEq ι]
  {c : ComplexShape ι} (K : HomologicalComplex C c) (n : ι)

/-- **The degree-`n` term of `K`, read as a complex concentrated in degree `n`.** -/
abbrev bottomSingle : HomologicalComplex C c := (single C c n).obj (K.X n)

variable (hd : ∀ i, c.Rel i n → K.d i n = 0) {A : C} (q : A ⟶ K.X n)

/-- **The projection of `K` onto its degree-`n` term.** It is a morphism of complexes because
the differential of `K` into degree `n` vanishes. -/
def toBottomSingle : K ⟶ K.bottomSingle n :=
  mkHomToSingle (𝟙 (K.X n)) (fun i hi => by rw [comp_id, hd i hi])

/-- In degree `n` the projection `toBottomSingle` is the inverse of the identification of the
degree-`n` term of the single complex with `K.X n`. -/
@[simp]
theorem toBottomSingle_f_self :
    (K.toBottomSingle n hd).f n = (singleObjXSelf c n (K.X n)).inv := by
  rw [toBottomSingle, mkHomToSingle_f, id_comp]

/-- The degree-`n` component of `toBottomSingle` is an isomorphism. -/
instance isIso_toBottomSingle_f_self : IsIso ((K.toBottomSingle n hd).f n) := by
  rw [toBottomSingle_f_self]
  infer_instance

/-- **`q` read as a morphism of complexes concentrated in degree `n`.** -/
abbrev coverSingleMap : (single C c n).obj A ⟶ K.bottomSingle n := (single C c n).map q

/-- If `q` is an epimorphism, so is the degree-`n` component of `coverSingleMap`. -/
theorem epi_coverSingleMap_f_self [Epi q] : Epi ((coverSingleMap K n q).f n) := by
  rw [single_map_f_self]
  exact epi_comp _ _

/-- Away from degree `n` the components of `coverSingleMap` are isomorphisms between zero
objects. -/
theorem isIso_coverSingleMap_f (i : ι) (hi : i ≠ n) : IsIso ((coverSingleMap K n q).f i) :=
  ⟨0, (isZero_single_obj_X c n A i hi).eq_of_src _ _,
    (isZero_single_obj_X c n (K.X n) i hi).eq_of_src _ _⟩

/-- **The complex `K` with its degree-`n` term replaced by `A`.** It is the pullback of the
projection of `K` onto its degree-`n` term along `q`, so it agrees with `K` away from degree `n`
and carries `A` in degree `n`. -/
abbrev bottomCover : HomologicalComplex C c :=
  pullback (K.toBottomSingle n hd) (coverSingleMap K n q)

/-- **The morphism `bottomCover ⟶ K`.** It is an isomorphism away from degree `n` and `q` in
degree `n`. -/
abbrev bottomCoverι : K.bottomCover n hd q ⟶ K := pullback.fst _ _

/-- The degree-`i` term of `bottomCover` is the pullback of the degree-`i` components, because
evaluation in degree `i` preserves limits. -/
def bottomCoverXIso (i : ι) :
    (K.bottomCover n hd q).X i ≅
      pullback ((K.toBottomSingle n hd).f i) ((coverSingleMap K n q).f i) :=
  PreservesPullback.iso (eval C c i) _ _

/-- `bottomCoverXIso` followed by the first projection is the degree-`i` component of
`bottomCoverι`. -/
@[reassoc (attr := simp)]
theorem bottomCoverXIso_hom_fst (i : ι) :
    (K.bottomCoverXIso n hd q i).hom ≫ pullback.fst _ _ = (K.bottomCoverι n hd q).f i :=
  PreservesPullback.iso_hom_fst _ _ _

/-- `bottomCoverXIso` followed by the second projection is the degree-`i` component of the
second projection of `bottomCover`. -/
@[reassoc (attr := simp)]
theorem bottomCoverXIso_hom_snd (i : ι) :
    (K.bottomCoverXIso n hd q i).hom ≫ pullback.snd _ _ =
      (pullback.snd (K.toBottomSingle n hd) (coverSingleMap K n q)).f i :=
  PreservesPullback.iso_hom_snd _ _ _

/-- **Away from degree `n` the morphism to `K` is an isomorphism**: there the two single
complexes vanish, so the pullback is `K` itself. -/
theorem isIso_bottomCoverι_f (i : ι) (hi : i ≠ n) : IsIso ((K.bottomCoverι n hd q).f i) := by
  rw [← bottomCoverXIso_hom_fst K n hd q i]
  have := isIso_coverSingleMap_f K n q i hi
  have : IsIso (pullback.fst ((K.toBottomSingle n hd).f i) ((coverSingleMap K n q).f i)) :=
    pullback_fst_iso_of_right_iso _ _
  infer_instance

/-- **In degree `n` the projection to the single complex on `A` is an isomorphism**: there the
projection of `K` onto its degree-`n` term is invertible. -/
instance isIso_bottomCover_snd_f_self :
    IsIso ((pullback.snd (K.toBottomSingle n hd) (coverSingleMap K n q)).f n) := by
  rw [← bottomCoverXIso_hom_snd K n hd q n]
  have : IsIso (pullback.snd ((K.toBottomSingle n hd).f n) ((coverSingleMap K n q).f n)) :=
    pullback_snd_iso_of_left_iso _ _
  infer_instance

/-- **The degree-`i` term of `bottomCover` is the degree-`i` term of `K`, for `i ≠ n`.** -/
def bottomCoverXIsoOfNe (i : ι) (hi : i ≠ n) : (K.bottomCover n hd q).X i ≅ K.X i :=
  have := isIso_bottomCoverι_f K n hd q i hi
  asIso ((K.bottomCoverι n hd q).f i)

/-- **The degree-`n` term of `bottomCover` is `A`.** -/
def bottomCoverXIsoSelf : (K.bottomCover n hd q).X n ≅ A :=
  asIso ((pullback.snd (K.toBottomSingle n hd) (coverSingleMap K n q)).f n) ≪≫
    singleObjXSelf c n A

/-- **In degree `n` the morphism to `K` is an epimorphism as soon as `q` is.** Under the
identification of the degree-`n` term with `A` it *is* `q`. -/
theorem epi_bottomCoverι_f [Epi q] : Epi ((K.bottomCoverι n hd q).f n) := by
  rw [← bottomCoverXIso_hom_fst K n hd q n]
  have hfst : pullback.fst ((K.toBottomSingle n hd).f n) ((coverSingleMap K n q).f n) =
      (pullback.fst ((K.toBottomSingle n hd).f n) ((coverSingleMap K n q).f n) ≫
        (K.toBottomSingle n hd).f n) ≫ inv ((K.toBottomSingle n hd).f n) := by
    simp
  have : Epi (pullback.fst ((K.toBottomSingle n hd).f n) ((coverSingleMap K n q).f n)) := by
    rw [hfst, pullback.condition]
    have := epi_coverSingleMap_f_self K n q
    exact epi_comp _ _
  exact epi_comp _ _

/-- The morphism to `K` is an epimorphism in every degree as soon as `q` is. -/
private theorem epi_bottomCoverι_f_of_epi [Epi q] (j : ι) :
    Epi ((K.bottomCoverι n hd q).f j) := by
  by_cases hj : j = n
  · subst hj
    exact epi_bottomCoverι_f K j hd q
  · have := isIso_bottomCoverι_f K n hd q j hj
    infer_instance

/-- **The morphism to `K` is an isomorphism on cohomology in the degrees `i` with `i ≠ n` and
`c.next i ≠ n`.** No hypothesis is needed in the degree `c.prev i`: there the morphism is an
epimorphism in every case, which is enough. -/
theorem isIso_homologyMap_bottomCoverι [Epi q] (i : ι) (hi : i ≠ n) (hnext : c.next i ≠ n) :
    IsIso (homologyMap (K.bottomCoverι n hd q) i) := by
  have := isIso_bottomCoverι_f K n hd q (c.next i) hnext
  exact isIso_homologyMap_of_epi_f _ i (epi_bottomCoverι_f_of_epi K n hd q _)
    (isIso_bottomCoverι_f K n hd q i hi) inferInstance

/-- **The morphism to `K` is an epimorphism on cohomology in every degree `i` with
`c.next i ≠ n`.** In particular in degree `n` itself. -/
theorem epi_homologyMap_bottomCoverι [Epi q] (i : ι) (hnext : c.next i ≠ n) :
    Epi (homologyMap (K.bottomCoverι n hd q) i) := by
  have := isIso_bottomCoverι_f K n hd q (c.next i) hnext
  exact epi_homologyMap_of_epi_f _ i (epi_bottomCoverι_f_of_epi K n hd q _) inferInstance

end HomologicalComplex

end
