module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FactorizationToRelation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationSheafSections

/-! # The sections of the sheaf of factorizations are the factorization data

Let `(C, J, O)` be a ringed site and `F` a sheaf of `O`-modules.  Fix `n` and `l`.  As for
relations, there are two descriptions of a rank-`l` finite-free factorization of `n` sections of
`F` over an object:

* a *concrete* one, `Stacks.SheafOfModules.FactorizationData O F U n l`, a structure carrying `n`
  coefficients, `l` generators, an `l × n` matrix and the matrix condition `∑ᵢ Bₖᵢ aᵢ = 0`,
  assembled into the presheaf of sets `Stacks.SheafOfModules.factorizationPresheaf O F n`;
* a *limit-theoretic* one, `Stacks.Sheaves.RelationSheaf.factorizationSheaf`, the equalizer of
  the `l` row morphisms `∑ᵢ Bₖᵢ aᵢ` of generalized elements and the zero morphism out of the
  sheaf of sets `Oⁿ ⨯ (Fˡ ⨯ (Oⁿ)ˡ)`.

This file identifies them, exactly as
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationSheafSections` does for relations, and then
proves the compatibility that is the point of the file: the relation
`Stacks.Sheaves.RelationSheaf.factorizationToRelation` attaches to a section of the sheaf of
factorizations is the relation `Stacks.SheafOfModules.relationOfFactorizationApp` attaches to the
corresponding factorization datum.  With that, the two presheaf-of-sets descriptions of Stacks
08FC part (2) and the two sheaf-of-sets descriptions are compatible on both sides of the map
reading a factorization as the relation it factors, which is the last bridge the proof of Stacks
05VD needs.

## Main definitions

* `Stacks.Sheaves.RelationSheaf.factorizationAmbientMk`: the section of `Oⁿ ⨯ (Fˡ ⨯ (Oⁿ)ˡ)` with
  prescribed coefficients, generators and matrix.
* `Stacks.Sheaves.RelationSheaf.factorizationSheafSectionsEquiv`: the bijection between the
  sections over `X` of the sheaf of rank-`l` factorizations and the rank-`l` factorization data
  over `X`.

## Main results

* `Stacks.Sheaves.RelationSheaf.factorizationSheafSectionsEquiv_coeffs`, `_gens` and `_matrix`:
  the three component families of the factorization attached to a section of the sheaf of
  factorizations are the images of the underlying section of `Oⁿ ⨯ (Fˡ ⨯ (Oⁿ)ˡ)` under the three
  families of projections.  These are the computation rules a consumer needs.
* `Stacks.Sheaves.RelationSheaf.relationSheafSectionsEquiv_factorizationToRelation`: **the
  relation a factorization factors is the same read either way.**
* `Stacks.Sheaves.RelationSheaf.exists_factorizationData_of_sections` and
  `exists_sections_of_factorizationData`: the two existence statements the consumers use, one for
  each direction.

## Implementation notes

**The scalar action and the multiplication on the two sides are the same instances, not merely
isomorphic.**  As recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationSheafSections` for the scalar action of
`Stacks.SheafOfModules.RelationData.relation`, the multiplication in the matrix condition
`Stacks.SheafOfModules.FactorizationData.matrix_coeffs` is the `Ring` structure of
`(Stacks.commRingSheafToRingSheaf O).obj.obj X`, while the row morphisms are evaluated through
`CategoryTheory.Sheaf.ringSectionsRing`, which is defined as `inferInstanceAs` of the former.  The
two matrix conditions are therefore literally the same proposition and no bridging lemma appears
below.

**The equalizer condition is turned into the `l` row conditions by the element calculus of the
finite product.**  `Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv` presents a section of the
sheaf of factorizations as a section `p` of `Oⁿ ⨯ (Fˡ ⨯ (Oⁿ)ˡ)` on which the contraction and the
zero morphism into `Oˡ` agree — a *single* equation between sections of `Oˡ`.
`CategoryTheory.Functor.piObjMk_ext` and the two projection lemmas
`map_piπ_map_factorizationContract` and `map_piπ_map_factorizationZero` make that equation
equivalent to the `l` equations `∑ᵢ Bₖᵢ aᵢ = 0`, which is what the concrete datum carries.  The
morphism-level version of one direction is already
`Stacks.Sheaves.RelationSheaf.factorizationIota_comp_factorizationRow`; the equivalence of
conditions on a *section* is what the bijection needs, and that is proved here.

**No tag is placed in this file.**  Nothing here is an assertion of a Stacks tag: it is a
comparison of two of the tree's own presentations of the same first-order condition.

## References

* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf CategoryTheory.Functor

universe w v u

namespace Stacks.Sheaves.RelationSheaf

/-! ### The element calculus of the factorization ambient -/

section Ambient

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R) (n l : ℕ) (X : Cᵒᵖ)

/-- The section of `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` over `X` with prescribed coefficients, generators and
matrix.  The sections functor preserves finite products, so this is a bijection onto the sections
of the product; the three halves of the bijection are
`map_factorizationCoeff_factorizationAmbientMk`, `map_factorizationGen_factorizationAmbientMk` and
`map_factorizationMatrix_factorizationAmbientMk`, together with `factorizationAmbient_ext`. -/
def factorizationAmbientMk (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (t : Fin l → (sectionsFunctor J X).obj (moduleSheaf R M))
    (B : Fin l → Fin n → (sectionsFunctor J X).obj (ringSheaf R)) :
    (sectionsFunctor J X).obj (factorizationAmbient R M n l) :=
  prodObjMk (P := sectionsFunctor.{w} J X)
    (A := ∏ᶜ fun _ : Fin n => ringSheaf R)
    (B := (∏ᶜ fun _ : Fin l => moduleSheaf R M) ⨯
      (∏ᶜ fun _ : Fin l => ∏ᶜ fun _ : Fin n => ringSheaf R))
    (piObjMk (P := sectionsFunctor.{w} J X) (A := fun _ : Fin n => ringSheaf R) a)
    (prodObjMk (P := sectionsFunctor.{w} J X)
      (A := ∏ᶜ fun _ : Fin l => moduleSheaf R M)
      (B := ∏ᶜ fun _ : Fin l => ∏ᶜ fun _ : Fin n => ringSheaf R)
      (piObjMk (P := sectionsFunctor.{w} J X) (A := fun _ : Fin l => moduleSheaf R M) t)
      (piObjMk (P := sectionsFunctor.{w} J X)
        (A := fun _ : Fin l => ∏ᶜ fun _ : Fin n => ringSheaf R)
        fun k => piObjMk (P := sectionsFunctor.{w} J X)
          (A := fun _ : Fin n => ringSheaf R) (B k)))

/-- The `i`-th coefficient of `factorizationAmbientMk a t B` is `a i`. -/
@[simp]
lemma map_factorizationCoeff_factorizationAmbientMk
    (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (t : Fin l → (sectionsFunctor J X).obj (moduleSheaf R M))
    (B : Fin l → Fin n → (sectionsFunctor J X).obj (ringSheaf R)) (i : Fin n) :
    (sectionsFunctor J X).map (factorizationCoeff R M n l i)
        (factorizationAmbientMk R M n l X a t B) = a i := by
  rw [factorizationCoeff, Functor.map_comp_apply, factorizationAmbientMk, map_fst_prodObjMk,
    map_piπ_piObjMk]

/-- The `k`-th generator of `factorizationAmbientMk a t B` is `t k`. -/
@[simp]
lemma map_factorizationGen_factorizationAmbientMk
    (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (t : Fin l → (sectionsFunctor J X).obj (moduleSheaf R M))
    (B : Fin l → Fin n → (sectionsFunctor J X).obj (ringSheaf R)) (k : Fin l) :
    (sectionsFunctor J X).map (factorizationGen R M n l k)
        (factorizationAmbientMk R M n l X a t B) = t k := by
  rw [factorizationGen, Functor.map_comp_apply, Functor.map_comp_apply, factorizationAmbientMk,
    map_snd_prodObjMk, map_fst_prodObjMk, map_piπ_piObjMk]

/-- The `(k, i)`-th matrix entry of `factorizationAmbientMk a t B` is `B k i`. -/
@[simp]
lemma map_factorizationMatrix_factorizationAmbientMk
    (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (t : Fin l → (sectionsFunctor J X).obj (moduleSheaf R M))
    (B : Fin l → Fin n → (sectionsFunctor J X).obj (ringSheaf R)) (k : Fin l) (i : Fin n) :
    (sectionsFunctor J X).map (factorizationMatrix R M n l k i)
        (factorizationAmbientMk R M n l X a t B) = B k i := by
  rw [factorizationMatrix, Functor.map_comp_apply, Functor.map_comp_apply,
    Functor.map_comp_apply, factorizationAmbientMk, map_snd_prodObjMk, map_snd_prodObjMk,
    map_piπ_piObjMk, map_piπ_piObjMk]

/-- Two sections of `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` with the same coefficients, the same generators and the
same matrix agree. -/
lemma factorizationAmbient_ext
    {p q : (sectionsFunctor J X).obj (factorizationAmbient R M n l)}
    (hc : ∀ i : Fin n, (sectionsFunctor J X).map (factorizationCoeff R M n l i) p =
      (sectionsFunctor J X).map (factorizationCoeff R M n l i) q)
    (hg : ∀ k : Fin l, (sectionsFunctor J X).map (factorizationGen R M n l k) p =
      (sectionsFunctor J X).map (factorizationGen R M n l k) q)
    (hm : ∀ (k : Fin l) (i : Fin n),
      (sectionsFunctor J X).map (factorizationMatrix R M n l k i) p =
        (sectionsFunctor J X).map (factorizationMatrix R M n l k i) q) :
    p = q := by
  refine prodObjMk_ext (piObjMk_ext fun i => ?_)
    (prodObjMk_ext (piObjMk_ext fun k => ?_) (piObjMk_ext fun k => piObjMk_ext fun i => ?_))
  · have h := hc i
    simp only [factorizationCoeff, Functor.map_comp_apply] at h
    exact h
  · have h := hg k
    simp only [factorizationGen, Functor.map_comp_apply] at h
    exact h
  · have h := hm k i
    simp only [factorizationMatrix, Functor.map_comp_apply] at h
    exact h

/-- Every section of `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` is `factorizationAmbientMk` of its coefficients, its
generators and its matrix. -/
@[simp]
lemma factorizationAmbientMk_components
    (p : (sectionsFunctor J X).obj (factorizationAmbient R M n l)) :
    factorizationAmbientMk R M n l X
        (fun i => (sectionsFunctor J X).map (factorizationCoeff R M n l i) p)
        (fun k => (sectionsFunctor J X).map (factorizationGen R M n l k) p)
        (fun k i => (sectionsFunctor J X).map (factorizationMatrix R M n l k i) p) = p :=
  factorizationAmbient_ext R M n l X
    (fun i => map_factorizationCoeff_factorizationAmbientMk R M n l X _ _ _ i)
    (fun k => map_factorizationGen_factorizationAmbientMk R M n l X _ _ _ k)
    (fun k i => map_factorizationMatrix_factorizationAmbientMk R M n l X _ _ _ k i)

/-- The `k`-th row of `factorizationAmbientMk a t B` is `∑ᵢ Bₖᵢ aᵢ`. -/
lemma map_factorizationRow_factorizationAmbientMk
    (a : Fin n → (sectionsFunctor J X).obj (ringSheaf R))
    (t : Fin l → (sectionsFunctor J X).obj (moduleSheaf R M))
    (B : Fin l → Fin n → (sectionsFunctor J X).obj (ringSheaf R)) (k : Fin l) :
    (sectionsFunctor J X).map (factorizationRow R M n l k)
        (factorizationAmbientMk R M n l X a t B) = ∑ i : Fin n, B k i * a i := by
  rw [sections_factorizationRow]
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_factorizationMatrix_factorizationAmbientMk,
      map_factorizationCoeff_factorizationAmbientMk]

/-- The `k`-th component in `Rˡ` of the value of the matrix condition at a section of
`Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` is the value of the `k`-th row at that section. -/
lemma map_piπ_map_factorizationContract (k : Fin l)
    (p : (sectionsFunctor J X).obj (factorizationAmbient R M n l)) :
    (sectionsFunctor J X).map (Limits.Pi.π (fun _ : Fin l => ringSheaf R) k)
        ((sectionsFunctor J X).map (factorizationContract R M n l) p) =
      (sectionsFunctor J X).map (factorizationRow R M n l k) p :=
  (Functor.map_comp_apply (sectionsFunctor J X) (factorizationContract R M n l)
      (Limits.Pi.π (fun _ : Fin l => ringSheaf R) k) p).symm.trans
    (congrArg (fun m => (sectionsFunctor J X).map m p)
      (Limits.Pi.lift_comp_π (factorizationRow R M n l) k))

/-- The `k`-th component in `Rˡ` of the value of the zero morphism at a section of
`Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` is zero. -/
lemma map_piπ_map_factorizationZero (k : Fin l)
    (p : (sectionsFunctor J X).obj (factorizationAmbient R M n l)) :
    (sectionsFunctor J X).map (Limits.Pi.π (fun _ : Fin l => ringSheaf R) k)
        ((sectionsFunctor J X).map (factorizationZero R M n l) p) = 0 :=
  ((Functor.map_comp_apply (sectionsFunctor J X) (factorizationZero R M n l)
        (Limits.Pi.π (fun _ : Fin l => ringSheaf R) k) p).symm.trans
      (congrArg (fun m => (sectionsFunctor J X).map m p)
        (Limits.Pi.lift_comp_π
          (fun _ : Fin l => (0 : factorizationAmbient R M n l ⟶ ringSheaf R)) k))).trans
    (sectionsFunctor_map_hom_ringZero X p)

/-- **The equalizer condition, on a section, is the vanishing of the `l` rows.**  A section of
`Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` over `X` equalizes the matrix condition and the zero morphism into `Rˡ`
exactly when each of the `l` rows `∑ᵢ Bₖᵢ aᵢ` vanishes on it.  The forward direction is a
projection out of `Rˡ`; the converse is the joint monicity of those projections, which holds on
sections because the sections functor preserves finite products. -/
lemma sections_factorizationContract_eq_iff
    (p : (sectionsFunctor J X).obj (factorizationAmbient R M n l)) :
    (sectionsFunctor J X).map (factorizationContract R M n l) p =
        (sectionsFunctor J X).map (factorizationZero R M n l) p ↔
      ∀ k : Fin l, (sectionsFunctor J X).map (factorizationRow R M n l k) p = 0 := by
  constructor
  · intro h k
    refine (map_piπ_map_factorizationContract R M n l X k p).symm.trans ?_
    refine Eq.trans (congrArg (fun z => (sectionsFunctor J X).map
      (Limits.Pi.π (fun _ : Fin l => ringSheaf R) k) z) h) ?_
    exact map_piπ_map_factorizationZero R M n l X k p
  · intro h
    refine piObjMk_ext fun k => ?_
    refine (map_piπ_map_factorizationContract R M n l X k p).trans ?_
    exact (h k).trans (map_piπ_map_factorizationZero R M n l X k p).symm

/-- The matrix condition does hold for the coefficients and the matrix of a section of the sheaf
of rank-`l` factorizations.  This is the equalizer condition, read through
`sections_factorizationRow` and `factorizationIota_comp_factorizationRow`. -/
lemma sum_mul_factorizationIota_eq_zero (y : (factorizationSheaf R M n l).obj.obj X)
    (k : Fin l) :
    ∑ i : Fin n, (sectionsFunctor J X).map (factorizationMatrix R M n l k i)
          ((factorizationIota R M n l).hom.app X y) *
        (sectionsFunctor J X).map (factorizationCoeff R M n l i)
          ((factorizationIota R M n l).hom.app X y) = 0 := by
  refine (sections_factorizationRow R M n l X k _).symm.trans ?_
  refine (Functor.map_comp_apply (sectionsFunctor J X) (factorizationIota R M n l)
      (factorizationRow R M n l k) y).symm.trans ?_
  refine Eq.trans (congrArg (fun m => (sectionsFunctor J X).map m y)
    (factorizationIota_comp_factorizationRow R M n l k)) ?_
  exact sectionsFunctor_map_hom_ringZero X y

end Ambient

/-! ### The sections of the sheaf of factorizations -/

section Comparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The sections over `X` of the sheaf of rank-`l` factorizations of `n` sections are the rank-`l`
factorization data over `X`. -/
def factorizationSheafSectionsEquiv (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) (n l : ℕ) (X : Cᵒᵖ) :
    (Stacks.Sheaves.RelationSheaf.factorizationSheaf
        (Stacks.commRingSheafToRingSheaf O) F n l).obj.obj X ≃
      Stacks.SheafOfModules.FactorizationData O F X n l where
  toFun y :=
    { coeffs := fun i => (sectionsFunctor J X).map
        (factorizationCoeff (Stacks.commRingSheafToRingSheaf O) F n l i)
        ((factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l).hom.app X y)
      gens := fun k => (sectionsFunctor J X).map
        (factorizationGen (Stacks.commRingSheafToRingSheaf O) F n l k)
        ((factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l).hom.app X y)
      matrix := fun k i => (sectionsFunctor J X).map
        (factorizationMatrix (Stacks.commRingSheafToRingSheaf O) F n l k i)
        ((factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l).hom.app X y)
      matrix_coeffs := fun k => sum_mul_factorizationIota_eq_zero
        (Stacks.commRingSheafToRingSheaf O) F n l X y k }
  invFun d :=
    (Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv
        (factorizationContract (Stacks.commRingSheafToRingSheaf O) F n l)
        (factorizationZero (Stacks.commRingSheafToRingSheaf O) F n l) X).symm
      ⟨factorizationAmbientMk (Stacks.commRingSheafToRingSheaf O) F n l X
          d.coeffs d.gens d.matrix,
        (sections_factorizationContract_eq_iff (Stacks.commRingSheafToRingSheaf O) F n l X _).2
          fun k => (map_factorizationRow_factorizationAmbientMk
            (Stacks.commRingSheafToRingSheaf O) F n l X d.coeffs d.gens d.matrix k).trans
            (d.matrix_coeffs k)⟩
  left_inv y :=
    (Equiv.symm_apply_eq _).2 (Subtype.ext
      (factorizationAmbientMk_components (Stacks.commRingSheafToRingSheaf O) F n l X
        ((factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l).hom.app X y)))
  right_inv d := by
    refine Stacks.SheafOfModules.FactorizationData.ext (funext fun i => ?_)
      (funext fun k => ?_) (funext fun k => funext fun i => ?_)
    · refine (congrArg (fun z => (sectionsFunctor J X).map
          (factorizationCoeff (Stacks.commRingSheafToRingSheaf O) F n l i) z)
        (Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv_symm_apply
          (factorizationContract (Stacks.commRingSheafToRingSheaf O) F n l)
          (factorizationZero (Stacks.commRingSheafToRingSheaf O) F n l) X _)).trans ?_
      exact map_factorizationCoeff_factorizationAmbientMk
        (Stacks.commRingSheafToRingSheaf O) F n l X _ _ _ i
    · refine (congrArg (fun z => (sectionsFunctor J X).map
          (factorizationGen (Stacks.commRingSheafToRingSheaf O) F n l k) z)
        (Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv_symm_apply
          (factorizationContract (Stacks.commRingSheafToRingSheaf O) F n l)
          (factorizationZero (Stacks.commRingSheafToRingSheaf O) F n l) X _)).trans ?_
      exact map_factorizationGen_factorizationAmbientMk
        (Stacks.commRingSheafToRingSheaf O) F n l X _ _ _ k
    · refine (congrArg (fun z => (sectionsFunctor J X).map
          (factorizationMatrix (Stacks.commRingSheafToRingSheaf O) F n l k i) z)
        (Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv_symm_apply
          (factorizationContract (Stacks.commRingSheafToRingSheaf O) F n l)
          (factorizationZero (Stacks.commRingSheafToRingSheaf O) F n l) X _)).trans ?_
      exact map_factorizationMatrix_factorizationAmbientMk
        (Stacks.commRingSheafToRingSheaf O) F n l X _ _ _ k i

variable (O : Sheaf J CommRingCat.{w})
  (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) (n l : ℕ)

/-- The coefficients of the factorization attached to a section of the sheaf of rank-`l`
factorizations are the images of its underlying section of `Oⁿ ⨯ (Fˡ ⨯ (Oⁿ)ˡ)` under the
coefficient projections. -/
@[simp]
lemma factorizationSheafSectionsEquiv_coeffs (X : Cᵒᵖ)
    (y : (factorizationSheaf (Stacks.commRingSheafToRingSheaf O) F n l).obj.obj X) (i : Fin n) :
    (factorizationSheafSectionsEquiv O F n l X y).coeffs i =
      (sectionsFunctor J X).map
        (factorizationCoeff (Stacks.commRingSheafToRingSheaf O) F n l i)
        ((factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l).hom.app X y) :=
  rfl

/-- The generators of the factorization attached to a section of the sheaf of rank-`l`
factorizations are the images of its underlying section of `Oⁿ ⨯ (Fˡ ⨯ (Oⁿ)ˡ)` under the
generator projections. -/
@[simp]
lemma factorizationSheafSectionsEquiv_gens (X : Cᵒᵖ)
    (y : (factorizationSheaf (Stacks.commRingSheafToRingSheaf O) F n l).obj.obj X) (k : Fin l) :
    (factorizationSheafSectionsEquiv O F n l X y).gens k =
      (sectionsFunctor J X).map
        (factorizationGen (Stacks.commRingSheafToRingSheaf O) F n l k)
        ((factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l).hom.app X y) :=
  rfl

/-- The matrix of the factorization attached to a section of the sheaf of rank-`l` factorizations
is the image of its underlying section of `Oⁿ ⨯ (Fˡ ⨯ (Oⁿ)ˡ)` under the matrix projections. -/
@[simp]
lemma factorizationSheafSectionsEquiv_matrix (X : Cᵒᵖ)
    (y : (factorizationSheaf (Stacks.commRingSheafToRingSheaf O) F n l).obj.obj X) (k : Fin l)
    (i : Fin n) :
    (factorizationSheafSectionsEquiv O F n l X y).matrix k i =
      (sectionsFunctor J X).map
        (factorizationMatrix (Stacks.commRingSheafToRingSheaf O) F n l k i)
        ((factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l).hom.app X y) :=
  rfl

/-- The underlying section of `Oⁿ ⨯ (Fˡ ⨯ (Oⁿ)ˡ)` of the section of the sheaf of factorizations
attached to a factorization datum is `factorizationAmbientMk` of its three component families. -/
@[simp]
lemma factorizationIota_app_factorizationSheafSectionsEquiv_symm (X : Cᵒᵖ)
    (d : Stacks.SheafOfModules.FactorizationData O F X n l) :
    (factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l).hom.app X
        ((factorizationSheafSectionsEquiv O F n l X).symm d) =
      factorizationAmbientMk (Stacks.commRingSheafToRingSheaf O) F n l X
        d.coeffs d.gens d.matrix :=
  Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv_symm_apply
    (factorizationContract (Stacks.commRingSheafToRingSheaf O) F n l)
    (factorizationZero (Stacks.commRingSheafToRingSheaf O) F n l) X _

/-! ### Compatibility with reading a factorization as the relation it factors -/

/-- **The relation a factorization factors is the same read either way.**  Transporting a section
of the sheaf of rank-`l` factorizations along
`Stacks.Sheaves.RelationSheaf.factorizationToRelation` and then reading it as a relation datum
gives the same relation datum as reading the section as a factorization datum and applying
`Stacks.SheafOfModules.relationOfFactorizationApp`.

The coefficient component is the coefficient projection on both sides; the element component is
`Stacks.Sheaves.RelationSheaf.factorizationElt`, which `sections_factorizationElt` evaluates as
`∑ₖ Bₖᵢ • tₖ`, and that is what `relationOfFactorizationApp` records. -/
theorem relationSheafSectionsEquiv_factorizationToRelation (X : Cᵒᵖ)
    (hc : ∀ (Y : Cᵒᵖ) (x y : (CategoryTheory.Sheaf.sectionsFunctor J Y).obj
      (CategoryTheory.Sheaf.ringSheaf (Stacks.commRingSheafToRingSheaf O))), x * y = y * x)
    (y : (Stacks.Sheaves.RelationSheaf.factorizationSheaf
      (Stacks.commRingSheafToRingSheaf O) F n l).obj.obj X) :
    relationSheafSectionsEquiv O F n X
        ((Stacks.Sheaves.RelationSheaf.factorizationToRelation
          (Stacks.commRingSheafToRingSheaf O) F n l hc).hom.app X y) =
      Stacks.SheafOfModules.relationOfFactorizationApp O F
        ⟨l, factorizationSheafSectionsEquiv O F n l X y⟩ := by
  refine Stacks.SheafOfModules.RelationData.ext (funext fun i => ?_) (funext fun i => ?_)
  · have hmor : factorizationToRelation (Stacks.commRingSheafToRingSheaf O) F n l hc ≫
          relationIota (Stacks.commRingSheafToRingSheaf O) F n ≫
            relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i =
        factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l ≫
          factorizationCoeff (Stacks.commRingSheafToRingSheaf O) F n l i := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine Eq.trans (congrArg
        (fun m => m ≫ relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i)
        (factorizationToRelation_comp_relationIota
          (Stacks.commRingSheafToRingSheaf O) F n l hc)) ?_
      refine (Category.assoc _ _ _).trans ?_
      exact congrArg
        (fun m => factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l ≫ m)
        (factorizationToRelationAmbient_comp_relationCoeff
          (Stacks.commRingSheafToRingSheaf O) F n l i)
    refine Eq.trans ((Functor.map_comp_apply (sectionsFunctor J X)
        (factorizationToRelation (Stacks.commRingSheafToRingSheaf O) F n l hc)
        (relationIota (Stacks.commRingSheafToRingSheaf O) F n ≫
          relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i) y).trans
      (Functor.map_comp_apply (sectionsFunctor J X)
        (relationIota (Stacks.commRingSheafToRingSheaf O) F n)
        (relationCoeff (Stacks.commRingSheafToRingSheaf O) F n i) _)).symm ?_
    refine Eq.trans (congrArg (fun m => (sectionsFunctor J X).map m y) hmor) ?_
    exact Functor.map_comp_apply (sectionsFunctor J X)
      (factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l)
      (factorizationCoeff (Stacks.commRingSheafToRingSheaf O) F n l i) y
  · have hmor : factorizationToRelation (Stacks.commRingSheafToRingSheaf O) F n l hc ≫
          relationIota (Stacks.commRingSheafToRingSheaf O) F n ≫
            relationElt (Stacks.commRingSheafToRingSheaf O) F n i =
        factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l ≫
          factorizationElt (Stacks.commRingSheafToRingSheaf O) F n l i := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine Eq.trans (congrArg
        (fun m => m ≫ relationElt (Stacks.commRingSheafToRingSheaf O) F n i)
        (factorizationToRelation_comp_relationIota
          (Stacks.commRingSheafToRingSheaf O) F n l hc)) ?_
      refine (Category.assoc _ _ _).trans ?_
      exact congrArg
        (fun m => factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l ≫ m)
        (factorizationToRelationAmbient_comp_relationElt
          (Stacks.commRingSheafToRingSheaf O) F n l i)
    refine Eq.trans ((Functor.map_comp_apply (sectionsFunctor J X)
        (factorizationToRelation (Stacks.commRingSheafToRingSheaf O) F n l hc)
        (relationIota (Stacks.commRingSheafToRingSheaf O) F n ≫
          relationElt (Stacks.commRingSheafToRingSheaf O) F n i) y).trans
      (Functor.map_comp_apply (sectionsFunctor J X)
        (relationIota (Stacks.commRingSheafToRingSheaf O) F n)
        (relationElt (Stacks.commRingSheafToRingSheaf O) F n i) _)).symm ?_
    refine Eq.trans (congrArg (fun m => (sectionsFunctor J X).map m y) hmor) ?_
    refine (Functor.map_comp_apply (sectionsFunctor J X)
      (factorizationIota (Stacks.commRingSheafToRingSheaf O) F n l)
      (factorizationElt (Stacks.commRingSheafToRingSheaf O) F n l i) y).trans ?_
    exact sections_factorizationElt (Stacks.commRingSheafToRingSheaf O) F n l X i _

/-- Every section of the sheaf of rank-`l` factorizations gives a rank-`l` factorization datum
factoring the same relation.  This is the form
`relationSheafSectionsEquiv_factorizationToRelation` is used in upstairs. -/
theorem exists_factorizationData_of_sections (X : Cᵒᵖ)
    (hc : ∀ (Y : Cᵒᵖ) (x y : (CategoryTheory.Sheaf.sectionsFunctor J Y).obj
      (CategoryTheory.Sheaf.ringSheaf (Stacks.commRingSheafToRingSheaf O))), x * y = y * x)
    (y : (Stacks.Sheaves.RelationSheaf.factorizationSheaf
      (Stacks.commRingSheafToRingSheaf O) F n l).obj.obj X) :
    ∃ d : Stacks.SheafOfModules.FactorizationData O F X n l,
      Stacks.SheafOfModules.relationOfFactorizationApp O F ⟨l, d⟩ =
        relationSheafSectionsEquiv O F n X
          ((Stacks.Sheaves.RelationSheaf.factorizationToRelation
            (Stacks.commRingSheafToRingSheaf O) F n l hc).hom.app X y) :=
  ⟨factorizationSheafSectionsEquiv O F n l X y,
    (relationSheafSectionsEquiv_factorizationToRelation O F n l X hc y).symm⟩

/-- Every rank-`l` factorization datum is the datum of a section of the sheaf of rank-`l`
factorizations, compatibly with reading a factorization as the relation it factors.  This is the
direction the downstairs half of the argument needs: the witness is the section of the sheaf of
factorizations attached to the datum. -/
theorem exists_sections_of_factorizationData (X : Cᵒᵖ)
    (hc : ∀ (Y : Cᵒᵖ) (x y : (CategoryTheory.Sheaf.sectionsFunctor J Y).obj
      (CategoryTheory.Sheaf.ringSheaf (Stacks.commRingSheafToRingSheaf O))), x * y = y * x)
    (d : Stacks.SheafOfModules.FactorizationData O F X n l) :
    ∃ y : (Stacks.Sheaves.RelationSheaf.factorizationSheaf
        (Stacks.commRingSheafToRingSheaf O) F n l).obj.obj X,
      relationSheafSectionsEquiv O F n X
          ((Stacks.Sheaves.RelationSheaf.factorizationToRelation
            (Stacks.commRingSheafToRingSheaf O) F n l hc).hom.app X y) =
        Stacks.SheafOfModules.relationOfFactorizationApp O F ⟨l, d⟩ :=
  ⟨(factorizationSheafSectionsEquiv O F n l X).symm d,
    (relationSheafSectionsEquiv_factorizationToRelation O F n l X hc _).trans
      (congrArg (fun e => Stacks.SheafOfModules.relationOfFactorizationApp O F ⟨l, e⟩)
        ((factorizationSheafSectionsEquiv O F n l X).apply_symm_apply d))⟩

end Comparison

end Stacks.Sheaves.RelationSheaf

end
