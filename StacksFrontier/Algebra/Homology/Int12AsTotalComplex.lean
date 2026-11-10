module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import StacksCore.Algebra.Homology.HomologicalTricomplex
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport

/-!
# `Tot₁₂` of a tricomplex is a total complex in the category of complexes

A tricomplex is a complex of bicomplexes, but it is equally a *bicomplex of complexes*: the two
types `HomologicalComplex (HomologicalComplex₂ C c₂ c₃) c₁` and
`HomologicalComplex₂ (HomologicalComplex C c₃) c₁ c₂` are literally the same. This file compares
the two things one can then call "integrate the first two indices":

* `HomologicalComplex₃.int₁₂`, `Tot₁₂(A^{•,•,•})`, which is built *termwise* from the
  slices `K.X' i₃` -- in bidegree `(i₁₂, i₃)` it is the degree-`i₁₂` term of the total complex of
  the slice at `i₃`, so each of its terms is a coproduct taken in `C`;
* the total complex `HomologicalComplex₂.total` of the bicomplex of complexes, whose term in
  degree `i₁₂` is a coproduct taken in `HomologicalComplex C c₃`.

They agree (`HomologicalComplex₃.int₁₂IsoTotal`), and the first consequence is that the second
total complex exists as soon as the first does: no coproducts of complexes need be assumed
(`HomologicalComplex₃.hasTotal_asBicomplex`).

## Main definitions

* `HomologicalComplex₃.asBicomplex`: a tricomplex read as a bicomplex of complexes.
* `HomologicalComplex₃.ιInt₁₂` and `HomologicalComplex₃.ιInt₁₂OrZero`: the inclusion of a term of
  `K` into `Tot₁₂(K)`, as a morphism of complexes.
* `HomologicalComplex₃.int₁₂IsoTotal`: `Tot₁₂(K)` is the total complex of `K` read as a
  bicomplex of complexes.
* `HomologicalComplex₃.int₁₂MapIsoOfFinite`: an additive functor of the category of complexes
  commutes with `Tot₁₂` of a tricomplex with finite support, `Tot(G(K)) ≅ G(Tot₁₂(K))`.

## Main results

* `HomologicalComplex₃.isColimitCofanInt₁₂`: the terms of `Tot₁₂(K)` are coproducts of the terms
  of `K` in the category of complexes.
* `HomologicalComplex₃.hasTotal_asBicomplex`: hence the bicomplex of complexes has a total
  complex.
* `HomologicalComplex₃.ιInt₁₂_d`: the differential of `Tot₁₂(K)` on a summand, `d₁ + (-1)^p d₂`
  up to the signs of the total complex shape.

## References

* [Stacks Project, Tag 08BI](https://stacks.math.columbia.edu/tag/08BI)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace HomologicalComplex₃

variable {C : Type*} [Category* C] [Preadditive C] {I₁ I₂ I₃ I₁₂ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}
  (K : HomologicalComplex₃ C c₁ c₂ c₃)

/-- A tricomplex read as a bicomplex with values in complexes: the two types are the same, and
this is the identity. -/
abbrev asBicomplex : HomologicalComplex₂ (HomologicalComplex C c₃) c₁ c₂ := K

variable (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]
  [K.HasInt₁₂ c₁₂]

/-- The inclusion of the term of `K` in position `(i₁, i₂)` into `Tot₁₂(K)`, as a morphism of
complexes: in degree `i₃` it is the inclusion of a summand into the total complex of the slice at
`i₃`. -/
@[simps]
def ιInt₁₂ (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    (K.X i₁).X i₂ ⟶ (K.int₁₂ c₁₂).X i₁₂ where
  f i₃ := (K.X' i₃).ιTotal c₁₂ i₁ i₂ i₁₂ h
  comm' i₃ i₃' _ := by
    have hd : ((K.int₁₂ c₁₂).X i₁₂).d i₃ i₃' =
        (HomologicalComplex₂.total.map (K.d' i₃ i₃') c₁₂).f i₁₂ := rfl
    rw [hd, HomologicalComplex₂.ιTotal_map]
    rfl

/-- The inclusion of a term of `K` into `Tot₁₂(K)`, or zero if the degrees do not match. -/
def ιInt₁₂OrZero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    (K.X i₁).X i₂ ⟶ (K.int₁₂ c₁₂).X i₁₂ :=
  if h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂ then K.ιInt₁₂ c₁₂ i₁ i₂ i₁₂ h else 0

/-- When the degrees match, `ιInt₁₂OrZero` is the inclusion `ιInt₁₂`. -/
lemma ιInt₁₂OrZero_eq (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιInt₁₂OrZero c₁₂ i₁ i₂ i₁₂ = K.ιInt₁₂ c₁₂ i₁ i₂ i₁₂ h := dite_eq_left h

/-- When the degrees do not match, `ιInt₁₂OrZero` is zero. -/
lemma ιInt₁₂OrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) ≠ i₁₂) :
    K.ιInt₁₂OrZero c₁₂ i₁ i₂ i₁₂ = 0 := dite_eq_right h

/-- In degree `i₃`, `ιInt₁₂OrZero` is the inclusion-or-zero into the total complex of the
slice at `i₃`. -/
@[simp]
lemma ιInt₁₂OrZero_f (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) (i₃ : I₃) :
    (K.ιInt₁₂OrZero c₁₂ i₁ i₂ i₁₂).f i₃ = (K.X' i₃).ιTotalOrZero c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂ <;>
    simp [h, ιInt₁₂OrZero_eq, ιInt₁₂OrZero_eq_zero, HomologicalComplex₂.ιTotalOrZero_eq,
      HomologicalComplex₂.ιTotalOrZero_eq_zero]

/-- In degree `i₃`, the differential of `Tot₁₂(K)` on a summand is the differential of the total
complex of the slice at `i₃` on that summand. -/
lemma ιInt₁₂_d_f (i₁ : I₁) (i₂ : I₂) (i₁₂ i₁₂' : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) (i₃ : I₃) :
    (K.ιInt₁₂ c₁₂ i₁ i₂ i₁₂ h ≫ (K.int₁₂ c₁₂).d i₁₂ i₁₂').f i₃ =
      (K.X' i₃).d₁ c₁₂ i₁ i₂ i₁₂' + (K.X' i₃).d₂ c₁₂ i₁ i₂ i₁₂' := by
  have hd : ((K.int₁₂ c₁₂).d i₁₂ i₁₂').f i₃ = ((K.X' i₃).total c₁₂).d i₁₂ i₁₂' := rfl
  have hι : (K.ιInt₁₂ c₁₂ i₁ i₂ i₁₂ h).f i₃ = (K.X' i₃).ιTotal c₁₂ i₁ i₂ i₁₂ h := rfl
  rw [HomologicalComplex.comp_f, hd, hι, HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]

/-- The differential of `Tot₁₂(K)` on a summand: the two differentials of `K` in the
integrated directions, with the signs of the total complex shape. -/
@[reassoc]
lemma ιInt₁₂_d (i₁ : I₁) (i₂ : I₂) (i₁₂ i₁₂' : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιInt₁₂ c₁₂ i₁ i₂ i₁₂ h ≫ (K.int₁₂ c₁₂).d i₁₂ i₁₂' =
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) •
          ((K.d i₁ (c₁.next i₁)).f i₂ ≫ K.ιInt₁₂OrZero c₁₂ (c₁.next i₁) i₂ i₁₂') +
        ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂) •
          ((K.X i₁).d i₂ (c₂.next i₂) ≫ K.ιInt₁₂OrZero c₁₂ i₁ (c₂.next i₂) i₁₂') := by
  refine HomologicalComplex.Hom.ext (funext fun i₃ => ?_)
  have key : ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) •
          (((K.d i₁ (c₁.next i₁)).f i₂).f i₃ ≫
            (K.X' i₃).ιTotalOrZero c₁₂ (c₁.next i₁) i₂ i₁₂') +
        ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂) •
          ((((K.X i₁).d i₂ (c₂.next i₂)).f i₃) ≫
            (K.X' i₃).ιTotalOrZero c₁₂ i₁ (c₂.next i₂) i₁₂') =
      (K.X' i₃).d₁ c₁₂ i₁ i₂ i₁₂' + (K.X' i₃).d₂ c₁₂ i₁ i₂ i₁₂' := rfl
  rw [ιInt₁₂_d_f, ← key]
  simp

/-- The cofan exhibiting the degree-`i₁₂` term of `Tot₁₂(K)` as the coproduct, in the category of
complexes, of the terms of `K` of total degree `i₁₂`. -/
def cofanInt₁₂ (i₁₂ : I₁₂) :
    GradedObject.CofanMapObjFun K.asBicomplex.toGradedObject
      (ComplexShape.π c₁ c₂ c₁₂) i₁₂ :=
  GradedObject.CofanMapObjFun.mk _ _ _ ((K.int₁₂ c₁₂).X i₁₂)
    (fun i hi => K.ιInt₁₂ c₁₂ i.1 i.2 i₁₂ hi)

/-- The terms of `Tot₁₂(K)` are coproducts in the category of complexes: the cofan
`cofanInt₁₂` is a colimit. -/
def isColimitCofanInt₁₂ (i₁₂ : I₁₂) : IsColimit (K.cofanInt₁₂ c₁₂ i₁₂) := by
  refine HomologicalComplex.isColimitOfEval _ _ (fun i₃ => ?_)
  exact (Cofan.isColimitMapCoconeEquiv (HomologicalComplex.eval C c₃ i₃) _ _).symm
    ((K.X' i₃).toGradedObject.isColimitCofanMapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂)

/-- A tricomplex which can be integrated in its first two indices has, as a bicomplex of
complexes, a total complex. -/
instance hasTotal_asBicomplex : K.asBicomplex.HasTotal c₁₂ :=
  letI : DecidableEq I₁₂ := Classical.decEq I₁₂
  GradedObject.CofanMapObjFun.hasMap _ _ (K.cofanInt₁₂ c₁₂) (K.isColimitCofanInt₁₂ c₁₂)

/-- The degree-`i₁₂` comparison between `Tot₁₂(K)` and the total complex of `K` read as a
bicomplex of complexes. -/
def int₁₂XIso (i₁₂ : I₁₂) :
    (K.int₁₂ c₁₂).X i₁₂ ≅ (K.asBicomplex.total c₁₂).X i₁₂ :=
  GradedObject.CofanMapObjFun.iso (K.isColimitCofanInt₁₂ c₁₂ i₁₂)

/-- The comparison `int₁₂XIso` carries the inclusion of a summand into `Tot₁₂(K)` to its
inclusion into the total complex of `K.asBicomplex`. -/
@[reassoc (attr := simp)]
lemma ιInt₁₂_int₁₂XIso_hom (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιInt₁₂ c₁₂ i₁ i₂ i₁₂ h ≫ (K.int₁₂XIso c₁₂ i₁₂).hom =
      K.asBicomplex.ιTotal c₁₂ i₁ i₂ i₁₂ h :=
  GradedObject.CofanMapObjFun.inj_iso_hom (K.isColimitCofanInt₁₂ c₁₂ i₁₂) (i₁, i₂) h

/-- The inverse of `int₁₂XIso` carries the inclusion of a summand into the total complex of
`K.asBicomplex` to its inclusion into `Tot₁₂(K)`. -/
@[reassoc (attr := simp)]
lemma ιTotal_int₁₂XIso_inv (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.asBicomplex.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ (K.int₁₂XIso c₁₂ i₁₂).inv =
      K.ιInt₁₂ c₁₂ i₁ i₂ i₁₂ h :=
  GradedObject.CofanMapObjFun.ιMapObj_iso_inv (K.isColimitCofanInt₁₂ c₁₂ i₁₂) (i₁, i₂) h

/-- The inverse of `int₁₂XIso` carries `ιTotalOrZero` for `K.asBicomplex` to `ιInt₁₂OrZero`. -/
@[reassoc (attr := simp)]
lemma ιTotalOrZero_int₁₂XIso_inv (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.asBicomplex.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ ≫ (K.int₁₂XIso c₁₂ i₁₂).inv =
      K.ιInt₁₂OrZero c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂ <;>
    simp [h, ιInt₁₂OrZero_eq, ιInt₁₂OrZero_eq_zero, HomologicalComplex₂.ιTotalOrZero_eq,
      HomologicalComplex₂.ιTotalOrZero_eq_zero]

/-- The first differential of the total complex of the bicomplex of complexes, read in
`Tot₁₂(K)`. -/
@[reassoc]
lemma d₁_int₁₂XIso_inv (i₁ : I₁) (i₂ : I₂) (i₁₂' : I₁₂) :
    K.asBicomplex.d₁ c₁₂ i₁ i₂ i₁₂' ≫ (K.int₁₂XIso c₁₂ i₁₂').inv =
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) •
        ((K.d i₁ (c₁.next i₁)).f i₂ ≫ K.ιInt₁₂OrZero c₁₂ (c₁.next i₁) i₂ i₁₂') := by
  change (ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) • ((K.d i₁ (c₁.next i₁)).f i₂ ≫
    K.asBicomplex.ιTotalOrZero c₁₂ (c₁.next i₁) i₂ i₁₂')) ≫ _ = _
  rw [Linear.units_smul_comp, Category.assoc, ιTotalOrZero_int₁₂XIso_inv]

/-- The second differential of the total complex of the bicomplex of complexes, read in
`Tot₁₂(K)`. -/
@[reassoc]
lemma d₂_int₁₂XIso_inv (i₁ : I₁) (i₂ : I₂) (i₁₂' : I₁₂) :
    K.asBicomplex.d₂ c₁₂ i₁ i₂ i₁₂' ≫ (K.int₁₂XIso c₁₂ i₁₂').inv =
      ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂) •
        ((K.X i₁).d i₂ (c₂.next i₂) ≫ K.ιInt₁₂OrZero c₁₂ i₁ (c₂.next i₂) i₁₂') := by
  change (ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂) • ((K.X i₁).d i₂ (c₂.next i₂) ≫
    K.asBicomplex.ιTotalOrZero c₁₂ i₁ (c₂.next i₂) i₁₂')) ≫ _ = _
  rw [Linear.units_smul_comp, Category.assoc, ιTotalOrZero_int₁₂XIso_inv]

/-- `Tot₁₂(K)` is the total complex of `K` read as a bicomplex of complexes. -/
def int₁₂IsoTotal : K.int₁₂ c₁₂ ≅ K.asBicomplex.total c₁₂ :=
  HomologicalComplex.Hom.isoOfComponents (K.int₁₂XIso c₁₂) (fun i₁₂ i₁₂' _ => by
    rw [← cancel_epi (K.int₁₂XIso c₁₂ i₁₂).inv, Iso.inv_hom_id_assoc,
      ← cancel_mono (K.int₁₂XIso c₁₂ i₁₂').inv, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    refine HomologicalComplex₂.total.hom_ext c₁₂ (fun i₁ i₂ hi => ?_)
    rw [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc, d₁_int₁₂XIso_inv,
      d₂_int₁₂XIso_inv, ιTotal_int₁₂XIso_inv_assoc, ιInt₁₂_d])

/-- An additive functor of the category of complexes commutes with `Tot₁₂`: if the tricomplex
`K` has, in each total degree of its first two indices, only finitely many nonzero terms -- as
*complexes* in the third index -- then `Tot(G(K)) ≅ G(Tot₁₂(K))` for every additive
`G : HomologicalComplex C c₃ ⥤ E`. -/
def int₁₂MapIsoOfFinite {E : Type*} [Category* E] [Preadditive E]
    (G : HomologicalComplex C c₃ ⥤ E) [G.Additive]
    [(HomologicalComplex₂.TotalMap.mapBicomplex G K.asBicomplex).HasTotal c₁₂]
    (hfin : ∀ i₁₂ : I₁₂, {p : I₁ × I₂ | ComplexShape.π c₁ c₂ c₁₂ p = i₁₂ ∧
      ¬ IsZero ((K.X p.1).X p.2)}.Finite) :
    (HomologicalComplex₂.TotalMap.mapBicomplex G K.asBicomplex).total c₁₂ ≅
      (G.mapHomologicalComplex c₁₂).obj (K.int₁₂ c₁₂) :=
  HomologicalComplex₂.TotalMap.totalIsoOfFinite G K.asBicomplex hfin ≪≫
    (G.mapHomologicalComplex c₁₂).mapIso (K.int₁₂IsoTotal c₁₂).symm

/-- In degree `i₁₂`, the isomorphism `int₁₂IsoTotal` is `int₁₂XIso`. -/
@[simp]
lemma int₁₂IsoTotal_hom_f (i₁₂ : I₁₂) :
    (K.int₁₂IsoTotal c₁₂).hom.f i₁₂ = (K.int₁₂XIso c₁₂ i₁₂).hom :=
  rfl

/-- The isomorphism `int₁₂IsoTotal` carries the inclusion of a summand into `Tot₁₂(K)` to its
inclusion into the total complex of `K.asBicomplex`. -/
@[reassoc (attr := simp)]
lemma ιInt₁₂_int₁₂IsoTotal_hom (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιInt₁₂ c₁₂ i₁ i₂ i₁₂ h ≫ (K.int₁₂IsoTotal c₁₂).hom.f i₁₂ =
      K.asBicomplex.ιTotal c₁₂ i₁ i₂ i₁₂ h :=
  K.ιInt₁₂_int₁₂XIso_hom c₁₂ i₁ i₂ i₁₂ h

end HomologicalComplex₃

end
