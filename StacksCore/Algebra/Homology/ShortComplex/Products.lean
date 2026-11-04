module

public import Mathlib.Algebra.Category.Grp.AB
import StacksCore.Tactic.StacksAttribute

/-! # Homology of a product of short complexes (Stacks 060K, exactness of products)

Stacks 060K: let `I` be a set and for `i ∈ I` let `L_i ⟶ M_i ⟶ N_i` be a complex of abelian
groups with cohomology `H_i`; then `∏ L_i ⟶ ∏ M_i ⟶ ∏ N_i` is a complex of abelian groups with
homology `∏ H_i`.

We prove the general version: `C` is an abelian category in which `I`-indexed products exist and
are exact, in Mathlib's spelling `HasProductsOfShape I C` and `HasExactLimitsOfShape (Discrete I) C`
(the latter says `lim : (Discrete I ⥤ C) ⥤ C` preserves finite colimits). For a family
`S : I → ShortComplex C`:

* `ShortComplex.pi S` is the product short complex `∏ (S i).X₁ ⟶ ∏ (S i).X₂ ⟶ ∏ (S i).X₃`
  with the `Pi.map`s of the differentials; its `zero` field is the clause "`∏ L_i ⟶ ∏ M_i ⟶ ∏ N_i`
  is a complex" (no exactness needed). `ShortComplex.piπ S i` are its projections and
  `ShortComplex.piMap` its functoriality.
* `ShortComplex.piHomologyIso S : (pi S).homology ≅ ∏ (S i).homology` is the clause "the homology
  is `∏ H_i`", in the general form; `ShortComplex.piHomologyIso_hom_π` identifies it on the
  projections, `ShortComplex.homologyFanIsLimit` states it as a universal property, and
  `ShortComplex.piHomologyIso_hom_naturality` is its naturality in `S`.
* `ShortComplex.piHomologyIsoAddCommGrpCat` is the statement of Stacks 060K itself, for
  `AddCommGrpCat.{u}` and `I : Type u`, where products are exact by Mathlib's instances
  `instHasExactLimitsOfShapeDiscreteAddCommGrpCat` and `instAB4StarAddCommGrpCat` (recorded with
  `add_to_stacks` since they carry the clause "products of abelian groups are exact").

The proof views the family as a short complex `ShortComplex.discreteFunctor S` in the functor
category `Discrete I ⥤ C`, identifies `pi S` with its image under `lim`
(`ShortComplex.piIsoMapLim`), and uses that `lim` preserves homology (it preserves finite limits
as a right adjoint and finite colimits by exactness, `Functor.preservesHomologyOfExact`), through
Mathlib's `ShortComplex.mapHomologyIso`.

Deliberately not done here: the comparison of `pi S` with the categorical product `∏ᶜ S` taken in
`ShortComplex C`, and the analogous statement for products of `HomologicalComplex`es (at this pin
the `HomologicalComplex.sc` boundary needs `respectTransparency false` even inside Mathlib). -/

add_to_stacks 060K "products in Ab are exact" instHasExactLimitsOfShapeDiscreteAddCommGrpCat
add_to_stacks 060K "products in Ab are exact (AB4*)" instAB4StarAddCommGrpCat

@[expose] public section

universe u

namespace CategoryTheory.ShortComplex

open Limits

section HasZeroMorphisms

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {I : Type*} (S : I → ShortComplex C)

/-- The family `S` viewed as a short complex in the functor category `Discrete I ⥤ C`. -/
@[implicit_reducible, simps]
def discreteFunctor : ShortComplex (Discrete I ⥤ C) where
  X₁ := Discrete.functor fun i ↦ (S i).X₁
  X₂ := Discrete.functor fun i ↦ (S i).X₂
  X₃ := Discrete.functor fun i ↦ (S i).X₃
  f := Discrete.natTrans fun i ↦ (S i.as).f
  g := Discrete.natTrans fun i ↦ (S i.as).g
  zero := by ext; simp

/-- Evaluating `discreteFunctor S` at `i` gives back `S i`. -/
@[simps!]
def discreteFunctorMapEvaluationIso (i : I) :
    (discreteFunctor S).map ((evaluation (Discrete I) C).obj ⟨i⟩) ≅ S i :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

variable [HasProductsOfShape I C]

/-- The product short complex `∏ (S i).X₁ ⟶ ∏ (S i).X₂ ⟶ ∏ (S i).X₃` of a family of short
complexes, with the differentials `Pi.map`. Its `zero` field is the clause of Stacks 060K that
`∏ L_i ⟶ ∏ M_i ⟶ ∏ N_i` is again a complex. -/
@[stacks 060K "The product `∏ L_i ⟶ ∏ M_i ⟶ ∏ N_i` is a complex (the `zero` field)",
  implicit_reducible, simps]
noncomputable def pi : ShortComplex C where
  X₁ := ∏ᶜ fun i ↦ (S i).X₁
  X₂ := ∏ᶜ fun i ↦ (S i).X₂
  X₃ := ∏ᶜ fun i ↦ (S i).X₃
  f := Limits.Pi.map fun i ↦ (S i).f
  g := Limits.Pi.map fun i ↦ (S i).g
  zero := by ext; simp

/-- The projection `pi S ⟶ S i` of the product short complex onto its `i`-th factor. -/
@[simps]
noncomputable def piπ (i : I) : pi S ⟶ S i where
  τ₁ := Pi.π _ i
  τ₂ := Pi.π _ i
  τ₃ := Pi.π _ i

variable {S} {T : I → ShortComplex C}

/-- The product short complex is functorial: a family of morphisms `S i ⟶ T i` induces
`pi S ⟶ pi T`, with components `Pi.map`. -/
@[simps]
noncomputable def piMap (φ : ∀ i, S i ⟶ T i) : pi S ⟶ pi T where
  τ₁ := Limits.Pi.map fun i ↦ (φ i).τ₁
  τ₂ := Limits.Pi.map fun i ↦ (φ i).τ₂
  τ₃ := Limits.Pi.map fun i ↦ (φ i).τ₃
  comm₁₂ := by dsimp; ext j; simp [Hom.comm₁₂]
  comm₂₃ := by dsimp; ext j; simp [Hom.comm₂₃]

/-- `piMap φ` is compatible with the projections. -/
@[reassoc (attr := simp)]
lemma piMap_comp_piπ (φ : ∀ i, S i ⟶ T i) (i : I) : piMap φ ≫ piπ T i = piπ S i ≫ φ i := by
  ext <;> simp

variable (S)

/-- The product short complex is the image of `discreteFunctor S` under `lim`. -/
@[simps!]
noncomputable def piIsoMapLim : pi S ≅ (discreteFunctor S).map lim :=
  isoMk (Pi.isoLimit (discreteFunctor S).X₁) (Pi.isoLimit (discreteFunctor S).X₂)
    (Pi.isoLimit (discreteFunctor S).X₃) (by dsimp; ext j; simp) (by dsimp; ext j; simp)

/-- Under `piIsoMapLim`, the projection `piπ S i` is the natural transformation `lim.π ⟨i⟩`
applied to `discreteFunctor S`. -/
lemma piIsoMapLim_hom_comp_mapNatTrans_lim_π (i : I) :
    (piIsoMapLim S).hom ≫ (discreteFunctor S).mapNatTrans (lim.π ⟨i⟩) ≫
      (discreteFunctorMapEvaluationIso S i).hom = piπ S i := by
  ext <;> simp

end HasZeroMorphisms

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {I : Type*} (S : I → ShortComplex C)
  [HasProductsOfShape I C] [HasExactLimitsOfShape (Discrete I) C]

/-- The value at `i` of the homology of `discreteFunctor S` is the homology of `S i`. -/
@[simps!]
noncomputable def homologyDiscreteFunctorObjIso (i : I) :
    (discreteFunctor S).homology.obj ⟨i⟩ ≅ (S i).homology :=
  (mapHomologyIso (discreteFunctor S) ((evaluation (Discrete I) C).obj ⟨i⟩)).symm ≪≫
    homologyMapIso (discreteFunctorMapEvaluationIso S i)

/-- **Exactness of products** (Stacks 060K, general version): when `I`-indexed products are
exact in the abelian category `C`, the homology of the product short complex `pi S` is the
product of the homologies of the `S i`. -/
@[stacks 060K "General version: exact products of short complexes in an abelian category"]
noncomputable def piHomologyIso : (pi S).homology ≅ ∏ᶜ fun i ↦ (S i).homology :=
  homologyMapIso (piIsoMapLim S) ≪≫ mapHomologyIso (discreteFunctor S) lim ≪≫
    (Pi.isoLimit _).symm ≪≫ Pi.mapIso (homologyDiscreteFunctorObjIso S)

/-- `piHomologyIso` followed by the `i`-th projection is the map on homology induced by the
projection `piπ S i`. -/
@[reassoc (attr := simp)]
lemma piHomologyIso_hom_π (i : I) :
    (piHomologyIso S).hom ≫ Pi.π _ i = homologyMap (piπ S i) := by
  rw [← piIsoMapLim_hom_comp_mapNatTrans_lim_π, homologyMap_comp, homologyMap_comp,
    homologyMap_mapNatTrans]
  simp [piHomologyIso]

/-- `piHomologyIso` is the map into the product induced by the maps on homology of the
projections `piπ S i`. -/
lemma piHomologyIso_hom : (piHomologyIso S).hom = Pi.lift fun i ↦ homologyMap (piπ S i) :=
  Pi.hom_ext _ _ fun i ↦ by simp

/-- The inverse of `piHomologyIso` followed by the map on homology of the projection `piπ S i`
is the `i`-th projection of the product. -/
@[reassoc (attr := simp)]
lemma piHomologyIso_inv_comp_homologyMap (i : I) :
    (piHomologyIso S).inv ≫ homologyMap (piπ S i) = Pi.π _ i := by
  rw [← piHomologyIso_hom_π, Iso.inv_hom_id_assoc]

/-- **Exactness of products** as a universal property: the maps on homology of the projections
`piπ S i` exhibit `(pi S).homology` as the product of the `(S i).homology`. -/
noncomputable def homologyFanIsLimit :
    IsLimit (Fan.mk (pi S).homology fun i ↦ homologyMap (piπ S i)) :=
  IsLimit.ofIsoLimit (productIsProduct fun i ↦ (S i).homology)
    (Cone.ext (piHomologyIso S).symm fun ⟨i⟩ ↦ by simp)

variable {S} {T : I → ShortComplex C}

/-- `piHomologyIso` is natural in the family of short complexes. -/
@[reassoc]
lemma piHomologyIso_hom_naturality (φ : ∀ i, S i ⟶ T i) :
    homologyMap (piMap φ) ≫ (piHomologyIso T).hom =
      (piHomologyIso S).hom ≫ Limits.Pi.map fun i ↦ homologyMap (φ i) :=
  Pi.hom_ext _ _ fun i ↦ by simp [← homologyMap_comp]

end Abelian

section AddCommGrpCat

variable {I : Type u} (S : I → ShortComplex AddCommGrpCat.{u})

/-- **Exactness of products** (Stacks 060K): for a family `L_i ⟶ M_i ⟶ N_i` of complexes of
abelian groups with cohomology `H_i`, the complex `∏ L_i ⟶ ∏ M_i ⟶ ∏ N_i` (`pi S`) has homology
`∏ H_i`. Products of abelian groups are exact by Mathlib's `AB4Star AddCommGrpCat`. -/
@[stacks 060K "The Stacks statement: products of complexes of abelian groups"]
noncomputable def piHomologyIsoAddCommGrpCat :
    (pi S).homology ≅ ∏ᶜ fun i ↦ (S i).homology :=
  piHomologyIso S

end AddCommGrpCat

end CategoryTheory.ShortComplex
