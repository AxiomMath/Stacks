module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingHomotopyEquivalence

/-!
# The explicit Čech complex is Mathlib's Čech complex

Let `X` be a topological space, `U : I → Opens X` a family of open subsets and `ℱ` an abelian
presheaf on `X`. The Čech complex of `U` with coefficients in `ℱ` has two descriptions: the
explicit one, `Stacks.Cech.cechComplex`, whose degree-`p` term is the group of families of
sections over the intersections `CechCochains.inter U i` and whose differential is the alternating
sum of restrictions, and Mathlib's `CategoryTheory.cechComplexFunctor`, whose degree-`p` term
is a categorical product and whose differential comes from the alternating coface map complex
of a cosimplicial object.

Tag 01FH identifies the two degreewise, by `Stacks.Cech.cechComplexObjIso`. This file upgrades
that identification to an isomorphism of complexes.

## Main definitions

* `Stacks.Cech.interSectionsIso`: the comparison between the two spellings of the sections over
  an iterated intersection.
* `Stacks.Cech.cochainEvalAddHom` and `Stacks.Cech.cochainEval`: evaluation of a Čech cochain
  at a tuple, as an additive map and as a morphism of abelian groups.
* `Stacks.Cech.cochainFace`: the `i`-th face map of the explicit Čech complex, of which the
  Čech differential is the alternating sum.
* `Stacks.Cech.cechComplexIso`: the identification of the explicit Čech complex with Mathlib's
  Čech complex, as an isomorphism of cochain complexes.
* `Stacks.Cech.alternatingCechInclusionToCechComplexFunctor`: the canonical inclusion of the
  alternating Čech complex of Tag 01FH into Mathlib's Čech complex.
* `Stacks.Cech.cechHomologyIso`: the induced identification of the two Čech cohomologies.
* `Stacks.Cech.alternatingCechHomotopyEquiv`: the homotopy equivalence between the alternating
  Čech complex and Mathlib's Čech complex, as a chosen equivalence.
* `Stacks.Cech.alternatingCechHomologyIso`: the induced identification of the cohomology of the
  alternating Čech complex with the cohomology of Mathlib's Čech complex.

## Main results

* `Stacks.Cech.cechD_eq_sum_cochainFace`: the Čech differential of the explicit model is the
  alternating sum of the face maps.
* `Stacks.Cech.cechComplexObjIso_hom_comp_cechπ_eval`: the degreewise identification sends a
  cochain to the family of its values.
* `Stacks.Cech.cechComplexIso_hom_f`: in every degree the isomorphism of complexes is the
  degreewise identification of Tag 01FH.
* `Stacks.Cech.cechComplexFunctor_d_comp_cechπ`: the differential of Mathlib's Čech complex,
  composed with a projection, is the alternating sum of the face restrictions, written with the
  intersections `CechCochains.inter` and the inclusions `CechCochains.inter_le_omit` of the
  explicit model.
* `Stacks.Cech.alternatingCechInclusionToCechComplexFunctor_homotopyEquivalence` and
  `Stacks.Cech.alternatingCechInclusion_comp_homotopyEquivalence`: the inclusion of the
  alternating Čech complex into Mathlib's Čech complex is a homotopy equivalence, which is
  Tag 01FM for that complex. The two differ only in whether the inclusion is written as the
  abbreviation `Stacks.Cech.alternatingCechInclusionToCechComplexFunctor` or as the composite
  it abbreviates.
* `Stacks.Cech.quasiIso_alternatingCechInclusion_comp`: that inclusion is in particular a
  quasi-isomorphism.
* `Stacks.Cech.mapOpens_comp`: two composites of restriction maps of a presheaf on a space
  agree as soon as their sources and targets do.

## Implementation notes

Both complexes are assembled from the same restriction maps, so every component identity below
comes down to the fact that `TopologicalSpace.Opens X` is a partial order: two morphisms of
opens with the same source and target are equal, hence so are their images under `ℱ`. This is
what `Subsingleton.elim` discharges, and it is why no transport along
`Stacks.Cech.cechComplexInter_eq` has to be computed.

The comparison of the differentials is factored through the face maps: the degree-`p`
differential of Mathlib's Čech complex is the alternating sum of
`Stacks.CategoryTheory.CechComplex.face` and the explicit one is the alternating sum of
`cochainFace`, and the two face maps are identified one at a time, so that no sum has to be
carried across the comparison isomorphism.

As for the degreewise identification, the ambient universe of abelian groups must contain the
indexing universe, since the products in `CategoryTheory.cechComplexFunctor` do.

Tag 01FM is proved for the inclusion into the *explicit* complex, in
`StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingHomotopyEquivalence`; being a homotopy
equivalence is stable under composition with an isomorphism of complexes, so the chain-level
comparison transports it to Mathlib's complex without redoing the homotopy.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

namespace Stacks.Cech

open CechCochains

/-- The underlying additive map of a finite sum of morphisms of abelian groups is the sum of
their underlying additive maps. -/
private theorem hom_finset_sum {A B : Ab.{w}} {κ : Type*} (G : Finset κ) (f : κ → (A ⟶ B)) :
    (∑ i ∈ G, f i).hom = ∑ i ∈ G, (f i).hom := by
  classical
  induction G using Finset.induction with
  | empty => simp
  | insert a G ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

section Auxiliary

variable {X : TopCat.{u}} (G : TopCat.Presheaf Ab.{w} X)

/-- Two composites of restriction maps of a presheaf on a topological space agree as soon as
their sources and targets agree: the opens form a partial order, so the two underlying
morphisms of opens are equal. -/
theorem mapOpens_comp {A B C : Opens X} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) :
    G.map g.op ≫ G.map f.op = G.map h.op := by
  rw [← G.map_comp, ← op_comp, Subsingleton.elim (f ≫ g) h]

end Auxiliary

variable {X : TopCat.{u}} {I : Type v} (U : I → Opens X) (ℱ : TopCat.Presheaf Ab.{max v w} X)

/-- The comparison along `cechComplexInter_eq` between the two spellings of the sections over
an iterated intersection, as an isomorphism. -/
noncomputable def interSectionsIso {p : ℕ} (x : Fin (p + 1) → I) :
    ℱ.obj (op (_root_.Stacks.CategoryTheory.CechComplex.inter U x)) ≅ ℱ.obj (op (inter U x)) :=
  ℱ.mapIso (eqToIso (congrArg op (cechComplexInter_eq U x)))

/-- The projection of the degree-`p` term of Mathlib's Čech complex onto the factor indexed by
a tuple is the categorical projection followed by that comparison. -/
theorem cechπ_eq (p : ℕ) (x : Fin (p + 1) → I) :
    cechπ U ℱ p x = _root_.Stacks.CategoryTheory.CechComplex.π U ℱ p x ≫
      (interSectionsIso U ℱ x).hom :=
  congrArg (_root_.Stacks.CategoryTheory.CechComplex.π U ℱ p x ≫ ·)
    (congrArg ℱ.map (Subsingleton.elim _ _))

/-- Restricting to an iterated intersection commutes with the comparison isomorphisms
`interSectionsIso`, the opens being a partial order. -/
private theorem interMap_comp_interSectionsIso {p : ℕ} (y : Fin (p + 2) → I) (i : Fin (p + 2)) :
    ℱ.map (_root_.Stacks.CategoryTheory.CechComplex.interMap U y i.succAbove).op ≫
      (interSectionsIso U ℱ y).hom =
      (interSectionsIso U ℱ (y ∘ i.succAbove)).hom ≫ ℱ.map (homOfLE (inter_le_omit U y i)).op := by
  rw [interSectionsIso, interSectionsIso, Functor.mapIso_hom, Functor.mapIso_hom,
    ← ℱ.map_comp, ← ℱ.map_comp]
  exact congrArg ℱ.map (Subsingleton.elim _ _)

/-- Two morphisms into the degree-`p` term of Mathlib's Čech complex agree as soon as their
components at every tuple agree. -/
theorem cechπ_hom_ext {p : ℕ} {T : Ab.{max v w}}
    {f g : T ⟶ ((CategoryTheory.cechComplexFunctor U).obj ℱ).X p}
    (h : ∀ x, f ≫ cechπ U ℱ p x = g ≫ cechπ U ℱ p x) : f = g := by
  refine _root_.Stacks.CategoryTheory.CechComplex.hom_ext U ℱ fun x ↦ ?_
  refine (cancel_mono (interSectionsIso U ℱ x).hom).mp ?_
  rw [Category.assoc, Category.assoc, ← cechπ_eq]
  exact h x

/-- Evaluation of a Čech cochain at a tuple, as an additive map. -/
def cochainEvalAddHom (p : ℕ) (x : Fin (p + 1) → I) :
    Cochain U ℱ p →+ (ℱ.obj (op (inter U x)) : Type (max v w)) where
  toFun s := s x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation of a Čech cochain at a tuple, as a morphism of abelian groups. -/
noncomputable def cochainEval (p : ℕ) (x : Fin (p + 1) → I) :
    AddCommGrpCat.of (Cochain U ℱ p) ⟶ ℱ.obj (op (inter U x)) :=
  AddCommGrpCat.ofHom (cochainEvalAddHom U ℱ p x)

/-- The degreewise identification of Tag 01FH sends a Čech cochain to the family of its
values. -/
theorem cechComplexObjIso_hom_comp_cechπ_eval (p : ℕ) (x : Fin (p + 1) → I) :
    (cechComplexObjIso U ℱ p).hom ≫ cechπ U ℱ p x = cochainEval U ℱ p x :=
  cechComplexObjIso_hom_comp_cechπ U ℱ p x

/-- The `i`-th face map of the explicit Čech complex: the value of the image of a cochain at a
tuple is the restriction of its value at the tuple with the `i`-th index omitted. -/
def cochainFace (p : ℕ) (i : Fin (p + 2)) : Cochain U ℱ p →+ Cochain U ℱ (p + 1) where
  toFun s := fun y ↦ restr ℱ (inter_le_omit U y i) (s (y ∘ i.succAbove))
  map_zero' := by funext y; exact map_zero _
  map_add' s t := by funext y; exact map_add _ _ _

/-- The Čech differential of the explicit model is the alternating sum of the face maps. -/
theorem cechD_eq_sum_cochainFace (p : ℕ) :
    cechD U ℱ p = ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • cochainFace U ℱ p i := by
  refine AddMonoidHom.ext fun s ↦ funext fun y ↦ ?_
  change (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      restr ℱ (inter_le_omit U y j) (s (y ∘ j.succAbove))) =
    cochainEvalAddHom U ℱ (p + 1) y
      ((∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • cochainFace U ℱ p i) s)
  rw [AddMonoidHom.finsetSum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ rfl

/-- The Čech differential of the explicit model is the alternating sum of the face maps, as
morphisms of abelian groups. -/
theorem ofHom_cechD_eq_sum (p : ℕ) :
    AddCommGrpCat.ofHom (cechD U ℱ p) =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        AddCommGrpCat.ofHom (cochainFace U ℱ p i) := by
  apply AddCommGrpCat.hom_ext
  rw [AddCommGrpCat.hom_ofHom, hom_finset_sum, cechD_eq_sum_cochainFace]
  exact Finset.sum_congr rfl fun i _ ↦ rfl

/-- The degreewise identification of Tag 01FH is compatible with the face maps. -/
theorem cechComplexObjIso_hom_comp_face (p : ℕ) (i : Fin (p + 2)) :
    (cechComplexObjIso U ℱ p).hom ≫ _root_.Stacks.CategoryTheory.CechComplex.face U ℱ p i =
      AddCommGrpCat.ofHom (cochainFace U ℱ p i) ≫ (cechComplexObjIso U ℱ (p + 1)).hom := by
  refine cechπ_hom_ext U ℱ fun y ↦ ?_
  calc ((cechComplexObjIso U ℱ p).hom ≫
          _root_.Stacks.CategoryTheory.CechComplex.face U ℱ p i) ≫ cechπ U ℱ (p + 1) y
      = (cechComplexObjIso U ℱ p).hom ≫
          ((_root_.Stacks.CategoryTheory.CechComplex.face U ℱ p i ≫
            _root_.Stacks.CategoryTheory.CechComplex.π U ℱ (p + 1) y) ≫
              (interSectionsIso U ℱ y).hom) := by
        rw [cechπ_eq]
        simp only [Category.assoc]
    _ = (cechComplexObjIso U ℱ p).hom ≫ cechπ U ℱ p (y ∘ i.succAbove) ≫
          AddCommGrpCat.ofHom (restr ℱ (inter_le_omit U y i)) := by
        rw [_root_.Stacks.CategoryTheory.CechComplex.face_comp_π, Category.assoc,
          interMap_comp_interSectionsIso, cechπ_eq]
        simp only [Category.assoc]
        rfl
    _ = cochainEval U ℱ p (y ∘ i.succAbove) ≫
          AddCommGrpCat.ofHom (restr ℱ (inter_le_omit U y i)) := by
        rw [← Category.assoc, cechComplexObjIso_hom_comp_cechπ_eval]
    _ = (AddCommGrpCat.ofHom (cochainFace U ℱ p i) ≫
          (cechComplexObjIso U ℱ (p + 1)).hom) ≫ cechπ U ℱ (p + 1) y := by
        rw [Category.assoc, cechComplexObjIso_hom_comp_cechπ_eval]
        rfl

/-- The degreewise identification of Tag 01FH is compatible with the Čech differentials. -/
theorem cechComplexObjIso_hom_comm (p : ℕ) :
    (cechComplexObjIso U ℱ p).hom ≫ ((CategoryTheory.cechComplexFunctor U).obj ℱ).d p (p + 1) =
      AddCommGrpCat.ofHom (cechD U ℱ p) ≫ (cechComplexObjIso U ℱ (p + 1)).hom := by
  rw [_root_.Stacks.CategoryTheory.CechComplex.d_eq, ofHom_cechD_eq_sum,
    Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, cechComplexObjIso_hom_comp_face]

/-- **The explicit Čech complex is Mathlib's Čech complex.** The degreewise identification of
Tag 01FH is an isomorphism of cochain complexes. -/
noncomputable def cechComplexIso :
    cechComplex U ℱ ≅ (CategoryTheory.cechComplexFunctor U).obj ℱ :=
  HomologicalComplex.Hom.isoOfComponents (fun p ↦ cechComplexObjIso U ℱ p)
    (fun p q (hpq : (ComplexShape.up ℕ).Rel p q) ↦ by
      obtain rfl : p + 1 = q := hpq
      rw [cechComplex_d]
      exact cechComplexObjIso_hom_comm U ℱ p)

/-- In every degree the isomorphism of complexes is the degreewise identification of Tag
01FH. -/
@[simp]
theorem cechComplexIso_hom_f (p : ℕ) :
    (cechComplexIso U ℱ).hom.f p = (cechComplexObjIso U ℱ p).hom :=
  rfl

/-- In every degree the inverse of the isomorphism of complexes is the inverse of the degreewise
identification of Tag 01FH. -/
@[simp]
theorem cechComplexIso_inv_f (p : ℕ) :
    (cechComplexIso U ℱ).inv.f p = (cechComplexObjIso U ℱ p).inv :=
  rfl

/-- **The Čech differential of Mathlib's complex, in the explicit model's spelling.** Composed
with the projection indexed by `y : Fin (p + 2) → I`, the differential from degree `p` to degree
`p + 1` is the alternating sum, over the omitted index, of the restrictions from
`CechCochains.inter U (y ∘ i.succAbove)` to `CechCochains.inter U y`. -/
theorem cechComplexFunctor_d_comp_cechπ (p : ℕ) (y : Fin (p + 2) → I) :
    ((CategoryTheory.cechComplexFunctor U).obj ℱ).d p (p + 1) ≫ cechπ U ℱ (p + 1) y =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (cechπ U ℱ p (y ∘ i.succAbove) ≫ ℱ.map (homOfLE (inter_le_omit U y i)).op) := by
  rw [cechπ_eq, ← Category.assoc, _root_.Stacks.CategoryTheory.CechComplex.d_comp_π,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, cechπ_eq]
  simp only [Category.assoc, interMap_comp_interSectionsIso]

/-- **Stacks 01FH.** The canonical inclusion of the alternating Čech complex into Mathlib's Čech
complex: the inclusion of the alternating subcomplex, followed by the identification of the
explicit Čech complex with Mathlib's. -/
noncomputable def alternatingCechInclusionToCechComplexFunctor :
    alternatingCechComplex U ℱ ⟶ (CategoryTheory.cechComplexFunctor U).obj ℱ :=
  alternatingCechInclusion U ℱ ≫ (cechComplexIso U ℱ).hom

/-- In every degree the transported inclusion is the inclusion of the subgroup of alternating
cochains followed by the degreewise identification of Tag 01FH. -/
@[simp]
theorem alternatingCechInclusionToCechComplexFunctor_f (p : ℕ) :
    (alternatingCechInclusionToCechComplexFunctor U ℱ).f p =
      AddCommGrpCat.ofHom (alternatingSubgroup U ℱ p).subtype ≫
        (cechComplexObjIso U ℱ p).hom := by
  simp [alternatingCechInclusionToCechComplexFunctor]

/-- The Čech cohomology computed from the explicit cochain model is the cohomology of Mathlib's
Čech complex, in every degree. -/
noncomputable def cechHomologyIso (p : ℕ) :
    (cechComplex U ℱ).homology p ≅ ((CategoryTheory.cechComplexFunctor U).obj ℱ).homology p :=
  (HomologicalComplex.homologyFunctor Ab.{max v w} (ComplexShape.up ℕ) p).mapIso
    (cechComplexIso U ℱ)

/-- **Stacks 01FM for Mathlib's Čech complex.** The canonical inclusion of the alternating Čech
complex into `CategoryTheory.cechComplexFunctor` is a homotopy equivalence: it is the inclusion
of the alternating subcomplex, which is a homotopy equivalence by Tag 01FM, followed by the
isomorphism of complexes `Stacks.Cech.cechComplexIso`. -/
theorem alternatingCechInclusionToCechComplexFunctor_homotopyEquivalence [LinearOrder I] :
    (HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.up ℕ))
      (alternatingCechInclusionToCechComplexFunctor U ℱ) := by
  obtain ⟨e, he⟩ := alternatingCechInclusion_homotopyEquivalence U ℱ
  refine ⟨e.trans (HomotopyEquiv.ofIso (cechComplexIso U ℱ)), ?_⟩
  rw [HomotopyEquiv.trans_hom, he]
  rfl

section Alternating

variable [LinearOrder I]

/-- **Stacks 01FM for Mathlib's Čech complex, as a chosen homotopy equivalence.** The
alternating Čech complex is homotopy equivalent to Mathlib's Čech complex: a homotopy inverse
of the inclusion of the alternating subcomplex, composed with
`Stacks.Cech.cechComplexIso`. Unlike
`Stacks.Cech.alternatingCechInclusionToCechComplexFunctor_homotopyEquivalence`, which only
asserts that such an equivalence exists, this is the equivalence itself, so that the induced
isomorphism on cohomology can be named. -/
noncomputable def alternatingCechHomotopyEquiv :
    HomotopyEquiv (alternatingCechComplex U ℱ)
      ((CategoryTheory.cechComplexFunctor U).obj ℱ) :=
  (alternatingCechInclusion_homotopyEquivalence U ℱ).choose.trans
    (HomotopyEquiv.ofIso (cechComplexIso U ℱ))

/-- The homotopy equivalence of `Stacks.Cech.alternatingCechHomotopyEquiv` is the canonical
inclusion followed by the comparison isomorphism. -/
theorem alternatingCechHomotopyEquiv_hom :
    (alternatingCechHomotopyEquiv U ℱ).hom =
      alternatingCechInclusion U ℱ ≫ (cechComplexIso U ℱ).hom :=
  congrArg (fun f : alternatingCechComplex U ℱ ⟶ cechComplex U ℱ =>
      f ≫ (cechComplexIso U ℱ).hom)
    (alternatingCechInclusion_homotopyEquivalence U ℱ).choose_spec

/-- The canonical inclusion of the alternating Čech complex into Mathlib's Čech complex is a
homotopy equivalence, stated for the composite
`alternatingCechInclusion U ℱ ≫ (cechComplexIso U ℱ).hom` rather than for the abbreviation
`Stacks.Cech.alternatingCechInclusionToCechComplexFunctor`. -/
theorem alternatingCechInclusion_comp_homotopyEquivalence :
    (HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.up ℕ))
      (alternatingCechInclusion U ℱ ≫ (cechComplexIso U ℱ).hom) :=
  ⟨alternatingCechHomotopyEquiv U ℱ, alternatingCechHomotopyEquiv_hom U ℱ⟩

/-- The canonical inclusion of the alternating Čech complex into Mathlib's Čech complex is a
quasi-isomorphism. -/
theorem quasiIso_alternatingCechInclusion_comp :
    QuasiIso (alternatingCechInclusion U ℱ ≫ (cechComplexIso U ℱ).hom) :=
  (HomologicalComplex.mem_quasiIso_iff _).mp
    (homotopyEquivalences_le_quasiIso AddCommGrpCat (ComplexShape.up ℕ) _
      (alternatingCechInclusion_comp_homotopyEquivalence U ℱ))

/-- **The alternating Čech complex computes Čech cohomology.** In every degree its cohomology
is the cohomology of Mathlib's Čech complex, by the map induced by the canonical inclusion. -/
noncomputable def alternatingCechHomologyIso (n : ℕ) :
    (alternatingCechComplex U ℱ).homology n ≅
      ((CategoryTheory.cechComplexFunctor U).obj ℱ).homology n :=
  (alternatingCechHomotopyEquiv U ℱ).toHomologyIso n

end Alternating

end Stacks.Cech

end
