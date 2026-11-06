module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
import StacksCore.Tactic.StacksAttribute

/-!
# The alternating Čech complex

Let `X` be a topological space, `U : I → Opens X` a family of open subsets and `ℱ` an abelian
presheaf on `X`. A Čech cochain of degree `p` is a family of sections
`s_{i_0 … i_p} ∈ ℱ(U_{i_0} ∩ … ∩ U_{i_p})`, and such a cochain is *alternating* when it
vanishes on tuples with a repeated index and changes by the sign of a permutation when the
indices are permuted. These cochains form a subcomplex of the Čech complex, the *alternating
Čech complex* of Stacks 01FH, and the inclusion of that subcomplex is the canonical map the
source displays.

This file builds that subcomplex and the inclusion, and identifies the Čech complex in the
explicit model of cochain families with Mathlib's `CategoryTheory.cechComplexFunctor`, which
is built from categorical products of sections over categorical products of the opens.

## Main definitions

* `Stacks.Cech.alternatingCechComplex`: the alternating Čech complex of an abelian presheaf
  with respect to an indexed family of opens.
* `Stacks.Cech.cechComplex`: the usual Čech complex in the same explicit model.
* `Stacks.Cech.alternatingCechInclusion`: the canonical inclusion of the alternating Čech
  complex into the usual one, which is the morphism of complexes Stacks 01FH displays.
* `Stacks.Cech.cechComplexObjIso`: the degreewise identification of the explicit model with
  Mathlib's `CategoryTheory.cechComplexFunctor`.

## Main results

* `Stacks.Cech.alternatingCechComplex_X` and `Stacks.Cech.alternatingCechComplex_d` identify
  the objects and the consecutive differentials.
* `Stacks.Cech.alternatingCechInclusion_f`: every component of the canonical inclusion is the
  inclusion of the subgroup of alternating cochains.
* `Stacks.Cech.isLimitCechFan`: the degree-`p` term of Mathlib's Čech complex is the product
  of the groups of sections over the intersections, in the spelling of the explicit model.

## Implementation notes

The explicit cochains, the alternating subgroup and the Čech differential are
`CechCochains.Cochain`, `CechCochains.alternatingSubgroup` and `CechCochains.cechD`, developed
for the comparison of the ordered and alternating Čech complexes in Tag 01FJ. Taking the usual and
the alternating complex in one and the same model is what makes their canonical comparison
*literally* a subgroup inclusion rather than a construction.

The explicit model is identified with Mathlib's `CategoryTheory.cechComplexFunctor` degreewise
by `cechComplexObjIso`, which is obtained from the degreewise description of the Čech complex
proved for Tag 01FG in `StacksFrontier.CategoryTheory.Sites.CechComplex` — `inter_eq_iInf`
identifies the categorical product of the selected opens with their infimum, so no choice of
limit has to be unfolded. For that comparison the ambient universe of abelian groups must
contain the indexing universe, as the products in `CategoryTheory.cechComplexFunctor` require;
the explicit complexes themselves allow independent indexing and coefficient universes.

The *chain-level* comparison `cechComplex U F ≅ (cechComplexFunctor U).obj F` is
`Stacks.Cech.cechComplexIso`, assembled from `Stacks.Cech.cechComplexObjIso_hom_comm`.

The construction depends only on the indexed family of opens, so neither the covered open nor
a covering equation is an argument: a client supplies those only where it uses them.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

namespace Stacks.Cech

open CechCochains

variable {X : TopCat.{u}} {I : Type v} (U : I → Opens X) (ℱ : TopCat.Presheaf Ab.{w} X)

/-- The Čech differential restricted to alternating cochains. -/
@[implicit_reducible]
def alternatingCechDifferential (p : ℕ) :
    AddCommGrpCat.of (alternatingSubgroup U ℱ p) ⟶
      AddCommGrpCat.of (alternatingSubgroup U ℱ (p + 1)) :=
  AddCommGrpCat.ofHom <|
    ((cechD U ℱ p).comp (alternatingSubgroup U ℱ p).subtype).codRestrict
      (alternatingSubgroup U ℱ (p + 1))
      (fun s ↦ cechD_mem_alternating U ℱ p s.1 s.2)

/-- Two consecutive restricted Čech differentials compose to zero. -/
theorem alternatingCechDifferential_comp (p : ℕ) :
    alternatingCechDifferential U ℱ p ≫ alternatingCechDifferential U ℱ (p + 1) = 0 := by
  ext s
  exact cechD_cechD U ℱ p s.1

/-- The usual Čech complex, presented using explicit families of sections.

This is the concrete model of Mathlib's `CategoryTheory.cechComplexFunctor` used by the
alternating-subcomplex construction. -/
@[implicit_reducible]
noncomputable def cechComplex : CochainComplex Ab ℕ :=
  CochainComplex.of
    (fun p ↦ AddCommGrpCat.of (Cochain U ℱ p))
    (fun p ↦ AddCommGrpCat.ofHom (cechD U ℱ p))
    (fun p ↦ AddCommGrpCat.hom_ext <| AddMonoidHom.ext <| cechD_cechD U ℱ p)

/-- The objects of the explicit usual Čech complex are the full cochain groups. -/
@[simp]
theorem cechComplex_X (p : ℕ) :
    (cechComplex U ℱ).X p = AddCommGrpCat.of (Cochain U ℱ p) := by simp [cechComplex]

/-- The consecutive differentials of the explicit usual Čech complex. -/
@[simp]
theorem cechComplex_d (p : ℕ) :
    (cechComplex U ℱ).d p (p + 1) = AddCommGrpCat.ofHom (cechD U ℱ p) :=
  CochainComplex.of_d
    (fun p ↦ AddCommGrpCat.of (Cochain U ℱ p))
    (fun p ↦ AddCommGrpCat.ofHom (cechD U ℱ p)) p

/-- **Stacks 01FH.** The alternating Čech complex associated to an abelian presheaf and an
indexed family of open subsets. -/
@[stacks 01FH, implicit_reducible, ega "0 12.1.2" "alternating Čech complex"]
noncomputable def alternatingCechComplex : CochainComplex Ab ℕ :=
  CochainComplex.of
    (fun p ↦ AddCommGrpCat.of (alternatingSubgroup U ℱ p))
    (alternatingCechDifferential U ℱ)
    (alternatingCechDifferential_comp U ℱ)

/-- The degree-`p` object of the alternating Čech complex is the group of alternating Čech
cochains. -/
@[simp]
theorem alternatingCechComplex_X (p : ℕ) :
    (alternatingCechComplex U ℱ).X p = AddCommGrpCat.of (alternatingSubgroup U ℱ p) := by
  simp [alternatingCechComplex]

/-- The differential from degree `p` to degree `p + 1` is the restricted Čech differential. -/
@[simp]
theorem alternatingCechComplex_d (p : ℕ) :
    (alternatingCechComplex U ℱ).d p (p + 1) = alternatingCechDifferential U ℱ p :=
  CochainComplex.of_d
    (fun p ↦ AddCommGrpCat.of (alternatingSubgroup U ℱ p))
    (alternatingCechDifferential U ℱ) p

/-- **Stacks 01FH.** The canonical inclusion of the alternating Čech complex into the usual
Čech complex: in each degree it is the inclusion of the subgroup of alternating cochains. -/
@[stacks 01FH "the canonical inclusion", implicit_reducible]
noncomputable def alternatingCechInclusion :
    alternatingCechComplex U ℱ ⟶ cechComplex U ℱ :=
  CochainComplex.ofHom
    (fun p ↦ AddCommGrpCat.ofHom (alternatingSubgroup U ℱ p).subtype)
    (fun p ↦ by
      rw [alternatingCechComplex_d, cechComplex_d]
      rfl)

/-- In every degree, the canonical map from the alternating Čech complex is the inclusion of
the alternating subgroup into all cochains. -/
@[simp]
theorem alternatingCechInclusion_f (p : ℕ) :
    (alternatingCechInclusion U ℱ).f p =
      AddCommGrpCat.ofHom (alternatingSubgroup U ℱ p).subtype := by
  simp [alternatingCechInclusion]

/-- The categorical product of a tuple of opens identifies with their intersection. -/
noncomputable abbrev cechIntersectionIso {p : ℕ} (i : Fin p → I) :
    ∏ᶜ (U ∘ i) ≅ inter U i :=
  limit.isoLimitCone ⟨_, Preorder.isLimitIInf (U ∘ i)⟩

section Comparison

/-- The intersection of the members of the family selected by a tuple, as formed by the
degreewise description of Mathlib's Čech complex (Tag 01FG), is the infimum `CechCochains.inter`
used by the explicit model. -/
theorem cechComplexInter_eq {p : ℕ} (x : Fin p → I) :
    _root_.Stacks.CategoryTheory.CechComplex.inter U x = inter U x :=
  _root_.Stacks.CategoryTheory.CechComplex.inter_eq_iInf U x

variable (F : TopCat.Presheaf Ab.{max v w} X)

/-- The projection of the degree-`p` term of Mathlib's Čech complex onto the factor indexed by
a tuple, retyped so that the intersection is spelled `CechCochains.inter`. -/
noncomputable def cechπ (p : ℕ) (x : Fin (p + 1) → I) :
    ((CategoryTheory.cechComplexFunctor U).obj F).X p ⟶ F.obj (op (inter U x)) :=
  _root_.Stacks.CategoryTheory.CechComplex.π U F p x ≫
    F.map (eqToHom (cechComplexInter_eq U x).symm).op

/-- The degree-`p` term of Mathlib's Čech complex is the product, indexed by the tuples
`x : Fin (p + 1) → I`, of the groups of sections over the intersections `CechCochains.inter U x`,
with projections `cechπ`. This is the degreewise description of Tag 01FG, transported along
`cechComplexInter_eq`. -/
noncomputable def isLimitCechFan (p : ℕ) :
    IsLimit (Fan.mk (((CategoryTheory.cechComplexFunctor U).obj F).X p) (cechπ U F p)) := by
  let e : (Discrete.functor fun x : Fin (p + 1) → I ↦
        F.obj (op (_root_.Stacks.CategoryTheory.CechComplex.inter U x))) ≅
      (Discrete.functor fun x : Fin (p + 1) → I ↦ F.obj (op (inter U x))) :=
    Discrete.natIso fun j ↦ F.mapIso (eqToIso (cechComplexInter_eq U j.as).symm).op
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv e
    (Fan.mk (((CategoryTheory.cechComplexFunctor U).obj F).X p)
      (_root_.Stacks.CategoryTheory.CechComplex.π U F p))).symm
    (_root_.Stacks.CategoryTheory.CechComplex.isLimitFan U F p)) (Cone.ext (Iso.refl _) ?_)
  rintro ⟨x⟩
  simp [cechπ, e]

/-- The explicit group of degree-`p` Čech cochains is the degree-`p` term of Mathlib's Čech
complex: both are the product of the groups of sections over the intersections. -/
noncomputable def cechComplexObjIso (p : ℕ) :
    AddCommGrpCat.of (Cochain U F p) ≅
      ((CategoryTheory.cechComplexFunctor U).obj F).X p :=
  IsLimit.conePointUniqueUpToIso
    (AddCommGrpCat.HasLimit.productLimitCone
      (fun x : Fin (p + 1) → I ↦ F.obj (op (inter U x)))).isLimit
    (isLimitCechFan U F p)

/-- The identification of the explicit cochain group with the categorical product is the one
sending a cochain to the family of its values. -/
theorem cechComplexObjIso_hom_comp_cechπ (p : ℕ) (x : Fin (p + 1) → I) :
    (cechComplexObjIso U F p).hom ≫
        (Fan.mk (((CategoryTheory.cechComplexFunctor U).obj F).X p)
          (cechπ U F p)).π.app ⟨x⟩ =
      (AddCommGrpCat.HasLimit.productLimitCone
        (fun x : Fin (p + 1) → I ↦ F.obj (op (inter U x)))).cone.π.app ⟨x⟩ :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (AddCommGrpCat.HasLimit.productLimitCone
      (fun x : Fin (p + 1) → I ↦ F.obj (op (inter U x)))).isLimit
    (isLimitCechFan U F p) ⟨x⟩

end Comparison

end Stacks.Cech
