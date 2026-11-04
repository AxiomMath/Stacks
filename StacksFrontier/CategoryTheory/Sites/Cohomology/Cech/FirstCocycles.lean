module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroAndSheafCondition
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cochains and the first Čech cohomology group of a family of morphisms

Let `C` be a category, let `X` be an object of `C` and let `E = {U_i → X}` be a family of
morphisms with target `X` whose finite nonempty fibre products exist. The Čech complex of
Stacks 03AM has as its degree-`n` term a product indexed by `(n+1)`-tuples of members of the
family, so a degree-`n` cochain is the same thing as a family of sections, one over each
iterated fibre product `U_{i_0} ×_X ⋯ ×_X U_{i_n}`, and the differential is the usual
alternating sum of the restrictions along the face projections.

This file records that description, together with the resulting explicit presentation of the
first Čech cohomology group as `Ȟ¹(E, F) = ker d¹ / im d⁰`, and identifies it with the
degree-one homology of the Čech complex.

## Main definitions

* `Stacks.CechSite.cechCochain`: degree-`n` Čech cochains, as families of sections indexed by
  `(n+1)`-tuples.
* `Stacks.CechSite.faceProjection`: the projection forgetting one factor of an iterated fibre
  product.
* `Stacks.CechSite.cechDifferential`: the Čech differential on cochain families.
* `Stacks.CechSite.cocycles1` and `Stacks.CechSite.coboundaries1`: the Čech `1`-cocycles and
  `1`-coboundaries.
* `Stacks.CechSite.cechH1`: first Čech cohomology, as `ker d¹ / im d⁰`.
* `Stacks.CechSite.cechCohomologyOneEquiv`: the identification of `cechH1` with the
  degree-one homology of the Čech complex.

## Main results

* `Stacks.CechSite.cechDifferential_apply`: the alternating-sum formula for the differential
  on cochain families.
* `Stacks.CechSite.mem_cocycles1_iff'`: the cocycle condition `c₁₂ + c₀₁ = c₀₂`.
* `Stacks.CechSite.mem_coboundaries1_iff`: a cocycle is a coboundary exactly when it is the
  differential of a degree-zero cochain.
* `Stacks.CechSite.cls_eq_zero_iff`: a cocycle has vanishing class exactly when it is a
  coboundary.
* `Stacks.CechSite.subsingleton_cechCohomologyOne_iff`: the degree-one Čech cohomology of the
  Čech complex vanishes exactly when every `1`-cocycle is a coboundary.

## Implementation notes

The faces of an iterated fibre product are indexed by `Fin.succAbove`: for a tuple
`k : Fin (n + 2) → E.I₀` the `j`-th face is the tuple `fun b ↦ k (j.succAbove b)`, and the
corresponding projection is `faceProjection`. The tuple is kept in that form throughout,
rather than being normalised to an explicit list of indices, because the object over which a
cochain is evaluated depends on the indexing function and not merely on its values.

The comparison with the Čech complex factors through the degree-one cycles. The degree-`n`
term of the complex is a product of abelian groups, which `Stacks.CechSite.productAddEquiv`
identifies with the dependent function type; the differential is transported along that
identification, and the alternating-sum formula is read off from the differential of the
alternating-coface-map complex. The homology of a cochain complex of abelian groups in a
positive degree is then the quotient of the kernel of the outgoing differential by the image
of the incoming one, which is what `homologySuccEquivQuotient` records.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03AL](https://stacks.math.columbia.edu/tag/03AL)
-/

@[expose] public section

universe a w v u

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

/-- Evaluating a finite sum of morphisms of abelian groups is the sum of the evaluations. -/
public lemma hom_sum_apply {M N : AddCommGrpCat.{a}} {ι : Type*} (s : Finset ι)
    (g : ι → (M ⟶ N)) (z : M) : (∑ j ∈ s, g j) z = ∑ j ∈ s, g j z := by
  show (AddCommGrpCat.homAddEquiv (∑ j ∈ s, g j)) z = _
  rw [map_sum]
  exact AddMonoidHom.finsetSum_apply _ _ _

variable {C : Type u} [Category.{v} C]

section Faces

variable {X : C} (E : PreZeroHypercover.{w} X)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- The `j`-th face projection of an iterated fibre product: the map to the iterated fibre
product of the subfamily obtained by forgetting the `j`-th factor. -/
public noncomputable def faceProjection {n : ℕ} (k : Fin (n + 2) → E.I₀) (j : Fin (n + 2)) :
    (∏ᶜ (fun b : Fin (n + 2) ↦ Over.mk (E.f (k b))) : Over X) ⟶
      ∏ᶜ (fun b : Fin (n + 1) ↦ Over.mk (E.f (k (j.succAbove b)))) :=
  Pi.lift (fun b ↦ Pi.π _ (j.succAbove b))

end Faces

section Cochains

variable {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a})

/-- The alternating-sum formula for the Čech differential, evaluated at a tuple of indices.
The statement never mentions the Čech complex, only the `Pi.lift`s that its differential
unfolds to, so every step of its proof stays inside the products `∏ᶜ cochainFactor E F n`;
`pi_π_differential_apply` then applies it to an actual cochain. -/
public lemma pi_π_alternatingSumFaces_apply (n : ℕ) (k : Fin (n + 2) → E.I₀)
    (y : (∏ᶜ cochainFactor E F n : AddCommGrpCat.{a})) :
    Pi.π (cochainFactor E F (n + 1)) k
      ((∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          Pi.lift (fun l : Fin (n + 2) → E.I₀ ↦
            Pi.π (cochainFactor E F n) (fun b ↦ l (j.succAbove b)) ≫
              F.map (Pi.lift (fun b : Fin (n + 1) ↦
                Pi.π (fun c : Fin (n + 2) ↦ Over.mk (E.f (l c))) (j.succAbove b))).left.op)) y) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        F.map (faceProjection E k j).left.op
          (Pi.π (cochainFactor E F n) (fun b ↦ k (j.succAbove b)) y) := by
  rw [← ConcreteCategory.comp_apply, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Pi.lift_π, hom_sum_apply, AddCommGrpCat.hom_zsmul,
    AddMonoidHom.zsmul_apply, ConcreteCategory.comp_apply, faceProjection]

/-- The Čech differential of a cochain, read off at a tuple of indices: the alternating sum
of the restrictions of the faces of the tuple along the face projections. -/
public lemma pi_π_differential_apply (n : ℕ) (x : (cechComplex E F).X n)
    (k : Fin (n + 2) → E.I₀) :
    Pi.π (cochainFactor E F (n + 1)) k ((cechComplex E F).d n (n + 1) x) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        F.map (faceProjection E k j).left.op
          (Pi.π (cochainFactor E F n) (fun b ↦ k (j.succAbove b)) x) := by
  simp only [cechComplex, cechComplexFunctor, Functor.comp_obj,
    FormalCoproduct.cochainComplexFunctor_obj_d, CochainComplex.of.d, ↓reduceDIte, eqToHom_refl,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  exact pi_π_alternatingSumFaces_apply E F n k x

/-- Degree-`n` Čech cochains of `F` along `E`: families of sections, one over each iterated
fibre product indexed by an `(n+1)`-tuple of members of the family. -/
public noncomputable abbrev cechCochain (n : ℕ) :=
  ∀ k : Fin (n + 1) → E.I₀, cochainFactor E F n k

/-- The Čech differential on cochain families, transported from the differential of the Čech
complex along the identification of its terms with products. -/
public noncomputable def cechDifferential (n : ℕ) :
    cechCochain E F n →+ cechCochain E F (n + 1) :=
  ((productAddEquiv (cochainFactor E F (n + 1))).toAddMonoidHom.comp
      ((cechComplex E F).d n (n + 1)).hom).comp
    (productAddEquiv (cochainFactor E F n)).symm.toAddMonoidHom

/-- The Čech differential on cochain families is the differential of the Čech complex. -/
public lemma cechDifferential_productAddEquiv (n : ℕ) (x : (cechComplex E F).X n) :
    cechDifferential E F n (productAddEquiv (cochainFactor E F n) x) =
      productAddEquiv (cochainFactor E F (n + 1)) ((cechComplex E F).d n (n + 1) x) :=
  congrArg (fun y : (∏ᶜ cochainFactor E F n : AddCommGrpCat.{a}) ↦
      productAddEquiv (cochainFactor E F (n + 1)) ((cechComplex E F).d n (n + 1) y))
    ((productAddEquiv (cochainFactor E F n)).symm_apply_apply x)

/-- The alternating-sum formula for the Čech differential of a cochain family. -/
public lemma cechDifferential_apply (n : ℕ) (c : cechCochain E F n) (k : Fin (n + 2) → E.I₀) :
    cechDifferential E F n c k =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        F.map (faceProjection E k j).left.op (c (fun b ↦ k (j.succAbove b))) := by
  have hc : ∀ l : Fin (n + 1) → E.I₀,
      Pi.π (cochainFactor E F n) l ((productAddEquiv (cochainFactor E F n)).symm c) = c l :=
    fun l ↦ congrFun ((productAddEquiv (cochainFactor E F n)).apply_symm_apply c) l
  have hbridge : (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        F.map (faceProjection E k j).left.op
          (Pi.π (cochainFactor E F n) (fun b ↦ k (j.succAbove b))
            ((productAddEquiv (cochainFactor E F n)).symm c))) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        F.map (faceProjection E k j).left.op (c (fun b ↦ k (j.succAbove b))) :=
    Finset.sum_congr rfl fun j _ ↦ by rw [hc]
  exact (pi_π_differential_apply E F n
    ((productAddEquiv (cochainFactor E F n)).symm c) k).trans hbridge

/-- The Čech differential of a degree-zero cochain is the difference of the two restrictions
of the family to the pairwise iterated fibre products. -/
public lemma cechDifferential_zero_apply (t : cechCochain E F 0) (k : Fin 2 → E.I₀) :
    cechDifferential E F 0 t k =
      F.map (faceProjection E k 0).left.op (t fun b ↦ k ((0 : Fin 2).succAbove b)) -
        F.map (faceProjection E k 1).left.op (t fun b ↦ k ((1 : Fin 2).succAbove b)) := by
  rw [cechDifferential_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul, ← sub_eq_add_neg]

/-- The Čech differential of a degree-one cochain, as the alternating sum of its three
faces. -/
public lemma cechDifferential_one_apply (c : cechCochain E F 1) (k : Fin 3 → E.I₀) :
    cechDifferential E F 1 c k =
      F.map (faceProjection E k 0).left.op (c fun b ↦ k ((0 : Fin 3).succAbove b)) -
          F.map (faceProjection E k 1).left.op (c fun b ↦ k ((1 : Fin 3).succAbove b)) +
        F.map (faceProjection E k 2).left.op (c fun b ↦ k ((2 : Fin 3).succAbove b)) := by
  rw [cechDifferential_apply, Fin.sum_univ_three]
  norm_num [← sub_eq_add_neg]

/-- The Čech differential squares to zero on cochain families. -/
public lemma cechDifferential_cechDifferential (n : ℕ) (t : cechCochain E F n) :
    cechDifferential E F (n + 1) (cechDifferential E F n t) = 0 := by
  obtain ⟨x, rfl⟩ : ∃ x : (cechComplex E F).X n,
      productAddEquiv (cochainFactor E F n) x = t :=
    (productAddEquiv (cochainFactor E F n)).surjective t
  rw [cechDifferential_productAddEquiv, cechDifferential_productAddEquiv]
  have h : (cechComplex E F).d (n + 1) (n + 2) ((cechComplex E F).d n (n + 1) x) = 0 := by
    rw [← ConcreteCategory.comp_apply, (cechComplex E F).d_comp_d n (n + 1) (n + 2)]
    rfl
  rw [h]
  exact map_zero (productAddEquiv (cochainFactor E F (n + 2)))

/-- The Čech `1`-cocycles: the kernel of the degree-one Čech differential. -/
public noncomputable def cocycles1 : AddSubgroup (cechCochain E F 1) :=
  (cechDifferential E F 1).ker

/-- A degree-one cochain is a cocycle exactly when the alternating sum of its three faces
vanishes over every triple iterated fibre product. -/
public lemma mem_cocycles1_iff (c : cechCochain E F 1) :
    c ∈ cocycles1 E F ↔ ∀ k : Fin 3 → E.I₀,
      ∑ j : Fin 3, (-1 : ℤ) ^ (j : ℕ) •
        F.map (faceProjection E k j).left.op (c (fun b ↦ k (j.succAbove b))) = 0 := by
  rw [cocycles1, AddMonoidHom.mem_ker, funext_iff]
  exact forall_congr' fun k ↦ by rw [cechDifferential_apply, Pi.zero_apply]

/-- The cocycle condition in its classical form: the restrictions of a `1`-cocycle to the
triple iterated fibre products satisfy `c₁₂ + c₀₁ = c₀₂`. -/
public lemma mem_cocycles1_iff' (c : cechCochain E F 1) :
    c ∈ cocycles1 E F ↔ ∀ k : Fin 3 → E.I₀,
      F.map (faceProjection E k 0).left.op (c fun b ↦ k ((0 : Fin 3).succAbove b)) +
          F.map (faceProjection E k 2).left.op (c fun b ↦ k ((2 : Fin 3).succAbove b)) =
        F.map (faceProjection E k 1).left.op (c fun b ↦ k ((1 : Fin 3).succAbove b)) := by
  rw [cocycles1, AddMonoidHom.mem_ker, funext_iff]
  refine forall_congr' fun k ↦ ?_
  rw [cechDifferential_one_apply, Pi.zero_apply, sub_add_eq_add_sub, sub_eq_zero]

/-- Coboundaries are cocycles, because the Čech differential squares to zero. -/
public lemma cechDifferential_mem_cocycles1 (t : cechCochain E F 0) :
    cechDifferential E F 0 t ∈ cocycles1 E F :=
  cechDifferential_cechDifferential E F 0 t

/-- The Čech `1`-coboundaries, as a subgroup of the `1`-cocycles. -/
public noncomputable def coboundaries1 : AddSubgroup (cocycles1 E F) :=
  (cechDifferential E F 0).range.comap (cocycles1 E F).subtype

/-- A cocycle is a coboundary exactly when it is the Čech differential of a degree-zero
cochain. -/
public lemma mem_coboundaries1_iff (c : cocycles1 E F) :
    c ∈ coboundaries1 E F ↔
      ∃ t : cechCochain E F 0, cechDifferential E F 0 t = (c : cechCochain E F 1) := by
  rw [coboundaries1, AddSubgroup.mem_comap]
  exact AddMonoidHom.mem_range

/-- First Čech cohomology `Ȟ¹(E, F) = ker d¹ / im d⁰`, as an explicit quotient of cocycle
families. -/
public noncomputable abbrev cechH1 := cocycles1 E F ⧸ coboundaries1 E F

/-- The class in `Ȟ¹(E, F)` of a Čech `1`-cocycle. -/
public noncomputable def cls (c : cocycles1 E F) : cechH1 E F := QuotientAddGroup.mk c

/-- A cocycle has vanishing Čech class exactly when it is a coboundary. -/
public lemma cls_eq_zero_iff (c : cocycles1 E F) :
    cls E F c = 0 ↔
      ∃ t : cechCochain E F 0, cechDifferential E F 0 t = (c : cechCochain E F 1) := by
  rw [cls, QuotientAddGroup.eq_zero_iff]
  exact mem_coboundaries1_iff E F c

/-- First Čech cohomology vanishes exactly when every `1`-cocycle is a coboundary. -/
public theorem subsingleton_cechH1_iff :
    Subsingleton (cechH1 E F) ↔
      ∀ c : cocycles1 E F, ∃ t : cechCochain E F 0,
        cechDifferential E F 0 t = (c : cechCochain E F 1) := by
  refine ⟨fun _ c ↦ (cls_eq_zero_iff E F c).1 (Subsingleton.elim _ _), fun h ↦ ⟨fun x y ↦ ?_⟩⟩
  have key : ∀ a : cocycles1 E F, (QuotientAddGroup.mk a : cechH1 E F) = 0 :=
    fun a ↦ (cls_eq_zero_iff E F a).2 (h a)
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [key, key]

/-- A degree-one cochain of the Čech complex is a cycle exactly when the corresponding
family of sections is a Čech `1`-cocycle. -/
public lemma productAddEquiv_mem_cocycles1_iff (x : (cechComplex E F).X 1) :
    productAddEquiv (cochainFactor E F 1) x ∈ cocycles1 E F ↔
      (cechComplex E F).d 1 2 x = 0 := by
  rw [cocycles1, AddMonoidHom.mem_ker, cechDifferential_productAddEquiv]
  exact map_eq_zero_iff _ (productAddEquiv (cochainFactor E F 2)).injective

/-- The degree-one cycles of the Čech complex are the Čech `1`-cocycles. -/
public noncomputable def kerEquivCocycles1 :
    AddMonoidHom.ker ((cechComplex E F).d 1 2).hom ≃+ cocycles1 E F where
  toFun x := ⟨productAddEquiv (cochainFactor E F 1) x.1,
    (productAddEquiv_mem_cocycles1_iff E F x.1).2 (AddMonoidHom.mem_ker.1 x.2)⟩
  invFun c := ⟨(productAddEquiv (cochainFactor E F 1)).symm c.1, by
    refine AddMonoidHom.mem_ker.2 ((productAddEquiv_mem_cocycles1_iff E F _).1 ?_)
    rw [AddEquiv.apply_symm_apply]
    exact c.2⟩
  left_inv x := Subtype.ext ((productAddEquiv (cochainFactor E F 1)).symm_apply_apply _)
  right_inv c := Subtype.ext ((productAddEquiv (cochainFactor E F 1)).apply_symm_apply _)
  map_add' x y := Subtype.ext (map_add (productAddEquiv (cochainFactor E F 1)) _ _)

/-- Under the identification of degree-one cycles with `1`-cocycles, the image of the
degree-zero differential is the subgroup of `1`-coboundaries. -/
public lemma range_map_abToCycles :
    (AddMonoidHom.range ((cechComplex E F).sc' 0 1 2).abToCycles).map
        (kerEquivCocycles1 E F).toAddMonoidHom = coboundaries1 E F := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := hz
    obtain ⟨t, ht⟩ := hy
    have h1 : ((kerEquivCocycles1 E F y : cocycles1 E F) : cechCochain E F 1) =
        (z : cechCochain E F 1) := congrArg Subtype.val hyz
    have h2 : (cechComplex E F).d 0 1 t = (y : (cechComplex E F).X 1) :=
      congrArg Subtype.val ht
    refine (mem_coboundaries1_iff E F z).2 ⟨productAddEquiv (cochainFactor E F 0) t, ?_⟩
    exact (cechDifferential_productAddEquiv E F 0 t).trans
      ((congrArg (productAddEquiv (cochainFactor E F 1)) h2).trans h1)
  · intro z hz
    obtain ⟨t, ht⟩ := (mem_coboundaries1_iff E F z).1 hz
    obtain ⟨t₀, rfl⟩ := (productAddEquiv (cochainFactor E F 0)).surjective t
    refine ⟨((cechComplex E F).sc' 0 1 2).abToCycles t₀, ⟨_, rfl⟩, ?_⟩
    exact Subtype.ext ((cechDifferential_productAddEquiv E F 0 t₀).symm.trans ht)

end Cochains

/-- The homology of a cochain complex of abelian groups in a degree with a chosen predecessor
and successor is the quotient of the kernel of the outgoing differential by the image of the
incoming one. -/
public noncomputable def homologyEquivQuotient
    (K : CochainComplex AddCommGrpCat.{a} ℕ) (i j k : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k) :
    (K.homology j : Type a) ≃+
      (AddMonoidHom.ker (K.d j k).hom ⧸ AddMonoidHom.range (K.sc' i j k).abToCycles) :=
  (K.homologyIsoSc' i j k hi hk ≪≫ (K.sc' i j k).abHomologyIso).addCommGroupIsoToAddEquiv

/-- The canonical identification of the explicit first Čech cohomology group with the
degree-one homology of the Čech complex. -/
public noncomputable def cechCohomologyOneEquiv {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    (cechCohomology E (A := AddCommGrpCat.{a}) F 1 : Type a) ≃+ cechH1 E F :=
  (homologyEquivQuotient (cechComplex E F) 0 1 2 (by simp) (by simp)).trans
    (QuotientAddGroup.congr
      (AddMonoidHom.range ((cechComplex E F).sc' 0 1 2).abToCycles) (coboundaries1 E F)
      (kerEquivCocycles1 E F) (range_map_abToCycles E F))

/-- The degree-one homology of the Čech complex vanishes exactly when every explicit Čech
`1`-cocycle is a coboundary. -/
public theorem subsingleton_cechCohomologyOne_iff {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    Subsingleton (cechCohomology E (A := AddCommGrpCat.{a}) F 1 : Type a) ↔
      ∀ c : cocycles1 E F, ∃ t : cechCochain E F 0,
        cechDifferential E F 0 t = (c : cechCochain E F 1) :=
  (cechCohomologyOneEquiv E F).toEquiv.subsingleton_congr.trans (subsingleton_cechH1_iff E F)

end Stacks.CechSite
