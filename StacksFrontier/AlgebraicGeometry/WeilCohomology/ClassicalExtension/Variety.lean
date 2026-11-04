module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Pushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Kunneth
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataAxioms
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The extension of a classical Weil cohomology theory agrees with it on varieties

The data (D0)–(D3) obtained from a classical Weil cohomology theory `H^*` by taking products over
connected components satisfy (A), (B) and (C)
(`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilDataAxioms`). A smooth projective
variety `V` is connected, so it is its own unique connected component, and the extended
cohomology of `V` is `H^*(V)`: as graded `F`-algebras, naturally in `V`
(`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.varietyEquiv`).

## Main definitions

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilDataAxioms`: the data (D0)–(D3) of
  the extension with axioms (A), (B), (C).
* `Stacks.WeilCohomology.SmoothProjective.compIso`: a component of a variety `V` is `V`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.varietyEquiv`: the `F`-algebra isomorphism
  between the extended and the classical cohomology of `V`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.varietyGradeEquiv`: its degree-`n` part,
  `H^n_ext(V) ≅ H^n(V)`.

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.varietyEquiv_extPull`,
  `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.varietyGradeEquiv_pullDeg`: naturality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum

universe u v

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

/-- **The extension of a classical Weil cohomology theory to all smooth projective schemes**:
data (D0)–(D3) satisfying (A), (B) and (C). -/
def toWeilDataAxioms : WeilDataAxioms k F where
  toWeilData := T.toWeilData
  poincareDuality := T.poincareDuality
  kunneth := T.toWeilData_kunneth
  cycleClassAxiom := T.cycleClassAxiom

end ClassicalWeilCohomologyTheory

/-! ### A variety is its own connected component -/

namespace SmoothProjective

variable {k : Type u} [Field k] (V : (SmoothProjective k).FullSubcategory)

/-- The underlying space of a smooth projective variety is connected. -/
instance connectedSpace_left : ConnectedSpace ((toSchemeCat k).obj V).obj.left := by
  have : IsIntegral V.obj.left := V.2.1.toIsVariety.toIsIntegral
  exact { toPreconnectedSpace := ⟨(IrreducibleSpace.isIrreducible_univ _).2.isPreconnected⟩
          toNonempty := inferInstance }

/-- A smooth projective variety has at most one connected component. -/
instance subsingleton_components : Subsingleton (Components ((toSchemeCat k).obj V)) :=
  ⟨fun a b ↦ by
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := _root_.ConnectedComponents.surjective_coe b
    exact _root_.ConnectedComponents.coe_eq_coe'.2 (by simp)⟩

/-- The index type of the connected components of a variety is a subsingleton. -/
instance subsingleton_idx : Subsingleton (Idx ((toSchemeCat k).obj V)) :=
  (idxEquiv _).injective.subsingleton

/-- The underlying scheme of a smooth projective variety is nonempty. -/
instance nonempty_left : Nonempty ((toSchemeCat k).obj V).obj.left :=
  ConnectedSpace.toNonempty

/-- The unique component of a variety. -/
def idx0 : Idx ((toSchemeCat k).obj V) :=
  (idxEquiv _).symm (_root_.ConnectedComponents.mk (Classical.arbitrary _))

/-- A smooth projective variety has exactly one connected component. -/
instance : Unique (Idx ((toSchemeCat k).obj V)) :=
  uniqueOfSubsingleton (idx0 V)

/-- The inclusion of a connected component of a variety `V` into `V` is an isomorphism. -/
instance isIso_compOpens_ι (c : Components ((toSchemeCat k).obj V)) :
    IsIso (compOpens ((toSchemeCat k).obj V) c).ι := by
  have : Surjective (compOpens ((toSchemeCat k).obj V) c).ι :=
    ⟨fun x ↦ ⟨⟨x, Subsingleton.elim _ _⟩, rfl⟩⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩

/-- **The component of index `i` of a variety `V` is `V`.** -/
def compIso (i : Idx ((toSchemeCat k).obj V)) : compAt ((toSchemeCat k).obj V) i ≅ V :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (Over.isoMk (asIso (compOpens ((toSchemeCat k).obj V) (idxEquiv _ i)).ι) rfl)

/-- The underlying morphism of `compIso V i` is the inclusion of the component into `V`. -/
@[simp]
theorem compIso_hom_left (i : Idx ((toSchemeCat k).obj V)) :
    (compIso V i).hom.hom.left = (compOpens ((toSchemeCat k).obj V) (idxEquiv _ i)).ι :=
  rfl

end SmoothProjective

/-! ### The extended cohomology of a variety -/

namespace ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

open SmoothProjective

/-- Pullback along an isomorphism of varieties, as an algebra isomorphism. -/
def pullTotalEquiv {V V' : (SmoothProjective k).FullSubcategory} (e : V ≅ V') :
    T.totalH V' ≃ₐ[F] T.totalH V :=
  AlgEquiv.ofAlgHom (T.pullTotal e.hom) (T.pullTotal e.inv)
    (by rw [← pullTotal_comp, e.hom_inv_id, pullTotal_id])
    (by rw [← pullTotal_comp, e.inv_hom_id, pullTotal_id])

/-- **The extended cohomology of a variety is its cohomology**, as `F`-algebras: the extended
cohomology is the product over the unique component `V_0`, and `V_0 = V`. -/
def varietyEquiv (V : (SmoothProjective k).FullSubcategory) :
    T.extH ((toSchemeCat k).obj V) ≃ₐ[F] T.totalH V :=
  AlgEquiv.ofAlgHom ((T.pullTotal (compIso V default).inv).comp (Pi.evalAlgHom F _ default))
    (Pi.algHom F _ fun i ↦ T.pullTotal (compIso V i).hom)
    (by
      refine AlgHom.ext fun x ↦ ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.algHom_apply,
        ← AlgHom.comp_apply, ← pullTotal_comp, Iso.inv_hom_id, pullTotal_id])
    (by
      refine AlgHom.ext fun a ↦ funext fun i ↦ ?_
      obtain rfl := Subsingleton.elim i default
      rw [AlgHom.comp_apply, Pi.algHom_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply,
        ← AlgHom.comp_apply, ← pullTotal_comp, Iso.hom_inv_id, pullTotal_id]
      rfl)

/-- `varietyEquiv` sends `a` to the pullback along `(compIso V i).inv` of its component `a i`. -/
theorem varietyEquiv_apply (V : (SmoothProjective k).FullSubcategory)
    (a : T.extH ((toSchemeCat k).obj V)) (i : Idx ((toSchemeCat k).obj V)) :
    T.varietyEquiv V a = T.pullTotal (compIso V i).inv (a i) := by
  obtain rfl := Subsingleton.elim i default
  rfl

/-- The component of index `i` of `(varietyEquiv V).symm x` is the pullback of `x` along
`(compIso V i).hom`. -/
theorem varietyEquiv_symm_apply (V : (SmoothProjective k).FullSubcategory) (x : T.totalH V)
    (i : Idx ((toSchemeCat k).obj V)) :
    (T.varietyEquiv V).symm x i = T.pullTotal (compIso V i).hom x := by
  obtain rfl := Subsingleton.elim i default
  rfl

/-- **Naturality of `varietyEquiv`**: it carries the pullback of the extension along
`f : V ⟶ V'` to the pullback of the classical theory. -/
theorem varietyEquiv_extPull {V V' : (SmoothProjective k).FullSubcategory} (f : V ⟶ V')
    (a : T.extH ((toSchemeCat k).obj V')) :
    T.varietyEquiv V (T.extPull ((toSchemeCat k).map f) a) =
      T.pullTotal f (T.varietyEquiv V' a) := by
  rw [T.varietyEquiv_apply V _ default, extPull_apply, T.varietyEquiv_apply V' _ default,
    ← AlgHom.comp_apply, ← pullTotal_comp, ← AlgHom.comp_apply, ← pullTotal_comp]
  refine T.pullTotal_congr (Subsingleton.elim _ _) _ _ ?_ a
  have h₁ := congrArg (fun φ ↦ φ.hom.left) (compIso V default).inv_hom_id
  have h₂ := congrArg (fun φ ↦ φ.hom.left) (compIso V' default).inv_hom_id
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    Over.comp_left, Over.id_left, compIso_hom_left] at h₁ h₂ ⊢
  rw [Category.assoc, resIdx_left_ι, reassoc_of% h₁, Category.assoc, h₂, Category.comp_id]
  rfl

/-- `varietyEquiv` sends an element of extended degree `n` to an element of degree `n`. -/
theorem varietyEquiv_mem_grade {V : (SmoothProjective k).FullSubcategory} {n : ℤ}
    {a : T.extH ((toSchemeCat k).obj V)} (ha : a ∈ T.extGrade _ n) :
    T.varietyEquiv V a ∈ (T.H V).grade n := by
  rw [T.varietyEquiv_apply V _ default]
  exact T.pullTotal_mem_grade _ (T.mem_extGrade.1 ha _)

/-- The inverse of `varietyEquiv` sends an element of degree `n` to an element of extended
degree `n`. -/
theorem varietyEquiv_symm_mem_extGrade {V : (SmoothProjective k).FullSubcategory} {n : ℤ}
    {x : T.totalH V} (hx : x ∈ (T.H V).grade n) :
    (T.varietyEquiv V).symm x ∈ T.extGrade _ n :=
  T.mem_extGrade.2 fun i ↦ by
    rw [varietyEquiv_symm_apply]
    exact T.pullTotal_mem_grade _ hx

/-- The image of the degree-`n` part of the extended cohomology under `varietyEquiv` is the
degree-`n` part of `H^*(V)`. -/
theorem map_varietyEquiv_extGrade (V : (SmoothProjective k).FullSubcategory) (n : ℤ) :
    (T.extGrade ((toSchemeCat k).obj V) n).map (T.varietyEquiv V).toLinearEquiv.toLinearMap =
      (T.H V).grade n := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨_, T.varietyEquiv_symm_mem_extGrade hx, by simp⟩⟩
  rintro ⟨a, ha, rfl⟩
  exact T.varietyEquiv_mem_grade ha

/-- **`H^n_ext(V) ≅ H^n(V)`** for a smooth projective variety `V`. -/
def varietyGradeEquiv (V : (SmoothProjective k).FullSubcategory) (n : ℤ) :
    T.toWeilData.grade ((toSchemeCat k).obj V) n ≃ₗ[F] (T.H V).piece n :=
  ((T.varietyEquiv V).toLinearEquiv.ofSubmodules (T.extGrade _ n) ((T.H V).grade n)
    (T.map_varietyEquiv_extGrade V n)).trans ((T.H V).gradeEquiv n)

/-- `varietyGradeEquiv V n a`, viewed in the direct sum, is `varietyEquiv V a`. -/
theorem varietyGradeEquiv_apply (V : (SmoothProjective k).FullSubcategory) (n : ℤ)
    (a : T.toWeilData.grade ((toSchemeCat k).obj V) n) :
    lof F ℤ _ n (T.varietyGradeEquiv V n a) = T.varietyEquiv V a := by
  rw [varietyGradeEquiv, LinearEquiv.trans_apply]
  have h := (T.H V).gradeEquiv_symm_apply_coe n ((T.H V).gradeEquiv n
    ((T.varietyEquiv V).toLinearEquiv.ofSubmodules (T.extGrade _ n) ((T.H V).grade n)
      (T.map_varietyEquiv_extGrade V n) a))
  rw [LinearEquiv.symm_apply_apply] at h
  rw [lof_eq_of, ← h]
  rfl

/-- Elements of `H^n(V)` are equal if their images in the direct sum are. -/
private theorem eq_of_lof_eq (V : (SmoothProjective k).FullSubcategory) {n : ℤ}
    {x y : (T.H V).piece n}
    (h : lof F ℤ (fun n ↦ (T.H V).piece n) n x = lof F ℤ (fun n ↦ (T.H V).piece n) n y) :
    x = y :=
  DirectSum.of_injective (β := fun n ↦ (T.H V).piece n) n h

/-- **Naturality of `H^n_ext(V) ≅ H^n(V)`**. -/
theorem varietyGradeEquiv_pullDeg {V V' : (SmoothProjective k).FullSubcategory} (f : V ⟶ V')
    (n : ℤ) (a : T.toWeilData.grade ((toSchemeCat k).obj V') n) :
    T.varietyGradeEquiv V n (T.toWeilData.pullDeg ((toSchemeCat k).map f) n a) =
      T.pullback f n (T.varietyGradeEquiv V' n a) := by
  refine T.eq_of_lof_eq V ?_
  rw [varietyGradeEquiv_apply, ← pullTotal_lof, varietyGradeEquiv_apply, ← varietyEquiv_extPull]
  rfl

/-- **`H^*_ext(V) ≅ H^*(V)` is multiplicative**: it carries the cup product of the extension to
the cup product of the classical theory. -/
theorem varietyGradeEquiv_cup (V : (SmoothProjective k).FullSubcategory) (i j : ℤ)
    (a : T.toWeilData.grade ((toSchemeCat k).obj V) i)
    (b : T.toWeilData.grade ((toSchemeCat k).obj V) j) :
    T.varietyGradeEquiv V (i + j) (T.toWeilData.cup _ i j (i + j) rfl a b) =
      (T.H V).mul i j (T.varietyGradeEquiv V i a) (T.varietyGradeEquiv V j b) := by
  refine T.eq_of_lof_eq V ?_
  rw [varietyGradeEquiv_apply, ← ExternallyGradedAlgebra.lof_mul_lof, varietyGradeEquiv_apply,
    varietyGradeEquiv_apply, WeilData.coe_cup, map_mul]

/-- **`H^*_ext(V) ≅ H^*(V)` is unital.** -/
theorem varietyGradeEquiv_one (V : (SmoothProjective k).FullSubcategory) :
    T.varietyGradeEquiv V 0 ⟨1, SetLike.GradedOne.one_mem⟩ = (T.H V).one := by
  refine T.eq_of_lof_eq V ?_
  rw [varietyGradeEquiv_apply, map_one]
  rfl

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
