module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataAxioms
public import StacksFrontier.CategoryTheory.GradedObject.KoszulBraiding
public import StacksFrontier.CategoryTheory.GradedObject.Linear
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The two sides of Stacks 0FHM

Proposition 0FHM of the Stacks Project puts in one-to-one correspondence

1. data (D0), (D1), (D2) and (D3) satisfying (A), (B) and (C) (Section 0FHA), and
2. `ℚ`-linear symmetric monoidal functors `G : M_k ⥤ graded F-vector spaces` such that
   `G(𝟏(1))` is nonzero only in degree `-2`.

Both are structures carrying choices (the line `F(1)`, the spaces `H^*(X)`, the images of
projectors), and the two constructions of Lemmas 0FHK and 0FHL are inverse to each other up to
isomorphism. This file sets up both sides together with their isomorphisms:

* side (1) is `Stacks.WeilCohomology.WeilDataAxioms k F`, and an isomorphism of such data is
  `Stacks.WeilCohomology.WeilData.Iso`: an isomorphism `F(1) ≅ F(1)'` and isomorphisms of graded
  `F`-algebras `H^*(X) ≅ H'^*(X)`, natural in `X`, compatible with the cycle class maps and the
  trace maps through the induced isomorphisms of Tate twists;
* side (2) is `Stacks.WeilCohomology.WeilRealization k F`, and an isomorphism of realizations is
  a monoidal natural isomorphism (`Stacks.WeilCohomology.WeilRealization.Iso`).

The target category is `GradedObject ℤ (ModuleCat F)` with the symmetric monoidal structure of
Stacks, Homology, Example 0FFX: the commutativity constraint carries the Koszul sign
(`CategoryTheory.GradedObject.koszulBraidedCategory`), the convention the chapter uses.

## Main definitions

* `Stacks.WeilCohomology.tateLineCongr`, `Stacks.WeilCohomology.tateTwistCongr`: the isomorphisms
  `L(n) ≅ L'(n)` and `V(n) ≅ V'(n)` induced by `L ≅ L'` and `V ≅ V'`.
* `Stacks.WeilCohomology.WeilData.Iso`: isomorphisms of data (D0)–(D3).
* `Stacks.WeilCohomology.WeilDataAxioms.isoSetoid`: isomorphism of data satisfying (A), (B), (C).
* `Stacks.WeilCohomology.WeilRealization`: side (2).
* `Stacks.WeilCohomology.WeilRealization.Iso`, `Stacks.WeilCohomology.WeilRealization.isoSetoid`:
  monoidal natural isomorphisms of realizations.

## References

* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TensorProduct

universe u w uF uL uL' uL'' uV uV' uV''

namespace Stacks.WeilCohomology

/-! ### Tate twists along isomorphisms -/

section Twists

variable {F : Type uF} [Field F]
  {L : Type uL} [AddCommGroup L] [Module F L] {L' : Type uL'} [AddCommGroup L'] [Module F L']
  {L'' : Type uL''} [AddCommGroup L''] [Module F L'']
  {V : Type uV} [AddCommGroup V] [Module F V] {V' : Type uV'} [AddCommGroup V'] [Module F V']
  {V'' : Type uV''} [AddCommGroup V''] [Module F V'']

/-- The isomorphism `L(n) ≅ L'(n)` of Tate lines induced by an isomorphism `L ≅ L'`: the tensor
power of `L ≅ L'` for `n ≥ 0`, and of the contragredient `L^∨ ≅ L'^∨` for `n < 0`. -/
def tateLineCongr (e : L ≃ₗ[F] L') : (n : ℤ) → tateLine F L n ≃ₗ[F] tateLine F L' n
  | .ofNat _ => PiTensorProduct.congr fun _ ↦ e
  | .negSucc _ => PiTensorProduct.congr fun _ ↦ e.symm.dualMap

/-- Two linear equivalences out of a tensor power agree if they agree on pure tensors. -/
private theorem piTensorProduct_equiv_ext {R ι M : Type*} {s : ι → Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
    {f g : (⨂[R] i, s i) ≃ₗ[R] M}
    (h : ∀ x, f (PiTensorProduct.tprod R x) = g (PiTensorProduct.tprod R x)) : f = g :=
  LinearEquiv.toLinearMap_injective (PiTensorProduct.ext (MultilinearMap.ext h))

/-- The isomorphism `L(n) ≅ L(n)` induced by the identity of `L` is the identity. -/
theorem tateLineCongr_refl (n : ℤ) :
    tateLineCongr (LinearEquiv.refl F L) n = LinearEquiv.refl F _ := by
  cases n <;>
  · refine piTensorProduct_equiv_ext fun x ↦ ?_
    simp [tateLineCongr]

/-- The inverse of the isomorphism `L(n) ≅ L'(n)` induced by `e` is induced by `e⁻¹`. -/
theorem tateLineCongr_symm (e : L ≃ₗ[F] L') (n : ℤ) :
    (tateLineCongr e n).symm = tateLineCongr e.symm n := by
  cases n <;>
  · refine piTensorProduct_equiv_ext fun x ↦ ?_
    simp [tateLineCongr, PiTensorProduct.congr_symm_tprod]

/-- The isomorphism of Tate lines induced by a composite is the composite of the induced
isomorphisms. -/
theorem tateLineCongr_trans (e : L ≃ₗ[F] L') (e' : L' ≃ₗ[F] L'') (n : ℤ) :
    (tateLineCongr e n).trans (tateLineCongr e' n) = tateLineCongr (e.trans e') n := by
  cases n with
  | ofNat =>
    refine piTensorProduct_equiv_ext fun x ↦ ?_
    simp only [tateLineCongr]
    simp
  | negSucc =>
    refine piTensorProduct_equiv_ext fun x ↦ ?_
    simp only [tateLineCongr]
    simp
    rfl

/-- The isomorphism `V(n) ≅ V'(n)` of Tate twists induced by isomorphisms `L ≅ L'` of lines and
`V ≅ V'` of vector spaces. -/
def tateTwistCongr (e : L ≃ₗ[F] L') (φ : V ≃ₗ[F] V') (n : ℤ) :
    tateTwist F L V n ≃ₗ[F] tateTwist F L' V' n :=
  TensorProduct.congr φ (tateLineCongr e n)

/-- The isomorphism `V(n) ≅ V'(n)` sends `v ⊗ l` to `φ v ⊗ e(l)`. -/
@[simp]
theorem tateTwistCongr_tmul (e : L ≃ₗ[F] L') (φ : V ≃ₗ[F] V') (n : ℤ) (v : V)
    (l : tateLine F L n) :
    tateTwistCongr e φ n (v ⊗ₜ l) = φ v ⊗ₜ tateLineCongr e n l :=
  rfl

/-- The isomorphism `V(n) ≅ V(n)` induced by the identities of `L` and `V` is the identity. -/
theorem tateTwistCongr_refl (n : ℤ) :
    tateTwistCongr (LinearEquiv.refl F L) (LinearEquiv.refl F V) n = LinearEquiv.refl F _ := by
  rw [tateTwistCongr, tateLineCongr_refl]
  exact TensorProduct.congr_refl_refl

/-- The inverse of the isomorphism `V(n) ≅ V'(n)` induced by `e` and `φ` is induced by `e⁻¹`
and `φ⁻¹`. -/
theorem tateTwistCongr_symm (e : L ≃ₗ[F] L') (φ : V ≃ₗ[F] V') (n : ℤ) :
    (tateTwistCongr e φ n).symm = tateTwistCongr e.symm φ.symm n := by
  rw [tateTwistCongr, tateTwistCongr, TensorProduct.congr_symm, tateLineCongr_symm]

/-- The isomorphism of Tate twists induced by composites is the composite of the induced
isomorphisms. -/
theorem tateTwistCongr_trans (e : L ≃ₗ[F] L') (e' : L' ≃ₗ[F] L'') (φ : V ≃ₗ[F] V')
    (φ' : V' ≃ₗ[F] V'') (n : ℤ) :
    (tateTwistCongr e φ n).trans (tateTwistCongr e' φ' n) =
      tateTwistCongr (e.trans e') (φ.trans φ') n := by
  rw [tateTwistCongr, tateTwistCongr, tateTwistCongr, ← TensorProduct.congr_trans,
    tateLineCongr_trans]

end Twists

/-! ### Isomorphisms of data (D0)–(D3) -/

variable {k : Type u} [Field k] {F : Type w} [Field F]

namespace WeilData

/-- **An isomorphism of data (D0), (D1), (D2), (D3)** (Section 0FHA): an isomorphism
`F(1) ≅ F(1)'` of Tate lines and isomorphisms `H^*(X) ≅ H'^*(X)` of graded `F`-algebras,
natural in `X` for pullbacks, such that the cycle class maps `γ` and the trace maps `∫_X`
correspond under the induced isomorphisms `H^n(X)(m) ≅ H'^n(X)(m)`. -/
structure Iso (W W' : WeilData k F) where
  /-- The isomorphism `F(1) ≅ F(1)'`. -/
  tateEquiv : W.tate ≃ₗ[F] W'.tate
  /-- The isomorphisms of algebras `H^*(X) ≅ H'^*(X)`. -/
  equiv : ∀ X, W.H X ≃ₐ[F] W'.H X
  /-- They preserve the grading. -/
  map_grade : ∀ X n, (W.grade X n).map (equiv X).toLinearMap = W'.grade X n
  /-- They commute with pullbacks. -/
  equiv_pull : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (a : W.H Y),
    equiv X (W.pull f a) = W'.pull f (equiv Y a)

namespace Iso

variable {W W' W'' : WeilData k F}

/-- The induced isomorphism `H^n(X) ≅ H'^n(X)`. -/
def gradeEquiv (e : Iso W W') (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    W.grade X n ≃ₗ[F] W'.grade X n :=
  (e.equiv X).toLinearEquiv.ofSubmodules _ _ (e.map_grade X n)

/-- The induced isomorphism `H^n(X) ≅ H'^n(X)` is the restriction of `H^*(X) ≅ H'^*(X)`. -/
@[simp]
theorem coe_gradeEquiv (e : Iso W W') (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a : W.grade X n) : (e.gradeEquiv X n a : W'.H X) = e.equiv X a :=
  rfl

/-- The induced isomorphism `H^n(X)(m) ≅ H'^n(X)(m)`. -/
def twEquiv (e : Iso W W') (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) :
    W.Tw X n m ≃ₗ[F] W'.Tw X n m :=
  tateTwistCongr e.tateEquiv (e.gradeEquiv X n) m

/-- The identity isomorphism. -/
def refl (W : WeilData k F) : Iso W W where
  tateEquiv := LinearEquiv.refl F _
  equiv _ := AlgEquiv.refl
  map_grade _ _ := Submodule.map_id _
  equiv_pull _ _ := rfl

/-- The inverse isomorphism. -/
def symm (e : Iso W W') : Iso W' W where
  tateEquiv := e.tateEquiv.symm
  equiv X := (e.equiv X).symm
  map_grade X n := by
    rw [← e.map_grade X n, ← Submodule.map_comp]
    have : (e.equiv X).symm.toLinearMap ∘ₗ (e.equiv X).toLinearMap = LinearMap.id :=
      LinearMap.ext fun a ↦ (e.equiv X).symm_apply_apply a
    rw [this, Submodule.map_id]
  equiv_pull f a := by
    apply (e.equiv _).injective
    simp [e.equiv_pull]

/-- The composite isomorphism. -/
def trans (e : Iso W W') (e' : Iso W' W'') : Iso W W'' where
  tateEquiv := e.tateEquiv.trans e'.tateEquiv
  equiv X := (e.equiv X).trans (e'.equiv X)
  map_grade X n := by
    rw [AlgEquiv.trans_toLinearMap, Submodule.map_comp, e.map_grade, e'.map_grade]
  equiv_pull f a := by
    change e'.equiv _ (e.equiv _ _) = W''.pull f (e'.equiv _ (e.equiv _ a))
    rw [e.equiv_pull, e'.equiv_pull]

/-- The identity isomorphism is the identity on `F(1)`. -/
@[simp] theorem refl_tateEquiv : (refl W).tateEquiv = LinearEquiv.refl F _ := rfl
/-- The identity isomorphism is the identity on `H^*(X)`. -/
@[simp] theorem refl_equiv (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (refl W).equiv X = AlgEquiv.refl := rfl
/-- The inverse isomorphism is the inverse on `F(1)`. -/
@[simp] theorem symm_tateEquiv (e : Iso W W') : e.symm.tateEquiv = e.tateEquiv.symm := rfl
/-- The inverse isomorphism is the inverse on `H^*(X)`. -/
@[simp] theorem symm_equiv (e : Iso W W') (X : (SmoothProjectiveScheme k).FullSubcategory) :
    e.symm.equiv X = (e.equiv X).symm := rfl
/-- The composite isomorphism is the composite on `F(1)`. -/
@[simp] theorem trans_tateEquiv (e : Iso W W') (e' : Iso W' W'') :
    (e.trans e').tateEquiv = e.tateEquiv.trans e'.tateEquiv := rfl
/-- The composite isomorphism is the composite on `H^*(X)`. -/
@[simp] theorem trans_equiv (e : Iso W W') (e' : Iso W' W'')
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (e.trans e').equiv X = (e.equiv X).trans (e'.equiv X) := rfl

/-- The identity isomorphism induces the identity of `H^n(X)`. -/
theorem gradeEquiv_refl (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    (refl W).gradeEquiv X n = LinearEquiv.refl F _ :=
  LinearEquiv.ext fun _ ↦ Subtype.ext rfl

/-- The inverse isomorphism induces the inverse of `H^n(X) ≅ H'^n(X)`. -/
theorem gradeEquiv_symm (e : Iso W W') (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    e.symm.gradeEquiv X n = (e.gradeEquiv X n).symm := by
  ext a
  apply (e.equiv X).injective
  rw [coe_gradeEquiv, symm_equiv, AlgEquiv.apply_symm_apply, ← coe_gradeEquiv,
    LinearEquiv.apply_symm_apply]

/-- The composite isomorphism induces the composite of the isomorphisms on `H^n(X)`. -/
theorem gradeEquiv_trans (e : Iso W W') (e' : Iso W' W'')
    (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    (e.trans e').gradeEquiv X n = (e.gradeEquiv X n).trans (e'.gradeEquiv X n) :=
  LinearEquiv.ext fun _ ↦ Subtype.ext rfl

/-- The identity isomorphism induces the identity of `H^n(X)(m)`. -/
theorem twEquiv_refl (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) :
    (refl W).twEquiv X n m = LinearEquiv.refl F _ := by
  rw [twEquiv, gradeEquiv_refl, refl_tateEquiv]
  exact tateTwistCongr_refl m

/-- The inverse isomorphism induces the inverse of `H^n(X)(m) ≅ H'^n(X)(m)`. -/
theorem twEquiv_symm (e : Iso W W') (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) :
    e.symm.twEquiv X n m = (e.twEquiv X n m).symm := by
  rw [twEquiv, twEquiv, tateTwistCongr_symm, gradeEquiv_symm, symm_tateEquiv]

/-- The composite isomorphism induces the composite of the isomorphisms on `H^n(X)(m)`. -/
theorem twEquiv_trans (e : Iso W W') (e' : Iso W' W'')
    (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) :
    (e.trans e').twEquiv X n m = (e.twEquiv X n m).trans (e'.twEquiv X n m) := by
  rw [twEquiv, twEquiv, twEquiv, tateTwistCongr_trans, gradeEquiv_trans, trans_tateEquiv]

/-- **The isomorphism preserves the cycle class maps (D2)**: `γ'(α) = e(γ(α))` in
`H'^{2i}(X)(i)`. -/
def PreservesCycleClass (e : Iso W W') : Prop :=
  ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : Stacks.Chow.codimensionChowGroup k X.obj.hom i),
    W'.cycleClass X i α = e.twEquiv X (2 * i) i (W.cycleClass X i α)

/-- **The isomorphism preserves the trace maps (D3)**: `∫'_X e(a) = ∫_X a`. -/
def PreservesTrace (e : Iso W W') : Prop :=
  ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) (hX : IsNonemptyEquidimensional X d)
    (a : W.Tw X (2 * (d : ℤ)) d), W'.trace X d hX (e.twEquiv X _ _ a) = W.trace X d hX a

end Iso

/-- **`W` and `W'` are isomorphic data (D0)–(D3)**: there is an isomorphism of the Tate lines and
of the cohomology algebras, natural in `X`, preserving the cycle class maps and the trace maps. -/
def IsIsomorphic (W W' : WeilData k F) : Prop :=
  ∃ e : Iso W W', e.PreservesCycleClass ∧ e.PreservesTrace

/-- Every datum (D0)–(D3) is isomorphic to itself. -/
theorem IsIsomorphic.refl (W : WeilData k F) : IsIsomorphic W W :=
  ⟨Iso.refl W, fun X i α ↦ by rw [Iso.twEquiv_refl]; rfl,
    fun X d hX a ↦ by rw [Iso.twEquiv_refl]; rfl⟩

/-- Isomorphism of data (D0)–(D3) is symmetric. -/
theorem IsIsomorphic.symm {W W' : WeilData k F} (h : IsIsomorphic W W') : IsIsomorphic W' W := by
  obtain ⟨e, hγ, htr⟩ := h
  refine ⟨e.symm, fun X i α ↦ ?_, fun X d hX a ↦ ?_⟩
  · rw [Iso.twEquiv_symm, LinearEquiv.eq_symm_apply, hγ]
  · rw [Iso.twEquiv_symm, ← htr, LinearEquiv.apply_symm_apply]

/-- Isomorphism of data (D0)–(D3) is transitive. -/
theorem IsIsomorphic.trans {W W' W'' : WeilData k F} (h : IsIsomorphic W W')
    (h' : IsIsomorphic W' W'') : IsIsomorphic W W'' := by
  obtain ⟨e, hγ, htr⟩ := h
  obtain ⟨e', hγ', htr'⟩ := h'
  refine ⟨e.trans e', fun X i α ↦ ?_, fun X d hX a ↦ ?_⟩
  · rw [Iso.twEquiv_trans, LinearEquiv.trans_apply, hγ', hγ]
  · rw [Iso.twEquiv_trans, LinearEquiv.trans_apply, htr', htr]

end WeilData

variable (k F) in
/-- **Isomorphism of data (D0)–(D3) satisfying (A), (B), (C)**, as a setoid: isomorphism of the
underlying data (D0)–(D3) (`Stacks.WeilCohomology.WeilData.IsIsomorphic`); the axioms are
properties. -/
def WeilDataAxioms.isoSetoid : Setoid (WeilDataAxioms k F) where
  r W W' := W.toWeilData.IsIsomorphic W'.toWeilData
  iseqv := ⟨fun _ ↦ .refl _, .symm, .trans⟩

/-! ### Realizations of Chow motives -/

variable (k F) in
/-- **Side (2) of Stacks 0FHM.** A `ℚ`-linear functor `G : M_k ⥤ graded F-vector spaces` of
symmetric monoidal categories such that `G(𝟏(1))` is nonzero only in degree `-2`. The category
of graded `F`-vector spaces is `GradedObject ℤ (ModuleCat F)` with the Koszul sign rule of
Stacks 0FFX (`CategoryTheory.GradedObject.koszulBraidedCategory`); a braided functor between
symmetric monoidal categories is a functor of symmetric monoidal categories. -/
structure WeilRealization [CharZero F] where
  /-- The functor `G : M_k ⥤ graded F-vector spaces`. -/
  functor : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{w} F)
  /-- `G` is a functor of symmetric monoidal categories. -/
  [braided : @Functor.Braided (ChowMotiveCat k) _ _ _ (GradedObject ℤ (ModuleCat.{w} F)) _ _
    GradedObject.koszulBraidedCategory functor]
  /-- `G` is additive. -/
  [additive : functor.Additive]
  /-- `G` is `ℚ`-linear. -/
  [linear : Functor.Linear ℚ functor]
  /-- `G(𝟏(1))` is nonzero only in degree `-2`. -/
  tate_degree : ∀ i : ℤ, i ≠ -2 → IsZero ((functor.obj (ChowMotiveCat.tate k 1)) i)

namespace WeilRealization

variable [CharZero F]

attribute [instance] WeilRealization.additive WeilRealization.linear

/-- The monoidal structure on `G` underlying its braided structure. -/
instance (G : WeilRealization k F) : G.functor.Monoidal :=
  @Functor.Braided.toMonoidal _ _ _ _ _ _ _ GradedObject.koszulBraidedCategory G.functor G.braided

/-- **An isomorphism of realizations**: a monoidal natural isomorphism `G ≅ G'`. -/
structure Iso (G G' : WeilRealization k F) where
  /-- The natural isomorphism `G ≅ G'`. -/
  iso : G.functor ≅ G'.functor
  /-- It is monoidal. -/
  isMonoidal : NatTrans.IsMonoidal iso.hom

attribute [instance] Iso.isMonoidal

variable (k F) in
/-- **Isomorphism of realizations**, as a setoid: there is a monoidal natural isomorphism. -/
def isoSetoid : Setoid (WeilRealization k F) where
  r G G' := Nonempty (Iso G G')
  iseqv := by
    refine ⟨fun G ↦ ⟨⟨CategoryTheory.Iso.refl _, ?_⟩⟩, fun ⟨e⟩ ↦ ⟨⟨e.iso.symm, ?_⟩⟩,
      fun ⟨e⟩ ⟨e'⟩ ↦ ⟨⟨e.iso ≪≫ e'.iso, ?_⟩⟩⟩
    · exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 G.functor))
    · exact inferInstanceAs (NatTrans.IsMonoidal e.iso.inv)
    · exact inferInstanceAs (NatTrans.IsMonoidal (e.iso.hom ≫ e'.iso.hom))

end WeilRealization

end Stacks.WeilCohomology

end
