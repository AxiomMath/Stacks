module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.Algebra.Category.Ring.PushoutTensorComparison
public import StacksFrontier.RingTheory.Descent.FiniteTensorDescent

/-!
# A cartesian presheaf of modules satisfies the sheaf axiom for a faithfully flat cover

Let `R` be a presheaf of commutative rings on a category `C` and let `M` be a presheaf of modules
over it which is *cartesian*: every restriction map of `M` exhibits its target as the base change
of its source (`Stacks.PresheafOfModules.restrictionBaseChange` is an isomorphism).  Let
`V i ⟶ U` be a finite family such that the induced map `R U ⟶ ∏ i, R (V i)` is faithfully flat
and such that the square of rings attached to each double overlap `W i j` is a pushout.  Then
`M` satisfies the sheaf axiom for that family.

This is descent of modules along a faithfully flat ring map, Stacks 023M, read on a site: the
cartesian condition identifies the sections over the members and the overlaps of the cover with
base changes of the sections over `U`, and descent of elements then produces the unique gluing.

## Main results

* `Stacks.Sites.isSheafFor_of_finite_tensor_descent`: the sheaf axiom for a presheaf of types
  whose sections over the members and the double overlaps of a finite cover are identified with
  base changes of a faithfully flat family, compatibly with the restriction maps.
* `Stacks.PresheafOfModules.isSheafFor_of_cartesian`: **a cartesian presheaf of modules satisfies
  the sheaf axiom for a finite family which is faithfully flat on rings of sections and whose
  double overlaps are pushouts of rings.**
* `Stacks.PresheafOfModules.isSheafFor_of_isIso_restrictionBaseChange`: the same conclusion for a
  presheaf of modules cartesian only over the arrows of the family and of its double overlaps.

## Implementation notes

The first statement is about a presheaf of types and takes the identifications as bijections
together with the three compatibility identities; it therefore applies to the underlying presheaf
of sets of `M` without any coherence work.  The second feeds it the bijections
`Stacks.PresheafOfModules.restrictionTensorEquiv` coming from the cartesian hypothesis and the
pushout comparisons `CommRingCat.pushoutTensorLinearEquiv`.

The double overlaps are given as abstract objects `W i j` with two maps to `V i` and `V j`, not
as fibre products, so the statement applies to a cover of a site with no pullbacks; what is
required of them is exactly that their rings of sections make the ring square a pushout.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v r m

namespace Stacks.Sites

/-- **The sheaf axiom from descent of elements along a finite faithfully flat family.**

The sections of `F` over `U`, over the members `V i` of the family and over the double overlaps
`W i j` are identified with `N`, with `A i ⊗[R] N` and with `P i j ⊗[R] N`, compatibly with the
restriction maps; `P i j` is identified with `A i ⊗[R] A j` compatibly with its two algebra
maps, and the product of the `A i` is faithfully flat over `R`.  Then `F` satisfies the
sheaf axiom for the family. -/
theorem isSheafFor_of_finite_tensor_descent
    {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type*)
    {U : C} {I : Type*} [Finite I]
    (V : I → C) (f : ∀ i, V i ⟶ U)
    (W : I → I → C) (p : ∀ i j, W i j ⟶ V i) (q : ∀ i j, W i j ⟶ V j)
    (hpq : ∀ i j, p i j ≫ f i = q i j ≫ f j)
    (R : Type*) (A : I → Type*) (P : I → I → Type*) (N : Type*)
    [CommRing R] [∀ i, CommRing (A i)] [∀ i j, CommRing (P i j)]
    [∀ i, Algebra R (A i)] [∀ i j, Algebra R (P i j)]
    [AddCommGroup N] [Module R N] [Module.FaithfullyFlat R (∀ i, A i)]
    (eP : ∀ i j, A i ⊗[R] A j ≃ₗ[R] P i j)
    (l : ∀ i j, A i →ₐ[R] P i j) (r : ∀ i j, A j →ₐ[R] P i j)
    (heP : ∀ i j a b, eP i j (a ⊗ₜ[R] b) = l i j a * r i j b)
    (e₀ : N ≃ F.obj (.op U))
    (e₁ : ∀ i, A i ⊗[R] N ≃ F.obj (.op (V i)))
    (e₂ : ∀ i j, P i j ⊗[R] N ≃ F.obj (.op (W i j)))
    (h₀ : ∀ i n, F.map (f i).op (e₀ n) = e₁ i ((1 : A i) ⊗ₜ[R] n))
    (h₁ : ∀ i j x, F.map (p i j).op (e₁ i x) =
      e₂ i j (TensorProduct.map (l i j).toLinearMap LinearMap.id x))
    (h₂ : ∀ i j x, F.map (q i j).op (e₁ j x) =
      e₂ i j (TensorProduct.map (r i j).toLinearMap LinearMap.id x)) :
    Presieve.IsSheafFor F (Presieve.ofArrows V f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let y := fun i => (e₁ i).symm (x i)
  have hy (i j : I) :
      TensorProduct.map (l i j).toLinearMap LinearMap.id (y i) =
      TensorProduct.map (r i j).toLinearMap LinearMap.id (y j) := by
    apply (e₂ i j).injective
    rw [← h₁, ← h₂]
    simpa [y] using hx i j (W i j) (p i j) (q i j) (hpq i j)
  obtain ⟨n, hn, hn_unique⟩ :=
    Module.Descent.existsUnique_forall_tmul_one_eq R I A N P eP l r heP y hy
  refine ⟨e₀ n, fun i => ?_, fun z hz => ?_⟩
  · rw [h₀, hn]
    exact (e₁ i).apply_symm_apply _
  · have hzn : e₀.symm z = n := hn_unique _ (fun i => (e₁ i).injective (by
      rw [← h₀, Equiv.apply_symm_apply, hz]
      exact ((e₁ i).apply_symm_apply _).symm))
    simpa using congrArg e₀ hzn

end Stacks.Sites

namespace Stacks.PresheafOfModules

/-- **A presheaf of modules satisfies the sheaf axiom for a finite family which is faithfully flat
on rings of sections and whose double overlaps are pushouts of rings, as soon as it is cartesian
over the arrows of the family and over the arrows from the double overlaps to `U`.**

These are the only restriction maps along which the descent argument identifies sections with base
changes, so the cartesian condition is needed only there; this is what lets the statement apply to
a presheaf of modules which is cartesian only along a class of arrows containing the cover. -/
theorem isSheafFor_of_isIso_restrictionBaseChange
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{r})
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {U : C} {I : Type*} [Finite I]
    (V : I → C) (f : ∀ i, V i ⟶ U)
    (W : I → I → C) (p : ∀ i j, W i j ⟶ V i) (q : ∀ i j, W i j ⟶ V j)
    (hpq : ∀ i j, p i j ≫ f i = q i j ≫ f j)
    (hff : (RingHom.pi (fun i => (R.map (f i).op).hom)).FaithfullyFlat)
    (hpo : ∀ i j, IsPushout (R.map (f i).op) (R.map (f j).op)
      (R.map (p i j).op) (R.map (q i j).op))
    (hMf : ∀ i, IsIso (restrictionBaseChange M (f i).op))
    (hMpf : ∀ i j, IsIso (restrictionBaseChange M (p i j ≫ f i).op)) :
    Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat) (Presieve.ofArrows V f) := by
  classical
  have _ (i : I) : IsIso (restrictionBaseChange M (f i).op) := hMf i
  have _ (i j : I) : IsIso (restrictionBaseChange M (p i j ≫ f i).op) := hMpf i j
  let R₀ := R.obj (.op U)
  let A (i : I) := R.obj (.op (V i))
  let P (i j : I) := R.obj (.op (W i j))
  let N := M.obj (.op U)
  let a (i : I) := R.map (f i).op
  let b (i j : I) := R.map (f i).op ≫ R.map (p i j).op
  let _ (i : I) : Algebra R₀ (A i) := (a i).hom.toAlgebra
  let _ (i j : I) : Algebra R₀ (P i j) := (b i j).hom.toAlgebra
  have _ : Module.FaithfullyFlat R₀ (∀ i, A i) := hff
  let l (i j : I) : A i →ₐ[R₀] P i j :=
    { (R.map (p i j).op).hom with
      commutes' := fun x => by
        show (R.map (p i j).op).hom ((a i).hom x) = (b i j).hom x
        simp [a, b] }
  let r' (i j : I) : A j →ₐ[R₀] P i j :=
    { (R.map (q i j).op).hom with
      commutes' := fun x => by
        show (R.map (f j).op ≫ R.map (q i j).op).hom x =
          (R.map (f i).op ≫ R.map (p i j).op).hom x
        rw [← R.map_comp, ← R.map_comp]
        exact congrArg (fun k => (R.map k.op).hom x) (hpq i j).symm }
  let eP (i j : I) : A i ⊗[R₀] A j ≃ₗ[R₀] P i j :=
    CommRingCat.pushoutTensorLinearEquiv _ _ _ _ _ _ _ _ (hpo i j)
  have heP (i j : I) (x : A i) (y : A j) :
      eP i j (x ⊗ₜ[R₀] y) = l i j x * r' i j y :=
    CommRingCat.pushoutTensorLinearEquiv_tmul _ _ _ _ _ _ _ _ (hpo i j) x y
  let e₁ (i : I) : A i ⊗[R₀] N ≃ M.obj (.op (V i)) :=
    restrictionTensorEquiv M (f i).op (a i) rfl
  let e₂ (i j : I) : P i j ⊗[R₀] N ≃ M.obj (.op (W i j)) :=
    restrictionTensorEquiv M (p i j ≫ f i).op (b i j) (by simp [b])
  have key (i j k : I) (s : W i j ⟶ V k) (hs : s ≫ f k = p i j ≫ f i)
      (φ : A k →ₐ[R₀] P i j) (hφ : ∀ z, φ z = (R.map s.op).hom z) (x : A k ⊗[R₀] N) :
      M.map s.op (e₁ k x) = e₂ i j (TensorProduct.map φ.toLinearMap LinearMap.id x) := by
    induction x using TensorProduct.induction_on with
    | zero =>
      have h1 : e₁ k 0 = 0 := restrictionTensorEquiv_zero M (f k).op (a k) rfl
      have h2 : e₂ i j 0 = 0 :=
        restrictionTensorEquiv_zero M (p i j ≫ f i).op (b i j) (by simp [b])
      simp only [map_zero]
      rw [h1, h2]
      exact map_zero (M.map s.op).hom
    | tmul c n =>
      have h1 : e₁ k (c ⊗ₜ[R₀] n) = c • M.map (f k).op n :=
        restrictionTensorEquiv_tmul M (f k).op (a k) rfl c n
      have h2 : e₂ i j (φ c ⊗ₜ[R₀] n) = φ c • M.map (p i j ≫ f i).op n :=
        restrictionTensorEquiv_tmul M (p i j ≫ f i).op (b i j) (by simp [b]) _ n
      have h3 : M.map s.op (c • M.map (f k).op n) =
          (R.map s.op).hom c • M.map s.op (M.map (f k).op n) :=
        M.map_smul _ _ _
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply]
      rw [h1, h2, h3, hφ]
      congr 1
      rw [← M.map_comp_apply]
      rw [show (f k).op ≫ s.op = (p i j ≫ f i).op from congrArg Quiver.Hom.op hs]
    | add x y hx hy =>
      have h1 : e₁ k (x + y) = e₁ k x + e₁ k y :=
        restrictionTensorEquiv_add M (f k).op (a k) rfl x y
      have h2 : ∀ u v, e₂ i j (u + v) = e₂ i j u + e₂ i j v :=
        restrictionTensorEquiv_add M (p i j ≫ f i).op (b i j) (by simp [b])
      simp only [map_add]
      rw [h1, h2, map_add, hx, hy]
      rfl
  apply Stacks.Sites.isSheafFor_of_finite_tensor_descent _ V f W p q hpq R₀ (fun i => A i)
    (fun i j => P i j) N eP l r' heP (Equiv.refl _) e₁ e₂
  · intro i n
    show M.map (f i).op n = e₁ i ((1 : A i) ⊗ₜ[R₀] n)
    exact ((restrictionTensorEquiv_tmul M (f i).op (a i) rfl 1 n).trans
      (one_smul _ _)).symm
  · intro i j x
    exact key i j i (p i j) rfl (l i j) (fun _ => rfl) x
  · intro i j x
    exact key i j j (q i j) (hpq i j).symm (r' i j) (fun _ => rfl) x

/-- **A cartesian presheaf of modules satisfies the sheaf axiom for a finite family which is
faithfully flat on rings of sections and whose double overlaps are pushouts of rings.**

The cartesian hypothesis `hM` identifies the sections over each object of the cover with a base
change of the sections over `U`, and `hpo` identifies the ring of the double overlap `W i j` with
the tensor product of the rings of `V i` and `V j`; descent of elements along the faithfully flat
map `R U ⟶ ∏ i, R (V i)` then glues. -/
theorem isSheafFor_of_cartesian
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{r})
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {U : C} {I : Type*} [Finite I]
    (V : I → C) (f : ∀ i, V i ⟶ U)
    (W : I → I → C) (p : ∀ i j, W i j ⟶ V i) (q : ∀ i j, W i j ⟶ V j)
    (hpq : ∀ i j, p i j ≫ f i = q i j ≫ f j)
    (hff : (RingHom.pi (fun i => (R.map (f i).op).hom)).FaithfullyFlat)
    (hpo : ∀ i j, IsPushout (R.map (f i).op) (R.map (f j).op)
      (R.map (p i j).op) (R.map (q i j).op))
    (hM : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y), IsIso (restrictionBaseChange M g)) :
    Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat) (Presieve.ofArrows V f) :=
  isSheafFor_of_isIso_restrictionBaseChange R M V f W p q hpq hff hpo (fun _ => hM _)
    (fun _ _ => hM _)

end Stacks.PresheafOfModules

end
