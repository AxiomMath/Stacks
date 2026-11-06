module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.UnitComplexMaps
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorMonoidalPureTensors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalPureTensorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductLocalFiniteSum
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Local sections of a total tensor complex

For a sheaf of rings `R` on a space, a section of the degree-zero term of the total complex
`Tot(A ⊗ B)` of two complexes of `R`-modules is, near each point, a finite sum of pure tensors
`a ⊗ b` of sections of `A^p` and `B^q` with `p + q = 0`
(`exists_nhd_sum_ιMapBifunctor_pureTensor`). The remaining lemmas compute restrictions and the
maps induced by a morphism of complexes on such sums.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TopologicalSpace Opposite Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.LeftDualPerfect

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable {T : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})

/-- The total tensor complex of two complexes of sheaves of `R`-modules exists. -/
instance hasMapBifunctor_curriedTensor (K L : CochainComplex (Mod R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (curriedTensor (Mod R)) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u} R K L

/-- A sheaf of rings on a space, as a ringed space. -/
def ringedSpaceOf : RingedSpace.{u, u} where
  carrier := T
  presheaf := R.obj
  IsSheaf := R.property

/-- The pure tensor `a ⊗ b` of two sections over the same open, as a section of the tensor
product of sheaves of modules. -/
abbrev pureTensor {F G : Mod R} {V : Opens T} (a : F.val.obj (op V)) (b : G.val.obj (op V)) :
    (((curriedTensor (Mod R)).obj F).obj G).val.obj (op V) :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (ringedSpaceOf R) F G (op V)
    (a ⊗ₜ b)

variable {R}

/-- Restriction of a pure tensor is the pure tensor of the restrictions. -/
theorem res_pureTensor {F G : Mod R} {V' V : Opens T} (h : V' ≤ V) (a : F.val.obj (op V))
    (b : G.val.obj (op V)) :
    res (((curriedTensor (Mod R)).obj F).obj G) h (pureTensor R a b) =
      pureTensor R (res F h a) (res G h b) :=
  (PresheafOfModules.naturality_apply (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit
    (ringedSpaceOf R) ((PresheafOfModules.tensorObj (O := ((ringedSpaceOf R)).presheaf) (F.val)
      (G.val)))) (homOfLE h).op
    (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj (op V)] b)).symm

/-- The map `φ ⊗ 𝟙` sends the pure tensor `a ⊗ b` to `φ a ⊗ b`. -/
theorem whiskerRight_pureTensor {F F' G : Mod R} (φ : F ⟶ F') {V : Opens T}
    (a : F.val.obj (op V)) (b : G.val.obj (op V)) :
    (((curriedTensor (Mod R)).map φ).app G).val.app (op V) (pureTensor R a b) =
      pureTensor R (φ.val.app (op V) a) b := by
  have h := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
    (ringedSpaceOf R) F G F' G φ (𝟙 G) V a b
  exact (congrArg (fun morphism :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj F).obj G ⟶
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj F').obj G =>
      (morphism.val.app (op V)).hom (pureTensor R a b))
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map R φ (𝟙 G))).symm.trans h

/-- A section of a tensor product of sheaves of modules is, near each point, a finite sum of pure
tensors. -/
theorem exists_nhd_sum_pureTensor {F G : Mod R} {V : Opens T}
    (t : (((curriedTensor (Mod R)).obj F).obj G).val.obj (op V)) (x : T) (hx : x ∈ V) :
    ∃ (V' : Opens T) (hV : V' ≤ V), x ∈ V' ∧
      ∃ (n : ℕ) (a : Fin n → F.val.obj (op V')) (b : Fin n → G.val.obj (op V')),
        res (((curriedTensor (Mod R)).obj F).obj G) hV t = ∑ j, pureTensor R (a j) (b j) :=
  Stacks.SheafOfModules.TensorUnit.exists_nhd_sum_monoidalTensorSection (ringedSpaceOf R) F G V t
    x hx

/-- A point lying in every open `f i`, `i ∈ s`, lies in their finite intersection. -/
theorem mem_finset_inf_opens {ι : Type*} (s : Finset ι) (f : ι → Opens T) (x : T)
    (h : ∀ i ∈ s, x ∈ f i) : x ∈ s.inf f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.inf_insert]
    exact ⟨h i (Finset.mem_insert_self i s), ih fun j hj => h j (Finset.mem_insert_of_mem hj)⟩

/-- **A section of the degree-zero term of a total tensor complex is, near each point, a finite
sum of sections of the summands `A^p ⊗ B^q`, `p + q = 0`.** -/
theorem exists_nhd_sum_ιMapBifunctor (A B : CochainComplex (Mod R) ℤ) {V : Opens T}
    (t : ((HomologicalComplex.mapBifunctor A B (curriedTensor (Mod R))
      (ComplexShape.up ℤ)).X 0).val.obj (op V)) (x : T) (hx : x ∈ V) :
    ∃ (V' : Opens T) (hV : V' ≤ V), x ∈ V' ∧
      ∃ (S : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = 0})
        (y : ∀ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = 0},
          (((curriedTensor (Mod R)).obj (A.X ij.1.1)).obj (B.X ij.1.2)).val.obj (op V')),
        res _ hV t = ∑ ij ∈ S,
          (HomologicalComplex.ιMapBifunctor A B (curriedTensor (Mod R)) (ComplexShape.up ℤ)
            ij.1.1 ij.1.2 0 (by simpa using ij.2)).val.app (op V') (y ij) := by
  obtain ⟨Sv, hSv, hsum⟩ :=
    Stacks.SheafOfModules.CoproductSheafification.exists_sieve_sum_inj_of_isColimit
      (Stacks.SheafOfModules.Tensor.ringSheaf R) _
      (HomologicalComplex.isColimitCofanιMapBifunctor A B (curriedTensor (Mod R)) 0) t
  obtain ⟨V', g, hg, hxV'⟩ := hSv x hx
  obtain ⟨S, y, hy⟩ := hsum g hg
  exact ⟨V', leOfHom g, hxV', S, y, hy⟩

/-- Restriction of sections commutes with finite sums. -/
theorem res_sum (M : Mod R) {V' V : Opens T} (h : V' ≤ V) {ι : Type*} (s : Finset ι)
    (f : ι → M.val.obj (op V)) : res M h (∑ i ∈ s, f i) = ∑ i ∈ s, res M h (f i) :=
  map_sum _ _ _

/-- A morphism of sheaves of modules commutes with finite sums of sections. -/
theorem app_sum {M N : Mod R} (φ : M ⟶ N) {V : Opens T} {ι : Type*} (s : Finset ι)
    (f : ι → M.val.obj (op V)) :
    φ.val.app (op V) (∑ i ∈ s, f i) = ∑ i ∈ s, φ.val.app (op V) (f i) :=
  map_sum _ _ _

/-- Restriction of a finite sum of pure tensors is the sum of the pure tensors of the
restrictions. -/
theorem res_sum_pureTensor {F G : Mod R} {V' V : Opens T} (h : V' ≤ V) {n : ℕ}
    (a : Fin n → F.val.obj (op V)) (b : Fin n → G.val.obj (op V)) :
    res (((curriedTensor (Mod R)).obj F).obj G) h (∑ k, pureTensor R (a k) (b k)) =
      ∑ k, pureTensor R (res F h (a k)) (res G h (b k)) :=
  (res_sum _ _ _ _).trans (Finset.sum_congr rfl fun _ _ => res_pureTensor _ _ _)

/-- If the restriction of `y` to `V'` is the sum of the pure tensors `a k ⊗ b k`, then its
restriction to `V'' ≤ V'` is the sum of the pure tensors of the restrictions of `a k` and `b k`. -/
theorem res_eq_sum_pureTensor_of_res_eq {F G : Mod R} {V'' V' V : Opens T} (h₁ : V'' ≤ V')
    (h₂ : V' ≤ V) (y : (((curriedTensor (Mod R)).obj F).obj G).val.obj (op V)) {n : ℕ}
    (a : Fin n → F.val.obj (op V')) (b : Fin n → G.val.obj (op V'))
    (hab : res _ h₂ y = ∑ k, pureTensor R (a k) (b k)) :
    res _ (h₁.trans h₂) y = ∑ k, pureTensor R (res F h₁ (a k)) (res G h₁ (b k)) := by
  rw [← res_res _ h₁ h₂, hab, res_sum_pureTensor]

/-- **A section of the degree-zero term of a total tensor complex is, near each point, a finite
sum of pure tensors `a ⊗ b` of sections of `A^p` and `B^q`, `p + q = 0`.** -/
theorem exists_nhd_sum_ιMapBifunctor_pureTensor (A B : CochainComplex (Mod R) ℤ) {V : Opens T}
    (t : ((HomologicalComplex.mapBifunctor A B (curriedTensor (Mod R))
      (ComplexShape.up ℤ)).X 0).val.obj (op V)) (x : T) (hx : x ∈ V) :
    ∃ (V' : Opens T) (hV : V' ≤ V), x ∈ V' ∧
      ∃ (S : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = 0}) (n : S → ℕ)
        (a : ∀ (ij : S) (_ : Fin (n ij)), (A.X ij.1.1.1).val.obj (op V'))
        (b : ∀ (ij : S) (_ : Fin (n ij)), (B.X ij.1.1.2).val.obj (op V')),
        res _ hV t = ∑ ij : S, ∑ k : Fin (n ij),
          (HomologicalComplex.ιMapBifunctor A B (curriedTensor (Mod R)) (ComplexShape.up ℤ)
            ij.1.1.1 ij.1.1.2 0 (by simpa using ij.1.2)).val.app (op V')
              (pureTensor R (a ij k) (b ij k)) := by
  classical
  obtain ⟨V₁, hV₁, hx₁, S, y, hy⟩ := exists_nhd_sum_ιMapBifunctor A B t x hx
  have h2 := fun ij : S => exists_nhd_sum_pureTensor (y ij) x hx₁
  choose V₂ h₂ hx₂ n a b hab using h2
  let V' : Opens T := V₁ ⊓ (Finset.univ : Finset S).inf V₂
  have hV'₁ : V' ≤ V₁ := inf_le_left
  have hV'₂ : ∀ ij, V' ≤ V₂ ij := fun ij =>
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ ij))
  refine ⟨V', hV'₁.trans hV₁, ⟨hx₁, mem_finset_inf_opens _ _ _ fun ij _ => hx₂ ij⟩,
    S, n, fun ij k => res _ (hV'₂ ij) (a ij k), fun ij k => res _ (hV'₂ ij) (b ij k), ?_⟩
  rw [← res_res _ hV'₁ hV₁, hy, res_sum, ← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [← map_res, res_eq_sum_pureTensor_of_res_eq (hV'₂ ij) (h₂ ij) _ _ _ (hab ij), app_sum]

/-- The map `Tot(K ⊗ B) ⟶ Tot(A ⊗ B)` induced by `j : K ⟶ A` sends the image of a pure tensor
`y ⊗ b` in the summand `K^p ⊗ B^q` to the image of `j y ⊗ b` in `A^p ⊗ B^q`. -/
theorem mapBifunctorMap_ι_pureTensor {A B K : CochainComplex (Mod R) ℤ} (j : K ⟶ A) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 0) {W : Opens T}
    (y : (K.X p).val.obj (op W)) (b : (B.X q).val.obj (op W)) :
    ((HomologicalComplex.mapBifunctorMap j (𝟙 B) (curriedTensor (Mod R)) (ComplexShape.up ℤ)).f
        0).val.app (op W)
      ((HomologicalComplex.ιMapBifunctor K B (curriedTensor (Mod R)) (ComplexShape.up ℤ) p q 0
        h).val.app (op W) (pureTensor R y b)) =
    (HomologicalComplex.ιMapBifunctor A B (curriedTensor (Mod R)) (ComplexShape.up ℤ) p q 0
        h).val.app (op W) (pureTensor R ((j.f p).val.app (op W) y) b) := by
  have e := HomologicalComplex.ι_mapBifunctorMap j (𝟙 B) (curriedTensor (Mod R))
    (ComplexShape.up ℤ) p q 0 h
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp] at e
  have e' := congrArg (fun φ => φ.val.app (op W) (pureTensor R y b)) e
  exact e'.trans (congrArg ((HomologicalComplex.ιMapBifunctor A B (curriedTensor (Mod R))
    (ComplexShape.up ℤ) p q 0 h).val.app (op W)) (whiskerRight_pureTensor (j.f p) y b))

/-- The finite-sum form of `mapBifunctorMap_ι_pureTensor`. -/
theorem mapBifunctorMap_sum_ι_pureTensor {A B K : CochainComplex (Mod R) ℤ} (j : K ⟶ A)
    {W : Opens T} {S : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = 0}} {n : S → ℕ}
    (y : ∀ (ij : S) (_ : Fin (n ij)), (K.X ij.1.1.1).val.obj (op W))
    (b : ∀ (ij : S) (_ : Fin (n ij)), (B.X ij.1.1.2).val.obj (op W)) :
    ((HomologicalComplex.mapBifunctorMap j (𝟙 B) (curriedTensor (Mod R)) (ComplexShape.up ℤ)).f
        0).val.app (op W) (∑ ij : S, ∑ k : Fin (n ij),
      (HomologicalComplex.ιMapBifunctor K B (curriedTensor (Mod R)) (ComplexShape.up ℤ)
        ij.1.1.1 ij.1.1.2 0 (by simpa using ij.1.2)).val.app (op W)
          (pureTensor R (y ij k) (b ij k))) =
    ∑ ij : S, ∑ k : Fin (n ij),
      (HomologicalComplex.ιMapBifunctor A B (curriedTensor (Mod R)) (ComplexShape.up ℤ)
        ij.1.1.1 ij.1.1.2 0 (by simpa using ij.1.2)).val.app (op W)
          (pureTensor R ((j.f _).val.app (op W) (y ij k)) (b ij k)) := by
  rw [app_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [app_sum]
  exact Finset.sum_congr rfl fun k _ => mapBifunctorMap_ι_pureTensor j _ _ _ _ _

/-- Restriction of a finite sum of images of pure tensors in `Tot(A ⊗ B)` is the corresponding sum
for the restricted sections. -/
theorem res_sum_ι_pureTensor {A B : CochainComplex (Mod R) ℤ} {W V : Opens T} (h : W ≤ V)
    {S : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = 0}} {n : S → ℕ}
    (a : ∀ (ij : S) (_ : Fin (n ij)), (A.X ij.1.1.1).val.obj (op V))
    (b : ∀ (ij : S) (_ : Fin (n ij)), (B.X ij.1.1.2).val.obj (op V)) :
    res _ h (∑ ij : S, ∑ k : Fin (n ij),
      (HomologicalComplex.ιMapBifunctor A B (curriedTensor (Mod R)) (ComplexShape.up ℤ)
        ij.1.1.1 ij.1.1.2 0 (by simpa using ij.1.2)).val.app (op V)
          (pureTensor R (a ij k) (b ij k))) =
    ∑ ij : S, ∑ k : Fin (n ij),
      (HomologicalComplex.ιMapBifunctor A B (curriedTensor (Mod R)) (ComplexShape.up ℤ)
        ij.1.1.1 ij.1.1.2 0 (by simpa using ij.1.2)).val.app (op W)
          (pureTensor R (res _ h (a ij k)) (res _ h (b ij k))) := by
  rw [res_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [res_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_res, res_pureTensor]

/-- **The lift of a decomposed section through a subcomplex.** If the sections `a` of `A` lift
along `j : K ⟶ A` over `W`, then the corresponding sum of pure tensors in `Tot(K ⊗ B)` maps to the
restriction of the sum in `Tot(A ⊗ B)`. -/
theorem mapBifunctorMap_lift_eq {A B K : CochainComplex (Mod R) ℤ} (j : K ⟶ A) {W V : Opens T}
    (hW : W ≤ V) {S : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = 0}} {n : S → ℕ}
    (a : ∀ (ij : S) (_ : Fin (n ij)), (A.X ij.1.1.1).val.obj (op V))
    (b : ∀ (ij : S) (_ : Fin (n ij)), (B.X ij.1.1.2).val.obj (op V))
    (y : ∀ (ij : S) (_ : Fin (n ij)), (K.X ij.1.1.1).val.obj (op W))
    (hy : ∀ ij k, (j.f _).val.app (op W) (y ij k) = res _ hW (a ij k)) :
    ((HomologicalComplex.mapBifunctorMap j (𝟙 B) (curriedTensor (Mod R)) (ComplexShape.up ℤ)).f
        0).val.app (op W) (∑ ij : S, ∑ k : Fin (n ij),
      (HomologicalComplex.ιMapBifunctor K B (curriedTensor (Mod R)) (ComplexShape.up ℤ)
        ij.1.1.1 ij.1.1.2 0 (by simpa using ij.1.2)).val.app (op W)
          (pureTensor R (y ij k) (res _ hW (b ij k)))) =
    res _ hW (∑ ij : S, ∑ k : Fin (n ij),
      (HomologicalComplex.ιMapBifunctor A B (curriedTensor (Mod R)) (ComplexShape.up ℤ)
        ij.1.1.1 ij.1.1.2 0 (by simpa using ij.1.2)).val.app (op V)
          (pureTensor R (a ij k) (b ij k))) := by
  rw [mapBifunctorMap_sum_ι_pureTensor, res_sum_ι_pureTensor]
  refine Finset.sum_congr rfl fun ij _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hy]

/-- A section of degree `0` whose image under a morphism of complexes that is injective in
degree `1` is a cocycle is itself a cocycle. -/
theorem d_eq_zero_of_mono {A B : CochainComplex (Mod R) ℤ} (φ : A ⟶ B) [Mono (φ.f 1)]
    {V : Opens T} (s : (A.X 0).val.obj (op V))
    (hs : (B.d 0 1).val.app (op V) ((φ.f 0).val.app (op V) s) = 0) :
    (A.d 0 1).val.app (op V) s = 0 := by
  apply Stacks.SheafOfModules.injective_app_of_mono (φ.f 1) (op V)
  have h := congrArg (fun ψ => ψ.val.app (op V) s) (φ.comm 0 1)
  refine (h.symm.trans hs).trans ?_
  exact (map_zero _).symm

section AnySite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- A section of degree `0` whose image under a morphism of complexes that is injective in
degree `1` is a cocycle is itself a cocycle, the section being taken over an object of an
arbitrary small site.

This is the general form of `d_eq_zero_of_mono` above, which takes the section over an open of a
space. The site is arbitrary because the only input is
`Stacks.SheafOfModules.injective_app_of_mono`, which holds at any object of any site; the open of
the ringed-space statement enters only as the object the sections are taken over, so widening it
to an arbitrary object costs nothing and the proof is the same one. -/
theorem d_eq_zero_of_mono_general {A B : CochainComplex (Mod R) ℤ} (φ : A ⟶ B) [Mono (φ.f 1)]
    {V : C} (s : (A.X 0).val.obj (op V))
    (hs : (B.d 0 1).val.app (op V) ((φ.f 0).val.app (op V) s) = 0) :
    (A.d 0 1).val.app (op V) s = 0 := by
  apply Stacks.SheafOfModules.injective_app_of_mono (φ.f 1) (op V)
  have h := congrArg (fun ψ => ψ.val.app (op V) s) (φ.comm 0 1)
  refine (h.symm.trans hs).trans ?_
  exact (map_zero _).symm

end AnySite

end Stacks.Cohomology.LeftDualPerfect
