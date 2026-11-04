module

public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Homology.Perfect.BalancedDerivedTensor

/-!
# Balanced tensoring with a finite free right module

Let `Λ` be a ring, not necessarily commutative, and let `N` be a right `Λ`-module which is free
with a finite basis `b : ι → N`. Then the balanced tensor product `N ⊗_Λ M` is, naturally in the
left `Λ`-module `M`, the abelian group `ι → M` of `ι`-tuples of elements of `M`: the pure tensor
`n ⊗ m` goes to the tuple `(bᵢ*(n) m)ᵢ` of coordinates, and a tuple `(mᵢ)` comes back as
`∑ᵢ bᵢ ⊗ mᵢ`. Consequently balanced tensoring with `N` is exact, and a strictly bounded complex of
finite free right `Λ`-modules is K-flat for the balanced tensor bifunctor in its first variable:
`Tot(R ⊗_Λ -)` preserves quasi-isomorphisms of arbitrary, unbounded, complexes of left
`Λ`-modules.

## Main definitions

* `StacksDraft.Perfect.balancedTensorFreeModel`: the functor `M ↦ (ι → M)` from left
  `Λ`-modules to abelian groups.
* `StacksDraft.Perfect.balancedTensorFreeIso`: for a finite basis `b` of `N`, the natural
  isomorphism `N ⊗_Λ - ≅ (ι → -)`.

## Main results

* `StacksDraft.Perfect.balancedTensorFunctor_additive_left`: balanced tensoring is additive in
  the right module.
* `StacksDraft.Perfect.exact_map_balancedTensorFunctor_obj_of_free`: tensoring with a finite
  free right module carries exact short complexes to exact short complexes.
* `StacksDraft.Perfect.kFlatLeft_balancedTensorFunctor_of_free`: a strictly bounded complex of
  finite free right modules is left K-flat for the balanced tensor bifunctor.
* `StacksDraft.Perfect.quasiIso_mapBifunctorMap_balancedTensorFunctor`: for such a complex `R`,
  `Tot(R ⊗_Λ -)` carries quasi-isomorphisms to quasi-isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace StacksDraft.Perfect

variable (Λ : Type u) [Ring Λ]

attribute [local instance] balancedTensorFunctor_additive

/-- **Balanced tensoring is additive in the right module**: `(f + g) ⊗ M = f ⊗ M + g ⊗ M`. -/
instance balancedTensorFunctor_additive_left : (balancedTensorFunctor.{u, v} Λ).Additive where
  map_add {N N' f g} := by
    refine NatTrans.ext (funext fun M => ?_)
    rw [NatTrans.app_add]
    refine balancedTensor_hom_ext Λ N M _ _ _ fun n m => ?_
    change balancedTensorMap Λ (f + g) (𝟙 M) (balancedTensorPure Λ N M n m) =
      balancedTensorMap Λ f (𝟙 M) (balancedTensorPure Λ N M n m) +
        balancedTensorMap Λ g (𝟙 M) (balancedTensorPure Λ N M n m)
    rw [balancedTensorMap_pure, balancedTensorMap_pure, balancedTensorMap_pure]
    simp

/-! ### The model `M ↦ (ι → M)` -/

/-- The functor sending a left `Λ`-module `M` to the abelian group `ι → M` of `ι`-tuples of its
elements. For a free right module with a basis indexed by a finite type `ι`, it is balanced
tensoring with that module (`StacksDraft.Perfect.balancedTensorFreeIso`). -/
def balancedTensorFreeModel (ι : Type v) : ModuleCat.{v} Λ ⥤ ModuleCat.{v} ℤ where
  obj M := ModuleCat.of ℤ (ι → M)
  map f := ModuleCat.ofHom (intLinearMapOfAddHom (AddMonoidHom.compLeft f.hom.toAddMonoidHom ι))

/-- The functor `M ↦ (ι → M)` is additive. -/
instance balancedTensorFreeModel_additive (ι : Type v) :
    (balancedTensorFreeModel Λ ι).Additive where
  map_add := rfl

/-- The functor `M ↦ (ι → M)` carries exact short complexes to exact short complexes. -/
theorem exact_map_balancedTensorFreeModel (ι : Type v) (S : ShortComplex (ModuleCat.{v} Λ))
    (hS : S.Exact) : (S.map (balancedTensorFreeModel Λ ι)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x hx
  choose y hy using fun i => hS (x i) (congr_fun hx i)
  exact ⟨y, funext hy⟩

section Free

variable {Λ} {ι : Type v} [Fintype ι] {N : ModuleCat.{v} (MulOpposite Λ)}
  (b : Module.Basis ι (MulOpposite Λ) N)

/-- The biadditive map `(n, m) ↦ (bᵢ*(n) m)ᵢ` attached to a basis `b` of the right module `N`,
where `bᵢ*(n) ∈ Λ` is the `i`-th coordinate of `n`. -/
def balancedTensorFreeCoord (M : ModuleCat.{v} Λ) :
    N →ₗ[ℤ] M →ₗ[ℤ] (balancedTensorFreeModel Λ ι).obj M :=
  intLinearMapOfAddHom
    (AddMonoidHom.mk' (fun n => intLinearMapOfAddHom
      (AddMonoidHom.mk' (fun m i => MulOpposite.unop (b.repr n i) • m)
        (fun m m' => by funext i; exact smul_add _ m m')))
      (fun n n' => by
        ext m
        funext i
        change MulOpposite.unop (b.repr (n + n') i) • m =
          MulOpposite.unop (b.repr n i) • m + MulOpposite.unop (b.repr n' i) • m
        simp [add_smul]))

omit [Fintype ι] in
/-- The `i`-th coordinate of the image of `(n, m)` is `bᵢ*(n) m`. -/
theorem balancedTensorFreeCoord_apply (M : ModuleCat.{v} Λ) (n : N) (m : M) (i : ι) :
    balancedTensorFreeCoord b M n m i = MulOpposite.unop (b.repr n i) • m :=
  rfl

omit [Fintype ι] in
/-- The coordinate map is balanced: `bᵢ*(n a) m = bᵢ*(n) (a m)`. -/
theorem balancedTensorFreeCoord_balanced (M : ModuleCat.{v} Λ) (n : N) (a : Λ) (m : M) :
    balancedTensorFreeCoord b M (MulOpposite.op a • n) m =
      balancedTensorFreeCoord b M n (a • m) := by
  funext i
  simp only [balancedTensorFreeCoord_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
    MulOpposite.unop_mul, MulOpposite.unop_op, mul_smul]

/-- The comparison `N ⊗_Λ M ⟶ (ι → M)`, `n ⊗ m ↦ (bᵢ*(n) m)ᵢ`. -/
def balancedTensorFreeHom (M : ModuleCat.{v} Λ) :
    balancedTensorObject Λ N M ⟶ (balancedTensorFreeModel Λ ι).obj M :=
  balancedTensorLift Λ N M _ (balancedTensorFreeCoord b M) (balancedTensorFreeCoord_balanced b M)

omit [Fintype ι] in
/-- The comparison sends the pure tensor `n ⊗ m` to `(bᵢ*(n) m)ᵢ`. -/
theorem balancedTensorFreeHom_pure (M : ModuleCat.{v} Λ) (n : N) (m : M) :
    balancedTensorFreeHom b M (balancedTensorPure Λ N M n m) = balancedTensorFreeCoord b M n m :=
  rfl

/-- The comparison `(ι → M) ⟶ N ⊗_Λ M`, `(mᵢ) ↦ ∑ᵢ bᵢ ⊗ mᵢ`. -/
def balancedTensorFreeInv (M : ModuleCat.{v} Λ) :
    (balancedTensorFreeModel Λ ι).obj M ⟶ balancedTensorObject Λ N M :=
  ModuleCat.ofHom (intLinearMapOfAddHom
    (AddMonoidHom.mk' (fun x : ι → M => ∑ i, balancedTensorPure Λ N M (b i) (x i))
      (fun x y => by simp only [Pi.add_apply, map_add]; exact Finset.sum_add_distrib)))

/-- The inverse comparison sends `(mᵢ)` to `∑ᵢ bᵢ ⊗ mᵢ`. -/
theorem balancedTensorFreeInv_apply (M : ModuleCat.{v} Λ)
    (x : (balancedTensorFreeModel Λ ι).obj M) :
    balancedTensorFreeInv b M x = ∑ i, balancedTensorPure Λ N M (b i) (x i) :=
  rfl

/-- The two comparisons are mutually inverse: `N ⊗_Λ M ≅ (ι → M)`. -/
def balancedTensorFreeIsoApp (M : ModuleCat.{v} Λ) :
    balancedTensorObject Λ N M ≅ (balancedTensorFreeModel Λ ι).obj M where
  hom := balancedTensorFreeHom b M
  inv := balancedTensorFreeInv b M
  hom_inv_id := by
    refine balancedTensor_hom_ext Λ N M _ _ _ fun n m => ?_
    rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, balancedTensorFreeHom_pure,
      balancedTensorFreeInv_apply]
    simp only [balancedTensorFreeCoord_apply]
    simp_rw [← balancedTensorPure_balanced, MulOpposite.op_unop]
    rw [← LinearMap.sum_apply, ← map_sum, b.sum_repr]
  inv_hom_id := by
    ext x
    rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, balancedTensorFreeInv_apply, map_sum]
    funext j
    refine (Finset.sum_apply (M := fun _ : ι => (M : Type v)) j Finset.univ
      (fun i => (balancedTensorFreeCoord b M (b i) (x i) : ι → M))).trans ?_
    simp only [balancedTensorFreeCoord_apply, Module.Basis.repr_self]
    rw [Finset.sum_eq_single j (fun c _ hc => by simp [hc]) (by simp)]
    simp

/-- **Balanced tensoring with a finite free right module is a finite power of the underlying
abelian group**: a basis `b` of `N` indexed by a finite type `ι` gives the natural isomorphism
`N ⊗_Λ - ≅ (ι → -)` of functors from left `Λ`-modules to abelian groups. -/
def balancedTensorFreeIso : (balancedTensorFunctor Λ).obj N ≅ balancedTensorFreeModel Λ ι :=
  NatIso.ofComponents (balancedTensorFreeIsoApp b) (fun {M M'} g => by
    refine balancedTensor_hom_ext Λ N M _ _ _ fun n m => ?_
    change balancedTensorFreeHom b M'
        (balancedTensorMap Λ (𝟙 N) g (balancedTensorPure Λ N M n m)) =
      (balancedTensorFreeModel Λ ι).map g
        (balancedTensorFreeHom b M (balancedTensorPure Λ N M n m))
    rw [balancedTensorMap_pure, balancedTensorFreeHom_pure, balancedTensorFreeHom_pure]
    funext i
    change MulOpposite.unop (b.repr n i) • g m = g (MulOpposite.unop (b.repr n i) • m)
    rw [map_smul])

end Free

/-! ### Exactness and K-flatness -/

/-- **Tensoring with a finite free right module is exact**: it carries exact short complexes of
left `Λ`-modules to exact short complexes of abelian groups. -/
theorem exact_map_balancedTensorFunctor_obj_of_free (N : ModuleCat.{v} (MulOpposite Λ))
    [Module.Free (MulOpposite Λ) N] [Module.Finite (MulOpposite Λ) N]
    (S : ShortComplex (ModuleCat.{v} Λ)) (hS : S.Exact) :
    (S.map ((balancedTensorFunctor Λ).obj N)).Exact :=
  (ShortComplex.exact_iff_of_iso
    (S.mapNatIso (balancedTensorFreeIso (Module.Free.chooseBasis (MulOpposite Λ) N)))).2
    (exact_map_balancedTensorFreeModel Λ _ S hS)

open CochainComplex.KFlatBifunctor in
/-- **A strictly bounded complex of finite free right modules is left K-flat** for the balanced
tensor bifunctor: `Tot(R ⊗_Λ G)` is acyclic for every acyclic complex `G` of left `Λ`-modules,
unbounded in either direction. -/
theorem kFlatLeft_balancedTensorFunctor_of_free
    (R : CochainComplex (ModuleCat.{v} (MulOpposite Λ)) ℤ)
    (a b : ℤ) [R.IsStrictlyGE a] [R.IsStrictlyLE b]
    [∀ q, Module.Free (MulOpposite Λ) (R.X q)] [∀ q, Module.Finite (MulOpposite Λ) (R.X q)] :
    KFlatLeft (balancedTensorFunctor Λ) R := by
  rw [kFlatLeft_iff_kFlat_flip]
  refine kFlat_of_isStrictlyLE_of_isStrictlyGE _ R b a
    (fun q => kFlat_single_of_exact _ _ q (fun G hG n => ?_))
  rw [HomologicalComplex.exactAt_iff]
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (exact_map_balancedTensorFunctor_obj_of_free Λ (R.X q) _
      ((HomologicalComplex.exactAt_iff G n).1 (hG n)))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

open CochainComplex.KFlatBifunctor in
/-- **`Tot(R ⊗_Λ -)` preserves quasi-isomorphisms** when `R` is a strictly bounded complex of
finite free right `Λ`-modules: for a quasi-isomorphism `f : E ⟶ E'` of complexes of left
`Λ`-modules, arbitrary and unbounded, the induced map `Tot(R ⊗_Λ E) ⟶ Tot(R ⊗_Λ E')` is a
quasi-isomorphism. -/
theorem quasiIso_mapBifunctorMap_balancedTensorFunctor
    (R : CochainComplex (ModuleCat.{v} (MulOpposite Λ)) ℤ)
    (a b : ℤ) [R.IsStrictlyGE a] [R.IsStrictlyLE b]
    [∀ q, Module.Free (MulOpposite Λ) (R.X q)] [∀ q, Module.Finite (MulOpposite Λ) (R.X q)]
    {E E' : CochainComplex (ModuleCat.{v} Λ) ℤ} (f : E ⟶ E') [QuasiIso f] :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 R) f (balancedTensorFunctor Λ)
      (ComplexShape.up ℤ)) :=
  quasiIso_of_kFlatLeft _ R (kFlatLeft_balancedTensorFunctor_of_free Λ R a b) f inferInstance

end StacksDraft.Perfect

end
