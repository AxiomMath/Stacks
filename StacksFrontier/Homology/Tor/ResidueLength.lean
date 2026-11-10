module

public import StacksFrontier.Homology.Tor.ResidueDevissage

/-!
# The length count at the residue field

Let `A` be a commutative ring, `m` a maximal ideal and `κ = A / m`. Let `F : D(A) → D(A)` be an
exact functor and `T` an object with bounded cohomology, every cohomology module finite and killed
by `m`, with nonzero bottom cohomology module and with `F(T) ≅ T`. If `F(κ[0])` has no cohomology
below zero, then

> `H⁰(F(κ[0])) ≅ κ`.

## Main results

* `StacksDraft.ResidueLength.residueLinearEquiv` — an `A`-linear equivalence between modules on
  which the residue field acts compatibly is `κ`-linear.
* `StacksDraft.ResidueLength.exists_nonempty_iso_pi_residueField` — a nonzero finite module killed
  by `m` is a positive finite power of `κ`.
* `StacksDraft.ResidueLength.mapPiIso` — an additive functor commutes with finite powers.
* `StacksDraft.ResidueLength.nonempty_linearEquiv_residueField_of_pi_linearEquiv`,
  `StacksDraft.ResidueLength.nonempty_iso_residueField_of_pi_iso` — a module a positive finite
  power of which is that power of `κ` is itself `κ`.
* `StacksDraft.ResidueLength.nonempty_iso_residueField_of_iso` — an additive endofunctor fixing
  one nonzero finite module killed by `m` carries `κ` to `κ`.
* `StacksDraft.ResidueLength.isIso_homologyMap_mor₁_of_isGE` — the first map of a distinguished
  triangle whose third object has no cohomology below `c` is invertible on cohomology below `c`.
* `StacksDraft.ResidueLength.nonempty_homology_iso_homology_map_single` — the bottom cohomology
  of `F(X)` is `F` at the bottom cohomology module of `X`.
* `StacksDraft.ResidueLength.nonempty_homology_iso_residueField_of_iso_of_isTorsionBySet` — for
  an exact endofunctor with `F(T) ≅ T` and `F(κ[0])` with no cohomology below zero,
  `H⁰(F(κ[0])) ≅ κ`.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.ResidueLength

universe u w w'

variable {A : Type u} [CommRing A]
  {D : Type w} [Category.{w'} D] [Abelian D]

/-! ### `κ`-linearity of `A`-linear maps -/

/-- On a module on which the residue field acts compatibly with the ring, the class of `a` acts
as `a` does. -/
theorem smul_residue_mk (m : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]
    [Module (A ⧸ m) M] [IsScalarTower A (A ⧸ m) M] (a : A) (x : M) :
    (Ideal.Quotient.mk m a) • x = a • x := by
  rw [show (Ideal.Quotient.mk m a) = algebraMap A (A ⧸ m) a from rfl,
    IsScalarTower.algebraMap_smul]

/-- An `A`-linear equivalence between modules on which the residue field acts compatibly is
`κ`-linear. -/
def residueLinearEquiv (m : Ideal A) {M N : Type u} [AddCommGroup M] [Module A M]
    [Module (A ⧸ m) M] [IsScalarTower A (A ⧸ m) M] [AddCommGroup N] [Module A N]
    [Module (A ⧸ m) N] [IsScalarTower A (A ⧸ m) N] (e : M ≃ₗ[A] N) :
    M ≃ₗ[A ⧸ m] N where
  toFun := e
  map_add' := e.map_add
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [RingHom.id_apply]
    rw [smul_residue_mk, smul_residue_mk, map_smul]
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

/-! ### Transport along an isomorphism of modules -/

/-- Being killed by a set of scalars transports along an isomorphism of modules. -/
theorem isTorsionBySet_of_iso {M N : ModuleCat.{u} A} (s : Set A) (e : M ≅ N)
    (h : Module.IsTorsionBySet A M s) : Module.IsTorsionBySet A N s := by
  intro x a
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
  rw [← e.toLinearEquiv.map_smul, @h y a, map_zero]

/-! ### A finite module killed by the maximal ideal is a finite power of the residue field -/

/-- A power of the residue field is killed by the maximal ideal. -/
theorem smul_eq_zero_of_mem (m : Ideal A) (n : ℕ) (y : Fin n → (A ⧸ m)) (a : A) (ha : a ∈ m) :
    a • y = 0 := by
  funext i
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (y i)
  change a • y i = 0
  rw [← hb, show a • (Ideal.Quotient.mk m b : A ⧸ m) = Ideal.Quotient.mk m (a * b) from rfl]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (m.mul_mem_right b ha)

/-- A nonzero finite module killed by a maximal ideal is, as an `A`-module, a positive finite
power of the residue field. -/
theorem exists_nonempty_iso_pi_residueField (m : Ideal A) [m.IsMaximal] (N : ModuleCat.{u} A)
    (hN : Module.IsTorsionBySet A N (m : Set A)) [Module.Finite A N] (hne : ¬ IsZero N) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (N ≅ ModuleCat.of A (Fin n → (A ⧸ m))) := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module (A ⧸ m) N := hN.module
  let : IsScalarTower A (A ⧸ m) N := hN.isScalarTower
  have : Module.Finite (A ⧸ m) N := Module.Finite.of_restrictScalars_finite A (A ⧸ m) N
  have : Nontrivial N := by
    refine (nontrivial_iff_exists_ne (0 : N)).mpr ?_
    by_contra! hc
    exact hne ((IsZero.iff_id_eq_zero N).2 (by ext y; simpa using hc y))
  exact ⟨_, Module.finrank_pos,
    ⟨((Module.finBasis (A ⧸ m) N).equivFun.restrictScalars A).toModuleIso⟩⟩

/-! ### Additive functors and finite powers -/

/-- An additive functor commutes with finite powers. -/
def mapPiIso (G : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [G.Additive] (n : ℕ)
    (M : ModuleCat.{u} A) :
    G.obj (ModuleCat.of A (Fin n → M)) ≅ ModuleCat.of A (Fin n → G.obj M) :=
  haveI : PreservesFiniteBiproducts G := Functor.preservesFiniteBiproductsOfAdditive G
  haveI : PreservesLimitsOfShape (Discrete (Fin n)) G :=
    preservesProductsOfShape_of_preservesBiproductsOfShape G
  G.mapIso (ModuleCat.piIsoPi (fun _ : Fin n => M)).symm ≪≫
    PreservesProduct.iso G _ ≪≫ ModuleCat.piIsoPi _

/-! ### The count -/

/-- If a positive finite power of a module `V` is the corresponding power of the residue field
`κ = A / m`, then `V` is the residue field. -/
theorem nonempty_linearEquiv_residueField_of_pi_linearEquiv (m : Ideal A) [m.IsMaximal] (n : ℕ)
    (hn : 0 < n) (V : Type u) [AddCommGroup V] [Module A V]
    (ψ : (Fin n → V) ≃ₗ[A] (Fin n → (A ⧸ m))) :
    Nonempty (V ≃ₗ[A] (A ⧸ m)) := by
  classical
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have hVtors : Module.IsTorsionBySet A V (m : Set A) := by
    intro x a
    have hx : ((a : A) • (fun _ ↦ x : Fin n → V)) = 0 :=
      ψ.map_eq_zero_iff.mp (by rw [map_smul]; exact smul_eq_zero_of_mem m n _ _ a.2)
    simpa using congrFun hx ⟨0, hn⟩
  let : Module (A ⧸ m) V := hVtors.module
  let : IsScalarTower A (A ⧸ m) V := hVtors.isScalarTower
  have : Module.Finite A (Fin n → V) := Module.Finite.equiv ψ.symm
  have : Module.Finite A V :=
    Module.Finite.of_surjective
      (LinearMap.proj (R := A) (φ := fun _ : Fin n => V) ⟨0, hn⟩)
      (fun x ↦ ⟨fun _ ↦ x, rfl⟩)
  have : Module.Finite (A ⧸ m) V := Module.Finite.of_restrictScalars_finite A (A ⧸ m) V
  have hdim : Module.finrank (A ⧸ m) (Fin n → V) =
      Module.finrank (A ⧸ m) (Fin n → (A ⧸ m)) :=
    LinearEquiv.finrank_eq (residueLinearEquiv m ψ)
  rw [show Module.finrank (A ⧸ m) (Fin n → V) = n * Module.finrank (A ⧸ m) V by
        simp [Module.finrank_pi_fintype, Finset.sum_const],
    show Module.finrank (A ⧸ m) (Fin n → (A ⧸ m)) = n by simp] at hdim
  have hone : Module.finrank (A ⧸ m) V = 1 :=
    Nat.eq_of_mul_eq_mul_left hn (by rw [hdim, mul_one])
  have ebas := (Module.finBasis (A ⧸ m) V).equivFun
  rw [hone] at ebas
  exact ⟨(ebas ≪≫ₗ LinearEquiv.funUnique (Fin 1) (A ⧸ m) (A ⧸ m)).restrictScalars A⟩

/-- The count, read in the category of modules. -/
theorem nonempty_iso_residueField_of_pi_iso (m : Ideal A) [m.IsMaximal] (n : ℕ) (hn : 0 < n)
    (V : ModuleCat.{u} A)
    (ψ : ModuleCat.of A (Fin n → V) ≅ ModuleCat.of A (Fin n → (A ⧸ m))) :
    Nonempty (V ≅ ModuleCat.of A (A ⧸ m)) :=
  (nonempty_linearEquiv_residueField_of_pi_linearEquiv m n hn V ψ.toLinearEquiv).map
    LinearEquiv.toModuleIso

/-- An additive endofunctor of `A`-modules which carries one nonzero finite module killed by the
maximal ideal `m` to itself carries the residue field `κ = A / m` to the residue field. -/
theorem nonempty_iso_residueField_of_iso (m : Ideal A) [m.IsMaximal]
    (G : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [G.Additive] (N : ModuleCat.{u} A)
    (hN : Module.IsTorsionBySet A N (m : Set A)) [Module.Finite A N] (hne : ¬ IsZero N)
    (e : G.obj N ≅ N) :
    Nonempty (G.obj (ModuleCat.of A (A ⧸ m)) ≅ ModuleCat.of A (A ⧸ m)) := by
  obtain ⟨n, hn, ⟨φ⟩⟩ := exists_nonempty_iso_pi_residueField m N hN hne
  exact nonempty_iso_residueField_of_pi_iso m n hn _
    ((mapPiIso G n (ModuleCat.of A (A ⧸ m))).symm ≪≫ G.mapIso φ.symm ≪≫ e ≪≫ φ)

/-! ### The degeneration -/

/-- In degrees below `c` the first map of a distinguished triangle whose third object has no
cohomology below `c` is invertible on cohomology. -/
theorem isIso_homologyMap_mor₁_of_isGE (T : Triangle (DerivedCategory D))
    (hT : T ∈ distTriang (DerivedCategory D)) (c i : ℤ) (hi : i < c) (h₃ : T.obj₃.IsGE c) :
    IsIso ((homologyFunctor D i).map T.mor₁) := by
  have : Epi ((homologyFunctor D i).map T.mor₁) := by
    rw [HomologySequence.epi_homologyMap_mor₁_iff _ hT i]
    exact (isZero_of_isGE T.obj₃ c i hi (hX := h₃)).eq_of_tgt _ _
  have : Mono ((homologyFunctor D i).map T.mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff _ hT (i - 1) i (by omega)]
    exact (isZero_of_isGE T.obj₃ c (i - 1) (by omega) (hX := h₃)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- Let `X` have cohomology concentrated in `[a, b]`, every cohomology module finite and killed
by the maximal ideal `m`, and let `F` be exact with `F(κ[0])` having no cohomology below zero.
Then the bottom cohomology of `F(X)` is `F` at the bottom cohomology module of `X`:

`H^a(F(X)) ≅ H⁰(F(H^a(X)[0]))`. -/
theorem nonempty_homology_iso_homology_map_single
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory D) [F.CommShift ℤ]
    [F.IsTriangulated] (m : Ideal A) [m.IsMaximal] (X : DerivedCategory (ModuleCat.{u} A))
    (a b : ℤ) (ha : X.IsGE a) (hb : X.IsLE b)
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((homologyFunctor (ModuleCat.{u} A) i).obj X) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj X))
    (hGE : (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (A ⧸ m)))).IsGE 0) :
    Nonempty ((homologyFunctor D a).obj (F.obj X) ≅
      (homologyFunctor D 0).obj (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
        ((homologyFunctor (ModuleCat.{u} A) a).obj X)))) := by
  have := ha
  have := hb
  have hup : (F.obj ((TStructure.t.truncGE (a + 1)).obj X)).IsGE (a + 1) := by
    refine ExtremalDegrees.isGE_map_of_homology F
      ((TStructure.t.truncGE (a + 1)).obj X) (a + 1) b (a + 1) inferInstance inferInstance
      (fun i ↦ ?_)
    by_cases hi : a + 1 ≤ i
    · have hiso := ExtremalDegrees.isIso_homology_truncGE (a + 1) i hi X
      have ecomp := @asIso _ _ _ _ ((homologyFunctor (ModuleCat.{u} A) i).map
        ((TStructure.t.truncGEπ (a + 1)).app X)) hiso
      have hfiniso := haveI := hfin i
        Module.Finite.equiv (M := (homologyFunctor (ModuleCat.{u} A) i).obj X) ecomp.toLinearEquiv
      have hkilliso := isTorsionBySet_of_iso (m : Set A) ecomp (hkill i)
      have hz := ResidueDevissage.isGE_map_single_of_isTorsionBySet F m 0 hGE _ hkilliso
      exact TStructure.t.isGE_of_ge _ (a + 1 - i) 0
    · apply TStructure.t.isGE_of_isZero
      exact F.map_isZero ((singleFunctor (ModuleCat.{u} A) 0).map_isZero
        (isZero_of_isGE ((TStructure.t.truncGE (a + 1)).obj X) (a + 1) i (by omega)))
  have hT := F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished (a + 1) X)
  have hiso := isIso_homologyMap_mor₁_of_isGE
    (F.mapTriangle.obj ((TStructure.t.triangleLTGE (a + 1)).obj X)) hT (a + 1) a (by omega) hup
  obtain ⟨e₁⟩ := ExtremalDegrees.nonempty_iso_truncLT_succ_singleFunctor X a ha
  refine ⟨(@asIso _ _ _ _ _ hiso).symm ≪≫ (homologyFunctor D a).mapIso (F.mapIso e₁) ≪≫ ?_⟩
  exact (homologyFunctor D a).mapIso
      (ExtremalDegrees.mapSingleShiftIso F ((homologyFunctor (ModuleCat.{u} A) a).obj X) a) ≪≫
    ((homologyFunctor D 0).shiftIso (-a) a 0 (by omega)).app _

/-! ### The length count -/

/-- Let `F : D(A) → D(A)` be exact, let `T` have cohomology concentrated in `[a, b]`, all of it
finite and killed by the maximal ideal `m`, with `H^a(T)` nonzero, and let `F(T) ≅ T`. If
`F(κ[0])` has no cohomology below zero, then

`H⁰(F(κ[0])) ≅ κ`. -/
theorem nonempty_homology_iso_residueField_of_iso_of_isTorsionBySet
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    [F.CommShift ℤ] [F.IsTriangulated] (m : Ideal A) [m.IsMaximal]
    (T : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ) (ha : T.IsGE a) (hb : T.IsLE b)
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hGE : (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (A ⧸ m)))).IsGE 0)
    (hbot : ¬ IsZero ((homologyFunctor (ModuleCat.{u} A) a).obj T))
    (e : F.obj T ≅ T) :
    Nonempty ((homologyFunctor (ModuleCat.{u} A) 0).obj
      (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ m)))) ≅
        ModuleCat.of A (A ⧸ m)) := by
  obtain ⟨d⟩ := nonempty_homology_iso_homology_map_single F m T a b ha hb hkill hfin hGE
  have := hfin a
  exact nonempty_iso_residueField_of_iso m
    (singleFunctor (ModuleCat.{u} A) 0 ⋙ F ⋙ homologyFunctor (ModuleCat.{u} A) 0)
    ((homologyFunctor (ModuleCat.{u} A) a).obj T) (hkill a) hbot
    (d.symm ≪≫ (homologyFunctor (ModuleCat.{u} A) a).mapIso e)

end StacksDraft.ResidueLength

end
