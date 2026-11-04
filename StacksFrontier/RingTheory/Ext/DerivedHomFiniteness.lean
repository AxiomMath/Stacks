module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of `Hom` in the derived category of modules

Over a Noetherian ring, finiteness of the `Hom`-modules of a derived category propagates along
exact sequences and along distinguished triangles: a module squeezed between two finite modules by
an exact sequence is finite, and the middle `Hom` of a distinguished triangle is finite when the
outer two are. From these, the canonical truncation triangles give finiteness of the `Hom`-modules
out of a finite module in degree `0` into any bounded-below object with finite cohomology.

## Main results

* `StacksDraft.DerivedHomFiniteness.module_finite_of_exact`: a module admitting an exact pair into
  and out of finite modules is finite.
* `StacksDraft.DerivedHomFiniteness.finite_hom_obj₂_of_distTriang`: finiteness of `Hom(X, -)` on
  the middle term of a distinguished triangle.
* `StacksDraft.DerivedHomFiniteness.finite_homology_truncLE` and
  `StacksDraft.DerivedHomFiniteness.finite_homology_truncGE`: the canonical truncations of an
  object with finite cohomology have finite cohomology.
* `StacksDraft.DerivedHomFiniteness.finite_ext_between_finite_modules`: the integer-graded `Ext`
  modules between two finite modules are finite.
* `StacksDraft.DerivedHomFiniteness.finite_hom_single_shift`,
  `StacksDraft.DerivedHomFiniteness.finite_hom_shift_of_isGE_of_isLE` and
  `StacksDraft.DerivedHomFiniteness.finite_hom_shift_of_bounded`: finiteness of the morphisms from
  a finite module in degree `0` to a shift of an object concentrated in one degree, or in a
  bounded window of degrees, with finite cohomology.
* `StacksDraft.DerivedHomFiniteness.finite_ext_of_isGE`: finiteness of `Ext^i` out of a finite
  module into a bounded-below object with finite cohomology.

## Implementation notes

The ring universe and the module universe are independent here, and the derived-category universe
is an instance hypothesis. Consumers instantiate the module universe at whatever they work in —
`ModuleCat.{u} R` and `ModuleCat.{max v u} R` are both instances — which is what lets one copy of
these lemmas serve files that disagree about it.

Because the module universe is independent of the ring universe, the `Ext`-modules of
`ModuleCat.{v} R` are only known to be finite when `R` is `Small.{v}`, so that hypothesis is
carried explicitly from `finite_ext_between_finite_modules` onwards. At `v = u` it is discharged by
`small_self`.

The `Ext`-modules appear here as `ShiftedHom`, that is as morphisms into a shift, which is the form
taken by the codomain of `CategoryTheory.Abelian.Ext.homLinearEquiv`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategory

namespace StacksDraft.DerivedHomFiniteness

universe u v w

/-- A module carrying an exact pair `M → N → P` with `M` and `P` finite, in the weak sense that
every element of `N` killed by `g` comes from `f`, is itself finite. -/
theorem module_finite_of_exact {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.Finite R M] [Module.Finite R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : ∀ x, g x = 0 → ∃ y, f y = x) : Module.Finite R N := by
  have hker : LinearMap.ker g ≤ LinearMap.range f := fun x hx => hex x hx
  have : IsNoetherian R (LinearMap.ker g) := isNoetherian_of_le hker
  have : Module.Finite R (N ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- `Hom(X, -)` on a distinguished triangle: finiteness of the outer terms gives finiteness of the
middle one. -/
theorem finite_hom_obj₂_of_distTriang (X : DerivedCategory (ModuleCat.{v} R))
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distTriang _)
    (h₁ : Module.Finite R (X ⟶ T.obj₁)) (h₃ : Module.Finite R (X ⟶ T.obj₃)) :
    Module.Finite R (X ⟶ T.obj₂) :=
  module_finite_of_exact (Linear.rightComp R X T.mor₁) (Linear.rightComp R X T.mor₂)
    fun x hx => (Triangle.coyoneda_exact₂ T hT x hx).imp fun _ => Eq.symm

/-- The canonical truncation `τ_{≤ m}` of an object with finite cohomology has finite
cohomology. -/
theorem finite_homology_truncLE (L : DerivedCategory (ModuleCat.{v} R))
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L)) (m k : ℤ) :
    Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj
      ((TStructure.t.truncLE m).obj L)) := by
  by_cases hk : k ≤ m
  · let T := (TStructure.t.triangleLEGE m (m + 1) rfl).obj L
    have hT : T ∈ distTriang _ := TStructure.t.triangleLEGE_distinguished m (m + 1) rfl L
    have hTge : TStructure.t.IsGE ((TStructure.t.truncGE (m + 1)).obj L) (m + 1) := inferInstance
    have hmono : Mono ((homologyFunctor (ModuleCat.{v} R) k).map T.mor₁) := by
      rw [HomologySequence.mono_homologyMap_mor₁_iff T hT (k - 1) k (by omega)]
      exact (isZero_of_isGE (hX := hTge) _ (m + 1) (k - 1) (by omega)).eq_of_src _ _
    have : IsNoetherian R ((homologyFunctor (ModuleCat.{v} R) k).obj T.obj₂) :=
      @isNoetherian_of_isNoetherianRing_of_finite R _ _ _ _ _ (hL k)
    exact Module.Finite.of_injective
      ((homologyFunctor (ModuleCat.{v} R) k).map T.mor₁).hom
      ((ModuleCat.mono_iff_injective _).1 hmono)
  · have : Subsingleton ((homologyFunctor (ModuleCat.{v} R) k).obj
        ((TStructure.t.truncLE m).obj L)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_of_isLE _ m k (by omega))
    infer_instance

omit [IsNoetherianRing R] in
/-- The canonical truncation `τ_{≥ m}` of an object with finite cohomology has finite
cohomology. -/
theorem finite_homology_truncGE (L : DerivedCategory (ModuleCat.{v} R))
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L)) (m k : ℤ) :
    Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj
      ((TStructure.t.truncGE m).obj L)) := by
  by_cases hk : m ≤ k
  · let T := (TStructure.t.triangleLEGE (m - 1) m (by omega)).obj L
    have hT : T ∈ distTriang _ :=
      TStructure.t.triangleLEGE_distinguished (m - 1) m (by omega) L
    have hTle : TStructure.t.IsLE ((TStructure.t.truncLE (m - 1)).obj L) (m - 1) := inferInstance
    have hepi : Epi ((homologyFunctor (ModuleCat.{v} R) k).map T.mor₂) := by
      rw [HomologySequence.epi_homologyMap_mor₂_iff T hT k (k + 1) (by omega)]
      exact (isZero_of_isLE (hX := hTle) _ (m - 1) (k + 1) (by omega)).eq_of_tgt _ _
    have : Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj T.obj₂) := hL k
    exact Module.Finite.of_surjective
      ((homologyFunctor (ModuleCat.{v} R) k).map T.mor₂).hom
      ((ModuleCat.epi_iff_surjective _).1 hepi)
  · have : Subsingleton ((homologyFunctor (ModuleCat.{v} R) k).obj
        ((TStructure.t.truncGE m).obj L)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_of_isGE _ m k (by omega))
    infer_instance

variable [Small.{v} R]

/-- The integer-graded `Ext` modules between two finite modules over a Noetherian ring are finite:
the nonnegative degrees are Mathlib's `ModuleCat.finite_ext`, and the negative ones vanish. -/
theorem finite_ext_between_finite_modules (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℤ) :
    Module.Finite R (ShiftedHom ((singleFunctor (ModuleCat.{v} R) 0).obj M)
      ((singleFunctor (ModuleCat.{v} R) 0).obj N) i) := by
  rcases lt_or_ge i 0 with hi | hi
  · have hN : (((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦i⟧).IsGE (-i) :=
      TStructure.t.isGE_shift _ 0 i (-i) (by omega)
    have : Subsingleton (ShiftedHom ((singleFunctor (ModuleCat.{v} R) 0).obj M)
        ((singleFunctor (ModuleCat.{v} R) 0).obj N) i) :=
      subsingleton_of_forall_eq 0 fun f => TStructure.t.zero f 0 (-i) (by omega)
    infer_instance
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    exact Module.Finite.equiv
      (Abelian.Ext.homLinearEquiv.{w, v} (R := R) (X := M) (Y := N) (n := n))

/-- Finiteness of the morphisms from a finite module in degree `0` to a finite module placed in
degree `n` and shifted by `j`. -/
theorem finite_hom_single_shift (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Finite R N] (n j : ℤ) :
    Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶
      ((singleFunctor (ModuleCat.{v} R) n).obj N)⟦j⟧) := by
  have e : ((singleFunctor (ModuleCat.{v} R) n).obj N)⟦j⟧ ≅
      ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j - n⟧ :=
    ((singleFunctors (ModuleCat.{v} R)).shiftIso j (n - j) n (by omega)).app N ≪≫
      (((singleFunctors (ModuleCat.{v} R)).shiftIso (j - n) (n - j) 0 (by omega)).app N).symm
  have := finite_ext_between_finite_modules M N (j - n)
  exact Module.Finite.equiv (Linear.homCongr R (Iso.refl _) e).symm

/-- Finiteness of the morphisms from a finite module to a shift of an object concentrated in a
single degree with finite cohomology. -/
theorem finite_hom_shift_of_isGE_of_isLE (M : ModuleCat.{v} R) [Module.Finite R M]
    (X : DerivedCategory (ModuleCat.{v} R)) (m : ℤ) [X.IsGE m] [X.IsLE m]
    (hX : Module.Finite R ((homologyFunctor (ModuleCat.{v} R) m).obj X)) (j : ℤ) :
    Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ X⟦j⟧) := by
  obtain ⟨N, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
  have : Module.Finite R N := Module.Finite.equiv
    ((homologyFunctor (ModuleCat.{v} R) m).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) m).app N).toLinearEquiv
  have := finite_hom_single_shift M N m j
  exact Module.Finite.equiv
    (Linear.homCongr R (Iso.refl _) ((shiftFunctor _ j).mapIso e)).symm

/-- Finiteness of the morphisms from a finite module to a shift of a bounded object with finite
cohomology, by induction on the width of the window. -/
theorem finite_hom_shift_of_bounded (M : ModuleCat.{v} R) [Module.Finite R M]
    (a : ℤ) (n : ℕ) :
    ∀ (X : DerivedCategory (ModuleCat.{v} R)) (_ : X.IsGE a) (_ : X.IsLE (a + n))
      (_ : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj X)) (j : ℤ),
      Module.Finite R ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ X⟦j⟧) := by
  induction n with
  | zero =>
    intro X _ h hX j
    have : X.IsLE a := by simpa using h
    exact finite_hom_shift_of_isGE_of_isLE M X a (hX a) j
  | succ n ih =>
    intro X hGE hLE hX j
    let T := (TStructure.t.triangleLEGE (a + n) (a + n + 1) rfl).obj X
    have h₁ : Module.Finite R
        ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ T.obj₁⟦j⟧) :=
      ih ((TStructure.t.truncLE (a + n)).obj X)
        (show TStructure.t.IsGE ((TStructure.t.truncLE (a + n)).obj X) a from inferInstance)
        (show TStructure.t.IsLE ((TStructure.t.truncLE (a + n)).obj X) (a + n) from inferInstance)
        (finite_homology_truncLE X hX _) j
    have hLE' : X.IsLE (a + n + 1) := by simpa [add_assoc] using hLE
    have h₃ : Module.Finite R
        ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ T.obj₃⟦j⟧) := by
      have : T.obj₃.IsGE (a + n + 1) :=
        show TStructure.t.IsGE ((TStructure.t.truncGE (a + n + 1)).obj X) (a + n + 1) from
          inferInstance
      have : T.obj₃.IsLE (a + n + 1) :=
        show TStructure.t.IsLE ((TStructure.t.truncGE (a + n + 1)).obj X) (a + n + 1) from
          inferInstance
      exact finite_hom_shift_of_isGE_of_isLE M T.obj₃ (a + n + 1)
        (finite_homology_truncGE X hX _ _) j
    exact finite_hom_obj₂_of_distTriang _ _ (Triangle.shift_distinguished T
      (TStructure.t.triangleLEGE_distinguished (a + n) (a + n + 1) rfl X) j) h₁ h₃

/-- Finiteness of `Ext^i` out of a finite module into a bounded-below object with finite
cohomology: the part of the target above degree `i` contributes nothing. -/
theorem finite_ext_of_isGE (M : ModuleCat.{v} R) [Module.Finite R M]
    (L : DerivedCategory (ModuleCat.{v} R)) (a : ℤ) [L.IsGE a]
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L)) (i : ℤ) :
    Module.Finite R (ShiftedHom ((singleFunctor (ModuleCat.{v} R) 0).obj M) L i) := by
  let m := max a i
  let T := (TStructure.t.triangleLEGE m (m + 1) rfl).obj L
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m = a + n := ⟨(m - a).toNat, by omega⟩
  have h₁ : Module.Finite R
      ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ T.obj₁⟦i⟧) := by
    have hle : T.obj₁.IsLE m :=
      show TStructure.t.IsLE ((TStructure.t.truncLE m).obj L) m from inferInstance
    rw [hn] at hle
    exact finite_hom_shift_of_bounded M a n _
      (show TStructure.t.IsGE ((TStructure.t.truncLE m).obj L) a from inferInstance) hle
      (finite_homology_truncLE L hL _) i
  have h₃ : Module.Finite R
      ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ T.obj₃⟦i⟧) := by
    have : T.obj₃.IsGE (m + 1) :=
      show TStructure.t.IsGE ((TStructure.t.truncGE (m + 1)).obj L) (m + 1) from inferInstance
    have : (T.obj₃⟦i⟧).IsGE (m + 1 - i) :=
      TStructure.t.isGE_shift T.obj₃ (m + 1) i (m + 1 - i) (by omega)
    have : Subsingleton ((singleFunctor (ModuleCat.{v} R) 0).obj M ⟶ T.obj₃⟦i⟧) :=
      subsingleton_of_forall_eq 0 fun x => TStructure.t.zero x 0 (m + 1 - i) (by omega)
    infer_instance
  exact finite_hom_obj₂_of_distTriang _ _ (Triangle.shift_distinguished T
    (TStructure.t.triangleLEGE_distinguished m (m + 1) rfl L) i) h₁ h₃

end StacksDraft.DerivedHomFiniteness

end
