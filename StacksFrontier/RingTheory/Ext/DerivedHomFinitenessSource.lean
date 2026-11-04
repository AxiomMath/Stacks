module

public import StacksFrontier.RingTheory.Ext.DerivedHomFiniteness
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# Finiteness of `Hom` out of a bounded-above object of the derived category of modules

Over a Noetherian ring `R`, let `L` be an object of `D(R)` which is bounded above and whose
cohomology modules are finite in the degrees `≥ -j`, and let `N` be a finite `R`-module. Then
`Hom_{D(R)}(L, N[j])` is a finite `R`-module. This is the contravariant companion of
`StacksDraft.DerivedHomFiniteness.finite_ext_of_isGE`: only the canonical truncation `τ_{≥ -j} L`
contributes, it is bounded with finite cohomology, and the truncation triangles reduce to an
object concentrated in one degree, where the morphisms are the `Ext` modules between two finite
modules.

In particular `Ext^j_R(L, N)` is finite for `L` pseudo-coherent from `m` and `j ≤ -m`, the form in
which part (B) of Stacks 08JR delivers the deformation groups of a coherent module.

## Main results

* `StacksDraft.DerivedHomFiniteness.finite_hom_obj₂_of_distTriang_source`: finiteness of
  `Hom(-, Y)` on the middle term of a distinguished triangle.
* `StacksDraft.DerivedHomFiniteness.finite_hom_to_single_shift_of_isLE`: the finiteness above.
* `StacksDraft.DerivedHomFiniteness.finite_hom_to_single_shift_of_isPseudoCoherentFrom`: its
  pseudo-coherent form.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategory

namespace StacksDraft.DerivedHomFiniteness

universe u v w

section General

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- `Hom(-, Y)` on a distinguished triangle: finiteness of the outer terms gives finiteness of
the middle one. -/
theorem finite_hom_obj₂_of_distTriang_source (Y : DerivedCategory (ModuleCat.{v} R))
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distTriang _)
    (h₁ : Module.Finite R (T.obj₁ ⟶ Y)) (h₃ : Module.Finite R (T.obj₃ ⟶ Y)) :
    Module.Finite R (T.obj₂ ⟶ Y) :=
  module_finite_of_exact (Linear.leftComp R Y T.mor₂) (Linear.leftComp R Y T.mor₁)
    fun x hx => by
      obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ T hT x hx
      exact ⟨y, hy.symm⟩

variable [Small.{v} R]

/-- Finiteness of the morphisms from an object concentrated in a single degree with finite
cohomology to a finite module placed in degree `0` and shifted by `j`. -/
theorem finite_hom_to_single_shift_of_isGE_of_isLE (N : ModuleCat.{v} R) [Module.Finite R N]
    (X : DerivedCategory (ModuleCat.{v} R)) (m : ℤ) [X.IsGE m] [X.IsLE m]
    (hX : Module.Finite R ((homologyFunctor (ModuleCat.{v} R) m).obj X)) (j : ℤ) :
    Module.Finite R (X ⟶ ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j⟧) := by
  obtain ⟨H, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
  have : Module.Finite R H := Module.Finite.equiv
    ((homologyFunctor (ModuleCat.{v} R) m).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) m).app H).toLinearEquiv
  let Y := ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j⟧
  let A := (singleFunctor (ModuleCat.{v} R) 0).obj H
  -- `X ≅ A⟦-m⟧`
  let eA : X ≅ A⟦-m⟧ := e ≪≫
    (((singleFunctors (ModuleCat.{v} R)).shiftIso (-m) m 0 (by omega)).app H).symm
  -- shifting by `m` embeds `Hom(A⟦-m⟧, Y)` into `Hom(A, Y⟦m⟧)`
  let e' := Linear.homCongr R ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{v} R)) (-m) m
    (by omega)).app A) (Iso.refl (Y⟦m⟧))
  let ι : (A⟦-m⟧ ⟶ Y) →ₗ[R] (A ⟶ Y⟦m⟧) :=
    e'.toLinearMap ∘ₗ (shiftFunctor (DerivedCategory (ModuleCat.{v} R)) m).mapLinearMap R
  have hι : Function.Injective ι :=
    e'.injective.comp ((shiftFunctor (DerivedCategory (ModuleCat.{v} R)) m).map_injective)
  have : Module.Finite R (A ⟶ Y⟦m⟧) := by
    have := finite_ext_between_finite_modules H N (j + m)
    exact Module.Finite.equiv (Linear.homCongr R (Iso.refl A)
      (((shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} R)) j m (j + m) rfl).app
        ((singleFunctor (ModuleCat.{v} R) 0).obj N))))
  have : IsNoetherian R (A⟦-m⟧ ⟶ Y) := isNoetherian_of_injective ι hι
  exact Module.Finite.equiv (Linear.homCongr R eA (Iso.refl Y)).symm

/-- Finiteness of the morphisms from a bounded object with finite cohomology to a finite module
in degree `0` shifted by `j`, by induction on the width of the window. -/
theorem finite_hom_to_single_shift_of_bounded (N : ModuleCat.{v} R) [Module.Finite R N]
    (j a : ℤ) (n : ℕ) :
    ∀ (X : DerivedCategory (ModuleCat.{v} R)) (_ : X.IsGE a) (_ : X.IsLE (a + n))
      (_ : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj X)),
      Module.Finite R (X ⟶ ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j⟧) := by
  induction n with
  | zero =>
    intro X _ h hX
    have : X.IsLE a := by simpa using h
    exact finite_hom_to_single_shift_of_isGE_of_isLE N X a (hX a) j
  | succ n ih =>
    intro X hGE hLE hX
    let T := (TStructure.t.triangleLEGE (a + n) (a + n + 1) rfl).obj X
    have hT : T ∈ distTriang _ :=
      TStructure.t.triangleLEGE_distinguished (a + n) (a + n + 1) rfl X
    have h₁ : Module.Finite R (T.obj₁ ⟶ ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j⟧) :=
      ih ((TStructure.t.truncLE (a + n)).obj X)
        (show TStructure.t.IsGE ((TStructure.t.truncLE (a + n)).obj X) a from inferInstance)
        (show TStructure.t.IsLE ((TStructure.t.truncLE (a + n)).obj X) (a + n) from inferInstance)
        (finite_homology_truncLE X hX _)
    have : X.IsLE (a + n + 1) := by simpa [add_assoc] using hLE
    have h₃ : Module.Finite R (T.obj₃ ⟶ ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j⟧) := by
      have : T.obj₃.IsGE (a + n + 1) :=
        show TStructure.t.IsGE ((TStructure.t.truncGE (a + n + 1)).obj X) (a + n + 1) from
          inferInstance
      have : T.obj₃.IsLE (a + n + 1) :=
        show TStructure.t.IsLE ((TStructure.t.truncGE (a + n + 1)).obj X) (a + n + 1) from
          inferInstance
      exact finite_hom_to_single_shift_of_isGE_of_isLE N T.obj₃ (a + n + 1)
        (finite_homology_truncGE X hX _ _) j
    exact finite_hom_obj₂_of_distTriang_source _ T hT h₁ h₃

/-- **`Hom(L, N[j])` is finite** for `L` bounded above with finite cohomology in degrees `≥ -j`
and `N` a finite module. -/
theorem finite_hom_to_single_shift_of_isLE (N : ModuleCat.{v} R) [Module.Finite R N] (j : ℤ)
    (L : DerivedCategory (ModuleCat.{v} R)) (b : ℤ) [L.IsLE b]
    (hL : ∀ k, -j ≤ k → Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L)) :
    Module.Finite R (L ⟶ ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j⟧) := by
  let Y := ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j⟧
  have hY : Y.IsGE (-j) := TStructure.t.isGE_shift _ 0 j (-j) (by omega)
  let L' := (TStructure.t.truncGE (-j)).obj L
  -- precomposition with `L ⟶ τ_{≥ -j} L` identifies `Hom(τ_{≥ -j} L, Y)` with `Hom(L, Y)`
  have hbij : Function.Bijective (Linear.leftComp R Y ((TStructure.t.truncGEπ (-j)).app L)) :=
    ⟨fun f g hfg ↦ TStructure.t.from_truncGE_obj_ext hfg, fun f ↦
      ⟨TStructure.t.descTruncGE f (-j), TStructure.t.π_descTruncGE f (-j)⟩⟩
  have hL'fin : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj L') := by
    intro k
    by_cases hk : -j ≤ k
    · let T := (TStructure.t.triangleLEGE (-j - 1) (-j) (by omega)).obj L
      have hT : T ∈ distTriang _ :=
        TStructure.t.triangleLEGE_distinguished (-j - 1) (-j) (by omega) L
      have hTle : TStructure.t.IsLE ((TStructure.t.truncLE (-j - 1)).obj L) (-j - 1) :=
        inferInstance
      have hepi : Epi ((homologyFunctor (ModuleCat.{v} R) k).map T.mor₂) := by
        rw [HomologySequence.epi_homologyMap_mor₂_iff T hT k (k + 1) (by omega)]
        exact (isZero_of_isLE (hX := hTle) _ (-j - 1) (k + 1) (by omega)).eq_of_tgt _ _
      have : Module.Finite R ((homologyFunctor (ModuleCat.{v} R) k).obj T.obj₂) := hL k hk
      exact Module.Finite.of_surjective
        ((homologyFunctor (ModuleCat.{v} R) k).map T.mor₂).hom
        ((ModuleCat.epi_iff_surjective _).1 hepi)
    · have : Subsingleton ((homologyFunctor (ModuleCat.{v} R) k).obj L') :=
        ModuleCat.isZero_iff_subsingleton.mp (isZero_of_isGE L' (-j) k (by omega))
      infer_instance
  obtain ⟨n, hn⟩ : ∃ n : ℕ, max b (-j) = -j + n := ⟨(max b (-j) + j).toNat, by omega⟩
  have hL'ge : L'.IsGE (-j) :=
    show TStructure.t.IsGE ((TStructure.t.truncGE (-j)).obj L) (-j) from inferInstance
  have hL'le : L'.IsLE (-j + n) := by
    rw [← hn]
    have : L.IsLE (max b (-j)) := TStructure.t.isLE_of_le L b _ (le_max_left _ _)
    exact show TStructure.t.IsLE ((TStructure.t.truncGE (-j)).obj L) (max b (-j)) from
      inferInstance
  have h := finite_hom_to_single_shift_of_bounded N j (-j) n L' hL'ge hL'le hL'fin
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ hbij)

end General

section Standard

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]

/-- **`Ext^j_R(L, N)` is finite for `L` pseudo-coherent from `m` and `j ≤ -m`**, `N` a finite
module over the Noetherian ring `R`. -/
theorem finite_hom_to_single_shift_of_isPseudoCoherentFrom (N : ModuleCat.{v} R)
    [Module.Finite R N] (L : DerivedCategory (ModuleCat.{v} R)) (m j : ℤ)
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom L m) (hj : j ≤ -m) :
    Module.Finite R (L ⟶ ((singleFunctor (ModuleCat.{v} R) 0).obj N)⟦j⟧) := by
  obtain ⟨⟨b, hb⟩, hfin⟩ :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology L m
      PUnit.{v + 1}).1.1 hL)
  have : L.IsLE b := (DerivedCategory.isLE_iff L b).2 fun i hi ↦ hb i hi
  exact finite_hom_to_single_shift_of_isLE N j L b fun k hk ↦ hfin k (by omega)

end Standard

end StacksDraft.DerivedHomFiniteness

end
