module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRetract
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TotalComplexLocalSections

/-!
# Local retracts for left duals of K-flat complexes

Let `N` be a left dual of `M` in the derived category of `O_X`-modules, with `M` and `N`
represented by K-flat complexes `M^•` and `N^•`. Near each point `x ∈ X`, finitely many local
sections of the terms of `M^•` control retractions: on a small enough open, any morphism of
complexes `K ⟶ M^•` that stays injective after `- ⊗ N^•` in degree `1` and through which these
sections lift exhibits the restriction of `M` as a retract of that of `K`.

## Main results

* `Stacks.Cohomology.LeftDualPerfect.exists_local_retract`: the local retract described above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TopologicalSpace Opposite Stacks.SheafOfModules.DerivedMonoidal
open Stacks.Cohomology.MonoidalDerived
open Stacks.Cohomology.MonoidalComplexes

universe u d d'

namespace Stacks.Cohomology.LeftDualPerfect

variable (X : RingedSpace.{u, u})

/-- The morphism `cocycleHom A s h` out of the unit complex depends only on the global section
`s`: equal degree-`0` cocycles give equal morphisms. -/
theorem cocycleHom_congr {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    (A : CochainComplex (Mod R) ℤ) {s₁ s₂ : (A.X 0).val.obj (op ⊤)}
    (h₁ : (A.d 0 1).val.app (op ⊤) s₁ = 0) (h₂ : (A.d 0 1).val.app (op ⊤) s₂ = 0) (h : s₁ = s₂) :
    cocycleHom A s₁ h₁ = cocycleHom A s₂ h₂ := by
  subst h
  rfl

/-- If `W ≤ V`, then the image `topOpen X W` of the whole of `X|_W` is contained in `V`. -/
theorem le_topOpen_of_le {W V : Opens X} (h : W ≤ V) : topOpen X W ≤ V := by
  rw [topOpen_eq]
  exact h

/-- **The local retract of Stacks 0FPD.** Let `N` be a left dual of `M` in `D(O_X)`, represented
by K-flat complexes `M^•` and `N^•`, and let `x ∈ X`. There are an open `U ∋ x` and finitely many
sections `a` of the terms of `M^•` over `U` such that, for every open `W ≤ U` and every morphism
of complexes `j : K ⟶ M^•` which stays injective after `- ⊗ N^•` in degree `1` and through which
the restrictions of the `a` to `W` lift, `M|_W` is a retract of `K|_W` in `D(O_{X|_W})`. -/
theorem exists_local_retract [HasDerivedCategory.{d} (Mod X.sheaf)]
    [∀ W : Opens X, HasDerivedCategory.{d'} (Mod (X.restrict W.isOpenEmbedding).sheaf)]
    (M N : DerivedModules X.sheaf)
    (pair : letI := derivedCategoryMonoidalCategory X; ExactPairing M N)
    (Mc Nc : Complexes X.sheaf) (eM : DerivedCategory.Q.obj Mc ≅ M)
    (eN : DerivedCategory.Q.obj Nc ≅ N) (hM : KFlat X.sheaf Mc) (hN : KFlat X.sheaf Nc)
    (x : X) :
    letI := cochainComplexMonoidalCategory X
    ∃ U : Opens X, x ∈ U ∧ ∃ (S : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = 0}) (n : S → ℕ)
      (a : ∀ (ij : S) (_ : Fin (n ij)), (Mc.X ij.1.1.1).val.obj (op U)),
      ∀ (W : Opens X) (hW : W ≤ U) (K : Complexes X.sheaf) (j : K ⟶ Mc)
        [Mono ((j ▷ Nc).f 1)],
        (∀ ij k, ∃ y : (K.X ij.1.1.1).val.obj (op (topOpen X W)),
          (j.f _).val.app _ y = res _ (le_topOpen_of_le X hW) (a ij k)) →
        Nonempty (Retract ((restrictMod X W).mapDerivedCategory.obj M)
          ((restrictMod X W).mapDerivedCategory.obj (DerivedCategory.Q.obj K))) := by
  let := cochainComplexMonoidalCategory X
  let := derivedCategoryMonoidalCategory X
  let := pair
  obtain ⟨G, γ, f, hf, hfac, U₁, hxU₁, t₁, ht₁, u, hid⟩ := exists_local_cocycle_data X (Mc ⊗ Nc)
    (coevaluationUnitHom X Mc Nc hM hN (η_ M N ≫ (eM.inv ⊗ₘ eN.inv))) x
  have hx' : x ∈ topOpen X U₁ := by rw [topOpen_eq]; exact hxU₁
  obtain ⟨V, hV, hxV, S, n, a, b, hab⟩ := exists_nhd_sum_ιMapBifunctor_pureTensor Mc Nc t₁ x hx'
  refine ⟨V, hxV, S, n, a, fun W hW K j _ hlift => ?_⟩
  choose y hy using hlift
  have hWV : topOpen X W ≤ V := le_topOpen_of_le X hW
  have hWU₁ : W ≤ U₁ := by
    have := hW.trans hV
    rwa [topOpen_eq] at this
  have heq := (mapBifunctorMap_lift_eq j hWV a b y hy).trans
    ((congrArg (res _ hWV) hab).symm.trans (res_res _ hWV hV t₁))
  have hd := d_eq_zero_of_mono (j ▷ Nc) _
    ((congrArg (((Mc ⊗ Nc).d 0 1).val.app (op (topOpen X W))) heq).trans
      (restrict_cocycle (topOpen_mono X hWU₁) t₁ ht₁))
  obtain ⟨Θ, hΘ⟩ := exists_iso_whiskerRight_comp X.sheaf j hM hN
  exact nonempty_retract_restrict X W M N pair Mc Nc eM eN hM hN K (K ⊗ Nc) j (j ▷ Nc) Θ hΘ _ hd
    ((restrict_map_eq_cocycleHom X _ γ f hf hfac hWU₁ t₁ ht₁ u hid).trans
      (congrArg (fun c => _ ≫ DerivedCategory.Q.map ((restrictUnitComplexIso X W).hom ≫ c))
        (cocycleHom_congr _ _ _ heq.symm)))

end Stacks.Cohomology.LeftDualPerfect
