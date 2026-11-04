module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.StratumPurityDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.OpenCoverDuality

/-!
# Gluing duality at coefficients supported on a stratum over a cover

Let `i : T → W` be a closed immersion and `j : W → X̄` an open immersion. Purity is available on
the opens `V` of `W` on which `T ∩ V` is cut out by a flag of smooth divisors, and such opens cover
`T`. This file glues duality on `X̄` at `j_! i_* G` from duality at the pieces
`(V → W → X̄)_! (i|_V)_* G|_{i⁻¹ V}` over the finite intersections of a finite cover, by the
Mayer–Vietoris sequence of the opens `i⁻¹ V` of `T` pushed forward along the exact functor
`j_! i_*` (`Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_sup'`), each piece being
identified by `j_! i_* a_! ≅ (V → W → X̄)_! (i|_V)_*` (base change of `i_*` to `V`, and composition
of extensions by zero).

## Main results

* `Stacks.EtaleCohomology.extensionByZeroDirectImageRestrictIso`.
* `Stacks.EtaleCohomology.isDualityPerfect_of_cover`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Cover

variable {T W X : Scheme.{u}} (i : T ⟶ W) [IsClosedImmersion i] (j : W ⟶ X) [IsOpenImmersion j]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)]

/-- `j_! i_* (a_! M) ≅ (V → W → X̄)_! (i|_V)_* M` for an open `V` of `W` and `a : i⁻¹ V → T`. -/
def extensionByZeroDirectImageRestrictIso (V : W.Opens)
    (M : EtaleModules.{u, 0} (ZMod ℓ) (i ⁻¹ᵁ V).toScheme) :
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (i ⁻¹ᵁ V).ι).obj M)) ≅
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (V.ι ≫ j)).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ∣_ V)).obj M) :=
  (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).mapIso
      ((etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) (i ∣_ V) (i ⁻¹ᵁ V).ι V.ι i
        (isPullback_morphismRestrict i V)).app M).symm ≪≫
    ((etaleModuleExtensionByZeroCompIso.{u, 0} (ZMod ℓ) V.ι j).app _).symm

/-- **Duality at coefficients supported on a closed `T ⊆ W` glues over a cover of `T` by opens of
`W`.** If `H^{N+1}` of `j_! i_* (a_! G|_A)` vanishes for every open `A` of `T`, and duality holds
at `(V → W → X̄)_! (i|_V)_* G|_{i⁻¹ V}` for every finite intersection `V` of members of a finite
family of opens of `W` covering `T`, then duality holds at `j_! i_* G`. -/
theorem isDualityPerfect_of_cover (D : EtaleModules.{u, 0} (ZMod ℓ) X) {N : ℕ}
    (t : Ext (unitSheaf (X := X) ℓ) D N →+ ZMod ℓ) (G : EtaleModules.{u, 0} (ZMod ℓ) T)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (V : ι → W.Opens)
    (hcov : ∀ x : T, ∃ a ∈ s, i x ∈ V a)
    (hvan : ∀ A : T.Opens, Subsingleton (Ext (unitSheaf (X := X) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) A.ι).obj G))) (N + 1)))
    (hloc : ∀ K ⊆ s, ∀ hK : K.Nonempty, Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) ((K.inf' hK V).ι ≫ j)).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ∣_ (K.inf' hK V))).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (i ⁻¹ᵁ (K.inf' hK V)).ι).obj G)))) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G)) := by
  have := (exactFunctor_iff _).1 (etaleModuleDirectImage_exact_of_isIntegralHom (ZMod ℓ) i)
  let Φ := etaleModuleDirectImage.{u, 0} (ZMod ℓ) i ⋙ etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j
  let A : ι → T.Opens := fun a => i ⁻¹ᵁ V a
  have hA : ∀ (K : Finset ι) (hK : K.Nonempty), K.inf' hK A = i ⁻¹ᵁ (K.inf' hK V) := by
    intro K hK
    induction hK using Finset.Nonempty.cons_induction with
    | singleton a => rw [Finset.inf'_singleton, Finset.inf'_singleton]
    | cons a K ha hK ih =>
      rw [Finset.inf'_cons hK, Finset.inf'_cons hK, ih]
      exact TopologicalSpace.Opens.ext rfl
  have htop : s.sup' hs A = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha, hx⟩ := hcov x
    exact Finset.le_sup' A ha hx
  have hglue := isDualityPerfect_extensionByZero_sup' N D t Φ G hs A hvan (fun K hKs hK => by
    rw [hA K hK]
    exact Ext.isDualityPerfect_of_iso
      (extensionByZeroDirectImageRestrictIso i j (K.inf' hK V) _).symm (hloc K hKs hK))
  rw [htop] at hglue
  have := isIso_etaleModuleExtensionByZeroAdj_counit_app_top (ZMod ℓ) G
  exact Ext.isDualityPerfect_of_iso
    (Φ.mapIso
      (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (⊤ : T.Opens).ι).counit.app G)))
    hglue

end Cover

end Stacks.EtaleCohomology
