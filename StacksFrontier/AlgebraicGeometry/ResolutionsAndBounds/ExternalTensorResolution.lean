module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.AffineGeneration
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorAffinePiece
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorBiproduct
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ProductAffineCover

/-!
# A coherent module on a product is a quotient of an external tensor product

Let `X` and `Y` be schemes of finite type over a Noetherian ring `R`, both with the resolution
property. Every coherent `𝒪_{X ×_R Y}`-module `F` is a quotient of `𝓔 ⊠ 𝓖` for a finite locally
free `𝒪_X`-module `𝓔` and a finite locally free `𝒪_Y`-module `𝓖`.

## Main results

* `AlgebraicGeometry.exists_isFiniteLocallyFree_epi_externalTensorProduct`: a coherent module on
  a Noetherian fibre product of two locally Noetherian schemes with the resolution property is a
  quotient of an external tensor product of finite locally free modules.
* `AlgebraicGeometry.exists_externalTensorProduct_epi`: the same for two schemes of finite type
  over a Noetherian ring.

## References

* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

noncomputable section

namespace AlgebraicGeometry

/-! ### Generalities on sections of modules on a scheme -/

variable {Z : Scheme.{u}}

/-- Restricting a section twice is restricting it once. -/
theorem map_homOfLE_map_homOfLE (M : Z.Modules) {W₁ W₂ W₃ : Z.Opens}
    (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂) (x : Γ(M, W₁)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← comp_apply, ← Functor.map_comp]
  rfl

/-- A morphism of modules commutes with restriction of sections. -/
theorem app_map_homOfLE {M N : Z.Modules} (φ : M ⟶ N) {W W' : Z.Opens} (h : W' ≤ W)
    (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op x

/-- **The section-level criterion for an epimorphism of modules on a scheme.** If every section
of `N` over an open is, near each of its points, in the image of `θ`, then `θ` is an
epimorphism. -/
theorem epi_of_exists_app_eq {M N : Z.Modules} (θ : M ⟶ N)
    (h : ∀ (W : Z.Opens) (t : Γ(N, W)) (p : Z), p ∈ W →
      ∃ (W' : Z.Opens) (hW : W' ≤ W), p ∈ W' ∧ ∃ x : Γ(M, W'),
        θ.app W' x = N.presheaf.map (homOfLE hW).op t) :
    Epi θ := by
  have hepi : @Epi (SheafOfModules Z.ringCatSheaf) _ _ _ θ :=
    Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun W t p hp ↦ by
      obtain ⟨W', hW, hpW', x, hx⟩ := h W t p hp
      exact ⟨W', hW, hpW', x, hx⟩
  exact ⟨fun g₁ g₂ hg ↦ hepi.left_cancellation g₁ g₂ hg⟩

/-- **Every section of the target of an epimorphism of modules on a scheme is locally in the
image.** -/
theorem exists_app_eq_of_epi {M N : Z.Modules} (θ : M ⟶ N) (hθ : Epi θ)
    (W : Z.Opens) (t : Γ(N, W)) (p : Z) (hp : p ∈ W) :
    ∃ (W' : Z.Opens) (hW : W' ≤ W), p ∈ W' ∧ ∃ x : Γ(M, W'),
      θ.app W' x = N.presheaf.map (homOfLE hW).op t := by
  have hepi : @Epi (SheafOfModules Z.ringCatSheaf) _ _ _ θ :=
    ⟨fun g₁ g₂ hg ↦ hθ.left_cancellation g₁ g₂ hg⟩
  obtain ⟨W', hW, hpW', x, hx⟩ :=
    Stacks.SheafOfModules.StalkEpiMono.exists_sections_of_epi θ W t p hp
  exact ⟨W', hW, hpW', x, hx⟩

/-- Finitely many opens containing a point, together with one more, have a common open refinement
containing it. -/
theorem exists_opens_mem_le_of_fin {T : Type u} [TopologicalSpace T] {p : T} :
    ∀ {k : ℕ} (W : Fin k → Opens T), (∀ j, p ∈ W j) → ∀ W₀ : Opens T, p ∈ W₀ →
      ∃ W' : Opens T, p ∈ W' ∧ W' ≤ W₀ ∧ ∀ j, W' ≤ W j := by
  intro k
  induction k with
  | zero => exact fun W _ W₀ hp₀ => ⟨W₀, hp₀, le_rfl, fun j => j.elim0⟩
  | succ k ih =>
    intro W hW W₀ hp₀
    obtain ⟨W', hpW', hle₀, hle⟩ := ih (fun j => W j.succ) (fun j => hW _) W₀ hp₀
    exact ⟨W' ⊓ W 0, ⟨hpW', hW 0⟩, inf_le_left.trans hle₀,
      Fin.cases inf_le_right fun j => inf_le_left.trans (hle j)⟩

/-! ### One cover member and one section over it -/

variable {X Y S : Scheme.{u}}

/-- For opens `U ⊆ X` and `V ⊆ Y` and a section `s` of `F` over `U ×_S V` there are finite
locally free modules `𝓔` on `X` and `𝓖` on `Y` and a morphism `φ : 𝓔 ⊠ 𝓖 ⟶ F` such that, for
every open `W' ⊆ U ×_S V`, every multiple `c · s|_{W'}` of `s` is, on a neighbourhood of any
given point of `W'`, the image under `φ` of a section of `𝓔 ⊠ 𝓖`. -/
theorem exists_hom_app_eq_smul_restrict (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [HasResolutionProperty X]
    [IsLocallyNoetherian Y] [HasResolutionProperty Y] [IsNoetherian (pullback f g)]
    (F : (pullback f g).Modules) [F.IsQuasicoherent] (U : X.Opens) (V : Y.Opens)
    (s : Γ(F, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) :
    ∃ (E : X.Modules) (G : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G)
      (φ : externalTensorProduct f g E G ⟶ F),
      ∀ (W' : (pullback f g).Opens)
        (hW' : W' ≤ pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
        (c : Γ(pullback f g, W')) (p : (pullback f g : Scheme.{u})), p ∈ W' →
        ∃ (W'' : (pullback f g).Opens) (h : W'' ≤ W'), p ∈ W'' ∧
          ∃ u : Γ(externalTensorProduct f g E G, W''),
            φ.app W'' u =
              F.presheaf.map (homOfLE h).op (c • F.presheaf.map (homOfLE hW').op s) := by
  obtain ⟨n, E, G, hE, hG, ε, hε, ψ, w, hw⟩ :=
    exists_epi_externalTensorProduct_hom_app_eq_of_opens f g U V F s
  refine ⟨E, G, hE, hG, ε ≫ ψ, fun W' hW' c p hp => ?_⟩
  obtain ⟨W'', h, hpW'', u, hu⟩ := exists_app_eq_of_epi ε hε W'
    (c • (idealPow (Scheme.IdealSheafData.externalProduct f g
      (Scheme.IdealSheafData.complementIdeal U)
      (Scheme.IdealSheafData.complementIdeal V)) n).presheaf.map (homOfLE hW').op w) p hp
  refine ⟨W'', h, hpW'', u, ?_⟩
  have h1 : (ε ≫ ψ).app W'' u = ψ.app W'' (ε.app W'' u) := rfl
  rw [h1, hu, app_map_homOfLE ψ h]
  refine congrArg (fun y => (F.presheaf.map (homOfLE h).op) y) ?_
  rw [Scheme.Modules.Hom.app_smul, app_map_homOfLE ψ hW', hw]

/-! ### The resolution -/

/-- A coherent module on a Noetherian fibre product of two locally Noetherian schemes with the
resolution property is a quotient of an external tensor product of finite locally free
modules. -/
theorem exists_isFiniteLocallyFree_epi_externalTensorProduct (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [HasResolutionProperty X]
    [IsLocallyNoetherian Y] [HasResolutionProperty Y] [IsNoetherian (pullback f g)]
    (F : (pullback f g).Modules) [F.IsCoherent] :
    ∃ (E : X.Modules) (G : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G)
      (q : externalTensorProduct f g E G ⟶ F), Epi q := by
  classical
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨m, U, V, haff, hcov⟩ := exists_finite_affine_product_cover f g
  have hgen : ∀ i : Fin m, ∃ (k : ℕ)
      (s : Fin k → Γ(F, pullback.fst f g ⁻¹ᵁ (U i).1 ⊓ pullback.snd f g ⁻¹ᵁ (V i).1)),
      ∀ (W₁ : (pullback f g).Opens)
        (h₁ : W₁ ≤ pullback.fst f g ⁻¹ᵁ (U i).1 ⊓ pullback.snd f g ⁻¹ᵁ (V i).1)
        (t : Γ(F, W₁)) (p : (pullback f g : Scheme.{u})), p ∈ W₁ →
        ∃ (W₂ : (pullback f g).Opens) (h₂ : W₂ ≤ W₁)
          (h₃ : W₂ ≤ pullback.fst f g ⁻¹ᵁ (U i).1 ⊓ pullback.snd f g ⁻¹ᵁ (V i).1), p ∈ W₂ ∧
          ∃ c : Fin k → Γ(pullback f g, W₂),
            F.presheaf.map (homOfLE h₂).op t =
              ∑ j, c j • F.presheaf.map (homOfLE h₃).op (s j) := by
    intro i
    obtain ⟨k, s, hs⟩ := exists_fin_sections_generating_of_isCoherent F ⟨_, haff i⟩
    exact ⟨k, s, fun W₁ h₁ t p hp => hs h₁ t p hp⟩
  choose k s hs using hgen
  choose Em Gm hEm hGm φ hφ using fun (i : Fin m) (j : Fin (k i)) =>
    exists_hom_app_eq_smul_restrict f g F (U i).1 (V i).1 (s i j)
  obtain ⟨E', G', hE', hG', θ, hfac⟩ := exists_factor_externalTensorProduct f g F
    (Λ := Σ i : Fin m, Fin (k i)) (fun l => Em l.1 l.2) (fun l => Gm l.1 l.2)
    (fun l => hEm l.1 l.2) (fun l => hGm l.1 l.2) (fun l => φ l.1 l.2)
  choose ι hι using hfac
  refine ⟨E', G', hE', hG', θ, epi_of_exists_app_eq θ fun W t p hp => ?_⟩
  have hpT : p ∈ ⨆ i, pullback.fst f g ⁻¹ᵁ (U i).1 ⊓ pullback.snd f g ⁻¹ᵁ (V i).1 := by
    rw [hcov]
    trivial
  obtain ⟨i, hpi⟩ := Opens.mem_iSup.mp hpT
  obtain ⟨W₂, h₂, h₃, hpW₂, c, hc⟩ :=
    hs i (W ⊓ (pullback.fst f g ⁻¹ᵁ (U i).1 ⊓ pullback.snd f g ⁻¹ᵁ (V i).1)) inf_le_right
      (F.presheaf.map (homOfLE (inf_le_left :
        W ⊓ (pullback.fst f g ⁻¹ᵁ (U i).1 ⊓ pullback.snd f g ⁻¹ᵁ (V i).1) ≤ W)).op t)
      p ⟨hp, hpi⟩
  choose Wl hWl hpWl u hu using fun j => hφ i j W₂ h₃ (c j) p hpW₂
  obtain ⟨Wc, hpWc, hWcW₂, hWcl⟩ := exists_opens_mem_le_of_fin Wl hpWl W₂ hpW₂
  let v : ∀ j, Γ(externalTensorProduct f g (Em i j) (Gm i j), Wc) := fun j =>
    (externalTensorProduct f g (Em i j) (Gm i j)).presheaf.map (homOfLE (hWcl j)).op (u j)
  refine ⟨Wc, hWcW₂.trans (h₂.trans inf_le_left), hpWc, ∑ j, (ι ⟨i, j⟩).app Wc (v j), ?_⟩
  refine Eq.trans (map_sum (θ.app Wc).hom _ Finset.univ) ?_
  have hterm : ∀ j : Fin (k i), θ.app Wc ((ι ⟨i, j⟩).app Wc (v j)) =
      F.presheaf.map (homOfLE hWcW₂).op (c j • F.presheaf.map (homOfLE h₃).op (s i j)) := by
    intro j
    have h4 : θ.app Wc ((ι ⟨i, j⟩).app Wc (v j)) = (φ i j).app Wc (v j) :=
      congrArg (fun χ => Scheme.Modules.Hom.app χ Wc (v j)) (hι ⟨i, j⟩)
    rw [h4, app_map_homOfLE (φ i j) (hWcl j), hu j, map_homOfLE_map_homOfLE]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← map_sum (F.presheaf.map (homOfLE hWcW₂).op).hom,
    ← hc, map_homOfLE_map_homOfLE, map_homOfLE_map_homOfLE]

/-! ### The statement over a Noetherian base ring -/

/-- Let `R` be a Noetherian ring and let `X`, `Y` be schemes of finite type over `R` having the
resolution property. Every coherent `𝒪_{X ×_R Y}`-module is a quotient of `𝓔 ⊠ 𝓖` with `𝓔` a
finite locally free `𝒪_X`-module and `𝓖` a finite locally free `𝒪_Y`-module. -/
@[stacks 0FZ0]
theorem exists_externalTensorProduct_epi (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasResolutionProperty X] [HasResolutionProperty Y]
    (F : (pullback f g).Modules) [F.IsCoherent] :
    ∃ (E : X.Modules) (G : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G)
      (q : externalTensorProduct f g E G ⟶ F), Epi q := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace (pullback f g : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f g)
  have : IsLocallyNoetherian (pullback f g : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g)
  have : IsNoetherian (pullback f g) := ⟨⟩
  exact exists_isFiniteLocallyFree_epi_externalTensorProduct f g F

end AlgebraicGeometry

end

end
