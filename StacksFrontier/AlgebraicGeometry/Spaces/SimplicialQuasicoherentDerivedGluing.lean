module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModulePasteUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleDegreeTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictTransitionCoherence

/-!
# Gluing quasi-coherent derived descent data along an fppf hypercovering (Stacks 0DLA)

Let `a : U → X` be an fppf hypercovering of an algebraic space `X`, `K₀ ∈ D_{QCoh}(𝒪_{U_0})` and
`α : L(f_{δ¹₁})^* K₀ ≅ L(f_{δ¹₀})^* K₀` satisfying the cocycle condition. If the objects
`K_n = L(f_{τⁿₙ})^* K₀` have no negative self-extensions, there is `K ∈ D_{QCoh}(𝒪_X)` with
`La_0^* K ≅ K₀`.

The proof follows the source: `(K₀, α)` gives a cartesian simplicial system of Stacks 0GMF, read
on the strict components of `U`; it is the system of an object `K'` (Stacks 0D9T, used in its
flatness-free form `exists_isCartesianDerivedModule_realizing_moduleSystem`); `K'` has
quasi-coherent cohomology, the face maps being flat (Stacks 0DER); and `K' = La^* K` by
Stacks 0DHF.

The source's hypothesis (1) of Stacks 0D9T, flatness of `f_φ^{-1}𝒪_{U_m} → 𝒪_{U_n}` for every
`φ`, fails for the degeneracies of an fppf hypercovering (the Čech nerve of
`Spec k[ε] → Spec k` has `s_0 : k[x, y]/(x², y²) → k[ε]` surjective and not flat), which is why
the flatness-free form is used.

## Main results

In the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `isFlat_map_delta_of_isHypercoveringAugmentation`: the face maps of an fppf hypercovering are
  flat (Stacks 0DER).
* `exists_derivedPullback_degreeZero_iso_compatible_of_transitions`: the gluing, relative to
  isomorphisms through which the strict transitions read.
* `exists_derivedPullback_degreeZero_iso_compatible_of_homotopy`: the gluing, given the transition
  identities on complexes.
* `exists_derivedPullback_degreeZero_iso_compatible`: Stacks 0DLA, with the compatibility with
  `α`.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open scoped Simplicial

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory

/-- **Transporting a descent isomorphism along componentwise comparisons.** Let `c_i : g₀F_i ⟶ g₁`
be the transitions of an object `K'` (in the two face directions), `eT` an isomorphism of a system
`(Q, p)` with them, `j : Q₀ ≅ P` turning `p₀⁻¹ p₁` into `F₁j ≫ ι ≫ F₀j⁻¹`, `T_i : F_iL₁ ≅ L₀G_i`
comparisons with `L₁ι = T₁ ≫ G₁e ≫ α ≫ G₀e⁻¹ ≫ T₀⁻¹`, and `Ψ_i : L_i g_i M ≅ A_i` comparisons
with `M ≅ K'` making the transitions of `M` the composites `T_i ≫ G_iΨ₀ ≫ θ_i`. Then
`A₀ ≅ K₀` is compatible with `α` and `θ₁ ≫ θ₀⁻¹`. -/
theorem exists_iso_comp_eq_of_transition_comparisons
    {D D₀ D₁ E₀ E₁ : Type*} [Category* D] [Category* D₀] [Category* D₁] [Category* E₀]
    [Category* E₁] (g₀ : D ⥤ D₀) (g₁ : D ⥤ D₁) (F₀ F₁ : D₀ ⥤ D₁) (L₀ : D₀ ⥤ E₀) (L₁ : D₁ ⥤ E₁)
    (G₀ G₁ : E₀ ⥤ E₁) (c₀ : g₀ ⋙ F₀ ⟶ g₁) (c₁ : g₀ ⋙ F₁ ⟶ g₁)
    (T₀ : F₀ ⋙ L₁ ≅ L₀ ⋙ G₀) (T₁ : F₁ ⋙ L₁ ≅ L₀ ⋙ G₁)
    {M K' : D} (β : M ≅ K') {Q₀ P : D₀} {Q₁ : D₁} (eT₀ : Q₀ ≅ g₀.obj K')
    (eT₁ : Q₁ ⟶ g₁.obj K') (p₀ : F₀.obj Q₀ ≅ Q₁) (p₁ : F₁.obj Q₀ ⟶ Q₁)
    (hp₀ : p₀.hom ≫ eT₁ = F₀.map eT₀.hom ≫ c₀.app K')
    (hp₁ : p₁ ≫ eT₁ = F₁.map eT₀.hom ≫ c₁.app K')
    (j : Q₀ ≅ P) (ι : F₁.obj P ≅ F₀.obj P)
    (hj : p₁ ≫ p₀.inv = F₁.map j.hom ≫ ι.hom ≫ F₀.map j.inv)
    {K₀ : E₀} (e : L₀.obj P ≅ K₀) (α : G₁.obj K₀ ≅ G₀.obj K₀)
    (hα : L₁.map ι.hom = T₁.hom.app P ≫ G₁.map e.hom ≫ α.hom ≫ G₀.map e.inv ≫ T₀.inv.app P)
    {A₀ : E₀} {A₁ : E₁} (Ψ₀ : L₀.obj (g₀.obj M) ≅ A₀) (Ψ₁ : L₁.obj (g₁.obj M) ≅ A₁)
    (θ₀ : G₀.obj A₀ ≅ A₁) (θ₁ : G₁.obj A₀ ≅ A₁)
    (hC₀ : L₁.map (c₀.app M) ≫ Ψ₁.hom = T₀.hom.app (g₀.obj M) ≫ G₀.map Ψ₀.hom ≫ θ₀.hom)
    (hC₁ : L₁.map (c₁.app M) ≫ Ψ₁.hom = T₁.hom.app (g₀.obj M) ≫ G₁.map Ψ₀.hom ≫ θ₁.hom) :
    ∃ eK : A₀ ≅ K₀, G₁.map eK.hom ≫ α.hom = (θ₁.hom ≫ θ₀.inv) ≫ G₀.map eK.hom := by
  let γ : g₀.obj M ≅ P := g₀.mapIso β ≪≫ eT₀.symm ≪≫ j
  have n₀ := c₀.naturality β.inv
  have n₁ := c₁.naturality β.hom
  simp only [Functor.comp_map] at n₀ n₁
  have hι : ι.hom = F₁.map j.inv ≫ p₁ ≫ p₀.inv ≫ F₀.map j.hom := by
    rw [reassoc_of% hj]
    simp
  have hp₀' : p₀.inv ≫ F₀.map eT₀.hom ≫ c₀.app K' = eT₁ := by
    rw [← hp₀, Iso.inv_hom_id_assoc]
  have hI : F₁.map γ.hom ≫ ι.hom ≫ F₀.map γ.inv ≫ c₀.app M = c₁.app M := by
    simp only [γ, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Functor.map_comp, Category.assoc, hι, n₀]
    simp only [Iso.hom_inv_id_map_assoc, reassoc_of% hp₀', reassoc_of% hp₁,
      Iso.inv_hom_id_map_assoc, reassoc_of% n₁, Iso.hom_inv_id_map, Category.comp_id]
  have hθ₀ : θ₀.hom = G₀.map Ψ₀.inv ≫ T₀.inv.app _ ≫ L₁.map (c₀.app M) ≫ Ψ₁.hom := by
    rw [hC₀]
    simp
  have hθ₁ : θ₁.hom = G₁.map Ψ₀.inv ≫ T₁.inv.app _ ≫ L₁.map (c₁.app M) ≫ Ψ₁.hom := by
    rw [hC₁]
    simp
  have hα' : G₁.map e.hom ≫ α.hom ≫ G₀.map e.inv =
      T₁.inv.app P ≫ L₁.map ι.hom ≫ T₀.hom.app P := by
    rw [hα]
    simp
  have m₁ := T₁.inv.naturality γ.hom
  have m₀ := T₀.hom.naturality γ.inv
  simp only [Functor.comp_map] at m₀ m₁
  refine ⟨Ψ₀.symm ≪≫ L₀.mapIso γ ≪≫ e, ?_⟩
  suffices H : G₁.map (Ψ₀.symm ≪≫ L₀.mapIso γ ≪≫ e).hom ≫ α.hom ≫
      G₀.map (Ψ₀.symm ≪≫ L₀.mapIso γ ≪≫ e).inv ≫ θ₀.hom = θ₁.hom by
    rw [← H]
    simp
  rw [hθ₀, hθ₁]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc]
  rw [reassoc_of% hα', reassoc_of% m₁, ← reassoc_of% m₀, Iso.hom_inv_id_app_assoc, ← hI]
  simp only [Functor.map_comp, Category.assoc]

/-- `exists_iso_comp_eq_of_transition_comparisons` with the comparisons `Ψ_i : b g_i L_i ≅ a_i` and
`θ_i : a₀ G_i ≅ a₁` given as natural isomorphisms, read at an object `K`. -/
theorem exists_iso_comp_eq_of_transition_comparisons_app
    {C D D₀ D₁ E₀ E₁ : Type*} [Category* C] [Category* D] [Category* D₀] [Category* D₁]
    [Category* E₀] [Category* E₁] (b : C ⥤ D) (g₀ : D ⥤ D₀) (g₁ : D ⥤ D₁) (F₀ F₁ : D₀ ⥤ D₁)
    (L₀ : D₀ ⥤ E₀) (L₁ : D₁ ⥤ E₁) (G₀ G₁ : E₀ ⥤ E₁) (a₀ : C ⥤ E₀) (a₁ : C ⥤ E₁)
    (c₀ : g₀ ⋙ F₀ ⟶ g₁) (c₁ : g₀ ⋙ F₁ ⟶ g₁)
    (T₀ : F₀ ⋙ L₁ ≅ L₀ ⋙ G₀) (T₁ : F₁ ⋙ L₁ ≅ L₀ ⋙ G₁)
    (Ψ₀ : b ⋙ g₀ ⋙ L₀ ≅ a₀) (Ψ₁ : b ⋙ g₁ ⋙ L₁ ≅ a₁) (θ₀ : a₀ ⋙ G₀ ≅ a₁) (θ₁ : a₀ ⋙ G₁ ≅ a₁)
    (K : C) {K' : D} (β : b.obj K ≅ K') {Q₀ P : D₀} {Q₁ : D₁} (eT₀ : Q₀ ≅ g₀.obj K')
    (eT₁ : Q₁ ⟶ g₁.obj K') (p₀ : F₀.obj Q₀ ≅ Q₁) (p₁ : F₁.obj Q₀ ⟶ Q₁)
    (hp₀ : p₀.hom ≫ eT₁ = F₀.map eT₀.hom ≫ c₀.app K')
    (hp₁ : p₁ ≫ eT₁ = F₁.map eT₀.hom ≫ c₁.app K')
    (j : Q₀ ≅ P) (ι : F₁.obj P ≅ F₀.obj P)
    (hj : p₁ ≫ p₀.inv = F₁.map j.hom ≫ ι.hom ≫ F₀.map j.inv)
    {K₀ : E₀} (e : L₀.obj P ≅ K₀) (α : G₁.obj K₀ ≅ G₀.obj K₀)
    (hα : L₁.map ι.hom = T₁.hom.app P ≫ G₁.map e.hom ≫ α.hom ≫ G₀.map e.inv ≫ T₀.inv.app P)
    (hC₀ : L₁.map (c₀.app (b.obj K)) ≫ Ψ₁.hom.app K =
      T₀.hom.app (g₀.obj (b.obj K)) ≫ G₀.map (Ψ₀.hom.app K) ≫ θ₀.hom.app K)
    (hC₁ : L₁.map (c₁.app (b.obj K)) ≫ Ψ₁.hom.app K =
      T₁.hom.app (g₀.obj (b.obj K)) ≫ G₁.map (Ψ₀.hom.app K) ≫ θ₁.hom.app K) :
    ∃ eK : a₀.obj K ≅ K₀,
      G₁.map eK.hom ≫ α.hom = (θ₁.hom.app K ≫ θ₀.inv.app K) ≫ G₀.map eK.hom :=
  exists_iso_comp_eq_of_transition_comparisons g₀ g₁ F₀ F₁ L₀ L₁ G₀ G₁ c₀ c₁ T₀ T₁ β eT₀ eT₁ p₀ p₁
    hp₀ hp₁ j ι hj e α hα (Ψ₀.app K) (Ψ₁.app K) (θ₀.app K) (θ₁.app K) hC₀ hC₁

end CategoryTheory

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  {a : U ⟶ (SimplicialObject.const T.Spaces).obj X}

/-- **The face maps of an fppf hypercovering are flat** (Stacks 0DER, `faces_in_p`). -/
theorem isFlat_map_delta_of_isHypercoveringAugmentation
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a) (k : ℕ)
    (i : Fin (k + 2)) :
    IsFlat T.schemeSite S T.scheme_mem (U.map (SimplexCategory.δ i).op).hom := by
  let P : MorphismProperty T.Spaces := fun _ _ f => IsFlat T.schemeSite S T.scheme_mem f.hom
  have : P.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange _ _ _
  have : P.IsMultiplicative :=
    { id_mem := fun Z => isFlat_id _ _ _ Z.2
      comp_mem := fun {Z₁ Z₂ Z₃} f g hf hg => isFlat_comp _ _ _ Z₁.2 Z₂.2 Z₃.2 f.hom g.hom hf hg }
  exact MorphismProperty.IsHypercovering.face_mem P (A := { left := U, right := X, hom := a })
    { map_zero := isFlat_of_singleton_mem_pretopology _ h.1
      map_one := isFlat_of_singleton_mem_pretopology _ h.2.1
      matching := fun n hn => isFlat_of_singleton_mem_pretopology _ (h.2.2 n hn) } k i

/-- The last vertex `τⁿ⁺¹ₙ₊₁` of `⦋n + 1⦌` is the last vertex of `⦋n⦌` followed by `δ 0`. -/
theorem const_last_succ_eq (n : ℕ) :
    SimplexCategory.const (SimplexCategory.mk 0) ⦋n + 1⦌ (Fin.last (n + 1)) =
      SimplexCategory.const (SimplexCategory.mk 0) ⦋n⦌ (Fin.last n) ≫ SimplexCategory.δ 0 :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by
    simp [SimplexCategory.δ]))

/-- **The last-vertex maps `U_n → U_0` of an fppf hypercovering are flat**: they are composites of
face maps. -/
theorem isFlat_map_const_last_of_isHypercoveringAugmentation
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a) (k : SimplexCategory) :
    IsFlat T.schemeSite S T.scheme_mem
      (U.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op).hom := by
  obtain ⟨n⟩ := k
  induction n with
  | zero =>
    have h0 : SimplexCategory.const (SimplexCategory.mk 0) ⦋0⦌ (Fin.last 0) = 𝟙 _ :=
      SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦
        Subsingleton.elim (α := Fin 1) _ _))
    rw [h0, op_id, U.map_id]
    exact isFlat_id _ _ _ (U.obj (op ⦋0⦌)).2
  | succ n ih =>
    have e : (U.map (SimplexCategory.const (SimplexCategory.mk 0) ⦋n + 1⦌
        (Fin.last (n + 1))).op).hom =
        (U.map (SimplexCategory.δ (0 : Fin (n + 2))).op).hom ≫
          (U.map (SimplexCategory.const (SimplexCategory.mk 0) ⦋n⦌ (Fin.last n)).op).hom := by
      rw [const_last_succ_eq, op_comp, U.map_comp]
      rfl
    rw [show (Fin.last (⦋n + 1⦌ : SimplexCategory).len) = Fin.last (n + 1) from rfl, e]
    exact isFlat_comp _ _ _ (U.obj _).2 (U.obj _).2 (U.obj _).2 _ _
      (isFlat_map_delta_of_isHypercoveringAugmentation h n 0) ih

open AlgebraicGeometry.Space renaming
preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
  → preservesFiniteLimits_pullbackModules_of_isFlat in
/-- **Gluing along an fppf hypercovering, relative to transition comparisons.** Let
`K₀ ∈ D_{QCoh}(𝒪_{U_0})` and `α : L(f_{δ¹₁})^* K₀ ≅ L(f_{δ¹₀})^* K₀` satisfy the cocycle condition
on `U_2`, and let `Ext^i(K_n, K_n) = 0` for `i < 0`, where `K_n = L(f_{τⁿₙ})^* K₀`. Given
isomorphisms `θ_i : L(f_{δ¹ᵢ})^* La_0^* ≅ La_1^*` through which the strict transitions of `Lb^*K`
read, there is `K ∈ D_{QCoh}(𝒪_X)` and `La_0^* K ≅ K₀` compatible with `α` and `θ₁ ≫ θ₀⁻¹`. -/
theorem exists_derivedPullback_degreeZero_iso_compatible_of_transitions
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)
    (K₀ : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌))).O)) _ _
      (HasDerivedCategory.standard _))
    (hK₀ : @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌))).O)) K₀)
    (α : (derivedPullback (spacesEtaleRingedToposHom
        (U.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback (spacesEtaleRingedToposHom
        (U.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀)
    (hα : SpacesEtaleDerivedCocycle U K₀ α)
    (hExt : ∀ (n : ℕ) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback (spacesEtaleRingedToposHom
          (U.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op))).obj K₀ ⟶
        (shiftFunctor (@DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋n⦌))).O)) _ _
          (HasDerivedCategory.standard _)) i).obj
          ((derivedPullback (spacesEtaleRingedToposHom
            (U.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op))).obj K₀), g = 0)
    (θ₀ : derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom (a.app (op ⦋0⦌))) ⋙
        derivedPullback
        (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
        (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (0 : Fin 2)).op)) ≅
      derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom (a.app (op ⦋0 + 1⦌))))
    (θ₁ : derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom (a.app (op ⦋0⦌))) ⋙
        derivedPullback
        (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
        (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (1 : Fin 2)).op)) ≅
      derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
        (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom (a.app (op ⦋0 + 1⦌))))
    (hC₀ : ∀ K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _),
      (derivedPullback (strictComponentRingedToposHom U ⦋0 + 1⦌)).map
        (((strictSituation U).derivedComponentModuleTransition (strictStructureSheaf U)
          (SimplexCategory.δ (0 : Fin 2))).app
            ((derivedPullback (X := strictRingedTopos U)
              (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
              (strictAugmentationRingedToposHom a)).obj K)) ≫
        (strictAugmentationDegreeDerivedIso a ⦋0 + 1⦌).hom.app K =
      (strictComponentDerivedTransitionIso U (SimplexCategory.δ (0 : Fin 2))).hom.app
          (((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) ⦋0⦌).obj
            ((derivedPullback (X := strictRingedTopos U)
              (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
              (strictAugmentationRingedToposHom a)).obj K)) ≫
        (derivedPullback
          (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
          (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (0 : Fin 2)).op))).map
          ((strictAugmentationDegreeDerivedIso a ⦋0⦌).hom.app K) ≫ θ₀.hom.app K)
    (hC₁ : ∀ K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _),
      (derivedPullback (strictComponentRingedToposHom U ⦋0 + 1⦌)).map
        (((strictSituation U).derivedComponentModuleTransition (strictStructureSheaf U)
          (SimplexCategory.δ (1 : Fin 2))).app
            ((derivedPullback (X := strictRingedTopos U)
              (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
              (strictAugmentationRingedToposHom a)).obj K)) ≫
        (strictAugmentationDegreeDerivedIso a ⦋0 + 1⦌).hom.app K =
      (strictComponentDerivedTransitionIso U (SimplexCategory.δ (1 : Fin 2))).hom.app
          (((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) ⦋0⦌).obj
            ((derivedPullback (X := strictRingedTopos U)
              (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
              (strictAugmentationRingedToposHom a)).obj K)) ≫
        (derivedPullback
          (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
          (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (1 : Fin 2)).op))).map
          ((strictAugmentationDegreeDerivedIso a ⦋0⦌).hom.app K) ≫ θ₁.hom.app K) :
    ∃ K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _),
      @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) K ∧
      ∃ eK : (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          (U.obj (op ⦋0⦌))) (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj K ≅ K₀,
        (derivedPullback (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (1 : Fin 2)).op))).map
            eK.hom ≫ α.hom =
          (θ₁.hom.app K ≫ θ₀.inv.app K) ≫
            (derivedPullback (spacesEtaleRingedToposHom
              (U.map (SimplexCategory.δ (0 : Fin 2)).op))).map eK.hom := by
  have hface : ∀ (k : ℕ) (i : Fin (k + 2)), PreservesFiniteLimits
      (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ i).op)).toModulesHom.pullbackModules :=
    fun k i ↦
      preservesFiniteLimits_pullbackModules_of_isFlat
        _ (isFlat_map_delta_of_isHypercoveringAugmentation h k i)
  have hK : ∀ k : SimplexCategory, @DerivedCategoryB.derivedCategoryB _ _ _
      (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op k))).O))
      ((derivedPullback (spacesEtaleRingedToposHom
          (U.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀) :=
    fun k ↦
      have := preservesFiniteLimits_pullbackModules_of_isFlat
          _ (isFlat_map_const_last_of_isHypercoveringAugmentation h k)
      open Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom in
      derivedCategoryB_isQuasicoherentOnSite_derivedPullback_of_exact
        _ K₀ hK₀
  have hExt' : ∀ (k : SimplexCategory) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback (spacesEtaleRingedToposHom
          (U.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀ ⟶
        (shiftFunctor (@DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op k))).O)) _ _
          (HasDerivedCategory.standard _)) i).obj
          ((derivedPullback (spacesEtaleRingedToposHom
            (U.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀),
        g = 0 := fun k ↦ by
    obtain ⟨n⟩ := k
    exact hExt n
  refine (exists_derivedModuleCocyclePair U K₀ α hα).elim fun Pr hPr ↦ hPr.elim fun e he ↦ ?_
  refine (exists_isCartesianDerivedModule_pairDerivedModuleSystem U Pr K₀ e hExt').elim
    fun K' hK' ↦ hK'.2.elim fun eT ↦ ?_
  have hqK' := derivedCategoryB_isQuasicoherentOnSite_of_pairDerivedModuleSystem_iso U hface Pr K₀ e
    hK K' hK'.1 eT
  refine ((strictSituation U).exists_iso_pairDerivedModuleTransition_comp_inv
    (strictStructureSheaf U) Pr).elim fun j hj ↦ ?_
  have :=
    RingedToposHom.isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules
      (strictRingedToposHom U)
  have hK'' :=
    open Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom in
    derivedCategoryB_isQuasicoherentOnSite_derivedPullback_of_exact
      (strictRingedToposHom U) K' hqK'
  refine (exists_derivedPullback_obj_iso h _ hK'').elim fun K hK ↦ hK.2.elim fun ε ↦
    ⟨K, hK.1, ?_⟩
  have := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := ringedTopos U) (Y := strictRingedTopos U)
        (Z := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (strictAugmentationRingedToposHom a) (strictRingedToposHom U))
  let β : (derivedPullback (strictAugmentationRingedToposHom a)).obj K ≅ K' :=
    (derivedPullback (X := ringedTopos U) (Y := strictRingedTopos U)
      (strictRingedToposHom U)).preimageIso
      ((derivedPullbackCompIso (strictRingedToposHom U) (strictAugmentationRingedToposHom a) ≪≫
        derivedPullbackIsoOfPullbackModulesIso
          (φ := RingedToposHom.comp (X := ringedTopos U) (Y := strictRingedTopos U)
            (Z := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
            (strictAugmentationRingedToposHom a) (strictRingedToposHom U))
          (ψ := augmentationRingedToposHom a)
          (strictAugmentationTwoIso a).pullbackModulesIso).app K ≪≫ ε)
  exact CategoryTheory.exists_iso_comp_eq_of_transition_comparisons_app
    (derivedPullback (X := strictRingedTopos U)
      (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
      (strictAugmentationRingedToposHom a))
    ((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) ⦋0⦌)
    ((strictSituation U).derivedComponentModuleRestriction (strictStructureSheaf U) ⦋0 + 1⦌)
    ((strictSituation U).derivedTransitionPullback (strictStructureSheaf U)
      (SimplexCategory.δ (0 : Fin 2)))
    ((strictSituation U).derivedTransitionPullback (strictStructureSheaf U)
      (SimplexCategory.δ (1 : Fin 2)))
    (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
      (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0⦌)
      (strictComponentRingedToposHom U ⦋0⦌))
    (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
      (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋0 + 1⦌)
      (strictComponentRingedToposHom U ⦋0 + 1⦌))
    (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
      (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
      (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (0 : Fin 2)).op)))
    (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
      (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
      (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (1 : Fin 2)).op)))
    (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)))
      (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
      (spacesEtaleRingedToposHom (a.app (op ⦋0⦌))))
    (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0 + 1⦌)))
      (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
      (spacesEtaleRingedToposHom (a.app (op ⦋0 + 1⦌))))
    ((strictSituation U).derivedComponentModuleTransition (strictStructureSheaf U)
      (SimplexCategory.δ (0 : Fin 2)))
    ((strictSituation U).derivedComponentModuleTransition (strictStructureSheaf U)
      (SimplexCategory.δ (1 : Fin 2)))
    (strictComponentDerivedTransitionIso U (SimplexCategory.δ (0 : Fin 2)))
    (strictComponentDerivedTransitionIso U (SimplexCategory.δ (1 : Fin 2)))
    (strictAugmentationDegreeDerivedIso a ⦋0⦌) (strictAugmentationDegreeDerivedIso a ⦋0 + 1⦌)
    θ₀ θ₁ K β ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation ⦋0⦌).mapIso eT)
    (eT.hom.app ⦋0 + 1⦌)
    ((strictSituation U).pairDerivedModuleTransitionIso (strictStructureSheaf U) Pr
      (SimplexCategory.δ (0 : Fin 2)))
    ((strictSituation U).pairDerivedModuleTransition (strictStructureSheaf U) Pr
      (SimplexCategory.δ (1 : Fin 2)))
    (SimplicialSiteSituation.SimplicialDerivedModuleSystem.Hom.naturality eT.hom
      (SimplexCategory.δ (0 : Fin 2)))
    (SimplicialSiteSituation.SimplicialDerivedModuleSystem.Hom.naturality eT.hom
      (SimplexCategory.δ (1 : Fin 2)))
    j Pr.iso hj e α he (hC₀ K) (hC₁ K)

/-- **Gluing along an fppf hypercovering, given the transition identities on complexes.** The
statement of Stacks 0DLA, for hypercoverings whose strict transitions along `δ¹₀`, `δ¹₁` satisfy
`StrictTransitionHomotopyIdentity`: `K ∈ D_{QCoh}(𝒪_X)` and `e : La_0^* K ≅ K₀` with
`L(f_{δ¹₁})^* e ≫ α = θ₁ ≫ θ₀⁻¹ ≫ L(f_{δ¹₀})^* e`,
`θ_i = augmentationTransitionDerivedIso a δ¹ᵢ`. -/
theorem exists_derivedPullback_degreeZero_iso_compatible_of_homotopy
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)
    (K₀ : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌))).O)) _ _
      (HasDerivedCategory.standard _))
    (hK₀ : @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌))).O)) K₀)
    (α : (derivedPullback (spacesEtaleRingedToposHom
        (U.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback (spacesEtaleRingedToposHom
        (U.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀)
    (hα : SpacesEtaleDerivedCocycle U K₀ α)
    (hhom₀ : StrictTransitionHomotopyIdentity a (SimplexCategory.δ (0 : Fin 2)))
    (hhom₁ : StrictTransitionHomotopyIdentity a (SimplexCategory.δ (1 : Fin 2)))
    (hExt : ∀ (n : ℕ) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback (spacesEtaleRingedToposHom
          (U.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op))).obj K₀ ⟶
        (shiftFunctor (@DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋n⦌))).O)) _ _
          (HasDerivedCategory.standard _)) i).obj
          ((derivedPullback (spacesEtaleRingedToposHom
            (U.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op))).obj K₀), g = 0) :
    ∃ K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _),
      @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) K ∧
      ∃ e : (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          (U.obj (op ⦋0⦌))) (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj K ≅ K₀,
        (derivedPullback (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (1 : Fin 2)).op))).map
            e.hom ≫ α.hom =
          ((augmentationTransitionDerivedIso a (SimplexCategory.δ (1 : Fin 2))).hom.app K ≫
            (augmentationTransitionDerivedIso a (SimplexCategory.δ (0 : Fin 2))).inv.app K) ≫
            (derivedPullback (spacesEtaleRingedToposHom
              (U.map (SimplexCategory.δ (0 : Fin 2)).op))).map e.hom :=
  exists_derivedPullback_degreeZero_iso_compatible_of_transitions h K₀ hK₀ α hα hExt
    (augmentationTransitionDerivedIso a (SimplexCategory.δ (0 : Fin 2)))
    (augmentationTransitionDerivedIso a (SimplexCategory.δ (1 : Fin 2)))
    (fun K ↦ strictAugmentationDegreeDerivedIso_transition_app_of_homotopy a
      (SimplexCategory.δ (0 : Fin 2)) hhom₀ K)
    (fun K ↦ strictAugmentationDegreeDerivedIso_transition_app_of_homotopy a
      (SimplexCategory.δ (1 : Fin 2)) hhom₁ K)

/-- **Stacks 0DLA: gluing quasi-coherent derived descent data along an fppf hypercovering.** Let
`a : U → X` be an fppf hypercovering of an algebraic space `X`, `K₀ ∈ D_{QCoh}(𝒪_{U_0})` and
`α : L(f_{δ¹₁})^* K₀ ≅ L(f_{δ¹₀})^* K₀` an isomorphism satisfying the cocycle condition (on `U_2`,
through the canonical identifications of the composite face maps). Set
`K_n = L(f_{τⁿₙ})^* K₀` with `τⁿₙ : ⦋0⦌ → ⦋n⦌, 0 ↦ n`, and assume `Ext^i(K_n, K_n) = 0` for
`i < 0`. Then there are `K ∈ D_{QCoh}(𝒪_X)` and an isomorphism `e : La_0^* K ≅ K₀` compatible with
`α`: `L(f_{δ¹₁})^* e ≫ α = θ₁ ≫ θ₀⁻¹ ≫ L(f_{δ¹₀})^* e`, where
`θ_i : L(f_{δ¹ᵢ})^* La_0^* ≅ La_1^*` are the canonical isomorphisms (`a_0 ∘ f_{δ¹ᵢ} = a_1`). -/
@[stacks 0DLA]
theorem exists_derivedPullback_degreeZero_iso_compatible
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)
    (K₀ : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌))).O)) _ _
      (HasDerivedCategory.standard _))
    (hK₀ : @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌))).O)) K₀)
    (α : (derivedPullback (spacesEtaleRingedToposHom
        (U.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback (spacesEtaleRingedToposHom
        (U.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀)
    (hα : SpacesEtaleDerivedCocycle U K₀ α)
    (hExt : ∀ (n : ℕ) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback (spacesEtaleRingedToposHom
          (U.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op))).obj K₀ ⟶
        (shiftFunctor (@DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op ⦋n⦌))).O)) _ _
          (HasDerivedCategory.standard _)) i).obj
          ((derivedPullback (spacesEtaleRingedToposHom
            (U.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op))).obj K₀), g = 0) :
    ∃ K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _),
      @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) K ∧
      ∃ e : (derivedPullback (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          (U.obj (op ⦋0⦌))) (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom (a.app (op ⦋0⦌)))).obj K ≅ K₀,
        (derivedPullback (spacesEtaleRingedToposHom (U.map (SimplexCategory.δ (1 : Fin 2)).op))).map
            e.hom ≫ α.hom =
          ((augmentationTransitionDerivedIso a (SimplexCategory.δ (1 : Fin 2))).hom.app K ≫
            (augmentationTransitionDerivedIso a (SimplexCategory.δ (0 : Fin 2))).inv.app K) ≫
            (derivedPullback (spacesEtaleRingedToposHom
              (U.map (SimplexCategory.δ (0 : Fin 2)).op))).map e.hom :=
  exists_derivedPullback_degreeZero_iso_compatible_of_transitions h K₀ hK₀ α hα hExt
    (augmentationTransitionDerivedIso a (SimplexCategory.δ (0 : Fin 2)))
    (augmentationTransitionDerivedIso a (SimplexCategory.δ (1 : Fin 2)))
    (fun K ↦ strictAugmentationDegreeDerivedIso_transition_app a (SimplexCategory.δ (0 : Fin 2)) K)
    (fun K ↦ strictAugmentationDegreeDerivedIso_transition_app a (SimplexCategory.δ (1 : Fin 2)) K)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
