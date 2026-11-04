module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.Representability
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ZeroSchemeCoordinates
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.Hyperplane
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSubstitution
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical coordinates on `𝐏(H⁰(X, 𝒪_X(D))^∨)` ([Stacks, Tag 0CCT])

The representability of the fibre of the Abel map by `𝐏(H⁰(X, 𝒪_X(D))^∨)` goes through coordinates:
a basis `w` of `Γ(X, 𝒪_X(D))` identifies the fibre with `Proj k[T₀, …, Tₙ]`, and a basis `bV` of
`H⁰(X, 𝒪_X(D))^∨` identifies `Proj k[T₀, …, Tₙ]` with `𝐏(H⁰(X, 𝒪_X(D))^∨)`. The composite is the
canonical bijection of the source when `w` comes from a `k`-basis `b` of `H⁰` and `bV` is the
dual basis of `b`. This file supplies the three facts that pin it down at closed points:

* `Stacks.LinearSystemScheme.globalSectionsBasis` and `sectionOf_eq_sum`: the basis `w` of
  `Γ(X, F)` attached to `b`, and the coordinates of a section in it;
* `Stacks.LinearSystemScheme.comap_coordDivisor_point`: over `Spec k`, the family of `[c]` is
  the zero scheme of `Σⱼ cⱼ wⱼ` on `X`;
* `Stacks.LinearSystemScheme.coordMor_comp_inv_eq_pointOfClosedPoint`: the `k`-point `[c]` of
  `Proj k[T₀, …, Tₙ]`, read in `𝐏(V)` through `bV`, is the closed point cut out by the functional
  `φ` with `φ(bVⱼ) = cⱼ`.

## References

* [Stacks Project, Tag 0CCT](https://stacks.math.columbia.edu/tag/0CCT)
* [Stacks Project, Example 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.Hilbert

universe u

namespace Stacks.LinearSystemScheme

section Basis

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The global section of `F` corresponding to an element of `H⁰(X, F)`. -/
def sectionOf (F : X.Modules) (s : cohomologyOverField k f F 0) : Γ(F, ⊤) :=
  (cohomologyOverFieldZeroIsoSections k f F).hom s

/-- The basis of `Γ(X, F)` over `Γ(Spec k, 𝒪)` corresponding to a `k`-basis `b` of `H⁰(X, F)`. -/
def globalSectionsBasis (F : X.Modules) {m : ℕ}
    (b : Module.Basis (Fin m) k (cohomologyOverField k f F 0)) :
    letI := baseModule f F ⊤; Module.Basis (Fin m) Γ(Spec (.of k), ⊤) Γ(F, ⊤) :=
  let e := (cohomologyOverFieldZeroIsoSections k f F).toLinearEquiv
  letI kmod : Module k Γ(F, ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let ι : ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F)) ≃ₗ[k]
      Γ(F, ⊤) :=
    { toFun := fun x => x, invFun := fun x => x, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  letI := baseModule f F ⊤
  ((b.map e).map ι).mapCoeffs (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
    fun c x => by
      change (f.appLE ⊤ ⊤ _).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c) • x =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c • x
      rw [show f.appLE ⊤ ⊤ (le_preimage_top f ⊤) = f.app ⊤ from
        Scheme.Hom.appLE_preimage_self f ⊤]
      rfl

/-- The `j`-th vector of `globalSectionsBasis k f F b` is the global section of `F` corresponding
to `b j`. -/
theorem globalSectionsBasis_apply (F : X.Modules) {m : ℕ}
    (b : Module.Basis (Fin m) k (cohomologyOverField k f F 0)) (j : Fin m) :
    globalSectionsBasis k f F b j = sectionOf k f F (b j) := by
  simp [globalSectionsBasis, sectionOf]
  rfl

/-- The section of `s` in the coordinates of `b`. -/
theorem sectionOf_eq_sum (F : X.Modules) {m : ℕ}
    (b : Module.Basis (Fin m) k (cohomologyOverField k f F 0))
    (s : cohomologyOverField k f F 0) :
    sectionOf k f F s = ∑ j, f.appTop ((Scheme.ΓSpecIso (.of k)).inv (b.repr s j)) •
      sectionOf k f F (b j) := by
  conv_lhs => rw [← b.sum_repr s]
  rw [sectionOf, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  rfl

end Basis

section ZeroScheme

variable {X T : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {n : ℕ}
  (w : Fin n → Γ(L, ⊤))

/-- A coordinate section along `p = 𝟙` is the corresponding combination of the `wⱼ`. -/
theorem zeroScheme_coordSection_of_eq_id (p : X ⟶ X) (hp : p = 𝟙 X) (q : X ⟶ T)
    (c : Fin n → Γ(T, ⊤))
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback p).obj L)] :
    zeroScheme X ((Scheme.Modules.pullback p).obj L) (coordSection p q L w c) =
      zeroScheme X L (∑ j, q.appTop (c j) • w j) := by
  subst hp
  refine zeroScheme_eq_of_iso ((Scheme.Modules.pullbackId X).app L) ?_
  simp only [coordSection, Iso.app_hom, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Scheme.Modules.Hom.app_smul, Stacks.Chow.FreeTower.pullbackGlobalSections_id]

end ZeroScheme

section Point

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {n : ℕ}
  (w : letI := baseModule f L ⊤; Module.Basis (Fin n) Γ(Spec (.of k), ⊤) Γ(L, ⊤))

/-- On `X ×_k k = X`, the divisor of a coordinate section is the zero scheme of `Σⱼ cⱼ wⱼ`. -/
theorem comap_coordDivisor_point (c : Fin n → Γ(Spec (.of k), ⊤)) :
    (coordDivisor k f L w (𝟙 (Spec (.of k))) c).comap
        (inv (pullback.fst f (𝟙 (Spec (.of k))))) =
      zeroScheme X L (∑ j, f.appTop (c j) • w j) := by
  rw [coordDivisor, comap_zeroScheme_coordSection]
  have hq : inv (pullback.fst f (𝟙 (Spec (.of k)))) ≫ pullback.snd f (𝟙 (Spec (.of k))) = f := by
    rw [IsIso.inv_comp_eq, pullback.condition, Category.comp_id]
  rw [zeroScheme_coordSection_of_eq_id L w _ (IsIso.inv_hom_id _), hq]

end Point

section ClosedPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] [IsAlgClosed k] {V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V] {n : ℕ} (bV : Module.Basis (Fin (n + 1)) k V)

/-- The structure morphism `𝐏(V) → Spec k` is locally of finite type. -/
instance locallyOfFiniteType_projectiveSpaceOfModuleToSpec :
    LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) :=
  have := AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_projectiveSpaceOfModuleToSpec k V
  inferInstance

/-- **The underlying point of `[c₀ : … : cₙ]` at a `k`-point**, read in `𝐏(V)` through a basis
`bV`: if `cⱼ = φ(bVⱼ)` for a nonzero functional `φ` on `V`, then `[c₀ : … : cₙ]` is the
`k`-point at the closed point of `𝐏(V)` cut out by `φ`. -/
theorem coordMor_comp_inv_eq_pointOfClosedPoint (φ : Module.Dual k V) (hφ : φ ≠ 0)
    (c : Fin (n + 1) → Γ(Spec (.of k), ⊤)) (hc : Ideal.span (Set.range c) = ⊤)
    (hcφ : ∀ j, c j = (Scheme.ΓSpecIso (.of k)).inv (φ (bV j))) :
    coordMor (𝟙 (Spec (.of k))) c hc ≫ (projectiveSpaceOfModuleIsoProjMvPolynomial bV).inv =
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V)
        (ProjectiveSpaceOfModule.linearFunctionalPoint k V φ hφ)
        (ProjectiveSpaceOfModule.linearFunctionalPoint_isClosed k V φ hφ) := by
  have hsec : (coordMor (𝟙 (Spec (.of k))) c hc ≫
      (projectiveSpaceOfModuleIsoProjMvPolynomial bV).inv) ≫
        projectiveSpaceOfModuleToSpec k V = 𝟙 _ := by
    rw [← projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_toSpecZero bV, Category.assoc,
      Iso.inv_hom_id_assoc]
    exact coordMor_comp_projToSpec _ c hc
  have key := congrArg Subtype.val ((pointEquivClosedPoint
    (projectiveSpaceOfModuleToSpec k V)).symm_apply_apply ⟨_, hsec⟩)
  refine key.symm.trans ?_
  suffices hpt : (pointEquivClosedPoint (projectiveSpaceOfModuleToSpec k V)) ⟨_, hsec⟩ =
      ⟨ProjectiveSpaceOfModule.linearFunctionalPoint k V φ hφ,
        ProjectiveSpaceOfModule.linearFunctionalPoint_isClosed k V φ hφ⟩ by
    rw [hpt]
    rfl
  refine Subtype.ext ?_
  show (coordMor (𝟙 (Spec (.of k))) c hc ≫
      (projectiveSpaceOfModuleIsoProjMvPolynomial bV).inv) (IsLocalRing.closedPoint k) = _
  set q := (coordMor (𝟙 (Spec (.of k))) c hc ≫
      (projectiveSpaceOfModuleIsoProjMvPolynomial bV).inv) (IsLocalRing.closedPoint k)
  have hq : q ∈ ProjectiveSpaceOfModule.linearSubspace k V (LinearMap.ker φ) := by
    rw [ProjectiveSpaceOfModule.mem_linearSubspace_iff]
    intro v hv
    rw [ProjectiveSpaceOfModule.mem_pointSubmodule_iff]
    by_contra hnot
    have hmem : q ∈ Proj.basicOpen (fun i => SymPow.symmetricPower i k V)
        (SymmetricAlgebra.ι k V v) := (Proj.mem_basicOpen _ _ _).2 hnot
    have hmem' : coordMor (𝟙 (Spec (.of k))) c hc (IsLocalRing.closedPoint k) ∈
        (projectiveSpaceOfModuleIsoProjMvPolynomial bV).inv ⁻¹ᵁ
          Proj.basicOpen (fun i => SymPow.symmetricPower i k V) (SymmetricAlgebra.ι k V v) :=
      hmem
    rw [projectiveSpaceOfModuleIsoProjMvPolynomial_inv, Proj.map_preimage_basicOpen] at hmem'
    have hpre : IsLocalRing.closedPoint k ∈ coordMor (𝟙 (Spec (.of k))) c hc ⁻¹ᵁ
        Proj.basicOpen (coordGrading k n)
          (SymmetricAlgebra.equivMvPolynomial bV (SymmetricAlgebra.ι k V v)) := hmem'
    have hdeg : SymmetricAlgebra.equivMvPolynomial bV (SymmetricAlgebra.ι k V v) ∈
        coordGrading k n 1 :=
      SymPow.gradedMvPolynomialHom_apply bV _ ▸ (SymPow.gradedMvPolynomialHom bV).map_mem
        (show SymmetricAlgebra.ι k V v ∈ SymPow.symmetricPower 1 k V by
          show _ ∈ LinearMap.range (SymmetricAlgebra.ι k V) ^ 1
          rw [pow_one]
          exact LinearMap.mem_range_self _ _)
    rw [coordMor, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos hdeg] at hpre
    have hzero : evalHom (𝟙 (Spec (.of k))) c
        (SymmetricAlgebra.equivMvPolynomial bV (SymmetricAlgebra.ι k V v)) = 0 := by
      conv_lhs => rw [← bV.sum_repr v]
      simp only [map_sum, map_smul, SymmetricAlgebra.equivMvPolynomial_ι_apply,
        MvPolynomial.smul_eq_C_mul, map_mul, evalHom, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, hcφ, structRingHom,
        Scheme.Hom.id_appTop, Category.comp_id]
      rw [show (∑ x, (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (bV.repr v x) *
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (φ (bV x))) =
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (∑ x, bV.repr v x * φ (bV x)) by
        simp [map_sum, map_mul]]
      have : ∑ x, bV.repr v x * φ (bV x) = φ v :=
        calc ∑ x, bV.repr v x * φ (bV x) = φ (∑ x, bV.repr v x • bV x) := by
              rw [map_sum]
              exact Finset.sum_congr rfl fun x _ => (map_smul φ _ _).symm
          _ = φ v := by rw [bV.sum_repr v]
      rw [this, LinearMap.mem_ker.mp hv, map_zero]
    rw [hzero, Scheme.basicOpen_zero] at hpre
    exact hpre
  rw [ProjectiveSpaceOfModule.linearSubspace_ker k V φ hφ] at hq
  exact hq

end ClosedPoint

end Stacks.LinearSystemScheme

end
