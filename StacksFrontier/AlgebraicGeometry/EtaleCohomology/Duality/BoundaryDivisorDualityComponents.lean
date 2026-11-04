module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryGysinTraceNonzero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryDivisorPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurveTorsionStatementsClopen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Duality along an étale boundary divisor

Let `f̄ : X̄ ⟶ S` be smooth projective of relative dimension one with geometrically irreducible
fibres, over `S` affine and smooth over the algebraically closed field `k`, and `i : Z ⟶ X̄` a
closed immersion with `Z` finite étale over `S`. For every top-degree trace `t : Rf̄_* Λ ⟶ Λ[-2]`
the trace map `Hom_X̄(i_* Λ_Z, Λ[m]) → Hom_S(Rf̄_* i_* Λ_Z, Λ[m - 2])` is bijective for every `m`:
this is `Stacks.EtaleCohomology.BoundaryDivisorDualityInput`
(`Stacks.EtaleCohomology.boundaryDivisorDualityInput`).

For `Z` irreducible it is `Stacks.EtaleCohomology.isBijectiveAt_directImage_of_isPurityClass`, with
global purity (`Stacks.EtaleCohomology.boundaryDivisorPurityInput`) and the nonvanishing of the
Gysin trace (`Stacks.EtaleCohomology.isIso_boundaryGysinTraceAdjoint_of_irreducibleSpace`). In
general `Z`, smooth over `k`, is locally irreducible, so its irreducible components are finitely
many, open, closed and pairwise disjoint
(`Stacks.EtaleCohomology.isOpen_of_mem_irreducibleComponents_of_forall_exists_isIrreducible`). For
a component `O`, `i_*(j_{O!} Λ_O) ≅ (i ∘ j_O)_* Λ_O`
(`Stacks.EtaleCohomology.directImageLocalUnitIso`), and the relative Mayer--Vietoris sequence of
two disjoint opens splits `j_{O ∪ O'!}` into `j_{O!} ⊕ j_{O'!}`; the five lemma for the trace map
on split sequences (`Stacks.RelativeDuality.isBijectiveAt_of_splitting`) adds the components up.

This is part of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Implementation notes

The statements consume the derived direct images in the standard model
`HasDerivedCategory.standard` of the derived category, as a local instance, as does
`Stacks.EtaleCohomology.BoundaryDivisorDualityInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.RelativeDuality

/-! ### The trace map at zero objects and at biproducts -/

section Biprod

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasShift C ℤ] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (Φ : C ⥤ C') [Φ.CommShift ℤ] [Φ.Additive] {B : C} {L : C'} {c₀ : ℤ}
  (t : ShiftedHom (Φ.obj B) L c₀)

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive] in
/-- **The trace map is bijective at a zero object**: both sides vanish. -/
theorem isBijectiveAt_of_isZero {A : C} (hA : IsZero A) : IsBijectiveAt Φ t A := by
  intro m c h
  have hΦA : IsZero (Φ.obj A) := Φ.map_isZero hA
  refine ⟨fun y₁ y₂ _ => hA.eq_of_src y₁ y₂, fun x => ⟨0, ?_⟩⟩
  exact hΦA.eq_of_src _ _

end Biprod

section BiprodPlus

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜] [HasExt 𝒜]
  {C' : Type*} [Category* C'] [Preadditive C'] [HasZeroObject C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (Φ : DerivedCategory.Plus 𝒜 ⥤ C') [Φ.CommShift ℤ] [Φ.Additive]
  {B : DerivedCategory.Plus 𝒜} {L : C'} {c₀ : ℤ} (t : ShiftedHom (Φ.obj B) L c₀)

include t in
/-- **The trace map is bijective at the middle term of a split short exact sequence of sheaves**
placed in degree zero as soon as it is at the two others: the five lemma
(`Stacks.RelativeDuality.isBijectiveAt_obj₂`). -/
theorem isBijectiveAt_of_splitting [Pretriangulated C'] [Φ.IsTriangulated] {S : ShortComplex 𝒜}
    (σ : S.Splitting)
    (h₁ : IsBijectiveAt Φ t ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj S.X₁))
    (h₃ : IsBijectiveAt Φ t ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj S.X₃)) :
    IsBijectiveAt Φ t ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj S.X₂) :=
  isBijectiveAt_obj₂ _ (Stacks.TopTruncationExt.plusSingleTriangle_distinguished σ.shortExact) h₁ h₃

end BiprodPlus

end Stacks.RelativeDuality

namespace Stacks.EtaleCohomology

open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality Stacks.EtaleCohomology.Purity

attribute [local instance] HasDerivedCategory.standard

/-! ### Irreducible components of a locally irreducible space -/

section Components

variable {α : Type*} [TopologicalSpace α]
  (h : ∀ z : α, ∃ U : Set α, IsOpen U ∧ z ∈ U ∧ IsIrreducible U)

include h in
/-- **The irreducible components of a locally irreducible space are open.** -/
theorem isOpen_of_mem_irreducibleComponents_of_forall_exists_isIrreducible {C : Set α}
    (hC : C ∈ irreducibleComponents α) : IsOpen C := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hVo, hxV, hVirr⟩ := h x
  obtain ⟨C', hC', hVC'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible V hVirr
  have hCC' : C = C' := component_eq_of_open_irreducible_nhd C C' hC hC' V hVo hVirr
    ⟨x, hx, hxV⟩ ⟨x, hVC' hxV, hxV⟩
  exact ⟨V, hCC' ▸ hVC', hVo, hxV⟩

include h in
/-- **The irreducible components of a locally irreducible space are pairwise disjoint.** -/
theorem eq_of_mem_irreducibleComponents_of_forall_exists_isIrreducible {C C' : Set α}
    (hC : C ∈ irreducibleComponents α) (hC' : C' ∈ irreducibleComponents α) {x : α}
    (hx : x ∈ C) (hx' : x ∈ C') : C = C' := by
  obtain ⟨V, hVo, hxV, hVirr⟩ := h x
  exact component_eq_of_open_irreducible_nhd C C' hC hC' V hVo hVirr ⟨x, hx, hxV⟩ ⟨x, hx', hxV⟩

end Components

/-! ### Extension by zero from an open and closed subscheme -/

section Clopen

variable {ℓ : ℕ} [Fact ℓ.Prime] {Z Xbar : Scheme.{u}} (i : Z ⟶ Xbar) (O : Z.Opens)
  [IsClosedImmersion O.ι]

/-- **`i_*(j_{O!} Λ_O) ≅ (i ∘ j_O)_* Λ_O` for an open and closed `O ⊆ Z`**: extension by zero
along the open and closed immersion `j_O` is its direct image (Tag 0GJ1 for the kernel pair of the
monomorphism `j_O`). -/
def directImageLocalUnitIso :
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (localUnit (N := ℓ) O) ≅
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) (O.ι ≫ i)).obj (unitSheaf (X := O) ℓ) :=
  let jO := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) O.ι
  let dO := etaleModuleDirectImage.{u, 0} (ZMod ℓ) O.ι
  let e₁ : localUnit (N := ℓ) O ≅ jO.obj (unitSheaf (X := O) ℓ) :=
    jO.mapIso (unitSheafRestrictionIso (N := ℓ) O)
  let e₂ : jO.obj (unitSheaf (X := O) ℓ) ≅
      jO.obj ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (𝟙 O.toScheme)).obj (unitSheaf (X := O) ℓ)) :=
    jO.mapIso ((etaleModuleDirectImageIdIso (ZMod ℓ) O.toScheme).app (unitSheaf (X := O) ℓ)).symm
  let e₃ : jO.obj ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (𝟙 O.toScheme)).obj
        (unitSheaf (X := O) ℓ)) ≅
      dO.obj ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (𝟙 O.toScheme)).obj
        (unitSheaf (X := O) ℓ)) :=
    (etaleModuleExtensionByZeroDirectImageIsoOfIsIntegralHom (ZMod ℓ) O.ι (𝟙 O.toScheme)
      (𝟙 O.toScheme) O.ι (IsKernelPair.id_of_mono O.ι)).app (unitSheaf (X := O) ℓ)
  let e₄ : dO.obj ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (𝟙 O.toScheme)).obj
      (unitSheaf (X := O) ℓ)) ≅ dO.obj (unitSheaf (X := O) ℓ) :=
    dO.mapIso ((etaleModuleExtensionByZeroIdIso (ZMod ℓ) O.toScheme).app (unitSheaf (X := O) ℓ))
  (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).mapIso (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄) ≪≫
    (etaleModuleDirectImageComp.{u, 0} (ZMod ℓ) O.ι i (O.ι ≫ i) rfl).app _

end Clopen

/-! ### Duality along the boundary divisor -/

section Duality

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

/-- **Duality along an étale boundary divisor of a smooth projective curve**
(`Stacks.EtaleCohomology.BoundaryDivisorDualityInput`): for every top-degree trace
`t : Rf̄_* Λ ⟶ Λ[-2]`, the trace map
`Hom_X̄(i_* Λ_Z, Λ[m]) → Hom_S(Rf̄_* i_* Λ_Z, Λ[m - 2])` is bijective for every `m`. On an
irreducible component `O` of `Z` this is
`Stacks.EtaleCohomology.isBijectiveAt_directImage_of_isPurityClass` with global purity and the
nonvanishing of the Gysin trace; the components are disjoint, open and closed, and the trace map
adds up along the relative Mayer--Vietoris sequences. -/
@[sga "4½ Dualite 2.2" "special case"]
theorem boundaryDivisorDualityInput : BoundaryDivisorDualityInput ℓ k := by
  intro hℓ S Xbar Z q e _ _ fbar i _ _ _ _ _ hproj t ht
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ fbar)
  have : Smooth (i ≫ fbar) := SmoothOfRelativeDimension.smooth 0 (i ≫ fbar)
  have : Smooth ((i ≫ fbar) ≫ q) := inferInstance
  have : LocallyOfFiniteType (i ≫ fbar) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType (i ≫ fbar)).mp inferInstance).2
  have : LocallyOfFiniteType q := inferInstance
  have : LocallyOfFiniteType ((i ≫ fbar) ≫ q) := inferInstance
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian ((i ≫ fbar) ≫ q)
  have : IsNoetherian Z := ⟨⟩
  have hloc := exists_isOpen_isIrreducible_of_smooth ((i ≫ fbar) ≫ q)
  let F := etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι
  let P := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) Xbar) 0
  let Pi := etaleModuleDirectImage.{u, 0} (ZMod ℓ) i
  let ιc := irreducibleComponents (Z : Type u)
  have : Finite ιc := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have : Fintype ιc := Fintype.ofFinite _
  let O : ιc → Z.Opens := fun C =>
    ⟨C.1, isOpen_of_mem_irreducibleComponents_of_forall_exists_isIrreducible hloc C.2⟩
  -- duality on each irreducible component
  have hcomp : ∀ C : ιc, IsBijectiveAt F t (P.obj (Pi.obj (localUnit (N := ℓ) (O C)))) := by
    intro C
    have : IsClosedImmersion (O C).ι :=
      isClosedImmersion_ι_of_isClosed _ (isClosed_of_mem_irreducibleComponents _ C.2)
    have : IrreducibleSpace (O C) := Subtype.irreducibleSpace C.2.1
    have : IsFinite (((O C).ι ≫ i) ≫ fbar) := by rw [Category.assoc]; infer_instance
    have : Etale (((O C).ι ≫ i) ≫ fbar) := by rw [Category.assoc]; infer_instance
    obtain ⟨γ, hγ⟩ := boundaryDivisorPurityInput ℓ k hℓ S Xbar (O C) q e fbar ((O C).ι ≫ i) hproj
    have hτ := isIso_boundaryGysinTraceAdjoint_of_irreducibleSpace ℓ k hℓ q e fbar
      ((O C).ι ≫ i) hproj γ hγ t ht
    exact isBijectiveAt_of_iso (P.mapIso (directImageLocalUnitIso i (O C))).symm
      (isBijectiveAt_directImage_of_isPurityClass ℓ fbar ((O C).ι ≫ i) γ hγ t hτ)
  -- along a short exact sequence with vanishing first term
  have key : ∀ {T : ShortComplex (EtaleModules.{u, 0} (ZMod ℓ) Z)}, T.ShortExact → IsZero T.X₁ →
      IsBijectiveAt F t (P.obj (Pi.obj T.X₂)) → IsBijectiveAt F t (P.obj (Pi.obj T.X₃)) := by
    intro T hT h0 h
    have := hT.isIso_g_iff.2 h0
    exact isBijectiveAt_of_iso (P.mapIso (Pi.mapIso (asIso T.g))) h
  -- disjoint unions
  have hunion : ∀ W₁ W₂ : Z.Opens, (∀ x : Z, x ∉ W₁ ⊓ W₂) →
      IsBijectiveAt F t (P.obj (Pi.obj (localUnit (N := ℓ) W₁))) →
      IsBijectiveAt F t (P.obj (Pi.obj (localUnit (N := ℓ) W₂))) →
      IsBijectiveAt F t (P.obj (Pi.obj (localUnit (N := ℓ) (W₁ ⊔ W₂)))) := by
    intro W₁ W₂ hdisj h₁ h₂
    refine key (shortExact_relativeCover (ZMod ℓ) W₁ W₂ (unitSheaf (X := Z) ℓ))
      (isZero_extensionByZero_of_forall_notMem _ hdisj _) ?_
    let σb : (ShortComplex.mk (biprod.inl : localUnit (N := ℓ) W₁ ⟶
        localUnit (N := ℓ) W₁ ⊞ localUnit (N := ℓ) W₂) biprod.snd biprod.inl_snd).Splitting :=
      { r := biprod.fst
        s := biprod.inr
        f_r := biprod.inl_fst
        s_g := biprod.inr_snd
        id := biprod.total }
    exact isBijectiveAt_of_splitting F t (σb.map (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)) h₁ h₂
  -- finite unions of components
  have hall : ∀ s : Finset ιc,
      IsBijectiveAt F t (P.obj (Pi.obj (localUnit (N := ℓ) (s.sup O)))) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      exact isBijectiveAt_of_isZero F t (P.map_isZero (Pi.map_isZero
        (isZero_extensionByZero_of_forall_notMem _ (fun x hx => by simp at hx) _)))
    | insert C s hC ih =>
      rw [Finset.sup_insert]
      refine hunion (O C) (s.sup O) ?_ (hcomp C) ih
      rintro x ⟨hx₁, hx₂⟩
      rw [Finset.sup_eq_iSup] at hx₂
      obtain ⟨C', hx₂⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₂
      obtain ⟨hC's, hx₂⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₂
      have hCC' : C = C' := Subtype.ext
        (eq_of_mem_irreducibleComponents_of_forall_exists_isIrreducible hloc C.2 C'.2 hx₁ hx₂)
      exact hC (hCC' ▸ hC's)
  -- all of `Z`
  have htop : ∀ x : Z, x ∈ (Finset.univ : Finset ιc).sup O := by
    intro x
    exact (Finset.le_sup (f := O) (Finset.mem_univ ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩)) mem_irreducibleComponent
  let eU : localUnit (N := ℓ) ((Finset.univ : Finset ιc).sup O) ≅ unitSheaf (X := Z) ℓ :=
    @asIso _ _ _ _ ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
      ((Finset.univ : Finset ιc).sup O).ι).counit.app (unitSheaf (X := Z) ℓ))
      (isIso_counit_extensionByZeroAdj_of_forall_mem _ htop _)
  let eZ : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) ≅
      unitSheaf (X := Z) ℓ :=
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).mapIso
        ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) fbar).app
          (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) ≪≫
      (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) i).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  exact isBijectiveAt_of_iso (P.mapIso (Pi.mapIso (eU ≪≫ eZ.symm))) (hall Finset.univ)

end Duality

end Stacks.EtaleCohomology

end
