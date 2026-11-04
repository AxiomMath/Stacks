module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementAffineSpace
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison

/-!
# A basis of global sections of a quasi-coherent module on an affine scheme

Let `T` be an affine scheme and `G` a quasi-coherent `𝒪_T`-module. A basis `b` of the
`Γ(T, 𝒪_T)`-module `Γ(T, G)`, indexed by a finite type `ι`, gives an isomorphism `𝒪_T^{⊕ ι} ≅ G`
carrying the `j`-th basis vector to `b j`: the morphism it defines is bijective on global sections,
hence an isomorphism (`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top`).

## Main definitions

* `Stacks.RelativeProj.freeHomOfBasis`: the morphism `𝒪_T^{⊕ ι} ⟶ G` of a family of sections.
* `Stacks.RelativeProj.freeIsoOfBasis`: the isomorphism of a basis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

variable {T : Scheme.{u}} (G : T.Modules) {ι : Type u}

/-- `𝒪_T^{⊕ ι}` as a module on the scheme `T`. -/
abbrev freeModule (ι : Type u) : T.Modules := SheafOfModules.free (R := T.ringCatSheaf) ι

/-- The morphism `𝒪_T^{⊕ ι} ⟶ G` sending the `j`-th basis vector to `b j`. -/
def freeHomOfBasis (b : ι → Γ(G, ⊤)) : freeModule (T := T) ι ⟶ G :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan ι) fun j =>
    Scheme.Modules.unitHomEquivTop G (b j)

/-- The composite of the `j`-th coprojection into `𝒪_T^{⊕ ι}` with `freeHomOfBasis G b` is the
morphism `𝒪_T ⟶ G` of the section `b j`. -/
theorem ιFree_freeHomOfBasis (b : ι → Γ(G, ⊤)) (j : ι) :
    SheafOfModules.ιFree j ≫ freeHomOfBasis G b = Scheme.Modules.unitHomEquivTop G (b j) :=
  Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan ι) _ j

/-- The `j`-th basis vector of `𝒪_T^{⊕ ι}` as a global section. -/
abbrev freeBasisSection (j : ι) : Γ(freeModule (T := T) ι, ⊤) :=
  Scheme.Modules.Hom.app (SheafOfModules.ιFree (R := T.ringCatSheaf) j) ⊤ (1 : Γ(T, ⊤))

/-- On global sections, `freeHomOfBasis G b` sends the `j`-th basis vector to `b j`. -/
theorem freeHomOfBasis_app_freeBasisSection (b : ι → Γ(G, ⊤)) (j : ι) :
    Scheme.Modules.Hom.app (freeHomOfBasis G b) ⊤ (freeBasisSection j) = b j :=
  (congrArg (fun φ : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ⟶ G =>
    Scheme.Modules.Hom.app φ ⊤ (1 : Γ(T, ⊤))) (ιFree_freeHomOfBasis G b j)).trans
    (UnitSplitting.unitHomEquivTop_app_top_of_eq_one G (b j) 1 rfl)

variable [Fintype ι]

/-- Every global section of `𝒪_T^{⊕ ι}` is a combination of the basis vectors. -/
theorem exists_eq_sum_freeBasisSection
    (s : Γ(freeModule (T := T) ι, ⊤)) :
    ∃ c : ι → Γ(T, ⊤), s = ∑ j, c j • freeBasisSection j := by
  classical
  let π : ι → (SheafOfModules.free (R := T.ringCatSheaf) ι ⟶
      SheafOfModules.unit T.ringCatSheaf) :=
    fun i => Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan ι) fun j =>
      if i = j then 𝟙 _ else 0
  have hf : ∀ i j, SheafOfModules.ιFree j ≫ π i = if i = j then 𝟙 _ else 0 := fun i j =>
    Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan ι) _ j
  have hsum : ∑ i, π i ≫ SheafOfModules.ιFree i = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan ι) _ _ fun j => ?_
    change SheafOfModules.ιFree j ≫ _ = SheafOfModules.ιFree j ≫ _
    rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
    · rw [← Category.assoc, hf, if_pos rfl, Category.id_comp]
    · intro i _ hij
      rw [← Category.assoc, hf, if_neg hij, zero_comp]
    · simp
  refine ⟨fun i => Scheme.Modules.Hom.app (π i) ⊤ s, ?_⟩
  refine (congrArg (fun φ : freeModule (T := T) ι ⟶ freeModule (T := T) ι =>
      Scheme.Modules.Hom.app φ ⊤ s) hsum).symm.trans ?_
  let ev : (freeModule (T := T) ι ⟶ freeModule (T := T) ι) →+ Γ(freeModule (T := T) ι, ⊤) :=
    { toFun := fun φ => Scheme.Modules.Hom.app φ ⊤ s
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine (map_sum ev _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  change Scheme.Modules.Hom.app (SheafOfModules.ιFree (R := T.ringCatSheaf) i) ⊤
      (Scheme.Modules.Hom.app (π i) ⊤ s) = _
  have h2 : ∀ c : Γ(T, ⊤), c = c • (1 : Γ(T, ⊤)) := fun c => (mul_one c).symm
  exact (congrArg (Scheme.Modules.Hom.app (SheafOfModules.ιFree (R := T.ringCatSheaf) i) ⊤)
    (h2 (Scheme.Modules.Hom.app (π i) ⊤ s))).trans (Scheme.Modules.Hom.app_smul _ _ _)

variable [IsAffine T] [G.IsQuasicoherent] (b : Module.Basis ι Γ(T, ⊤) Γ(G, ⊤))

omit [IsAffine T] [G.IsQuasicoherent] in
/-- The image of a combination of the basis vectors of `𝒪_T^{⊕ ι}`. -/
theorem freeHomOfBasis_app_sum (c : ι → Γ(T, ⊤)) :
    Scheme.Modules.Hom.app (freeHomOfBasis G b) ⊤ (∑ j, c j • freeBasisSection j) =
      ∑ j, c j • b j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Scheme.Modules.Hom.app_smul, freeHomOfBasis_app_freeBasisSection]

/-- **A basis of the global sections of a quasi-coherent module on an affine scheme makes it
free**: the morphism `𝒪_T^{⊕ ι} ⟶ G` of the basis is an isomorphism. -/
instance isIso_freeHomOfBasis : IsIso (freeHomOfBasis G b) := by
  have : (freeModule (T := T) ι).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free ι
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _ ?_
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun s t hst => ?_, fun y => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_eq_sum_freeBasisSection s
    obtain ⟨c', rfl⟩ := exists_eq_sum_freeBasisSection t
    have h : ∑ j, c j • b j = ∑ j, c' j • b j :=
      (freeHomOfBasis_app_sum G b c).symm.trans (hst.trans (freeHomOfBasis_app_sum G b c'))
    obtain rfl : c = c' := funext fun j => by
      simpa only [Module.Basis.repr_sum_self] using congrArg (fun y => b.repr y j) h
    rfl
  · exact ⟨∑ j, b.repr y j • freeBasisSection j,
      (freeHomOfBasis_app_sum G b _).trans (b.sum_repr y)⟩

/-- **The isomorphism `𝒪_T^{⊕ ι} ≅ G` of a basis of `Γ(T, G)`.** -/
def freeIsoOfBasis : freeModule (T := T) ι ≅ G :=
  asIso (freeHomOfBasis G b)

/-- The `j`-th basis vector of `freeIsoOfBasis` is the morphism of the section `b j`. -/
theorem basisMap_freeIsoOfBasis (j : ι) :
    UnitSplitting.basisMap (freeIsoOfBasis G b) j = Scheme.Modules.unitHomEquivTop G (b j) :=
  ιFree_freeHomOfBasis G b j

/-- The `j`-th basis vector of `freeIsoOfBasis` sends `1` to `b j`. -/
theorem basisMap_freeIsoOfBasis_app_one (j : ι) :
    Scheme.Modules.Hom.app (UnitSplitting.basisMap (freeIsoOfBasis G b) j) ⊤ (1 : Γ(T, ⊤)) = b j :=
  freeHomOfBasis_app_freeBasisSection G b j

end Stacks.RelativeProj

end
