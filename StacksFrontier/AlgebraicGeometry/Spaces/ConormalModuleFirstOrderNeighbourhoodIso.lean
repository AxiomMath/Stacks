module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePullbackEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningImmersion

/-!
# The conormal module of a closed subspace in its first order neighbourhood

Let `Z` be a closed subspace of an algebraic space `X` over a scheme `S`, with defining ideal
sheaf `𝓘 ⊆ 𝒪_X`, and let `N ⊆ X` be its first order infinitesimal neighbourhood: the closed
subspace whose ideal sheaf is, on every étale chart of `X`, the square of that of `Z`.  Write
`g : N ⟶ X` for the inclusion and `Z_N = g⁻¹(Z) ⊆ N`.  The fibre product square
```
Z_N --→ N
 |      |
 Z ---→ X
```
induces by [Stacks Project, Tag 04CP] a map `𝒞_{Z/X} ⟶ 𝒞_{Z_N/N}` of conormal modules, and
[Stacks Project, Tag 05ZX] asserts that it is an isomorphism.  This file proves it.

## Main results

* `Ideal.map_eq_zero_of_mem_sq`: a linear map out of an ideal into a module the ideal
  annihilates kills the square of the ideal.
* `CategoryTheory.Adjunction.isIso_map_of_forall_exists_comp_eq`: a left adjoint inverts an
  epimorphism through which every morphism into the image of the right adjoint factors.
* `AlgebraicGeometry.Space.submodule_le_of_forall_isAffine`: a submodule of a module on the
  small étale site of an algebraic space is contained in another as soon as it is on every
  affine chart.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward_preimageSubspace`: a direct
  image along `Z_N ⟶ N ⟶ X` is annihilated by the ideal of `Z`.
* `AlgebraicGeometry.Space.mem_definingIdealAt_of_idealSheafMapTranspose_eq_zero` and
  `AlgebraicGeometry.Space.ker_idealSheafMapTranspose_le`: the kernel of `τ` lies in the ideal of
  `N`, and is killed by every morphism into a module annihilated by `𝓘`.
* `AlgebraicGeometry.Space.exists_idealSheafMap_comp_eq_of_ker_eq_ker_sq`: the factorization of
  every `ψ : g^*𝓘 ⟶ j_*M` through `ι`.
* `AlgebraicGeometry.Space.isIso_conormalMap_of_ker_eq_ker_sq`: **[Stacks Project, Tag 05ZX]**
  for a closed subspace.

## Implementation notes

The neighbourhood is described in the chart-level spelling of
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_infinitesimalNeighbourhood`: on every
étale chart of `X` the kernel ideal sheaf of the chart-level closed immersion of `N` is the
square of that of `Z`.  At most one closed subspace has this property
(`AlgebraicGeometry.Space.eq_of_ker_eq_ker_pow`) and one does
(`AlgebraicGeometry.Space.exists_ker_eq_ker_sq`), so the hypothesis names the neighbourhood.

The source states [Stacks Project, Tag 05ZX] for an immersion and reduces it to a closed
immersion into an open subspace; the closed case is the one stated here, as for
`AlgebraicGeometry.Space.conormalModule`.

## References

* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **A linear map out of an ideal into a module it annihilates kills the square of the
ideal.** -/
theorem Ideal.map_eq_zero_of_mem_sq {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    {I : Ideal A} (f : I →ₗ[A] M) (hann : ∀ a ∈ I, ∀ m : M, a • m = 0) {y : A}
    (hy : y ∈ I ^ 2) (hyI : y ∈ I) : f ⟨y, hyI⟩ = 0 := by
  rw [Submodule.pow_succ, Submodule.pow_one] at hy
  refine Submodule.mul_induction_on' (C := fun y _ => ∀ hyI : y ∈ I, f ⟨y, hyI⟩ = 0)
    ?_ ?_ hy hyI
  · intro a ha b hb hab
    have hsm : (⟨a * b, hab⟩ : I) = a • (⟨b, hb⟩ : I) := rfl
    rw [hsm, map_smul]
    exact hann a ha _
  · intro y hy z hz ihy ihz hyz
    have hle : I * I ≤ I := Submodule.mul_le.2 fun a _ b hb => I.mul_mem_left a hb
    have hsum : (⟨y + z, hyz⟩ : I) = ⟨y, hle hy⟩ + ⟨z, hle hz⟩ := rfl
    rw [hsum, map_add, ihy, ihz, add_zero]

namespace CategoryTheory

/-- **A morphism out of a left adjoint factors through `ι` once its transpose factors through the
transpose of `ι`.**  For an adjunction `F ⊣ G` with `G` full and faithful, a morphism
`ψ : F X ⟶ Y'` factors through `ι : F X ⟶ Y` as soon as its transpose factors through the
transpose of `ι` by some morphism `G Y ⟶ G Y'`. -/
theorem Adjunction.exists_comp_eq_of_homEquiv_comp_eq {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Full] [G.Faithful] {X : C} {Y Y' : D}
    (ι : F.obj X ⟶ Y) (ψ : F.obj X ⟶ Y') (γ : G.obj Y ⟶ G.obj Y')
    (h : adj.homEquiv _ _ ι ≫ γ = adj.homEquiv _ _ ψ) :
    ∃ β : Y ⟶ Y', ι ≫ β = ψ := by
  refine ⟨G.preimage γ, (adj.homEquiv _ _).injective ?_⟩
  rw [Adjunction.homEquiv_naturality_right, Functor.map_preimage]
  exact h

/-- **The transpose of a morphism out of a left adjoint is an epimorphism** when the unit is one
at its source and the right adjoint carries the morphism to an epimorphism. -/
theorem Adjunction.epi_homEquiv {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {Y : D} (f : F.obj X ⟶ Y)
    (h₁ : Epi (adj.unit.app X)) (h₂ : Epi (G.map f)) : Epi (adj.homEquiv _ _ f) := by
  rw [adj.homEquiv_unit]
  exact epi_comp _ _

/-- **In an abelian category a morphism killing the kernel of an epimorphism factors through
it**, the kernel being given by any limit kernel fork. -/
theorem Abelian.exists_comp_eq_of_isLimit {C : Type*} [Category C] [Abelian C] {A B T : C}
    (τ : A ⟶ B) [Epi τ] (s : KernelFork τ) (hs : IsLimit s) (ψ : A ⟶ T)
    (h : s.ι ≫ ψ = 0) : ∃ γ : B ⟶ T, τ ≫ γ = ψ := by
  obtain ⟨γ, hγ⟩ := CokernelCofork.IsColimit.desc' (Abelian.epiIsCokernelOfKernel s hs) ψ h
  exact ⟨γ, hγ⟩

/-- **A left adjoint inverts an epimorphism through which every morphism into the image of the
right adjoint factors.**  For an adjunction `L ⊣ R` and an epimorphism `ψ : M ⟶ M'` such that
every morphism `M ⟶ R P` factors through `ψ`, the morphism `L ψ` is an isomorphism. -/
theorem Adjunction.isIso_map_of_forall_exists_comp_eq {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M M' : C} (ψ : M ⟶ M') [Epi ψ]
    (h : ∀ (P : D) (χ : M ⟶ R.obj P), ∃ φ : M' ⟶ R.obj P, ψ ≫ φ = χ) :
    IsIso (L.map ψ) := by
  refine (isIso_iff_coyoneda_map_bijective _).2 fun P => ⟨fun x y hxy => ?_, fun χ => ?_⟩
  · apply (adj.homEquiv _ _).injective
    have hxy' := congrArg (adj.homEquiv _ _) hxy
    simp only [Adjunction.homEquiv_naturality_left] at hxy'
    exact (cancel_epi ψ).1 hxy'
  · obtain ⟨φ, hφ⟩ := h P (adj.homEquiv _ _ χ)
    refine ⟨(adj.homEquiv _ _).symm φ, (adj.homEquiv _ _).injective ?_⟩
    simp only [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hφ

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A submodule of a module on the small étale site is contained in another as soon as it is
on every affine étale chart.** -/
theorem submodule_le_of_forall_isAffine (X : AlgebraicSpaces B S hS)
    {M : Modules.{u, u} B S hS X.1 X.2} (N₁ N₂ : M.Submodule)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      N₁.obj (op A) ≤ N₂.obj (op A)) :
    N₁ ≤ N₂ := by
  have : (AffineEtale.inclusion B S hS X.1).IsCoverDense
      (SmallEtale.topology B S hS X.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2.isCoverDense'
  intro W s hs
  refine N₂.isSheaf s ((SmallEtale.topology B S hS X.1).superset_covering ?_
    ((AffineEtale.inclusion B S hS X.1).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS X.1) W.unop))
  rintro Y f ⟨A, l, m, ⟨rfl⟩⟩
  have h1 : M.val.map m.op s ∈ N₂.obj (op ((AffineEtale.inclusion B S hS X.1).obj A)) :=
    h _ A.property (N₁.map m.op hs)
  exact (N₂.toSubfunctor.sieveOfSection s).downward_closed
    (show (N₂.toSubfunctor.sieveOfSection s).arrows m from h1) l

section Neighbourhood

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **A direct image along `g⁻¹(Z) ⟶ Y ⟶ X` is annihilated by the ideal of `Z`**, for a
morphism `g : Y ⟶ X` and a closed subspace `Z ⊆ X`. -/
theorem annihilatedByKerIdeal_modulePushforward_preimageSubspace {Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ X)
    (M : Modules.{u, u} B S hS (preimageSubspace B S hS g Z).1.toFunctor
      (preimageSubspace B S hS g Z).2.1) :
    AnnihilatedByKerIdeal B S hS (subspaceInclusion B S hS X Z)
      ((modulePushforward B S hS g).obj ((modulePushforward B S hS
        (subspaceInclusion B S hS Y (preimageSubspace B S hS g Z))).obj M)) := by
  have hsq : subspaceInclusion B S hS Y (preimageSubspace B S hS g Z) ≫ g =
      preimageProjection B S hS g Z ≫ subspaceInclusion B S hS X Z :=
    conormalEtaleRestrictionSquare B S hS g Z
  have e1 : (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        ((modulePushforward B S hS (preimageProjection B S hS g Z)).obj M) ≅
      (modulePushforward B S hS
        (preimageProjection B S hS g Z ≫ subspaceInclusion B S hS X Z)).obj M :=
    (modulePushforwardCompIso B S hS (preimageProjection B S hS g Z)
      (subspaceInclusion B S hS X Z)).app M
  have e2 : (modulePushforward B S hS
        (preimageProjection B S hS g Z ≫ subspaceInclusion B S hS X Z)).obj M ≅
      (modulePushforward B S hS
        (subspaceInclusion B S hS Y (preimageSubspace B S hS g Z) ≫ g)).obj M :=
    eqToIso (by rw [hsq])
  have e3 : (modulePushforward B S hS
        (subspaceInclusion B S hS Y (preimageSubspace B S hS g Z) ≫ g)).obj M ≅
      (modulePushforward B S hS g).obj ((modulePushforward B S hS
        (subspaceInclusion B S hS Y (preimageSubspace B S hS g Z))).obj M) :=
    ((modulePushforwardCompIso B S hS
      (subspaceInclusion B S hS Y (preimageSubspace B S hS g Z)) g).app M).symm
  exact annihilatedByKerIdeal_of_essImage_modulePushforward B S hS _
    ⟨(modulePushforward B S hS (preimageProjection B S hS g Z)).obj M, ⟨e1 ≪≫ e2 ≪≫ e3⟩⟩

/-- **A section of `𝓘_Z` killed by the transpose of the map of ideal sheaves lies in the ideal
of `N`.** -/
theorem mem_definingIdealAt_of_idealSheafMapTranspose_eq_zero (Z N : ClosedSubspaces B S hS X.1)
    (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ((definingIdealSheaf B S hS X Z).toSheafOfModules).val.obj W)
    (hx : ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
      (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
        (subspaceInclusion B S hS X N)
        (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z))).val.app W x =
          0) :
    x.1 ∈ definingIdealAt B S hS X N W := by
  have hcomp : (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
        (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
          (subspaceInclusion B S hS X N)
          (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z)) ≫
        (modulePushforward B S hS (subspaceInclusion B S hS X N)).map
          (definingIdealSheaf B S hS _
            (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z)).ι =
      (definingIdealSheaf B S hS X Z).ι ≫
        (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
          (structureModulePullbackMap B S hS (subspaceInclusion B S hS X N)) :=
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv_naturality_right
      _ _).symm.trans
      ((congrArg ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _)
        (idealSheafMap_comp_definingIdealSheaf_ι B S hS
          (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
          (subspaceInclusion B S hS X N)
          (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z))).trans
        ((modulePullbackAdjunction B S hS
          (subspaceInclusion B S hS X N)).homEquiv_naturality_left _ _))
  have h2 : ((modulePushforward B S hS (subspaceInclusion B S hS X N)).map
        (definingIdealSheaf B S hS _
          (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z)).ι).val.app W
        (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
          (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
            (subspaceInclusion B S hS X N)
            (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
            (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z))).val.app
          W x) =
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
          (structureModulePullbackMap B S hS (subspaceInclusion B S hS X N))).val.app W
        ((definingIdealSheaf B S hS X Z).ι.val.app W x) :=
    SheafOfModules.hom_congr_app_apply hcomp W x
  rw [hx, map_zero] at h2
  have h4 := Sheaf.hom_congr_app_apply
    (moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS
      (subspaceInclusion B S hS X N)) W ((definingIdealSheaf B S hS X Z).ι.val.app W x)
  exact (mem_definingIdealAt_iff B S hS X N W x.1).2 (h4.symm.trans h2.symm)

variable {Z} {N : ClosedSubspaces B S hS X.1}
variable (hN : ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ 2)

include hN in
/-- **Every morphism out of `𝓘_Z` into a module annihilated by `𝓘_Z` kills the kernel of the
transpose of the map of ideal sheaves**, when `N` is the first order neighbourhood of `Z`. -/
theorem ker_idealSheafMapTranspose_le (P : Modules.{u, u} B S hS X.1 X.2)
    (hP : AnnihilatedByKerIdeal B S hS (subspaceInclusion B S hS X Z) P)
    (χ : (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶ P)
    (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ((definingIdealSheaf B S hS X Z).toSheafOfModules).val.obj W)
    (hx : x ∈ (SheafOfModules.Submodule.ker
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
          (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
            (subspaceInclusion B S hS X N)
            (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
            (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z)))).obj W) :
    x ∈ (SheafOfModules.Submodule.ker χ).obj W :=
  submodule_le_of_forall_isAffine B S hS X
      (M := (definingIdealSheaf B S hS X Z).toSheafOfModules) _ _ (fun A hA x hx => by
    have hAaff : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
    have h4 : x.1 ∈ definingIdealAt B S hS X Z (op A) ^ 2 := by
      rw [← definingIdealAt_eq_pow_of_ker_eq_ker_pow B S hS Z N hN A]
      exact mem_definingIdealAt_of_idealSheafMapTranspose_eq_zero B S hS Z N (op A) x hx
    exact Ideal.map_eq_zero_of_mem_sq (χ.val.app (op A)).hom
      (fun a ha m => hP (op A) a ((SheafOfModules.mem_kerIdeal _ _ a).2 ha) m) h4 x.2) W hx

include hN in
/-- Let `N` be the first order infinitesimal neighbourhood of a closed subspace `Z` of `X`,
`g : N ⟶ X` its inclusion, and `ι : g^*𝓘 ⟶ 𝓙` the map of defining ideal sheaves of the fibre
product square `g⁻¹(Z) ⊆ N` over `Z ⊆ X`.  Every morphism `ψ : g^*𝓘 ⟶ j_*M` into a direct image
along the inclusion `j` of `g⁻¹(Z)` factors through `ι`. -/
theorem exists_idealSheafMap_comp_eq_of_ker_eq_ker_sq
    (M : Modules.{u, u} B S hS
      (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z).1.toFunctor
      (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z).2.1)
    (ψ : (modulePullback B S hS (subspaceInclusion B S hS X N)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      (modulePushforward B S hS (subspaceInclusion B S hS _
        (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z))).obj M) :
    ∃ β : (definingIdealSheaf B S hS _
          (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z)).toSheafOfModules ⟶
        (modulePushforward B S hS (subspaceInclusion B S hS _
          (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z))).obj M,
      idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
          (subspaceInclusion B S hS X N)
          (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z) ≫ β = ψ := by
  have hgc : IsClosedImmersion B S hS (subspaceInclusion B S hS X N).hom := N.2.2
  have hunit : Epi ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).unit.app
      (definingIdealSheaf B S hS X Z).toSheafOfModules) :=
    epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS _ hgc
      (fun M hM => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS _ hgc M hM) _
  have hpe : Epi ((modulePushforward B S hS (subspaceInclusion B S hS X N)).map
      (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
        (subspaceInclusion B S hS X N)
        (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z))) :=
    epi_modulePushforward_map B S hS _ hgc _ (epi_idealSheafMap B S hS _ Z)
  have hτe : Epi ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
      (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
        (subspaceInclusion B S hS X N)
        (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z))) :=
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).epi_homEquiv _ hunit hpe
  have hker := ker_idealSheafMapTranspose_le B S hS hN _
    (annihilatedByKerIdeal_modulePushforward_preimageSubspace B S hS Z
      (subspaceInclusion B S hS X N) M)
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _ ψ)
  have hzero : (SheafOfModules.Submodule.ker
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
        (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
          (subspaceInclusion B S hS X N)
          (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z)))).ι ≫
        (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _ ψ = 0 := by
    ext W s
    exact hker W s.1 s.2
  obtain ⟨γ, hγ⟩ := Abelian.exists_comp_eq_of_isLimit _ _
    (SheafOfModules.Submodule.isLimitKernelFork
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X N)).homEquiv _ _
        (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
          (subspaceInclusion B S hS X N)
          (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z)))) _ hzero
  have hff := fullyFaithfulModulePushforward B S hS _ hgc
  have := hff.full
  have := hff.faithful
  exact (modulePullbackAdjunction B S hS
    (subspaceInclusion B S hS X N)).exists_comp_eq_of_homEquiv_comp_eq _ ψ γ hγ

include hN in
/-- Let `Z` be a closed subspace of an algebraic space `X` and let `N ⊆ X` be its first order
infinitesimal neighbourhood, the closed subspace whose ideal sheaf is on every étale chart of `X`
the square of that of `Z`.  The map `𝒞_{Z/X} ⟶ 𝒞_{Z_N/N}` of conormal modules of
[Stacks Project, Tag 04CP] attached to the fibre product square of `Z_N = Z ×_X N ⊆ N` over
`Z ⊆ X` is an isomorphism. -/
@[stacks 05ZX "the isomorphism, for a closed subspace"]
theorem isIso_conormalMap_of_ker_eq_ker_sq :
    IsIso (conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
      (subspaceInclusion B S hS X N)
      (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z)) := by
  have hιe := epi_idealSheafMap B S hS (subspaceInclusion B S hS X N) Z
  have hj : IsIso ((modulePullback B S hS (subspaceInclusion B S hS _
      (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z))).map
      (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) Z
        (subspaceInclusion B S hS X N)
        (preimageProjection B S hS (subspaceInclusion B S hS X N) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X N) Z))) :=
    (modulePullbackAdjunction B S hS _).isIso_map_of_forall_exists_comp_eq _
      (exists_idealSheafMap_comp_eq_of_ker_eq_ker_sq B S hS hN)
  rw [conormalMap_eq]
  exact IsIso.comp_isIso' (isIso_conormalPullbackComparison B S hS _ _ _ _ _) hj

end Neighbourhood

end AlgebraicGeometry.Space

end
