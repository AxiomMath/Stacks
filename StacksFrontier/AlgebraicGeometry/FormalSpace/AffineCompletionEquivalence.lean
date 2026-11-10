module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineRigEtaleAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLiftGluing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleAwayFromClosedFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismEqualityFromCompletion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType

/-!
# The completion functor over a Noetherian affine base

Let `X = Spec R` be a Noetherian affine scheme of the big fppf site of `S`, let `T ⊆ |X|` be
closed and let `U ⊂ X` be the open subspace with `|U| = |X| ∖ T`. **Stacks 0ARA** says that the
completion functor of Stacks 0AR5, from the morphisms `f : X' ⟶ X` of algebraic spaces locally
of finite type which are an isomorphism over `U` to the rig-étale morphisms `W ⟶ X_{/T}` with
`W` a locally Noetherian formal algebraic space, is an equivalence. This file shows that a
rig-étale `g : W ⟶ X_{/T}` with `W` a Noetherian affine formal algebraic space is, up to
isomorphism over `X_{/T}`, the completion of a finite-type modification of `X`, and defines the
completion functor on finite-type modifications.

## Main definitions

* `AlgebraicGeometry.FormalSpace.finiteTypeModificationCompletion`: the completion functor on
  finite-type modifications.

## Main results

* `AlgebraicGeometry.FormalSpace.etale_comp_of_forall_etaleAt`: an étale morphism of schemes
  followed by a morphism étale at every point of its image is étale.
* `AlgebraicGeometry.FormalSpace.isEtale_pullback_snd_openSubspaceOfPoints_of_etaleAt`: a
  morphism of the site étale at every point lying over `|X| ∖ T` is étale over the open subspace
  `U` cut out by `|X| ∖ T`, in the sense of morphisms of algebraic spaces.
* `AlgebraicGeometry.FormalSpace.exists_finiteTypeModification_completion_iso_of_isNoetherian`:
  a rig-étale morphism from a Noetherian affine formal algebraic space to `X_{/T}` is isomorphic
  over `X_{/T}` to the completion of a finite-type modification of `X`.

## References

* [Stacks Project, Tag 0ARA](https://stacks.math.columbia.edu/tag/0ARA)
* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
* [Stacks Project, Tag 0AR9](https://stacks.math.columbia.edu/tag/0AR9)
* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Étaleness over the open complement of `T` -/

/-- An étale morphism of schemes `ψ : W ⟶ X'` followed by a morphism `f : X' ⟶ X` which is
étale at every point of the image of `ψ` is étale. -/
theorem etale_comp_of_forall_etaleAt {W X' X : Scheme.{u}} (ψ : W ⟶ X') [Etale ψ]
    (f : X' ⟶ X) (hf : ∀ w, EtaleAt f (ψ w)) : Etale (ψ ≫ f) := by
  have key : ∀ w : W, ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ ψ ≫ f) := by
    intro w
    obtain ⟨V, -, hwV, hV⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt f (ψ w) (hf w)
    refine ⟨ψ ⁻¹ᵁ V, hwV, ?_⟩
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance
  choose V hwV hV using key
  exact IsZariskiLocalAtSource.of_iSup_eq_top V
    (eq_top_iff.mpr fun w _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨w, hwV w⟩) hV

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- A morphism `f : X' ⟶ X` of the big fppf site which is étale, as a morphism of schemes, at
every point lying over `|X| ∖ T` is étale over the open subspace `U` of `X` cut out by
`|X| ∖ T`: the base change of `f` to `U` is an étale morphism of algebraic spaces. -/
theorem isEtale_pullback_snd_openSubspaceOfPoints_of_etaleAt {X X' : BigFppfOver B S hS}
    (f : X' ⟶ X) (T : Set (Space.points B S hS (yoneda.obj X))) (hT : IsClosed T)
    (hf : ∀ p : Space.points B S hS (yoneda.obj X'),
      Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) p ∉ T →
        EtaleAt ((BigFppfOver.toScheme B S hS).map f) (Space.pointsToScheme B S hS X' p)) :
    Space.IsEtale B S hS
      (pullback.snd (yoneda.map f) (Space.openSubspaceOfPoints B S hS (yoneda.obj X) Tᶜ).ι) := by
  set U := Space.openSubspaceOfPoints B S hS (yoneda.obj X) Tᶜ with hUdef
  set U' := Space.openSubspaceOfPoints B S hS (yoneda.obj X')
    (Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) ⁻¹' Tᶜ) with hU'def
  have hXsp := isAlgebraicSpace_yoneda B S hS X
  have hX'sp := isAlgebraicSpace_yoneda B S hS X'
  have hUo : Space.IsOpenSubspace B S hS U :=
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hXsp _ hT.isOpen_compl
  have hU'o : Space.IsOpenSubspace B S hS U' :=
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hX'sp _
      (hT.isOpen_compl.preimage (Space.continuous_pointsMap B S hS _))
  have hcomp : Space.IsEtale B S hS (U'.ι ≫ yoneda.map f) := by
    intro W φ hφ
    have hφι := Space.isEtale_ι_of_isOpenSubspace hU'o W φ hφ
    obtain ⟨ψ, hψ⟩ : ∃ ψ : W ⟶ X', yoneda.map ψ = φ ≫ U'.ι :=
      ⟨yoneda.preimage _, yoneda.map_preimage _⟩
    rw [← hψ] at hφι
    have hψe := (Space.presheaf_yoneda_map_etale_iff B S hS ψ).mp hφι
    rw [← Category.assoc, ← hψ, ← Functor.map_comp]
    refine (Space.presheaf_yoneda_map_etale_iff B S hS _).mpr ?_
    rw [Functor.map_comp]
    refine etale_comp_of_forall_etaleAt _ _ fun w ↦ ?_
    obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B S hS W w
    rw [← Space.pointsToScheme_pointsMap]
    apply hf
    have hmem : Space.pointsMap B S hS _ (yoneda.map ψ) p ∈
        Set.range (Space.pointsMap B S hS U'.toFunctor U'.ι) := by
      rw [hψ, Space.pointsMap_comp_apply]
      exact ⟨_, rfl⟩
    rwa [hU'def, Space.range_pointsMap_ι_openSubspaceOfPoints] at hmem
  have hres : Space.IsEtale B S hS (Space.openComplementRestriction B S hS (yoneda.map f) T) :=
    Space.isEtale_of_isEtale_over B S hS hU'o.1 hUo.1 hXsp _ _ _ hcomp
      (Space.isEtale_ι_of_isOpenSubspace hUo) (Space.openComplementRestriction_ι B S hS _ T)
  have hsq := Space.isPullback_openComplementRestriction B S hS (yoneda.map f) T
  rw [← hsq.isoPullback_inv_snd]
  exact Space.isEtale_comp B S hS (Space.isEtale_of_isIso B S hS _) hres

/-! ### Noetherian affine formal algebraic spaces -/

/-- Let `X = Spec R` be a Noetherian affine scheme of the big fppf site, let `T ⊆ |X|` be
closed, let `W` be a Noetherian affine formal algebraic space and let `g : W ⟶ X_{/T}` be
rig-étale. Then there is a morphism `p : X'' ⟶ X` of algebraic spaces, locally of finite type
and an isomorphism over the open subspace `U` cut out by `|X| ∖ T`, whose completion `p_{/T}` is
isomorphic to `g` over `X_{/T}`. -/
theorem exists_finiteTypeModification_completion_iso_of_isNoetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (hWaff : IsAffineFormalAlgebraicSpace B S hS W)
    (hWnoeth : IsNoetherian B S hS W)
    (g : W ⟶ Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T)
    (hg : IsRigEtale B S hS g) :
    ∃ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS (yoneda.obj (affineOver B S hS hR s)) Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj M.obj ≅ Over.mk g) := by
  obtain ⟨X', -, f, e, hlft, -, het, he, -⟩ :=
    exists_affine_algebraization_of_isRigEtale B S hS hR s T hT hWaff hWnoeth g hg
  have hXsp := isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s)
  have hX'sp := isAlgebraicSpace_yoneda B S hS X'
  have hfU := isEtale_pullback_snd_openSubspaceOfPoints_of_etaleAt f T hT het
  obtain ⟨X'', hX'', g', p, hgp, hp, hpU, hiso⟩ :=
    exists_factorization_isIso_completionSheafMap B S hS hXsp hX'sp T hT (yoneda.map f)
      ((Space.isLocallyOfFiniteType_yoneda_map_iff B S hS f).mpr hlft)
      (by rwa [openSubspacesOrderIso_symm_compl B S hS hXsp T hT])
  rw [openSubspacesOrderIso_symm_compl B S hS hXsp T hT] at hpU
  refine ⟨⟨Over.mk p, ⟨hX'', hpU⟩, hp⟩, ⟨?_⟩⟩
  let a : Over.mk (yoneda.map f) ⟶ Over.mk p := Over.homMk g' hgp
  have : IsIso ((Over.forget _).map ((Space.completionOverFunctor B S hS T).map a)) := by
    change IsIso (Space.completionOverMap B S hS T a)
    unfold Space.completionOverMap
    have : IsIso (Space.completionSheafMap B S hS a.left
        (Space.pointsMap B S hS (Over.mk p).left (Over.mk p).hom ⁻¹' T)) := hiso
    infer_instance
  have : IsIso ((Space.completionOverFunctor B S hS T).map a) :=
    isIso_of_reflects_iso _ (Over.forget _)
  exact (asIso ((Space.completionOverFunctor B S hS T).map a)).symm ≪≫ Over.isoMk e he

/-! ### The completion functor on finite-type modifications -/

/-- The completion functor of Stacks 0AR5 on finite-type modifications of `X` outside the open
subspace cut out by `|X| ∖ T`, valued in the category of all morphisms of fppf sheaves into
`X_{/T}`: the inclusion of the finite-type modifications into the algebraic spaces over `X`,
followed by completion along `T`. -/
noncomputable abbrev finiteTypeModificationCompletion {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) :
    Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ) ⥤
      Over (Space.completionSheaf B S hS X T) :=
  ObjectProperty.ι _ ⋙ Space.completionOverFunctor B S hS T

end AlgebraicGeometry.FormalSpace

end
