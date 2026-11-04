module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Normalized
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Product
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.ModuleCohomologyDeltaFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology on a quasi-compact scheme with affine diagonal

Let `X` be a quasi-compact scheme whose diagonal is affine, for instance a separated scheme.
Every quasi-coherent `𝒪_X`-module `ℱ` embeds into a quasi-coherent module `ℱ'` with
`Hᵖ(X, ℱ') = 0` for all `p ≥ 1`, and consequently `{Hⁿ(X, -)}_{n ≥ 0}` is a universal
δ-functor from `QCoh(𝒪_X)` to `Ab`.

The embedding is the source's: choose a finite affine open cover `X = ⋃ Uᵢ` and take
`ℱ' = ∏ᵢ (ιᵢ)_* (ℱ|_{Uᵢ})`, where `ιᵢ : Uᵢ → X` is the inclusion. Affineness of the diagonal
makes each `ιᵢ` an affine morphism, the canonical map `ℱ → ℱ'` is injective because the `Uᵢ`
cover `X`, the higher cohomology of `ℱ|_{Uᵢ}` on the affine scheme `Uᵢ` vanishes, and cohomology
along an affine morphism is unchanged. Universality is then Grothendieck's criterion: a δ-functor
all of whose positive-degree components are effaceable is universal.

## Main definitions

* `Stacks.Cohomology.QcohDelta.coverLift`: the canonical map from a module to the product of the
  pushforwards of its restrictions to the members of a family of open subschemes.
* `Stacks.Cohomology.QcohDelta.cohomologyDeltaFunctor`: the δ-functor on `QCoh(𝒪_X)` whose
  degree-`n` component is `Hⁿ(X, -)` on the underlying module sheaf.

## Main results

* `Stacks.Cohomology.QcohDelta.mono_coverLift`: the canonical map is a monomorphism when the
  family of opens covers the scheme.
* `Stacks.Cohomology.QcohDelta.exists_mono_isZero_hfunctor`: part (1), the embedding of a
  quasi-coherent module into one with vanishing positive-degree cohomology.
* `Stacks.Cohomology.QcohDelta.cohomologyDeltaFunctor_isUniversal`: part (2), universality of
  the cohomology δ-functor on quasi-coherent modules.

## Implementation notes

The δ-functor is the cohomology δ-functor on all of `Mod(𝒪_X)` precomposed with the inclusion
of the quasi-coherent modules, which is exact; so its degree-`n` component is literally
`ObjectProperty.ι _ ⋙ Hfunctor X.ringCatSheaf ⊤ n`, as recorded by
`cohomologyDeltaFunctor_functor`.

Affineness of the diagonal is spelled `IsAffineHom (pullback.diagonal (terminal.from X))` and
quasi-compactness of the scheme is `CompactSpace`.

## References

* [Stacks Project, Tag 0BDY](https://stacks.math.columbia.edu/tag/0BDY)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Cohomology.QcohDelta

/-! ### The inclusion of an affine open is an affine morphism -/

/-- On a scheme with affine diagonal the inclusion of an affine open subscheme is an affine
morphism: its base change along the inclusion of an affine open `V` is the intersection of the
two affine opens, which is affine. -/
theorem isAffineHom_ι_of_isAffineOpen (X : Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) : IsAffineHom U.ι := by
  refine isAffineHom_of_forall_exists_isAffineOpen U.ι fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (by simp)
  refine ⟨V, hxV, hV, ?_⟩
  have hpairs := ((AlgebraicGeometry.isAffineHom_diagonal_tfae X).out 1 2).mp
    ‹IsAffineHom (pullback.diagonal (terminal.from X))›
  exact U.ι.isAffineOpen_iff_of_isOpenImmersion.mp
    (by simpa [U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] using
      hpairs U V hU hV)

/-! ### The embedding into a product of pushforwards along an open cover -/

variable {X : Scheme.{u}} {ι : Type u}

/-- The canonical map `ℱ → ∏ᵢ (ιᵢ)_*(ℱ|_{Uᵢ})` from a module to the product of the pushforwards
of its restrictions to a family of open subschemes, whose `i`-th component is the unit of the
restriction-pushforward adjunction. -/
def coverLift (U : ι → X.Opens) (F : X.Modules) :
    F ⟶ ∏ᶜ fun i ↦ (Scheme.Modules.pushforward (U i).ι).obj
      ((Scheme.Modules.restrictFunctor (U i).ι).obj F) :=
  Pi.lift fun i ↦ (Scheme.Modules.restrictAdjunction (U i).ι).unit.app F

/-- **The canonical map into the product of pushforwards along an open cover is injective.**
Its `i`-th component is, on sections over an open `V`, the restriction map to `Uᵢ ⊓ V`, and these
opens cover `V`, so a section killed by all of them vanishes. -/
theorem mono_coverLift (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (F : X.Modules) :
    Mono (coverLift U F) := by
  refine (Scheme.Modules.toPresheaf X).mono_of_mono_map ?_
  rw [NatTrans.mono_iff_mono_app]
  intro V
  rw [AddCommGrpCat.mono_iff_injective]
  intro s t hst
  have key : ∀ i, F.presheaf.map (homOfLE ((U i).ι.image_preimage_le V.unop)).op s =
      F.presheaf.map (homOfLE ((U i).ι.image_preimage_le V.unop)).op t := by
    intro i
    have hπ : coverLift U F ≫ Pi.π _ i =
        (Scheme.Modules.restrictAdjunction (U i).ι).unit.app F := Pi.lift_π _ _
    have happ : ∀ x, ((Scheme.Modules.toPresheaf X).map (Pi.π _ i)).app V
        (((Scheme.Modules.toPresheaf X).map (coverLift U F)).app V x) =
          F.presheaf.map (homOfLE ((U i).ι.image_preimage_le V.unop)).op x := fun x ↦ by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp, hπ]
      rfl
    rw [← happ s, ← happ t, hst]
  have hcover : V.unop ≤ ⨆ i, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ V.unop := by
    intro x hx
    have hxT : x ∈ ⨆ i, U i := hU ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxT
    refine Opens.mem_iSup.mpr ⟨i, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨hi, hx⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf _ _)
    (fun i ↦ (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ V.unop) V.unop
    (fun i ↦ homOfLE ((U i).ι.image_preimage_le V.unop)) hcover s t key

/-! ### Cohomology of a finite product -/

/-- The cohomology of a finite product of modules vanishes in a degree in which the cohomology
of every factor vanishes: cohomology is additive, hence preserves finite products. -/
theorem isZero_hfunctor_pi (X : Scheme.{u}) (p : ℕ) [Finite ι] (M : ι → X.Modules)
    (hM : ∀ i, IsZero ((Hfunctor X.ringCatSheaf ⊤ p).obj (M i))) :
    IsZero ((Hfunctor X.ringCatSheaf ⊤ p).obj (∏ᶜ M)) := by
  have hadd : (Hfunctor X.ringCatSheaf ⊤ p).Additive :=
    (Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor X.ringCatSheaf ⊤).additive p
  have hfin : PreservesFiniteProducts (Hfunctor X.ringCatSheaf ⊤ p) := inferInstance
  have hshape : PreservesLimitsOfShape (Discrete ι) (Hfunctor X.ringCatSheaf ⊤ p) := inferInstance
  have hdiag : IsZero (Discrete.functor fun i : ι ↦ (Hfunctor X.ringCatSheaf ⊤ p).obj (M i)) := by
    rw [Functor.isZero_iff]
    rintro ⟨i⟩
    exact hM i
  exact IsZero.of_iso
    ((limit.isLimit (Discrete.functor fun i : ι ↦
      (Hfunctor X.ringCatSheaf ⊤ p).obj (M i))).isZero_pt hdiag)
    (PreservesProduct.iso (Hfunctor X.ringCatSheaf ⊤ p) M)

/-! ### Part (1): the embedding with vanishing higher cohomology -/

/-- **Stacks 0BDY, part (1).** On a quasi-compact scheme with affine diagonal every
quasi-coherent `𝒪_X`-module `ℱ` admits an embedding `ℱ → ℱ'` into a quasi-coherent module with
`Hᵖ(X, ℱ') = 0` for all `p ≥ 1`.

Take `ℱ' = ∏ᵢ (ιᵢ)_*(ℱ|_{Uᵢ})` for a finite affine open cover `X = ⋃ Uᵢ`: each `ιᵢ` is affine
because the diagonal of `X` is, so `ℱ'` is quasi-coherent and its cohomology is the product of
the cohomologies of the `ℱ|_{Uᵢ}` on the affine schemes `Uᵢ`, which vanish in positive
degrees. -/
@[stacks 0BDY "part (1): the embedding with vanishing higher cohomology"]
theorem exists_mono_isZero_hfunctor (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ∃ (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (φ : F ⟶ G),
      Mono ((ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)).map φ) ∧
        ∀ p : ℕ, 0 < p → IsZero ((Hfunctor X.ringCatSheaf ⊤ p).obj G.obj) := by
  obtain ⟨Us, hUs, hUsFinite, hUsSup⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact
    (U := (⊤ : X.Opens)) (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  have : Finite Us := hUsFinite.to_subtype
  let U : Us → X.Opens := Subtype.val
  have hUaff : ∀ i, IsAffineOpen (U i) := fun i ↦ hUs i.property
  have hUcover : ⨆ i, U i = ⊤ := by
    rw [hUsSup, sSup_eq_iSup']
  have hAffine : ∀ i, IsAffine (U i).toScheme := fun i ↦ hUaff i
  have hAffHom : ∀ i, IsAffineHom (U i).ι := fun i ↦
    isAffineHom_ι_of_isAffineOpen X (U i) (hUaff i)
  have hFqc : F.obj.IsQuasicoherent := F.property
  let M : Us → X.Modules := fun i ↦ (Scheme.Modules.pushforward (U i).ι).obj
    ((Scheme.Modules.restrictFunctor (U i).ι).obj F.obj)
  have hRqc : ∀ i, ((Scheme.Modules.restrictFunctor (U i).ι).obj F.obj).IsQuasicoherent :=
    fun i ↦ Scheme.Modules.isQuasicoherent_restrictFunctor (U i).ι F.obj
  have hMqc : ∀ i, (M i).IsQuasicoherent := fun i ↦
    have := hAffHom i
    have := hRqc i
    inferInstanceAs (((Scheme.Modules.pushforward (U i).ι).obj
      ((Scheme.Modules.restrictFunctor (U i).ι).obj F.obj)).IsQuasicoherent)
  have hGqc : (∏ᶜ M).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_pi M hMqc
  refine ⟨⟨∏ᶜ M, hGqc⟩, ObjectProperty.homMk (coverLift U F.obj), mono_coverLift U hUcover F.obj,
    fun p hp ↦ isZero_hfunctor_pi X p M fun i ↦ ?_⟩
  have := hAffHom i
  have := hAffine i
  have := hRqc i
  have hAff : IsZero ((Hfunctor (U i).toScheme.ringCatSheaf ⊤ p).obj
      ((Scheme.Modules.restrictFunctor (U i).ι).obj F.obj)) :=
    Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen (U i).toScheme _ ⊤
      (isAffineOpen_top _) p hp
  exact IsZero.of_iso hAff
    ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso (U i).ι p).app
      ⟨(Scheme.Modules.restrictFunctor (U i).ι).obj F.obj, hRqc i⟩).symm

/-! ### Part (2): the universal δ-functor -/

variable (X) in
/-- **The cohomology δ-functor on quasi-coherent modules.** The δ-functor from `QCoh(𝒪_X)` to
`Ab` whose degree-`n` component is `Hⁿ(X, -)` on the underlying module sheaf, obtained by
precomposing the cohomology δ-functor on `Mod(𝒪_X)` with the exact inclusion of the
quasi-coherent modules. -/
def cohomologyDeltaFunctor :
    DeltaFunctor (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
      AddCommGrpCat.{u} :=
  (Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor X.ringCatSheaf ⊤).precomp
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))

variable (X) in
/-- The degree-`n` component of the cohomology δ-functor on quasi-coherent modules is `Hⁿ(X, -)`
read on the underlying module sheaf. -/
@[simp]
theorem cohomologyDeltaFunctor_functor (n : ℕ) :
    (cohomologyDeltaFunctor X).functor n =
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Hfunctor X.ringCatSheaf ⊤ n :=
  rfl

variable (X) in
/-- **Stacks 0BDY, part (2).** On a quasi-compact scheme with affine diagonal the cohomology
functors `{Hⁿ(X, -)}_{n ≥ 0}` form a *universal* δ-functor from `QCoh(𝒪_X)` to `Ab`.

Part (1) effaces every positive-degree component, and an effaceable δ-functor is universal. -/
@[stacks 0BDY "part (2): universality of the delta-functor"]
theorem cohomologyDeltaFunctor_isUniversal [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    (cohomologyDeltaFunctor X).IsUniversal :=
  have : (cohomologyDeltaFunctor X).Effaceable :=
    DeltaFunctor.Effaceable.precomp _ _ fun F ↦ by
      obtain ⟨G, φ, hφ, hzero⟩ := exists_mono_isZero_hfunctor X F
      exact ⟨G, φ,
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)).mono_of_mono_map hφ,
        fun n ↦ hzero (n + 1) n.succ_pos⟩
  DeltaFunctor.isUniversal_of_effaceable _

end Stacks.Cohomology.QcohDelta

end
