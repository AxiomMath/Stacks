module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsUnit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstVanishingAndSections
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks

/-!
# Extensions of quasi-coherent modules on the small étale site

Let `S` be a scheme contained in a big étale site.  The quasi-coherent `𝒪`-modules on the small
étale site of `S` are closed under extensions inside all `𝒪`-modules: if `0 → 𝒜 → ℳ → 𝒞 → 0` is
short exact with `𝒜` and `𝒞` quasi-coherent, then `ℳ` is quasi-coherent.  This is the middle-term
case of the two-out-of-three clause of Descent, Lemma 0GNB; the kernel, cokernel and colimit
clauses are in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentAbelian.lean`.

The proof is the source's.  The cohomological input is the vanishing of the first Čech
cohomology of `𝓕^a`, for `𝓕` quasi-coherent on `S`, on the finite affine coverings of an affine
object (the étale case of [Stacks, Tag 03FJ]), which by [Stacks, Tag 03F8] makes the sections of
`ℳ → 𝒞` surjective over every affine object.  Hence the restriction of the sequence to the small
Zariski site of `S` is short exact, its middle term is quasi-coherent, and the five lemma applied
to the counit of `𝓕 ↦ 𝓕^a ⊣ restriction` identifies `ℳ` with the associated module of that middle
term.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_cechCohomology_quasiCoherentPresheaf`: the positive-degree
  Čech cohomology of `𝓕^a` vanishes on a finite affine jointly surjective family of an affine
  object of the small étale site.
* `AlgebraicGeometry.SmallEtale.exists_finite_affine_le`: such families are cofinal among the
  covering sieves of an affine object.
* `AlgebraicGeometry.SmallEtale.surjective_val_app_g_of_shortExact`: the sections over an affine
  object of a short exact sequence with quasi-coherent first term are surjective.
* `AlgebraicGeometry.SmallEtale.isClosedUnderExtensions_isQuasicoherentOnSite`: **an extension of
  quasi-coherent modules on the small étale site is quasi-coherent.**

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical functor from the small étale site of `S` to the schemes over `S` preserves
fibre products: it does so after forgetting the structure morphism, and `Over.forget` reflects
fibre products. -/
instance preservesPullbacks_toOver :
    PreservesLimitsOfShape WalkingCospan (toOver B S hS) :=
  have : PreservesLimitsOfShape WalkingCospan (toOver B S hS ⋙ Over.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (toScheme B S hS))
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-- The canonical functor from the small étale site of `S` to the schemes over `S` preserves the
iterated fibre products of an arbitrary family. -/
theorem isIso_cechProductMapOfFunctor_toOver {V : SmallEtale B S hS}
    (E : PreZeroHypercover.{u} V) (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    IsIso (cechProductMapOfFunctor (toOver B S hS) E n i) :=
  have : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a))))
      (Over.post (X := V) (toOver B S hS)) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost (toOver B S hS) E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  isIso_cechProductMapOfFunctor (toOver B S hS) E n i

/-- **The positive-degree Čech cohomology of `𝓕^a` vanishes on a finite affine covering of an
affine object of the small étale site.**  The image of such a family in the schemes over `S` is a
standard étale covering, the Čech complex of the family is that of its image, and the Čech
cohomology of the image vanishes by [Stacks, Tag 03FJ]. -/
theorem isZero_cechCohomology_quasiCoherentPresheaf (F : S.Modules) [F.IsQuasicoherent]
    {V : SmallEtale B S hS} (hV : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V))
    (E : PreZeroHypercover.{u} V) (hfin : Finite E.I₀)
    (haff : ∀ i, _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (E.X i)))
    (hsurj : ∀ x : (toScheme B S hS).obj V,
      ∃ i, x ∈ Set.range ((toScheme B S hS).map (E.f i)))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E ((toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S F) p) := by
  have : _root_.AlgebraicGeometry.IsAffine ((toOver B S hS).obj V).left := hV
  have h : IsStandardCovering .etale (fun i ↦ ((E.map (toOver B S hS)).X i).left)
      (fun i ↦ ((E.map (toOver B S hS)).f i).left) :=
    { finite_index := hfin
      affine_source := haff
      jointly_surjective := Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (hsurj x)
      standard := fun i ↦ inferInstanceAs (Etale ((toScheme B S hS).map (E.f i))) }
  exact (isZero_cechCohomology_succ_quasiCoherentPresheaf ((toOver B S hS).obj V) .etale F
      (E.map (toOver B S hS)) h p hp).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
      (cechComplexIsoOfFunctor (toOver B S hS) E (quasiCoherentPresheafFunctor S F)
        (fun n i ↦ isIso_cechProductMapOfFunctor_toOver B S hS E n i)).symm)

/-- **Finite affine coverings are cofinal among the coverings of an affine object** of the small
étale site of `S`: every covering sieve of such an object contains the sieve generated by a
finite jointly surjective family of objects with affine underlying schemes.  Each point is in the
image of a member of the sieve, hence of an affine open of that member, and quasi-compactness of
the affine object extracts finitely many of these, their images being open. -/
theorem exists_finite_affine_le {V : SmallEtale B S hS}
    (hV : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V)) {R : Sieve V}
    (hR : R ∈ topology B S hS V) :
    ∃ E : PreZeroHypercover.{u} V, Finite E.I₀ ∧
      (∀ i, _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (E.X i))) ∧
      (∀ x : (toScheme B S hS).obj V,
        ∃ i, x ∈ Set.range ((toScheme B S hS).map (E.f i))) ∧ E.sieve₀ ≤ R := by
  classical
  have key : ∀ x : (toScheme B S hS).obj V, ∃ (W : SmallEtale B S hS) (g : W ⟶ V), R g ∧
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj W) ∧
        x ∈ Set.range ((toScheme B S hS).map g) := by
    intro x
    obtain ⟨W, g, hg, y, rfl⟩ := exists_mem_arrows_mem_range B S hS hR x
    obtain ⟨-, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      ((toScheme B S hS).obj W).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y)
        isOpen_univ
    refine ⟨openSubObj B S hS W U, openSubHom B S hS W U ≫ g, R.downward_closed hg _, hU,
      ⟨⟨y, hyU⟩, ?_⟩⟩
    rw [Functor.map_comp]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Scheme.Opens.ι_apply U ⟨y, hyU⟩))
  choose W g hg hW hx using key
  have hopen : ∀ x, IsOpen (Set.range ((toScheme B S hS).map (g x))) := fun x ↦ by
    simpa only [Set.image_univ] using
      ((toScheme B S hS).map (g x)).isOpenMap Set.univ isOpen_univ
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ Set.range ((toScheme B S hS).map (g x))) hopen
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨⟨{x // x ∈ s}, fun t ↦ W t.1, fun t ↦ g t.1⟩, inferInstance, fun t ↦ hW t.1,
    fun x ↦ ?_, ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hxy⟩
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro _ _ ⟨t⟩
    exact hg t.1

/-- **Sections over an affine object of a short exact sequence with quasi-coherent first term
are surjective.**  This is [Stacks, Tag 03F8] applied to the finite affine coverings of the
object, which are cofinal among its coverings by
`AlgebraicGeometry.SmallEtale.exists_finite_affine_le`, and on which the first Čech cohomology of
the first term vanishes: that term is `𝓕^a` for its restriction `𝓕` to the small Zariski site,
and `AlgebraicGeometry.SmallEtale.isZero_cechCohomology_quasiCoherentPresheaf` applies. -/
theorem surjective_val_app_g_of_shortExact
    (T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))) (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) {V : SmallEtale B S hS}
    (hV : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V)) :
    Function.Surjective (T.g.val.app (op V)) := by
  have hT' : (T.map (SheafOfModules.toSheaf (structureSheaf B S hS))).ShortExact :=
    hT.map_of_exact _
  have hr₁ := isQuasicoherent_restrictModule B S hS T.X₁ h₁
  let F := (restrictModule B S hS).obj T.X₁
  have : F.IsQuasicoherent := hr₁
  let e : (sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).obj
      (T.map (SheafOfModules.toSheaf (structureSheaf B S hS))).X₁ ≅
        (toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S F :=
    ((SheafOfModules.toSheaf (structureSheaf B S hS) ⋙
      sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).mapIso
        (@asIso _ _ _ _ _ (isIso_counit B S hS T.X₁ h₁ hr₁))).symm ≪≫
      associatedModulePresheafIso B S hS F
  refine surjective_on_sections_of_isZero_cechCohomology.{u, u, u + 1, u}
    (topology B S hS) _ hT' V
    {E | Finite E.I₀ ∧ (∀ i, _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (E.X i))) ∧
      ∀ x : (toScheme B S hS).obj V, ∃ i, x ∈ Set.range ((toScheme B S hS).map (E.f i))}
    (fun E hE ↦ mem_topology_of_jointlySurjective fun x ↦ ?_) ?_
    (fun _ _ _ _ ↦ inferInstance) ?_
  · obtain ⟨i, hi⟩ := hE.2.2 x
    exact ⟨E.X i, E.f i, Sieve.ofArrows_mk _ _ i, hi⟩
  · intro R hR
    obtain ⟨E, hfin, haff, hsurj, hle⟩ := exists_finite_affine_le B S hS hV hR
    exact ⟨E, ⟨hfin, haff, hsurj⟩, hle⟩
  · rintro E ⟨hfin, haff, hsurj⟩
    exact (isZero_cechCohomology_quasiCoherentPresheaf B S hS F hV E hfin haff hsurj 1
      one_pos).of_iso ((HomologicalComplex.homologyFunctor _ _ 1).mapIso
        ((Stacks.CechSite.cechComplexFunctor E).mapIso e))

/-- **Extensions of quasi-coherent modules on the small étale site are quasi-coherent** (Descent,
Lemma 0GNB, the extension clause).  Let `0 → 𝒜 → ℳ → 𝒞 → 0` be a short exact sequence of
`𝒪`-modules on `S_étale` with `𝒜` and `𝒞` quasi-coherent.  Its restriction to the small Zariski
site of `S` is short exact: restriction is left exact, being a right adjoint, and the restriction
of `ℳ → 𝒞` is surjective on every affine open by
`AlgebraicGeometry.SmallEtale.surjective_val_app_g_of_shortExact`.  The outer restrictions are
quasi-coherent, hence so is the middle one, quasi-coherent modules on a scheme being closed under
extensions.  The counit of `𝓕 ↦ 𝓕^a ⊣ restriction` is invertible at `𝒜` and `𝒞`, and `𝓕 ↦ 𝓕^a`
is exact, so by the five lemma it is invertible at `ℳ`, which is therefore the associated module
of a quasi-coherent `𝒪_S`-module. -/
instance isClosedUnderExtensions_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    let r := restrictModule B S hS
    let a := associatedModule B S hS
    let adj := associatedModuleAdjunction B S hS
    have hr₁ := isQuasicoherent_restrictModule B S hS T.X₁ h₁
    have hr₃ := isQuasicoherent_restrictModule B S hS T.X₃ h₃
    have : PreservesLimitsOfSize.{u, u} r := adj.rightAdjoint_preservesLimits
    have : PreservesFiniteLimits r := PreservesLimitsOfSize.preservesFiniteLimits r
    have : a.Additive := SheafOfModules.pullback_additive (structureMap B S hS)
    have : r.Additive := adj.right_adjoint_additive
    have hex := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono r).1 inferInstance
      T hT
    have hepi : Epi (r.map T.g) := by
      apply (SheafOfModules.toSheaf.{u} S.ringCatSheaf).epi_of_epi_map
      apply (TopCat.Sheaf.isLocallySurjective_iff_epi (X := S.carrier)
        ((SheafOfModules.toSheaf.{u} S.ringCatSheaf).map (r.map T.g))).mp
      rw [TopCat.Presheaf.isLocallySurjective_iff]
      intro U s x hx
      obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
      exact ⟨W, hWU, surjective_val_app_g_of_shortExact B S hS T hT h₁
        (V := (opensToSmallEtale B S hS).obj W) hW _, hxW⟩
    have hrT : (T.map r).ShortExact := ShortComplex.ShortExact.mk' hex.1 hex.2 hepi
    have hr₂ : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) (r.obj T.X₂) :=
      Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_X₂_of_shortExact hrT
        hr₁ hr₃
    have : PreservesFiniteLimits a := preservesFiniteLimits_associatedModule B S hS
    let φ : (T.map r).map a ⟶ T :=
      { τ₁ := adj.counit.app T.X₁
        τ₂ := adj.counit.app T.X₂
        τ₃ := adj.counit.app T.X₃
        comm₁₂ := (adj.counit.naturality T.f).symm
        comm₂₃ := (adj.counit.naturality T.g).symm }
    have : IsIso φ.τ₁ := isIso_counit B S hS T.X₁ h₁ hr₁
    have : IsIso φ.τ₃ := isIso_counit B S hS T.X₃ h₃ hr₃
    have : IsIso φ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ (hrT.map_of_exact a) hT
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).prop_of_iso (asIso φ.τ₂)
        (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _ hr₂)

end AlgebraicGeometry.SmallEtale

end
