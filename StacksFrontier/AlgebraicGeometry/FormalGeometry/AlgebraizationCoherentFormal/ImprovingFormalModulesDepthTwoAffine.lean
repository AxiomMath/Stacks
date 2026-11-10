module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoSections
public import StacksFrontier.RingTheory.Module.AdicSystem.ExtensionAdicReplacement
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.EssentiallyConstantCover
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProIsoTransfer
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ModuleTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence

/-!
# The depth-two improvement over an affine open: the module-level data

Let `X` be a Noetherian scheme, `ℐ` an ideal sheaf, `(ℱₙ)` an object of `Coh(X, ℐ)`, and let
`(ℱₙ) ⟶ (ℱ'ₙ) ⟶ (ℱ''ₙ)` be the canonical maps of [Stacks, Tag 0EJF]: the depth-one quotient along
`T` followed by the depth-two extension along `T'`. Fix an affine open `U` with ring
`A₀ = Γ(X, U)` and write `M = lim Γ(U, ℱₙ)`, `M'ₙ = Γ(U, ℱ'ₙ)` and `M''ₙ = Γ(U, ℱ''ₙ)`.

We organise the sections over `U` into extension data in the sense of
`Stacks.AdicSystem.ExtensionData`, and identify the quotients `M''ₙ / M'ₙ` with `H¹_{T'}(M'ₙ)`,
naturally in `n`, which is the identification of the third paragraph of the source's proof.

## Main definitions

* `Stacks.Algebraization.sectionsShortComplexSystem`: the inverse system of short exact sequences
  `0 → M'ₙ → M''ₙ → M''ₙ/M'ₙ → 0`.
* `Stacks.Algebraization.affineExtensionData`: the extension data of the sections over `U`, given
  the two properties of the system `(M'ₙ)` established in the proof of [Stacks, Tag 0EJE].

## Main results

* `Stacks.Algebraization.quotientSectionsIsoLocalCohomologyOne`: the natural isomorphism
  `M''ₙ / M'ₙ ≅ H¹_{T'}(M'ₙ)`.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open InverseSequence

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
  (hdual : HasDualizingComplexOnAffineCover X) (F : Stacks.Coherent.CoherentAdicSystems I)
  {T T' : Set X} (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
  (hTY : T ⊆ I.support) (hTT' : T' ⊆ T)
  (himm : ∀ x x' : X, x ∈ I.support → IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
  {U : X.Opens} (hU : IsAffineOpen U)

/-! ### The short exact sequences of sections -/

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The primes of `Γ(X, U)` lying in a specialization-stable subset form a specialization-stable
subset of the spectrum. -/
theorem stableUnderSpecialization_primesIn {S : Set X} (hS : StableUnderSpecialization S) :
    StableUnderSpecialization (primesIn hU S) :=
  hS.preimage hU.fromSpec.continuous

/-- The square of sections induced by a transition of the depth-two improvement. -/
theorem appₗ_extend_comp {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (Stacks.AlgebraicGeometry.QcohLimits.appₗ
        ((canonicalImprovedSystem hdual F hT hT' hTY himm).map f) U).comp
      (Stacks.AlgebraicGeometry.QcohLimits.appₗ
        ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend m) U) =
    (Stacks.AlgebraicGeometry.QcohLimits.appₗ
        ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend n) U).comp
      (Stacks.AlgebraicGeometry.QcohLimits.appₗ ((improvedSystem T hT F.obj).map f) U) := by
  ext s
  have h := extend_comp_universalImprovedMap
    (isUniversal_canonicalDepthTwoImprovement hdual F hT hT' hTY himm) f
  change ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend m ≫
      universalImprovedMap (isUniversal_canonicalDepthTwoImprovement hdual F hT hT' hTY himm) f).app
        U s = (((improvedSystem T hT F.obj).map f) ≫
      (canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend n).app U s
  rw [h]

variable (U) in
/-- The map of short complexes of sections induced by a transition. -/
def sectionsShortComplexMap {m n : ℕᵒᵖ} (f : m ⟶ n) :
    sectionsShortComplex ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend m) U ⟶
      sectionsShortComplex ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend n) U where
  τ₁ := ModuleCat.ofHom
    (Stacks.AlgebraicGeometry.QcohLimits.appₗ ((improvedSystem T hT F.obj).map f) U)
  τ₂ := ModuleCat.ofHom
    (Stacks.AlgebraicGeometry.QcohLimits.appₗ
      ((canonicalImprovedSystem hdual F hT hT' hTY himm).map f) U)
  τ₃ := ModuleCat.ofHom (Submodule.mapQ _ _
    (Stacks.AlgebraicGeometry.QcohLimits.appₗ
      ((canonicalImprovedSystem hdual F hT hT' hTY himm).map f) U) (by
        rintro _ ⟨s, rfl⟩
        refine ⟨Stacks.AlgebraicGeometry.QcohLimits.appₗ ((improvedSystem T hT F.obj).map f) U s,
          ?_⟩
        exact (LinearMap.congr_fun (appₗ_extend_comp hdual F hT hT' hTY himm (U := U) f) s).symm))
  comm₁₂ := ModuleCat.hom_ext (appₗ_extend_comp hdual F hT hT' hTY himm (U := U) f).symm
  comm₂₃ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

variable (U) in
/-- **The inverse system of short exact sequences `0 → M'ₙ → M''ₙ → M''ₙ/M'ₙ → 0`.** -/
public def sectionsShortComplexSystem : ℕᵒᵖ ⥤ ShortComplex (ModuleCat.{u} Γ(X, U)) where
  obj n := sectionsShortComplex ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend n) U
  map f := sectionsShortComplexMap hdual F hT hT' hTY himm U f
  map_id n := by
    ext s
    · change ((improvedSystem T hT F.obj).map (𝟙 n)).app U s = s
      rw [(improvedSystem T hT F.obj).map_id]
      rfl
    · change ((canonicalImprovedSystem hdual F hT hT' hTY himm).map (𝟙 n)).app U s = s
      rw [(canonicalImprovedSystem hdual F hT hT' hTY himm).map_id]
      rfl
    · obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ s
      change Submodule.Quotient.mk
        (((canonicalImprovedSystem hdual F hT hT' hTY himm).map (𝟙 n)).app U s) = _
      rw [(canonicalImprovedSystem hdual F hT hT' hTY himm).map_id]
      rfl
  map_comp f g := by
    ext s
    · change ((improvedSystem T hT F.obj).map (f ≫ g)).app U s = _
      rw [(improvedSystem T hT F.obj).map_comp]
      rfl
    · change ((canonicalImprovedSystem hdual F hT hT' hTY himm).map (f ≫ g)).app U s = _
      rw [(canonicalImprovedSystem hdual F hT hT' hTY himm).map_comp]
      rfl
    · obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ s
      change Submodule.Quotient.mk
        (((canonicalImprovedSystem hdual F hT hT' hTY himm).map (f ≫ g)).app U s) = _
      rw [(canonicalImprovedSystem hdual F hT hT' hTY himm).map_comp]
      rfl

include hTT' in
/-- Each sequence `0 → M'ₙ → M''ₙ → M''ₙ/M'ₙ → 0` is short exact. -/
theorem sectionsShortComplexSystem_shortExact (n : ℕᵒᵖ) :
    ((sectionsShortComplexSystem hdual F hT hT' hTY himm U).obj n).ShortExact := by
  have := mono_canonicalExtend hdual F hT hT' hTY hTT' himm n
  exact sectionsShortComplex_shortExact _ U

/-- Each map `M'ₙ → M''ₙ` is a depth-two embedding with respect to the primes of `Γ(X, U)` lying
in `T'`. -/
theorem isDepthTwoEmbedding_sectionsShortComplexSystem (n : ℕᵒᵖ) :
    Stacks.LocalCohomology.IsDepthTwoEmbedding.{u, u} (primesIn hU T')
      ((sectionsShortComplexSystem hdual F hT hT' hTY himm U).obj n) := by
  set S := canonicalDepthTwoImprovement hdual F hT hT' hTY himm
  have : (S.term n).IsCoherent := (S.extend_isDepthTwoExtension n).1
  have : ((improvedSystem T hT F.obj).obj n).IsCoherent :=
    (isDepthOneQuotient_toImprovedSystem_app T hT F.obj n).1
  have : ((improvedSystem T hT F.obj).obj n).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : (S.term n).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : (S.term n).IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).2
  exact isDepthTwoEmbedding_sections (S.extend n)
    (bijective_stalkMapLinear_canonicalExtend hdual F hT hT' hTY himm n)
    (fun x hx => (S.extend_isDepthTwoExtension n).2.2 x hx) hU

include hTT' in
/-- **`M''ₙ / M'ₙ ≅ H¹_{T'}(M'ₙ)`, naturally in `n`.** -/
public def quotientSectionsIsoLocalCohomologyOne :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    sectionsShortComplexSystem hdual F hT hT' hTY himm U ⋙ ShortComplex.π₃ ≅
      sectionsShortComplexSystem hdual F hT hT' hTY himm U ⋙ ShortComplex.π₁ ⋙
        Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u} Γ(X, U)
          (primesIn hU T') 1 :=
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  Stacks.LocalCohomology.cokernelNatIsoLocalCohomologyOne.{u, u} (primesIn hU T')
    (stableUnderSpecialization_primesIn hU hT') _
    (sectionsShortComplexSystem_shortExact hdual F hT hT' hTY hTT' himm (U := U))
    (isDepthTwoEmbedding_sectionsShortComplexSystem hdual F hT hT' hTY himm hU)

/-! ### The extension data of the sections over an affine open -/

section ExtensionData

variable (U) in
/-- The sections over `U`, as a functor to modules over `Γ(X, U)`. -/
public abbrev sectionsOver : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  _root_.SheafOfModules.evaluation X.ringCatSheaf (op U)

variable (U) in
/-- The module `M = lim Γ(U, ℱₙ)` of formal sections over `U`. -/
public abbrev formalSectionsOver : ModuleCat.{u} Γ(X, U) :=
  limit (F.obj ⋙ sectionsOver U)

variable (U) in
/-- The maps `M → M'ₙ = Γ(U, ℱ'ₙ)`. -/
public def toDepthOneSections (n : ℕ) :
    formalSectionsOver F U →ₗ[Γ(X, U)] (improvedSystem T hT F.obj ⋙ sectionsOver U).obj (op n) :=
  ((limit.π (F.obj ⋙ sectionsOver U) (op n)) ≫
    (sectionsOver U).map ((toImprovedSystem T hT F.obj).app (op n))).hom

variable (U) in
/-- The maps `M → M''ₙ = Γ(U, ℱ''ₙ)`. -/
public def toDepthTwoSections (n : ℕ) :
    formalSectionsOver F U →ₗ[Γ(X, U)]
      (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙ sectionsOver U).obj (op n) :=
  ((limit.π (F.obj ⋙ sectionsOver U) (op n)) ≫
    (sectionsOver U).map ((toCanonicalImprovedSystem hdual F hT hT' hTY himm).app (op n))).hom

include hdual hT' hTY himm in
/-- The map `M → M''ₙ` is the composite of `M → M'ₙ` with the extension map `M'ₙ → M''ₙ`. -/
theorem toDepthTwoSections_apply (n : ℕ) (m : formalSectionsOver F U) :
    toDepthTwoSections hdual F hT hT' hTY himm U n m =
      ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend (op n)).app U
        (toDepthOneSections F hT U n m) := by
  change ((limit.π (F.obj ⋙ sectionsOver U) (op n)) ≫ (sectionsOver U).map
    ((toImprovedSystem T hT F.obj).app (op n) ≫
      (canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend (op n))).hom m = _
  rw [Functor.map_comp]
  rfl

/-- The maps `lim Γ(U, 𝒢ₙ) → M''ₙ` induced by a map `(𝒢ₙ) ⟶ (ℱ''ₙ)` of inverse systems are
compatible with the transition maps of `(M''ₙ)`. -/
private theorem tr_limit_comp_sectionsOver_map {G : ℕᵒᵖ ⥤ X.Modules}
    (φ : G ⟶ canonicalImprovedSystem hdual F hT hT' hTY himm) {n m : ℕ} (h : n ≤ m)
    (x : (limit (G ⋙ sectionsOver U) : ModuleCat.{u} Γ(X, U))) :
    tr (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙ sectionsOver U) h
        ((limit.π (G ⋙ sectionsOver U) (op m) ≫ (sectionsOver U).map (φ.app (op m))).hom x) =
      (limit.π (G ⋙ sectionsOver U) (op n) ≫ (sectionsOver U).map (φ.app (op n))).hom x := by
  have hnat := φ.naturality (homOfLE h).op
  change ((limit.π (G ⋙ sectionsOver U) (op m) ≫
      (sectionsOver U).map (φ.app (op m))) ≫
      (sectionsOver U).map ((canonicalImprovedSystem hdual F hT hT' hTY himm).map
        (homOfLE h).op)).hom x = _
  rw [Category.assoc, ← Functor.map_comp, ← hnat, Functor.map_comp, ← Category.assoc]
  change ((limit.π (G ⋙ sectionsOver U) (op m) ≫ (G ⋙ sectionsOver U).map _) ≫ _).hom x = _
  rw [limit.w]

/-- The maps `M → M''ₙ` are compatible with the transition maps of `(M''ₙ)`. -/
theorem tr_toDepthTwoSections {n m : ℕ} (h : n ≤ m) (x : formalSectionsOver F U) :
    tr (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙ sectionsOver U) h
        (toDepthTwoSections hdual F hT hT' hTY himm U m x) =
      toDepthTwoSections hdual F hT hT' hTY himm U n x :=
  tr_limit_comp_sectionsOver_map hdual F hT hT' hTY himm
    (toCanonicalImprovedSystem hdual F hT hT' hTY himm) h x

include hTT' in
/-- The extension maps `M'ₙ → M''ₙ` on sections over `U` are injective. -/
theorem injective_extend_app (n : ℕ) :
    Function.Injective (((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend
      (op n)).app U) := by
  have := mono_canonicalExtend hdual F hT hT' hTY hTT' himm (op n)
  exact injective_app_of_mono _ U

end ExtensionData

/-! ### The quotient system is the system of `H¹_{T'}` -/

section Quotient

/-- The transition maps of the sections `Γ(U, ℱₙ)` are surjective. -/
private theorem surjective_map_succ_sectionsOver {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : Stacks.Coherent.CoherentAdicSystems I) {U : X.Opens} (hU : IsAffineOpen U) (k : ℕ) :
    Function.Surjective ((F.obj ⋙ sectionsOver U).map (homOfLE (Nat.le_succ k)).op).hom := by
  have : Epi (F.obj.map (homOfLE (Nat.le_succ k)).op) := F.property.epi_map_succ k
  have : (F.obj.obj (op k)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : (F.obj.obj (op (k + 1))).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X _ U hU

omit [AlgebraicGeometry.IsNoetherian X] in
include hU in
/-- The projections `M → Γ(U, ℱₙ)` are surjective. -/
theorem surjective_limitπ_formalSectionsOver (n : ℕ) :
    Function.Surjective (limit.π (F.obj ⋙ sectionsOver U) (op n)).hom :=
  Stacks.Coherent.moduleLimit_projection_surjective _
    (surjective_map_succ_sectionsOver F hU) n

end Quotient

/-! ### The levels of the formal sections -/

section Levels

/-- A coherent adic system as an adic inverse system of quasi-coherent modules. -/
public def adicInverseSystemOf : AdicInverseSystem.{u} where
  X := X
  I := I
  system := F.obj
  isQuasicoherent _ :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  quotientIso := fun n => (F.property.2.2 n).choose
  quotientIso_hom_comp := fun n => (F.property.2.2 n).choose_spec

include hU in
/-- The kernel of `M → Γ(U, ℱₙ)` is `ℐ(U)^{n+1} M`. -/
theorem ker_limitπ_formalSectionsOver (n : ℕ) :
    LinearMap.ker (limit.π (F.obj ⋙ sectionsOver U) (op n)).hom =
      I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) (formalSectionsOver F U)) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  refine Stacks.Coherent.moduleLimit_projection_ker _ (fun k => ?_) (fun k => ?_)
    (Ideal.fg_of_isNoetherianRing _) n
  · exact surjective_map_succ_sectionsOver F hU k
  · exact Stacks.Coherent.adicInverseSystem_transition_ker (adicInverseSystemOf F) ⟨U, hU⟩ k

include hU in
/-- `Γ(U, ℱₙ) ≅ M / ℐ(U)^{n+1} M`. -/
public def levelEquiv (n : ℕ) :
    (formalSectionsOver F U ⧸ I.ideal ⟨U, hU⟩ ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (formalSectionsOver F U))) ≃ₗ[Γ(X, U)]
      (F.obj ⋙ sectionsOver U).obj (op n) :=
  (Submodule.quotEquivOfEq _ _ (ker_limitπ_formalSectionsOver F hU n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_limitπ_formalSectionsOver F hU n))

/-- `levelEquiv` sends the class of `m ∈ M` to its image in `Γ(U, ℱₙ)`. -/
theorem levelEquiv_mk (n : ℕ) (m : formalSectionsOver F U) :
    levelEquiv F hU n (Submodule.Quotient.mk m) = limit.π (F.obj ⋙ sectionsOver U) (op n) m :=
  rfl

end Levels


/-! ### The extension data of a model of the depth-one quotients -/

section Model

/-- **A model of the depth-one quotients in `Coh(X, ℐ)`**, as produced in the proof of
[Stacks, Tag 0EJE]: an object `(𝒢ₙ)` of `Coh(X, ℐ)` with a map `κ : (𝒢ₙ) ⟶ (ℱ'ₙ)` and maps
`πₘ : ℱ'_{μ(m)} → 𝒢ₘ` inverting it up to transition maps. -/
public structure DepthOneAdicModel where
  /-- The object of `Coh(X, ℐ)`. -/
  G : Stacks.Coherent.CoherentAdicSystems I
  /-- The map to the depth-one quotients. -/
  κ : G.obj ⟶ improvedSystem T hT F.obj
  /-- The reindexing of the inverse maps. -/
  μ : ℕ → ℕ
  le_μ : ∀ n, n ≤ μ n
  monotone_μ : Monotone μ
  /-- The inverse maps up to transition maps. -/
  π : ∀ m, (improvedSystem T hT F.obj).obj (op (μ m)) ⟶ G.obj.obj (op m)
  π_κ : ∀ m, π m ≫ κ.app (op m) = (improvedSystem T hT F.obj).map (homOfLE (le_μ m)).op
  map_π : ∀ {m m' : ℕ} (h : m ≤ m'),
    (improvedSystem T hT F.obj).map (homOfLE (monotone_μ h)).op ≫ π m =
      π m' ≫ G.obj.map (homOfLE h).op
  κ_π : ∀ m, κ.app (op (μ m)) ≫ π m = G.obj.map (homOfLE (le_μ m)).op

variable (Mo : DepthOneAdicModel F hT)

/-- The extension maps `ℱ'ₙ ⟶ ℱ''ₙ` as a map of inverse systems. -/
public def extendNatTrans :
    improvedSystem T hT F.obj ⟶ canonicalImprovedSystem hdual F hT hT' hTY himm where
  app n := (canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend n
  naturality _ _ f := (extend_comp_universalImprovedMap
    (isUniversal_canonicalDepthTwoImprovement hdual F hT hT' hTY himm) f).symm

variable (U) in
/-- The maps `M_𝒢 → M''ₙ`, `M_𝒢 = lim Γ(U, 𝒢ₙ)`. -/
public def modelSections (n : ℕ) :
    formalSectionsOver Mo.G U →ₗ[Γ(X, U)]
      (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙ sectionsOver U).obj (op n) :=
  ((limit.π (Mo.G.obj ⋙ sectionsOver U) (op n)) ≫
    (sectionsOver U).map ((Mo.κ ≫ extendNatTrans hdual F hT hT' hTY himm).app (op n))).hom

/-- The map `M_𝒢 → M''ₙ` is the projection to `Γ(U, 𝒢ₙ)` followed by `κ` and the extension map
`M'ₙ → M''ₙ`. -/
theorem modelSections_apply (n : ℕ) (x : formalSectionsOver Mo.G U) :
    modelSections hdual F hT hT' hTY himm U Mo n x =
      ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend (op n)).app U
        ((Mo.κ.app (op n)).app U (limit.π (Mo.G.obj ⋙ sectionsOver U) (op n) x)) := by
  change ((limit.π (Mo.G.obj ⋙ sectionsOver U) (op n)) ≫ (sectionsOver U).map
    (Mo.κ.app (op n) ≫ (canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend (op n))).hom
      x = _
  rw [Functor.map_comp]
  rfl

/-- The maps `M_𝒢 → M''ₙ` are compatible with the transition maps of `(M''ₙ)`. -/
theorem tr_modelSections {n m : ℕ} (h : n ≤ m) (x : formalSectionsOver Mo.G U) :
    tr (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙ sectionsOver U) h
        (modelSections hdual F hT hT' hTY himm U Mo m x) =
      modelSections hdual F hT hT' hTY himm U Mo n x := by
  exact tr_limit_comp_sectionsOver_map hdual F hT hT' hTY himm
    (Mo.κ ≫ extendNatTrans hdual F hT hT' hTY himm) h x

include hTT' hU in
/-- Elements of `M_𝒢` killed at level `μ(n)` lie in `ℐ(U)^{n+1} M_𝒢`. -/
theorem ker_modelSections_le (n : ℕ) :
    LinearMap.ker (modelSections hdual F hT hT' hTY himm U Mo (Mo.μ n)) ≤
      I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) (formalSectionsOver Mo.G U)) := by
  intro x hx
  rw [LinearMap.mem_ker, modelSections_apply] at hx
  have h0 : (Mo.κ.app (op (Mo.μ n))).app U (limit.π (Mo.G.obj ⋙ sectionsOver U) (op (Mo.μ n)) x)
      = 0 := injective_extend_app hdual F hT hT' hTY hTT' himm (Mo.μ n) (hx.trans
        (map_zero (Stacks.AlgebraicGeometry.QcohLimits.appₗ
          ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend (op (Mo.μ n))) U)).symm)
  rw [← ker_limitπ_formalSectionsOver Mo.G hU n, LinearMap.mem_ker]
  have hw := congrArg (fun g => g.hom x) (limit.w (Mo.G.obj ⋙ sectionsOver U)
    (homOfLE (Mo.le_μ n)).op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hw
  rw [← hw]
  change (Mo.G.obj.map (homOfLE (Mo.le_μ n)).op).app U
    (limit.π (Mo.G.obj ⋙ sectionsOver U) (op (Mo.μ n)) x) = 0
  rw [← Mo.κ_π n]
  change (Mo.π n).app U ((Mo.κ.app (op (Mo.μ n))).app U
    (limit.π (Mo.G.obj ⋙ sectionsOver U) (op (Mo.μ n)) x)) = 0
  rw [h0]
  exact map_zero (Stacks.AlgebraicGeometry.QcohLimits.appₗ (Mo.π n) U)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Every compatible family of sections of a coherent adic system comes from the limit. -/
theorem exists_limit_eq (G : Stacks.Coherent.CoherentAdicSystems I)
    (x : ∀ n : ℕ, (G.obj ⋙ sectionsOver U).obj (op n))
    (hx : ∀ n, ((G.obj ⋙ sectionsOver U).map (homOfLE (Nat.le_succ n)).op) (x (n + 1)) = x n) :
    ∃ m : formalSectionsOver G U, ∀ n, limit.π (G.obj ⋙ sectionsOver U) (op n) m = x n :=
  ⟨_, Stacks.Coherent.limit_lift_functorNatSection_π _ x hx⟩

include hTT' in
/-- **The extension data of the sections over an affine open of a model of the depth-one
quotients.** -/
public def modelExtensionData :
    Stacks.AdicSystem.ExtensionData (I.ideal ⟨U, hU⟩)
      (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙ sectionsOver U)
      (formalSectionsOver Mo.G U) where
  μ := modelSections hdual F hT hT' hTY himm U Mo
  μ_tr := tr_modelSections hdual F hT hT' hTY himm Mo
  ann n := affine_smul_top_eq_bot_of_idealPowerMultiple_eq_bot
    (idealPowerMultiple_canonicalImprovedSystem_eq_bot hdual F hT hT' hTY himm n) ⟨U, hU⟩
  H := ⊥
  e := 0
  ann_H := Submodule.smul_bot _
  le_ker _ := bot_le
  kerLevel := Mo.μ
  ker_le n := (ker_modelSections_le hdual F hT hT' hTY hTT' himm hU Mo n).trans le_sup_right
  iInf_ker_le x hx := by
    rw [Submodule.mem_bot]
    refine Concrete.limit_ext (Mo.G.obj ⋙ sectionsOver U) x 0 fun j => ?_
    have hj := ker_modelSections_le hdual F hT hT' hTY hTT' himm hU Mo j.unop (hx (Mo.μ j.unop))
    rw [← ker_limitπ_formalSectionsOver Mo.G hU j.unop, LinearMap.mem_ker] at hj
    rwa [map_zero]
  lift x hx hrange := by
    choose y hy using hrange
    set S := canonicalDepthTwoImprovement hdual F hT hT' hTY himm
    set q : ∀ k, (improvedSystem T hT F.obj ⋙ sectionsOver U).obj (op k) := fun k =>
      (Mo.κ.app (op k)).app U (limit.π (Mo.G.obj ⋙ sectionsOver U) (op k) (y k))
    have hq : ∀ k, (S.extend (op k)).app U (q k) = x k := fun k =>
      (modelSections_apply hdual F hT hT' hTY himm Mo k (y k)).symm.trans (hy k)
    have hqtr : ∀ {k l : ℕ} (hkl : k ≤ l),
        ((improvedSystem T hT F.obj).map (homOfLE hkl).op).app U (q l) = q k := by
      intro k l hkl
      apply injective_extend_app hdual F hT hT' hTY hTT' himm k
      rw [hq]
      have hsq := LinearMap.congr_fun (appₗ_extend_comp hdual F hT hT' hTY himm (U := U)
        (homOfLE hkl).op) (q l)
      refine hsq.symm.trans ?_
      change ((canonicalImprovedSystem hdual F hT hT' hTY himm).map (homOfLE hkl).op).app U
        ((S.extend (op l)).app U (q l)) = x k
      rw [hq l]
      exact hx k l hkl
    set g : ∀ n, (Mo.G.obj ⋙ sectionsOver U).obj (op n) := fun n => (Mo.π n).app U (q (Mo.μ n))
    have hg : ∀ n, ((Mo.G.obj ⋙ sectionsOver U).map (homOfLE (Nat.le_succ n)).op) (g (n + 1)) =
        g n := by
      intro n
      have h1 := congrArg (fun φ => φ.app U (q (Mo.μ (n + 1)))) (Mo.map_π (Nat.le_succ n))
      simp only [Scheme.Modules.Hom.comp_app] at h1
      change (Mo.G.obj.map (homOfLE (Nat.le_succ n)).op).app U ((Mo.π (n + 1)).app U
        (q (Mo.μ (n + 1)))) = (Mo.π n).app U (q (Mo.μ n))
      rw [← hqtr (Mo.monotone_μ (Nat.le_succ n))]
      exact h1.symm
    obtain ⟨m, hm⟩ := exists_limit_eq Mo.G g hg
    refine ⟨m, fun n => ?_⟩
    change modelSections hdual F hT hT' hTY himm U Mo n m = x n
    rw [modelSections_apply, hm, ← hq]
    congr 1
    have h2 := congrArg (fun φ => φ.app U (q (Mo.μ n))) (Mo.π_κ n)
    simp only [Scheme.Modules.Hom.comp_app] at h2
    change (Mo.κ.app (op n)).app U ((Mo.π n).app U (q (Mo.μ n))) = q n
    refine h2.trans ?_
    exact hqtr (Mo.le_μ n)

include hU in
/-- The maps `Γ(U, 𝒢ₙ) → Γ(U, ℱ'ₙ)` are surjective. -/
theorem surjective_κ_app (n : ℕ) : Function.Surjective ((Mo.κ.app (op n)).app U) := by
  have hq := isDepthOneQuotient_toImprovedSystem_app T hT F.obj (op (Mo.μ n))
  have : Epi ((toImprovedSystem T hT F.obj).app (op (Mo.μ n))) := hq.2.1
  have : (F.obj.obj (op (Mo.μ n))).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : (F.obj.obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hq' := isDepthOneQuotient_toImprovedSystem_app T hT F.obj (op n)
  have : Epi ((toImprovedSystem T hT F.obj).app (op n)) := hq'.2.1
  have : ((improvedSystem T hT F.obj).obj (op n)).IsCoherent := hq'.1
  have : ((improvedSystem T hT F.obj).obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : Epi (F.obj.map (homOfLE (Mo.le_μ n)).op) := F.property.epi_map (Mo.le_μ n)
  have hsurj : Function.Surjective ((F.obj.map (homOfLE (Mo.le_μ n)).op ≫
      (toImprovedSystem T hT F.obj).app (op n)).app U) :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
      (F.obj.map (homOfLE (Mo.le_μ n)).op ≫ (toImprovedSystem T hT F.obj).app (op n)) U hU
  intro z
  obtain ⟨w, hw⟩ := hsurj z
  refine ⟨(Mo.π n).app U (((toImprovedSystem T hT F.obj).app (op (Mo.μ n))).app U w), ?_⟩
  have h2 := congrArg (fun φ => φ.app U (((toImprovedSystem T hT F.obj).app (op (Mo.μ n))).app U
    w)) (Mo.π_κ n)
  simp only [Scheme.Modules.Hom.comp_app] at h2
  refine h2.trans (Eq.trans ?_ hw)
  have hnat := congrArg (fun φ => φ.app U w) ((toImprovedSystem T hT F.obj).naturality
    (homOfLE (Mo.le_μ n)).op)
  simp only [Scheme.Modules.Hom.comp_app] at hnat
  exact hnat.symm

include hU in
/-- The image of `M_𝒢 → M''ₙ` is the image of the extension map `M'ₙ → M''ₙ`. -/
theorem range_modelSections (n : ℕ) :
    LinearMap.range (modelSections hdual F hT hT' hTY himm U Mo n) =
      LinearMap.range (Stacks.AlgebraicGeometry.QcohLimits.appₗ
        ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend (op n)) U) := by
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨_, (modelSections_apply hdual F hT hT' hTY himm Mo n m).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨g, rfl⟩ := surjective_κ_app F hT hU Mo n z
    obtain ⟨m, rfl⟩ := surjective_limitπ_formalSectionsOver Mo.G hU n g
    exact ⟨m, modelSections_apply hdual F hT hT' hTY himm Mo n m⟩

include hTT' in
/-- The quotient system of the extension data is the system of cokernels of the sections. -/
public def modelQuotientSystemIso :
    (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).quotientSystem ≅
      sectionsShortComplexSystem hdual F hT hT' hTY himm U ⋙ ShortComplex.π₃ :=
  NatIso.ofComponents
    (fun n => (Submodule.quotEquivOfEq _ _
      (range_modelSections hdual F hT hT' hTY himm hU Mo n.unop)).toModuleIso)
    (fun {m n} f => by
      apply ModuleCat.hom_ext
      apply Submodule.linearMap_qext
      ext y
      rfl)

include hTT' in
/-- **Essential constancy of the quotient system from that of `H¹_{T'}(M'ₙ)`.** -/
public theorem isEssentiallyConstantPro_modelQuotientSystem
    (hβ : letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
        (sectionsShortComplexSystem hdual F hT hT' hTY himm U ⋙ ShortComplex.π₁ ⋙
          Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u} Γ(X, U)
            (primesIn hU T') 1)) :
    CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
      (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).quotientSystem :=
  (hβ.of_iso (quotientSectionsIsoLocalCohomologyOne hdual F hT hT' hTY hTT' himm hU).symm).of_iso
    (modelQuotientSystemIso hdual F hT hT' hTY hTT' himm hU Mo).symm

end Model

end Stacks.Algebraization

end
