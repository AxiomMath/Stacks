module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGeneration
import all StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGeneration
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFactorizationInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalSectionsGeneration
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimensionSupplement
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalSectionsGenerationExtra
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationCoherent

/-!
# Further results on `DualizingTwistGeneration`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGeneration` that need imports
beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ModuleSkyscraper (modulesStalkFunctor)
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace AlgebraicGeometry

/-! ### Untwisting a morphism into a twist -/

section Invertible

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

private theorem exists_tensorInverse_injective_hom_aux (Z : RingedSpace.{u, u})
    (L W M F : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z))
    [Stacks.SheafOfModules.IsInvertible Z.presheaf (structureSheafRing Z).property L]
    (hF : F = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf,
          CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ Z.presheaf
            (CategoryTheory.forget₂ CommRingCat RingCat)
            (structureSheafRing Z).property⟩).obj W).obj L)) :
    ∃ N : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z),
      Stacks.SheafOfModules.IsInvertible Z.presheaf (structureSheafRing Z).property N ∧
      ∀ P : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z),
        P = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf,
              CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ Z.presheaf
                (CategoryTheory.forget₂ CommRingCat RingCat)
                (structureSheafRing Z).property⟩).obj M).obj N) →
        ∃ f : (M ⟶ F) → (P ⟶ W), Function.Injective f := by
  subst hF
  have hL : MonoidalCategory.HasInverse L :=
    Stacks.SheafOfModules.TensorFactorization.hasInverse Z L
  refine ⟨hL.inv, Stacks.SheafOfModules.TensorFactorization.isInvertible_of_tensorInverse Z
    hL.inv hL.hasInverseInv, ?_⟩
  intro P hP
  subst hP
  have hfaith : (MonoidalCategory.tensorRight hL.inv).Faithful :=
    have : (MonoidalCategory.tensorRight hL.inv).IsEquivalence :=
      hL.hasInverseInv.tensorRightEquivalence.isEquivalence_functor
    inferInstance
  let w := MonoidalCategory.associator W L hL.inv ≪≫
    MonoidalCategory.whiskerLeftIso W hL.isoLeft ≪≫ MonoidalCategory.rightUnitor W
  refine ⟨fun v => (MonoidalCategory.tensorRight hL.inv).map v ≫ w.hom, ?_⟩
  intro v₁ v₂ hv
  exact (MonoidalCategory.tensorRight hL.inv).map_injective
    ((Iso.cancel_iso_hom_right _ _ w).mp hv)

end Invertible

/-- An invertible module over a scheme is invertible over its underlying ringed space. -/
private theorem isInvertible_structureSheafRing_of_isInvertible {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf
    X.ringCatSheaf.property L).2 inferInstance

/-- **Morphisms into a twist by an invertible module are morphisms out of the matching twist.**
For an invertible `ℒ` there are a tensor inverse `𝒩` of `ℒ` and an injection
`Hom(ℳ, 𝒲 ⊗ ℒ) ↪ Hom(ℳ ⊗ 𝒩, 𝒲)`, namely `v ↦ (v ⊗ 1_𝒩) ≫ ((𝒲 ⊗ ℒ) ⊗ 𝒩 ≅ 𝒲)`. It is injective
because tensoring by `𝒩` is an equivalence ([Stacks, Tag 0FFM]), and the isomorphism cancelling
`ℒ` against `𝒩` is the associator followed by the inverse and the right unitor.

The two targets are taken as arguments `ℱ` and `𝒫` together with equations identifying them
with the tensor products, so that the two morphism groups are formed at `X.Modules`; written
directly the tensor product sheaf carries its own spelling of the category and the morphism
groups of the conclusion are then not the ones a consumer has. -/
public theorem exists_tensorInverse_injective_hom {X : Scheme.{u}} (L W M F : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hF : F = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (CategoryTheory.forget₂ CommRingCat RingCat)
            X.ringCatSheaf.property⟩).obj W).obj L)) :
    ∃ N : X.Modules, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N ∧
      ∀ P : X.Modules, P = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
            CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
              (CategoryTheory.forget₂ CommRingCat RingCat)
              X.ringCatSheaf.property⟩).obj M).obj N) →
        ∃ f : (M ⟶ F) → (P ⟶ W), Function.Injective f :=
  have := isInvertible_structureSheafRing_of_isInvertible L
  have h := exists_tensorInverse_injective_hom_aux X.toRingedSpace L W M F hF
  h.imp fun _ hN => ⟨(Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf
    X.ringCatSheaf.property _).1 hN.1, hN.2⟩

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-! ### The carried geometric input -/

/-- **The presentation of `ℱ` produced by a section of `ℒ` vanishing at `x`**, as
[Stacks, Tag 0B58] provides it at a closed `k`-rational point of a curve over an infinite field:
an exact sequence `ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` whose quotient `𝒬` is quasi-coherent with zero-dimensional
support and has `d` global sections, and whose first map has image inside `𝔪_x ℱ_x` at `x`. For
`ℱ = ω ⊗ ℒ` the count `d` is the degree of `ℒ`.

The two consequences of the zero-dimensional support that [Stacks, Tag 0B5F] uses —
`AlgebraicGeometry.CohenMacaulayCurveSituation.FirstCohomologyVanishingOnSub` and
`AlgebraicGeometry.CohenMacaulayCurveSituation.IsZeroOnQuotientsWithoutSections` — are not
fields of this structure: `AlgebraicGeometry.CohenMacaulayCurveSituation`
`.epi_globalSectionsHom_comp` proves both from `supp_dim_le` together with the coherence of
`𝒬`. -/
public structure VanishingSectionPresentation (ω F : S.X.Modules) (d : ℤ) (x : S.X) where
  /-- The quotient of `ℱ` by the image of `ω`. -/
  Q : S.X.Modules
  /-- Multiplication by the chosen section of `ℒ`. -/
  α : ω ⟶ F
  /-- The quotient map. -/
  β : F ⟶ Q
  /-- The two maps compose to zero. -/
  comp_eq_zero : α ≫ β = 0
  /-- The sequence `ω ⟶ ℱ ⟶ 𝒬` is exact at `ℱ`. -/
  exact : (ShortComplex.mk α β comp_eq_zero).Exact
  /-- `𝒬` is a quotient of `ℱ`. -/
  epi : Epi β
  /-- `𝒬` is quasi-coherent. -/
  isQuasicoherent : Q.IsQuasicoherent
  /-- The support of `𝒬` has dimension zero. -/
  supp_dim_le : topologicalKrullDim (SheafOfModules.supp Q) ≤ 0
  /-- `𝒬` has `d` global sections. -/
  finrank_cohomology_zero : (Module.finrank S.k (cohomologyOverField S.k S.f Q 0) : ℤ) = d
  /-- The chosen section vanishes at `x`. -/
  range_modulesStalk_le :
    LinearMap.range ((modulesStalkFunctor S.X x).map α).hom ≤
      IsLocalRing.maximalIdeal (S.X.presheaf.stalk x) •
        (⊤ : Submodule (S.X.presheaf.stalk x) ((modulesStalkFunctor S.X x).obj F))

variable {S}

/-- **`dim_k H⁰(X, 𝒬) ≥ 2`**, the first hypothesis of [Stacks, Tag 0B5F]: the quotient has `d`
global sections, and `d` is at least two. -/
public theorem VanishingSectionPresentation.two_le_finrank {ω F : S.X.Modules} {d : ℤ} {x : S.X}
    (D : S.VanishingSectionPresentation ω F d x) (hd : 2 ≤ d) :
    2 ≤ Module.finrank S.k (cohomologyOverField S.k S.f D.Q 0) := by
  have h := D.finrank_cohomology_zero
  omega

/-- **No nonzero coherent submodule of `ℱ` injects into `𝒬`**, the second hypothesis of
[Stacks, Tag 0B5F]: a submodule of `ℱ` injecting into `𝒬` has support inside the support of
`𝒬`, hence of dimension zero, and `ℱ` has no nonzero coherent submodule supported in dimension
zero. -/
public theorem VanishingSectionPresentation.isZero_of_mono {ω F : S.X.Modules} {d : ℤ} {x : S.X}
    (D : S.VanishingSectionPresentation ω F d x)
    (hnosub : S.NoCoherentSubmoduleOfZeroDimensionalSupport F)
    (M : S.X.Modules) (u : M ⟶ F) (hu : Mono u) (hMc : M.IsCoherent)
    (huβ : Mono (u ≫ D.β)) : IsZero M :=
  have := huβ
  hnosub M u hu hMc ((topologicalKrullDim_supp_le_of_supp_subset
    (supp_subset_of_mono (u ≫ D.β))).trans D.supp_dim_le)

/-! ### The carried input, discharged at a twist of a module with duality -/

/-- **A twist of a module with first-cohomology duality has no nonzero coherent submodule
supported in dimension zero.** For an invertible `ℒ` and a module `ω` for which clause (5) of
[Stacks, Tag 0BS2] holds — `Hom(ℳ, ω) ≅ H¹(X, ℳ)^∨` naturally in the quasi-coherent `ℳ` — the
module `ω ⊗ ℒ` satisfies
`AlgebraicGeometry.CohenMacaulayCurveSituation.NoCoherentSubmoduleOfZeroDimensionalSupport`.

A coherent `ℳ` whose support has dimension at most zero has `H¹(X, ℳ) = 0` by the vanishing
clause of [Stacks, Tag 0B3J], so clause (5) makes `Hom(ℳ, ω)` trivial. It is `Hom(ℳ, ω ⊗ ℒ)`
that has to be trivial, and the two agree: tensoring by a tensor inverse `𝒩` of `ℒ` injects
`Hom(ℳ, ω ⊗ ℒ)` into `Hom(ℳ ⊗ 𝒩, ω)` by
`AlgebraicGeometry.exists_tensorInverse_injective_hom`, and `ℳ ⊗ 𝒩 ≅ ℳ` because an invertible
module does not move a coherent module with zero-dimensional support — that is
[Stacks, Tag 0AYT] at rank one,
`AlgebraicGeometry.nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero`. So the
given monomorphism `ℳ ⟶ ω ⊗ ℒ` is zero, and a monomorphism that is zero has zero source. -/
public theorem noSubmoduleOfZeroDimensionalSupport_tensorSheaf (ω L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hdual : S.FirstCohomologyDuality ω) :
    S.NoCoherentSubmoduleOfZeroDimensionalSupport
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
              (CategoryTheory.forget₂ CommRingCat RingCat)
              S.X.ringCatSheaf.property⟩).obj ω).obj L)) := by
  intro M u hu hMc hdim
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have := hMc
  obtain ⟨N, hNinv, hfs⟩ := exists_tensorInverse_injective_hom L ω M _ rfl
  obtain ⟨f, hf⟩ := hfs _ rfl
  obtain ⟨e⟩ : Nonempty (_ ≅ M) := by
    have := hNinv
    exact nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero M hdim N
  have hMq : M.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  have hlin : Subsingleton (cohomologyOverField S.k S.f M 1 →ₗ[S.k] S.k) :=
    have hz := ModuleCat.subsingleton_of_isZero
      (isZero_firstCohomology_of_supp_dim_le_zero hMc hdim)
    ⟨fun a b => LinearMap.ext fun z => by rw [Subsingleton.elim z 0, map_zero, map_zero]⟩
  have hMsub : Subsingleton (M ⟶ ω) := (hdual.dual M hMq).injective.subsingleton
  have hginj : Function.Injective (fun v : M ⟶ _ => e.inv ≫ f v) :=
    fun v₁ v₂ hv => hf ((Iso.cancel_iso_inv_left e _ _).mp hv)
  have hsub := @Function.Injective.subsingleton _ _ _ hginj hMsub
  refine (IsZero.iff_id_eq_zero M).mpr (hu.right_cancellation (𝟙 M) 0 ?_)
  exact @Subsingleton.elim _ hsub _ _

/-- **The global sections of `ℱ` generate it modulo the image of `ω`**, by [Stacks, Tag 0B5F]
applied to the presentation of `ℱ` attached to a vanishing section.

[Stacks, Tag 0B5F] reads the zero-dimensional support of `𝒬` itself, so the field
`supp_dim_le` of the vanishing section data is what is passed to it, and coherence of `ℱ` —
quasi-coherence together with `hFft` on the locally Noetherian `X` — is what it needs of `ℱ`.
It proves the vanishing of `H²(X, -)` rather than consuming it, so no such hypothesis is taken
here or in the three results below. -/
public theorem VanishingSectionPresentation.epi_globalSections_quotient {ω F : S.X.Modules} {d : ℤ}
    {x : S.X} (D : S.VanishingSectionPresentation ω F d x) (hωq : ω.IsQuasicoherent)
    (hFq : F.IsQuasicoherent) (hFft : F.IsFiniteType) (hdual : S.FirstCohomologyDuality ω)
    (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
    (hnosub : S.NoCoherentSubmoduleOfZeroDimensionalSupport F) (hd : 2 ≤ d) :
    Epi (globalSectionsHom F ≫ D.β) :=
  have := D.epi
  epi_globalSectionsHom_comp_of_isCoherent hωq hFq hFft D.isQuasicoherent hdual hone D.α D.β
    D.comp_eq_zero D.exact D.supp_dim_le (D.two_le_finrank hd)
    (fun M u hc hu hm => D.isZero_of_mono hnosub M u hu hc hm)

/-- **The cokernel of the map from the free module on all global sections of `ℱ` vanishes at
`x`.** The global sections of `ℱ` generate it modulo the image of `ω`, so `ω` surjects onto that
cokernel; the chosen section vanishes at `x`, so the image of `ω_x` lies in `𝔪_x ℱ_x`; Nakayama
finishes. -/
public theorem VanishingSectionPresentation.subsingleton_modulesStalk_cokernel {ω F : S.X.Modules}
    {d : ℤ} {x : S.X} (D : S.VanishingSectionPresentation ω F d x) (hωq : ω.IsQuasicoherent)
    (hFq : F.IsQuasicoherent) (hFft : F.IsFiniteType) (hdual : S.FirstCohomologyDuality ω)
    (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
    (hnosub : S.NoCoherentSubmoduleOfZeroDimensionalSupport F) (hd : 2 ≤ d) :
    Subsingleton ((modulesStalkFunctor S.X x).obj (cokernel (globalSectionsHom F))) :=
  have := D.epi
  subsingleton_modulesStalk_of_epi_of_range_le_maximalIdeal_smul x D.α
    (cokernel.π (globalSectionsHom F))
    (isFiniteType_of_epi (cokernel.π (globalSectionsHom F)) hFft)
    (epi_comp_cokernelπ_of_epi_comp D.α D.β D.comp_eq_zero D.exact (globalSectionsHom F)
      (D.epi_globalSections_quotient hωq hFq hFft hdual hone hnosub hd))
    D.range_modulesStalk_le

/-- **The global sections of `ℱ` generate `ℱ`**, given at every closed point of `X` a section of
`ℒ` vanishing there in the sense of
`AlgebraicGeometry.CohenMacaulayCurveSituation.VanishingSectionPresentation`.

The cokernel `𝒞` of the map from the free module on all global sections of `ℱ` is of finite
type, so its support is closed; were it nonempty it would contain a point closed in the proper
scheme `X`, and at such a point `𝒞` vanishes. -/
public theorem epi_globalSectionsHom_of_forall_isClosed_of_presentation {ω F : S.X.Modules}
    (hωq : ω.IsQuasicoherent) (hFq : F.IsQuasicoherent) (hFft : F.IsFiniteType)
    (hdual : S.FirstCohomologyDuality ω)
    (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
    (hnosub : S.NoCoherentSubmoduleOfZeroDimensionalSupport F) {d : ℤ} (hd : 2 ≤ d)
    (hsec : ∀ x : S.X, IsClosed ({x} : Set S.X) → S.VanishingSectionPresentation ω F d x) :
    Epi (globalSectionsHom F) := by
  have : CompactSpace S.X := QuasiCompact.compactSpace_of_compactSpace S.f
  refine epi_of_isZero_cokernel _ ?_
  refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _ ?_
  by_contra hne
  obtain ⟨x, hx, hxcl⟩ := Stacks.SerreAffinenessCriterion.exists_isClosed_singleton_mem
    (isClosed_supp (cokernel (globalSectionsHom F))
      (isFiniteType_of_epi (cokernel.π (globalSectionsHom F)) hFft))
    (Set.nonempty_iff_ne_empty.mpr hne)
  have hsub := (hsec x hxcl).subsingleton_modulesStalk_cokernel hωq hFq hFft hdual hone
    hnosub hd
  obtain ⟨a, ha⟩ := hx
  exact ha (Subsingleton.elim (α := (modulesStalkFunctor S.X x).obj
    (cokernel (globalSectionsHom F))) a 0)

/-- In Situation [Stacks, Tag 0B5D], let `ω` be a quasi-coherent module with first-cohomology
duality `hdual` and `dim_k H¹(X, ω) = 1`, and let `ℒ` be an invertible module with `deg(ℒ) ≥ 2`.
If `ω ⊗ ℒ` is quasi-coherent of finite type, has no nonzero coherent submodule supported in
dimension zero, and at every closed point `x` has the presentation `hsec` by a section of `ℒ`
vanishing at `x`, then `ω ⊗ ℒ` is generated by its global sections.

The hypothesis `hnosub` follows from `hdual` by `noSubmoduleOfZeroDimensionalSupport_tensorSheaf`,
and `hsec` can hold only over an algebraically closed field. -/
public theorem nonempty_generatingSections_tensorSheaf_of_presentation (ω L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] (hωq : ω.IsQuasicoherent)
    (hdual : S.FirstCohomologyDuality ω)
    (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
    (hFq : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L))).IsQuasicoherent)
    (hFft : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L))).IsFiniteType)
    (hnosub : S.NoCoherentSubmoduleOfZeroDimensionalSupport
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
              (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L))))
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L)
    (hsec : ∀ x : S.X, IsClosed ({x} : Set S.X) →
      S.VanishingSectionPresentation ω ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
              (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L)))
        (invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) x) :
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L))).GeneratingSections :=
  nonempty_generatingSections_of_epi_globalSectionsHom _
    (epi_globalSectionsHom_of_forall_isClosed_of_presentation hωq hFq hFft hdual hone hnosub hd
      hsec)

/-- In Situation [Stacks, Tag 0B5D], let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of
[Stacks, Tag 0BS2] and let `ℒ` be an invertible `𝒪_X`-module with `deg(ℒ) ≥ 2`. If `ω_X ⊗ ℒ` is of
finite type and at every closed point `x` has the presentation `hsec` by a section of `ℒ`
vanishing at `x`, then `ω_X ⊗ ℒ` is generated by its global sections. -/
public theorem nonempty_generatingSections_dualizing_tensorSheaf (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hFft : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
            (CategoryTheory.forget₂ CommRingCat RingCat)
            S.X.ringCatSheaf.property⟩).obj
        (Stacks.Duality.dualizingSheafOverField S.f)).obj L)).IsFiniteType)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L)
    (hsec : ∀ x : S.X, IsClosed ({x} : Set S.X) →
      S.VanishingSectionPresentation (Stacks.Duality.dualizingSheafOverField S.f)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
              CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
                (CategoryTheory.forget₂ CommRingCat RingCat)
                S.X.ringCatSheaf.property⟩).obj
            (Stacks.Duality.dualizingSheafOverField S.f)).obj L))
        (invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) x) :
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf
            (CategoryTheory.forget₂ CommRingCat RingCat)
            S.X.ringCatSheaf.property⟩).obj
        (Stacks.Duality.dualizingSheafOverField S.f)).obj L)).GeneratingSections :=
  have hLq : L.IsQuasicoherent :=
    have := isInvertible_structureSheafRing_of_isInvertible L
    Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible S.X L
  nonempty_generatingSections_tensorSheaf_of_presentation
    (Stacks.Duality.dualizingSheafOverField S.f) L
    (Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f)
    (firstCohomologyDuality_dualizingSheafOverField S)
    (finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one S)
    (@AlgebraicGeometry.tensorSheaf_isQuasicoherent S.X.toRingedSpace _ _
      (Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f) hLq)
    hFft
    (noSubmoduleOfZeroDimensionalSupport_tensorSheaf
      (Stacks.Duality.dualizingSheafOverField S.f) L
      (firstCohomologyDuality_dualizingSheafOverField S))
    hd hsec

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
