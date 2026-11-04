module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.SectionExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDown
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDownUnconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SplittingStep
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalSectionsGeneration
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularityGlobalGeneration
public import StacksCore.Tactic.StacksAttribute

/-!
# The genus does not increase along a proper birational morphism

Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`.
[Stacks, Tag 0CE4] asserts that a birational proper morphism `f : X' ⟶ X` satisfies
`dim_k H¹(X, 𝒪_X) ≥ dim_k H¹(X', 𝒪_{X'})`, and that if moreover `X` is reduced, the map
`H⁰(X, 𝒪_X) ⟶ H⁰(X', 𝒪_{X'})` is surjective and the two dimensions agree, then `f` is an
isomorphism.

## Main results

* `AlgebraicGeometry.isAlgebraic_residueFieldMap_of_isIso_stalkMap`: at a point where the map on
  local rings is an isomorphism, the induced extension of residue fields is algebraic.
* `AlgebraicGeometry.isFinite_of_isProper_of_isBirational`: **a proper birational morphism onto
  a locally Noetherian scheme of dimension at most one is finite.**
* `AlgebraicGeometry.genus_le_of_isProper_of_isBirational`: **the inequality of
  [Stacks, Tag 0CE4]**, that the genus does not increase along a proper birational morphism onto
  a proper scheme of dimension at most one.
* `AlgebraicGeometry.genus_le_of_isProper_of_isBirational_of_isZero`: the same inequality under
  three additional cohomological hypotheses.
* `AlgebraicGeometry.isIso_of_isProper_of_isBirational_of_genus_eq`: **the equality case of
  [Stacks, Tag 0CE4]**, that a proper birational morphism onto a reduced such `X` which is
  surjective on global sections and preserves `dim_k H¹` is an isomorphism.
* `AlgebraicGeometry.genus_le_and_isIso_of_isProper_of_isBirational`: **[Stacks, Tag 0CE4]**,
  the two assertions together.

## References

* [Stacks Project, Tag 0CE4](https://stacks.math.columbia.edu/tag/0CE4)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Order TopologicalSpace
open Stacks.AlgebraicGeometry.ComponentDegrees
open Stacks.AlgebraicGeometry.CurveEulerBridge
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent
open Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport

universe u

namespace AlgebraicGeometry

/-- At a point where the map on local rings induced by a morphism of schemes is an isomorphism,
the induced extension of residue fields is algebraic. -/
theorem isAlgebraic_residueFieldMap_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hx : IsIso (f.stalkMap x)) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) := by
  let algRes : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hsq : ((f.residueFieldMap x).hom).comp ((Y.residue (f x)).hom) =
      ((X.residue x).hom).comp ((f.stalkMap x).hom) :=
    congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x)
  have hc : Function.Surjective (((f.residueFieldMap x).hom).comp ((Y.residue (f x)).hom)) := by
    rw [hsq]
    exact IsLocalRing.residue_surjective.comp
      (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).surjective
  refine ⟨fun a ↦ ?_⟩
  obtain ⟨b, rfl⟩ := hc a
  exact isAlgebraic_algebraMap ((Y.residue (f x)).hom b)

/-- **A proper birational morphism onto a locally Noetherian scheme of dimension at most one is
finite.** -/
theorem isFinite_of_isProper_of_isBirational {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (hf : IsBirational f) (hY : topologicalKrullDim Y ≤ 1) :
    IsFinite f := by
  have key : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := by
    intro y
    have hstalk : ringKrullDim (Y.presheaf.stalk y) ≤ 1 := by
      rw [ringKrullDim_stalk_eq_coheight]
      calc (coheight y : WithBot ℕ∞)
          ≤ topologicalKrullDim (Y : Type u) := by
            rw [topologicalKrullDim,
              krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := (Y : Type u)))]
            exact coheight_le_krullDim y
        _ ≤ 1 := hY
    exact exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one f y hstalk
      (Or.inl fun η hη ↦ isAlgebraic_residueFieldMap_of_isIso_stalkMap f η (hf.2 η hη))
  have : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict key

variable (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) {X' : Scheme.{u}}

/-- **The inequality of [Stacks, Tag 0CE4].** For `X` proper of dimension at most one over a
field `k` and `f : X' ⟶ X` proper birational, `dim_k H¹(X', 𝒪_{X'}) ≤ dim_k H¹(X, 𝒪_X)`. -/
theorem genus_le_of_isProper_of_isBirational [IsProper g] (f : X' ⟶ X) [IsProper f]
    (hf : IsBirational f) (hX : topologicalKrullDim (X : Type u) ≤ 1) :
    genus (f ≫ g) ≤ genus g := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k g
  have : IsFinite f := isFinite_of_isProper_of_isBirational f hf hX
  obtain ⟨V, hVd, hViso⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian f hf
  have : IsIso (pullback.snd f V.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V]; infer_instance
  exact genus_le_of_isFinite_of_isClosedImmersion_over_dense_open k g f hX V hVd inferInstance

/-- **The inequality of [Stacks, Tag 0CE4], under three cohomological hypotheses.** Let `X` be a
proper scheme of dimension at most one over a field `k` and let `f : X' ⟶ X` be a proper
birational morphism. If `H¹(X, coker(𝒪_X ⟶ f_*𝒪_{X'})) = 0`, if
`H²(X, ker(𝒪_X ⟶ f_*𝒪_{X'})) = 0` and if `H¹(X, 𝒪_X)` is finite dimensional over `k`, then
`dim_k H¹(X', 𝒪_{X'}) ≤ dim_k H¹(X, 𝒪_X)`. -/
theorem genus_le_of_isProper_of_isBirational_of_isZero [IsProper g] (f : X' ⟶ X) [IsProper f]
    (hf : IsBirational f) (hX : topologicalKrullDim X ≤ 1)
    (_hcoker : IsZero (cohomologyOverField k g (cokernel (structureSheafToPushforward f)) 1))
    (_hker : IsZero (cohomologyOverField k g (kernel (structureSheafToPushforward f)) 2))
    (_hfin : FiniteDimensional k (cohomologyOverField k g (structureSheafModule X) 1)) :
    genus (f ≫ g) ≤ genus g :=
  genus_le_of_isProper_of_isBirational k g f hf hX

/-- **The equality case of [Stacks, Tag 0CE4].** Let `X` be a *reduced* proper scheme of
dimension at most one over a field `k` and let `f : X' ⟶ X` be proper birational. If
`H⁰(X, 𝒪_X) ⟶ H⁰(X', 𝒪_{X'})` is surjective and `dim_k H¹(X', 𝒪_{X'}) = dim_k H¹(X, 𝒪_X)`, then
`f` is an isomorphism — the source's `X' = X`. -/
theorem isIso_of_isProper_of_isBirational_of_genus_eq [IsProper g] (f : X' ⟶ X) [IsProper f]
    (hf : IsBirational f) (hX : topologicalKrullDim (X : Type u) ≤ 1) [IsReduced X]
    (hΓ : Function.Surjective f.appTop) (hgenus : genus (f ≫ g) = genus g) : IsIso f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k g
  have : NoetherianSpace (X : Type u) := IsNoetherian.noetherianSpace
  have : IsFinite f := isFinite_of_isProper_of_isBirational f hf hX
  have : IsLocallyNoetherian X' := isLocallyNoetherian_of_isProper_over_field k (f ≫ g)
  have : IsDominant f := hf.isDominant
  have : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have : Mono (structureSheafToPushforward f) := by
    refine Scheme.Modules.mono_of_injective_app _ fun U => ?_
    rw [structureSheafToPushforward_app]
    exact Scheme.Hom.app_injective f U
  obtain ⟨V, hVd, hViso⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian f hf
  have hQ : SheafOfModules.IsCoherent (cokernel (structureSheafToPushforward f)) :=
    isCoherent_cokernel (Scheme.Modules.pushforwardUnitHom f)
  have : (cokernel (structureSheafToPushforward f)).IsCoherent := hQ
  have hgen : ∀ y ∈ genericPointsOne X,
      y ∉ _root_.SheafOfModules.supp (cokernel (Scheme.Modules.pushforwardUnitHom f)) :=
    fun y hy => notMem_supp_cokernel_pushforwardUnitHom_of_mem f V
      (Stacks.Topology.mem_of_dense_of_mem_genericPoints V.isOpen hVd
        (mem_genericPointsOne_iff.mp hy).1)
  have hsupp : topologicalKrullDim
      (_root_.SheafOfModules.supp (cokernel (structureSheafToPushforward f)) : Set X) ≤ 0 :=
    topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hX
      (cokernel (Scheme.Modules.pushforwardUnitHom f)) hQ hgen
  have hSE : (ShortComplex.cokernelSequence (structureSheafToPushforward f)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := show Mono (structureSheafToPushforward f) from inferInstance }
  have : (structureSheafModule X).IsCoherent := isCoherent_unit k g
  have : (pushedForwardStructureSheaf f).IsCoherent :=
    isCoherent_pushforward_of_isFinite f (SheafOfModules.unit X'.ringCatSheaf)
  have : FiniteDimensional k (cohomologyOverField k g (structureSheafModule X) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k g _ 1
  have : FiniteDimensional k (cohomologyOverField k g (pushedForwardStructureSheaf f) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k g _ 1
  have hgX : genus g = Module.finrank k (cohomologyOverField k g (structureSheafModule X) 1) := by
    rw [genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField k g 1).toLinearEquiv.finrank_eq]
  have hgY : genus (f ≫ g) =
      Module.finrank k (cohomologyOverField k g (pushedForwardStructureSheaf f) 1) := by
    rw [genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField k (f ≫ g) 1).toLinearEquiv.finrank_eq,
      finrank_cohomologyOverField_pushforward_of_isAffineHom k f g (structureSheafModule X') 1]
  have hdimeq : Module.finrank k (cohomologyOverField k g (structureSheafModule X) 1) =
      Module.finrank k (cohomologyOverField k g (pushedForwardStructureSheaf f) 1) := by
    rw [← hgX, ← hgY, hgenus]
  have hcoker1 : IsZero
      (cohomologyOverField k g (cokernel (structureSheafToPushforward f)) 1) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k g
      (cokernel (structureSheafToPushforward f)) hsupp 1 Nat.one_pos
  have hcinj : Function.Injective
      ((cohomologyOverFieldMap k g (structureSheafToPushforward f) 1).hom) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimeq).mpr
      (surjective_cohomologyOverFieldMap_f_of_isZero_X₃ k g hSE 1 hcoker1)
  have hsurj0 :
      Function.Surjective (cohomologyOverFieldMap k g (structureSheafToPushforward f) 0) := by
    rwa [surjective_cohomologyOverFieldMap_zero_iff, structureSheafToPushforward_app]
  obtain ⟨d, -, hab, hbc, hca⟩ := exists_cohomologyOverField_longExactSequence k g hSE
  have hb0 : ∀ b, cohomologyOverFieldMap k g
      (cokernel.π (structureSheafToPushforward f)) 0 b = 0 := fun b => (hab 0 b).mpr (hsurj0 b)
  have hdker : ∀ c, d 0 c = 0 → c = 0 := fun c hc => by
    obtain ⟨b, hb⟩ := (hbc 0 c).mp hc
    exact hb.symm.trans (hb0 b)
  have hd0 : ∀ c, d 0 c = 0 := by
    intro c
    have h1 : cohomologyOverFieldMap k g (structureSheafToPushforward f) 1 (d 0 c) = 0 :=
      (hca 0 (d 0 c)).mpr ⟨c, rfl⟩
    exact hcinj (h1.trans (map_zero _).symm)
  have : Subsingleton
      (cohomologyOverField k g (cokernel (structureSheafToPushforward f)) 0 : Type u) :=
    ⟨fun a b => by rw [hdker a (hd0 a), hdker b (hd0 b)]⟩
  have hzero0 : IsZero (cohomologyOverField k g (cokernel (structureSheafToPushforward f)) 0) :=
    ModuleCat.isZero_of_subsingleton _
  have hZ : IsZero (cokernel (structureSheafToPushforward f)) :=
    isZero_of_isZero_cohomologyOverField_zero_of_supp_dim_le_zero g hQ hsupp hzero0
  have : Epi (structureSheafToPushforward f) := Preadditive.epi_of_isZero_cokernel _ hZ
  have : IsIso (structureSheafToPushforward f) := isIso_of_mono_of_epi _
  have happ : ∀ U : X.Opens, IsIso (f.app U) := fun U => by
    have hbij := ConcreteCategory.bijective_of_isIso ((structureSheafToPushforward f).app U)
    rw [structureSheafToPushforward_app] at hbij
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact (MorphismProperty.isomorphisms.iff f).mp
    (IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun _ : Unit => (⊤ : X.Opens)) (by simp) fun _ => (MorphismProperty.isomorphisms.iff _).mpr
        (Stacks.GlueSquishFactor.isIso_of_isAffineHom_of_isIso_app f fun U _ _ => happ U))

/-- Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`. If
`f : X' ⟶ X` is a birational proper morphism, then

  `dim_k H¹(X, 𝒪_X) ≥ dim_k H¹(X', 𝒪_{X'})`,

and if moreover `X` is reduced, `H⁰(X, 𝒪_X) ⟶ H⁰(X', 𝒪_{X'})` is surjective and equality holds,
then `X' = X`.

Here `dim_k H¹` is `AlgebraicGeometry.genus` of the structure morphism, and `X' = X` means that
`f` is an isomorphism of schemes. -/
@[stacks 0CE4]
theorem genus_le_and_isIso_of_isProper_of_isBirational [IsProper g] (f : X' ⟶ X) [IsProper f]
    (hf : IsBirational f) (hX : topologicalKrullDim (X : Type u) ≤ 1) :
    genus (f ≫ g) ≤ genus g ∧
      (IsReduced X → Function.Surjective f.appTop → genus (f ≫ g) = genus g → IsIso f) :=
  ⟨genus_le_of_isProper_of_isBirational k g f hf hX, fun _ hΓ hgenus =>
    isIso_of_isProper_of_isBirational_of_genus_eq k g f hf hX hΓ hgenus⟩

end AlgebraicGeometry

end
