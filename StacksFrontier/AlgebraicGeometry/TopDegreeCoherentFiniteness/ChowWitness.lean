module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.LerayCollapse
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.OpenRestrictionSurjective
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.SupportedDevissage
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowTwist
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Refinements
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.Finiteness
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A coherent module with finite top cohomology and full support

Let `Z` be an integral scheme, separated and of finite type over a field `k`, of dimension at
most `d`. This file produces a coherent `𝒪_Z`-module `𝒢` whose support contains the generic
point of `Z` and whose cohomology `H^d(Z, 𝒢)` is a finite-dimensional `k`-vector space. This is
the geometric heart of the proof of [Stacks, Tag 0A3M]; the remaining dévissage compares an
arbitrary coherent module with `𝒢`.

The construction is the source's. Chow's lemma ([Stacks, Tag 0200], with the refinement
[Stacks, Tag 0201] making the inverse image of the dense open dense) gives a proper surjection
`π : Y ⟶ Z`, an isomorphism over a dense open `U`, together with an immersion
`j : Y ⟶ ℙⁿ_k`. The pullback `ℒ = j^* 𝒪(1)` is ample relative to `Y ⟶ Spec k`
([Stacks, Tag 01VT]), hence relative to `π` ([Stacks, Tag 0C4L]), so by
[Stacks, Tag 02O1] some twist `ℳ = ℒ^{⊗ n}` has `Rᵖ π_* ℳ = 0` for `p > 0`, and `𝒢 = π_* ℳ` is
coherent ([Stacks, Tag 02O5]). By the Leray spectral sequence ([Stacks, Tag 01F4])
`H^d(Z, 𝒢) = H^d(Y, ℳ)`. Finally `Y` is open in its scheme-theoretic closure `Y̅ ⊆ ℙⁿ_k`, which
is proper over `k` and of dimension at most `d`; `ℳ` extends to a coherent module on `Y̅`
([Stacks, Tag 0G41]) whose top cohomology is finite-dimensional by [Stacks, Tag 02O6] and
surjects onto `H^d(Y, ℳ)` by [Stacks, Tag 0A3G] (2).

The support condition is the stalk computation of `π_* ℳ` at the generic point:
`AlgebraicGeometry.ProperCoherenceWitness.length_stalk_pushforward_chowTwist`.

## Main results

* `TopDegreeFiniteness.finiteDimensional_cohomologyOverField_of_immersion`: top degree cohomology
  of a coherent module on a scheme immersed in `ℙⁿ_k` is finite-dimensional.
* `TopDegreeFiniteness.exists_isCoherent_genericPoint_mem_supp_finiteDimensional`: the module `𝒢`
  above.

## References

* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 0201](https://stacks.math.columbia.edu/tag/0201)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AmpleProjectiveImmersion

universe u

namespace AlgebraicGeometry.TopDegreeFiniteness

attribute [local instance 10000] HasDerivedCategory.standard

variable (k : Type u) [Field k]

/-- A scheme of finite type over a field is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_quasiCompact {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g] : IsNoetherian Y :=
  { __ := LocallyOfFiniteType.isLocallyNoetherian g
    __ := QuasiCompact.compactSpace_of_compactSpace g }

/-- **Top degree cohomology on a scheme immersed in projective space over a field.** Let
`j : Y ⟶ ℙⁿ_k` be an immersion from a Noetherian scheme `Y`, and let `ℳ` be a coherent
`𝒪_Y`-module. If the scheme-theoretic closure of `Y` has dimension at most `d`, then `H^d(Y, ℳ)`
is finite-dimensional over `k`.

`Y` is an open subscheme of its scheme-theoretic image `Y̅`, a closed subscheme of `ℙⁿ_k` and so
proper over `k`; `ℳ` extends to a coherent module `ℳ̅` on `Y̅` by [Stacks, Tag 0G41];
`H^d(Y̅, ℳ̅)` is finite-dimensional by [Stacks, Tag 02O6], and it surjects onto
`H^d(Y, ℳ̅|_Y) = H^d(Y, ℳ)` by [Stacks, Tag 0A3G] (2). -/
theorem finiteDimensional_cohomologyOverField_of_immersion {Y : Scheme.{u}} [IsNoetherian Y]
    {n : ℕ} (j : Y ⟶ ProjectiveSpace n (Spec (.of k))) [IsImmersion j] (M : Y.Modules)
    [M.IsCoherent] (d : ℕ) (hdim : topologicalKrullDim j.image ≤ (d : WithBot ℕ∞)) :
    FiniteDimensional k
      (cohomologyOverField k (j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))) M d) := by
  let p : ProjectiveSpace n (Spec (.of k)) ⟶ Spec (.of k) :=
    ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)
  let p' : j.image ⟶ Spec (.of k) := j.imageι ≫ p
  have : IsOpenImmersion j.toImage := isOpenImmersion_toImage j (.inl inferInstance)
  have : IsProper p' := inferInstance
  have : IsNoetherian j.image := isNoetherian_of_locallyOfFiniteType_quasiCompact k p'
  let W : j.image.Opens := j.toImage.opensRange
  have hW : IsCompact (W : Set j.image) := by
    have : CompactSpace Y := inferInstance
    simpa [W, Scheme.Hom.coe_opensRange] using isCompact_range j.toImage.continuous
  let e : Y ≅ W.toScheme := j.toImage.isoOpensRange
  have he : e.hom ≫ W.ι = j.toImage := Scheme.Hom.isoOpensRange_hom_ι j.toImage
  -- `ℳ` transported to the open `W`.
  have : IsLocallyNoetherian W.toScheme := inferInstance
  let MW : W.toScheme.Modules := (Scheme.Modules.pushforward e.hom).obj M
  have hMW : MW.IsCoherent := ProperCoherenceWitness.isCoherent_pushforward e.hom M
  have : MW.IsQuasicoherent := isQuasicoherent_of_isCoherent MW
  have : MW.IsFiniteType := hMW.isFiniteType
  obtain ⟨Mbar, hqc, hft, ⟨eM⟩⟩ := exists_extension_of_isQuasicoherent_isFiniteType W hW MW
  have : Mbar.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType Mbar
  have hfin : FiniteDimensional k (cohomologyOverField k p' Mbar d) :=
    forall_finiteDimensional_cohomologyOverField_of_isProper k p' Mbar inferInstance d
  have hfinW := finiteDimensional_cohomologyOverField_restrict k p' Mbar d hdim W hW hfin
  have hfinMW : FiniteDimensional k (cohomologyOverField k (W.ι ≫ p') MW d) :=
    Module.Finite.equiv (cohomologyOverFieldIso k (W.ι ≫ p') eM d).toLinearEquiv
  have hstr : j ≫ p = e.hom ≫ W.ι ≫ p' := by
    rw [← Category.assoc, he]
    simp only [p', ← Category.assoc, Scheme.Hom.toImage_imageι]
  rw [show j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) = e.hom ≫ W.ι ≫ p' from hstr]
  exact Module.Finite.equiv
    (cohomologyOverFieldPushforwardIso k e.hom (W.ι ≫ p') M d).symm.toLinearEquiv

/-- The dimension of a dense open subscheme bounds the dimension of a Noetherian scheme locally of
finite type over a field. -/
@[ega "IV 10.6.2" "partial", ega "IV 5.2.5" "special case"]
theorem topologicalKrullDim_le_of_dense_opens {Y : Scheme.{u}} [NoetherianSpace Y]
    (h : Y ⟶ Spec (.of k)) [LocallyOfFiniteType h] (V : Y.Opens) (hV : Dense (V : Set Y)) :
    topologicalKrullDim Y ≤ topologicalKrullDim V.toScheme :=
  Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion k V.ι (V.ι ≫ h)
    h rfl (by simpa only [Scheme.Opens.range_ι] using hV)

/-- **A coherent module with finite top cohomology and full support.** Let `Z` be an integral
scheme, separated and of finite type over a field `k`, of dimension at most `d`. There is a
coherent `𝒪_Z`-module `𝒢` whose support contains the generic point of `Z` and with `H^d(Z, 𝒢)`
finite-dimensional over `k`.

This is the part of the proof of [Stacks, Tag 0A3M] that uses Chow's lemma: `𝒢 = π_* ℳ` for the
modification `π : Y ⟶ Z` of [Stacks, Tag 0200] and [Stacks, Tag 0201] and a twist `ℳ` of the
pullback of `𝒪(1)` along the immersion `Y ⟶ ℙⁿ_k` with vanishing higher direct images
([Stacks, Tag 02O1]); see the module docstring. -/
theorem exists_isCoherent_genericPoint_mem_supp_finiteDimensional {Z : Scheme.{u}}
    [IsIntegral Z] (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated g] (d : ℕ) (hdim : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) :
    ∃ G : Z.Modules, G.IsCoherent ∧ genericPoint Z ∈ SheafOfModules.supp G ∧
      FiniteDimensional k (cohomologyOverField k g G d) := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType_quasiCompact k g
  -- Chow's lemma, with the inverse image of the dense open scheme-theoretically dense.
  obtain ⟨n, X', π, i, U, hπ, -, hi, hcomm, hU, hiso⟩ := hasDenseChowModification g
  have := hπ
  have := hi
  have := hiso
  obtain ⟨Y, ρ, j, hρ, -, hj, hcomm', -, hiso', hdense⟩ :=
    exists_isSchemeTheoreticallyDense_chowModification g π i U hcomm hU hiso
  have := hρ
  have := hj
  have := hiso'
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType_quasiCompact k (ρ ≫ g)
  -- The relatively ample module `ℒ = j^* 𝒪(1)`.
  let L : Y.Modules := (Scheme.Modules.pullback j).obj
    (projectiveSpaceTwistingSheaf n (Spec (.of k)))
  have hLinv : IsInvertibleModule Y L :=
    Stacks.TwistInvertibleOverBase.isInvertibleModule_pullback_projectiveSpaceTwistingSheaf n
      (S := Spec (.of k)) j
  have hLh : Stacks.RelativeAmple.IsRelativelyAmple (ρ ≫ g) L :=
    Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver (ρ ≫ g) L
      inferInstance ⟨1, le_rfl, n, j, hj, hcomm'.symm, ⟨tensorPowModuleOneIso Y _⟩⟩
  have hLρ : Stacks.RelativeAmple.IsRelativelyAmple ρ L :=
    Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp ρ g L hLh inferInstance
  -- The twist killing the higher direct images, [Stacks, Tag 02O1].
  have hO : (unitModule Y).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  open Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing in
  obtain ⟨n₀, hn₀⟩ :=
    exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
      Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.vanishingOverAffineBase ρ (unitModule Y) L hLρ
  let M : Y.Modules :=
    Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y) (tensorPowModule Y L (n₀ : ℤ))
  have hpow : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (tensorPowModule Y L (n₀ : ℤ)) := isInvertibleModule_tensorPowModule Y L (n₀ : ℤ)
  have hMcoh : M.IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible Y
      (unitModule Y) (tensorPowModule Y L (n₀ : ℤ))
  have hMinv : IsInvertibleModule Y M :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules Y (unitModule Y)
      (tensorPowModule Y L (n₀ : ℤ))
  refine ⟨(Scheme.Modules.pushforward ρ).obj M, ProperCoherenceWitness.isCoherent_pushforward ρ M,
    ?_, ?_⟩
  · -- The stalk at the generic point has length one.
    have hgen : IsGenericPoint (genericPoint Z) (Set.range (𝟙 Z : Z ⟶ Z).base) := by
      simpa using genericPoint_spec Z
    have hlen := ProperCoherenceWitness.length_stalk_pushforward_chowTwist (𝟙 Z) ρ U hU M hgen
    rw [Category.comp_id] at hlen
    exact (mem_supp_iff_length_ne_zero _ _).2 (by rw [hlen]; exact one_ne_zero)
  · -- The Leray collapse, and the top cohomology on `Y`.
    refine finiteDimensional_cohomologyOverField_pushforward_of_isZero ρ k g M
      (fun q hq => (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).2
        (hn₀ n₀ q le_rfl hq)) d ?_
    rw [hcomm']
    refine finiteDimensional_cohomologyOverField_of_immersion k j M d ?_
    have : IsOpenImmersion j.toImage := isOpenImmersion_toImage j (.inl inferInstance)
    have : IsProper (j.imageι ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))) :=
      inferInstance
    have : IsNoetherian j.image := isNoetherian_of_locallyOfFiniteType_quasiCompact k
      (j.imageι ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)))
    have h1 : topologicalKrullDim j.image ≤ topologicalKrullDim Y :=
      Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion k j.toImage
        (ρ ≫ g) (j.imageι ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)))
        (by rw [← Category.assoc, Scheme.Hom.toImage_imageι, hcomm']) j.toImage.denseRange
    have h2 : topologicalKrullDim Y ≤ topologicalKrullDim (ρ ⁻¹ᵁ U).toScheme :=
      topologicalKrullDim_le_of_dense_opens k (ρ ≫ g) (ρ ⁻¹ᵁ U)
        (dense_of_isSchemeTheoreticallyDense _ hdense)
    have h3 : topologicalKrullDim (ρ ⁻¹ᵁ U).toScheme = topologicalKrullDim U.toScheme :=
      (Scheme.Hom.homeomorph (ρ ∣_ U)).isHomeomorph.topologicalKrullDim_eq
    have h4 : topologicalKrullDim U.toScheme ≤ topologicalKrullDim Z :=
      topologicalKrullDim_subspace_le Z (U : Set Z)
    exact h1.trans (h2.trans (h3.le.trans (h4.trans hdim)))

end AlgebraicGeometry.TopDegreeFiniteness

end
