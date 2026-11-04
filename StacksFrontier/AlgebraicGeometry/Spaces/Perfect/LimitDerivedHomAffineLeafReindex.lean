module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineFinitePresentationFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimitOfSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentedHomotopyPullbackCoherenceConsequences
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnconditionalPullbackData

/-!
# The pseudo-coherent case of Stacks 09RI

Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms, a chosen limit `X` and a chosen index `0` —
is Situation 0DKU for the system `Y_i = X_i` with `X₀ = Y₀` and structure morphism the identity:
the identity is flat and of finite presentation, the square

`X_i --𝟙--> X_i`, `X_i --f_{i0}--> X₀`, `X₀ --𝟙--> X₀`

is cartesian, and the base changes of `X₀ = Y₀` to the later stages and to the limit are the
`X_i` and `X` themselves. Under this reading the system of homomorphism groups of Stacks 09RI is
the system of Stacks 0DKV, so Stacks 0DKV gives the pseudo-coherent case of Stacks 09RI, clause
(2) of the tag: `E₀` pseudo-coherent and `K₀` in `D_QCoh(𝒪_{X₀})` locally of finite Tor
dimension along `𝟙 X₀`. The index type is assumed to lie in the universe of the site and to have
fewer elements than the cofinality `B.cutoff.ord.cof` of the site's size cutoff.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.relativeSituation`: Situation 09RH read as
  Situation 0DKU with `X₀ = Y₀` and `p₀ = 𝟙`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.projHom_eq_homComparison` and
  `trans_eq_homTransition`: the maps to the limit and the transition maps of the system of
  Stacks 09RI are those of Stacks 0DKV on the relative reading.
* `AlgebraicGeometry.Space.DescentSituation.isColim_limitSystem_of_pseudoCoherent`: **the
  pseudo-coherent case of Stacks 09RI**.
* `AlgebraicGeometry.Space.DescentSituation`'s
  `isHomColimit_canonicalDerivedPullbackSystem_of_pseudoCoherent`: the same, in the
  `AlgebraicGeometry.Space.DescentSituation.IsHomColimit` form of the tag's conclusion.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Situation 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Lemma 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-! ### Situation 09RH as Situation 0DKU over itself -/

/-- **Situation 09RH read as Situation 0DKU with `X₀ = Y₀` and `p₀ = 𝟙`.**  The inverse system,
its chosen limit cone and its chosen index are those of Situation 09RH; the flat finitely
presented space over the chosen stage is `X₀` itself with the identity as structure morphism,
and the base changes to the later stages and to the limit are the stages `X_i` and the limit `X`,
each cartesian because two parallel sides of its square are identities. -/
abbrev relativeSituation : RelativeDescentSituation B S hS hZ I where
  Y := D.system
  limitCone := D.limitCone
  isLimit := D.isLimit
  stage_isAlgebraicSpace := D.algebraicSpace
  limit_isAlgebraicSpace := D.limitAlgebraicSpace
  stage_isQuasiCompact := D.quasiCompact
  stage_isQuasiSeparated := D.quasiSeparated
  transition_isAffine _ _ hij := D.transition_affine (homOfLE hij).op
  i₀ := D.base
  X₀ := D.system.obj (op D.base)
  p₀ := 𝟙 _
  initial_isAlgebraicSpace := D.algebraicSpace D.base
  initial_isFlat := isFlat_id B S hS (D.algebraicSpace D.base)
  initial_isFinitePresentation := isFinitePresentation_id B S hS (D.algebraicSpace D.base)
  Xᵢ i _ := D.system.obj (op i)
  stageX_isAlgebraicSpace i _ := D.algebraicSpace i
  toX₀ _ hi := D.system.map (homOfLE hi).op
  toYᵢ i _ := 𝟙 (D.system.obj (op i))
  stage_isPullback _ hi := IsPullback.id_horiz (D.system.map (homOfLE hi).op)
  fᵢⱼ _ _ _ _ hij := D.system.map (homOfLE hij).op
  fᵢⱼ_toYᵢ _ _ _ _ _ := by rw [Category.comp_id, Category.id_comp]
  fᵢⱼ_toX₀ _ _ _ _ _ := by rw [← D.system.map_comp]; rfl
  X := D.limitCone.pt
  X_isAlgebraicSpace := D.limitAlgebraicSpace
  toInitial := D.limitCone.π.app (op D.base)
  toLimit := 𝟙 D.limitCone.pt
  limit_isPullback := IsPullback.id_horiz (D.limitCone.π.app (op D.base))
  fᵢ i _ := D.limitCone.π.app (op i)
  fᵢ_toYᵢ _ _ := by rw [Category.comp_id, Category.id_comp]
  fᵢ_toX₀ _ hi := D.limitCone.w (homOfLE hi).op

/-! ### The two systems of homomorphism groups coincide -/

variable (E₀ K₀ : derivedModules B S hS (D.stage D.base))

/-- **The maps to the limit of Stacks 09RI are those of Stacks 0DKV on the relative reading.**
Both are the derived pullback along the projection `f_i : X ⟶ X_i`, conjugated by the
identification of the factorisation `f_i ≫ f_{i0} = f_0` of
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`. -/
theorem projHom_eq_homComparison (i : D.Stages) :
    D.limitSystem.projHom (canonicalPullbackData B S hS) E₀ K₀ i =
      D.relativeSituation.homComparison
        (DerivedPullbackComposition.canonical B S hS) E₀ K₀ i := by
  funext φ
  rw [projHom_canonicalPullbackData]
  exact (DerivedPullbackComposition.factorHom_eq_comp _ _ _ _ _ _ _ φ).symm

/-- **The transition maps of Stacks 09RI are those of Stacks 0DKV on the relative reading.** -/
theorem trans_eq_homTransition {i j : D.Stages} (h : i ≤ j) :
    D.limitSystem.trans (canonicalPullbackData B S hS) E₀ K₀ i j h =
      D.relativeSituation.homTransition
        (DerivedPullbackComposition.canonical B S hS) E₀ K₀ h := by
  funext φ
  rw [trans_canonicalPullbackData]
  exact (DerivedPullbackComposition.factorHom_eq_comp _ _ _ _ _ _ _ φ).symm

/-- The maps to the limit of Stacks 09RI, for the pullback-pseudofunctor datum of the total left
derived functor, are those of Stacks 0DKV on the relative reading. -/
theorem projHom_smallEtale_eq_homComparison (i : D.Stages) :
    D.limitSystem.projHom (smallEtaleDerivedPullbackData B S hS) E₀ K₀ i =
      D.relativeSituation.homComparison
        (DerivedPullbackComposition.canonical B S hS) E₀ K₀ i := by
  rw [← projHom_canonicalPullbackData_eq_smallEtale D.limitSystem E₀ K₀]
  exact projHom_eq_homComparison D E₀ K₀ i

/-- The transition maps of Stacks 09RI, for the pullback-pseudofunctor datum of the total left
derived functor, are those of Stacks 0DKV on the relative reading. -/
theorem trans_smallEtale_eq_homTransition {i j : D.Stages} (h : i ≤ j) :
    D.limitSystem.trans (smallEtaleDerivedPullbackData B S hS) E₀ K₀ i j h =
      D.relativeSituation.homTransition
        (DerivedPullbackComposition.canonical B S hS) E₀ K₀ h := by
  rw [← trans_canonicalPullbackData_eq_smallEtale D.limitSystem E₀ K₀]
  exact trans_eq_homTransition D E₀ K₀ h

/-! ### The pseudo-coherent case of Stacks 09RI -/

/-- **The pseudo-coherent case of Stacks 09RI**, clause (2) of the tag. In Situation 09RH,
indexed by a directed preorder `I` in the universe of the site with fewer elements than the
cofinality of the site's size cutoff, let `E₀` and `K₀` be objects of `D(𝒪_{X₀})` with `E₀`
pseudo-coherent and `K₀` in `D_QCoh(𝒪_{X₀})` of locally finite Tor dimension. Then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`

is bijective. -/
theorem isColim_limitSystem_of_pseudoCoherent (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (hE : IsPseudoCoherentObject E₀) (hK : IsInQuasicoherentDerived (D.stage D.base) K₀)
    (hTor : HasLocallyFiniteTorDimensionAlong (𝟙 (D.stage D.base)) K₀) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ := by
  obtain ⟨hsurj, hinj⟩ :=
    RelativeDescentSituation.homDescentOfPseudoCoherent_proved I D.relativeSituation
      (D.relativeSituation.isSchemeLimit_of_size hI) E₀ K₀ hE hK hTor
  refine ⟨fun i j h s =>
    PullbackData.LimitSystem.projHom_trans
      (smallEtaleDerivedPullbackData_isCoherent B S hS) E₀ K₀ h s, fun t => ?_,
    fun i s s' hss => ?_⟩
  · obtain ⟨i, φ, hφ⟩ := hsurj t
    exact ⟨i, φ, by rwa [projHom_smallEtale_eq_homComparison]⟩
  · obtain ⟨j, h, hj⟩ := hinj i s s' (by rwa [projHom_smallEtale_eq_homComparison] at hss)
    exact ⟨j, h, by rwa [trans_smallEtale_eq_homTransition]⟩

/-- **The pseudo-coherent case of Stacks 09RI, in the `IsHomColimit` form of the tag's
conclusion**: `Hom_{D(𝒪_X)}(E, K)` is the filtered colimit of the `Hom_{D(𝒪_{X_i})}(E_i, K_i)`
for the system of derived pullbacks of Situation 09RH with the canonical comparisons. -/
theorem isHomColimit_canonicalDerivedPullbackSystem_of_pseudoCoherent
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (hE : IsPseudoCoherentObject E₀) (hK : IsInQuasicoherentDerived (D.stage D.base) K₀)
    (hTor : HasLocallyFiniteTorDimensionAlong (𝟙 (D.stage D.base)) K₀) :
    IsHomColimit D.canonicalDerivedPullbackSystem E₀ K₀ :=
  (isHomColimit_canonicalDerivedPullbackSystem_iff D E₀ K₀).2
    (isColim_limitSystem_of_pseudoCoherent D E₀ K₀ hI hE hK hTor)

/-- **The pseudo-coherent case of Stacks 09RI**, with `E₀` a pseudo-coherent object of the small
étale ringed site of `X₀` and every cohomology sheaf of `K₀` quasi-coherent. -/
theorem isColim_limitSystem_of_isPseudoCoherent_of_isQuasicoherentOnSite
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (hE : (smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).IsPseudoCoherent E₀)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
        n).obj K₀).IsQuasicoherentOnSite)
    (hTor : HasLocallyFiniteTorDimensionAlong (𝟙 (D.stage D.base)) K₀) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ :=
  isColim_limitSystem_of_pseudoCoherent D E₀ K₀ hI hE hK hTor

end DescentSituation

end AlgebraicGeometry.Space

end
