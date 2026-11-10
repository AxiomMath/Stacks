module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.ModuleSmoothCoveringSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.SmoothCoveringSpectralSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# The relative Čech spectral sequence of modules along a presentation (Stacks 072G (b))

Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable 1-morphisms of algebraic stacks over `S`, with
`f` representable by algebraic spaces and surjective, and either smooth (part (1), étale
topology) or flat and locally of finite presentation (part (2), fppf topology). For a sheaf of
`𝒪_𝒳`-modules `𝓕` there is a first-quadrant spectral sequence of sheaves of `𝒪_𝒴`-modules

`E₁^{p,q} = R^q(g ∘ fₚ)_* fₚ^*𝓕 ⇒ R^{p+q} g_* 𝓕`,

where `fₚ` is the projection of the degree `p` term of the relative Čech nerve of `f`. This is
parts (1)(b) and (2)(b) of **Stacks 072G**; parts (1)(a) and (2)(a), for abelian sheaves, are
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleDirectImageSpectralSequenceData` and
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfDirectImageSpectralSequenceData`.

The spectral sequence is the one of **Stacks 072E**,
`Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData`, whose hypotheses hold for
algebraic stacks (objects in `Type (u + 1)`, morphisms in `Type u`, module sections in `u + 1`):

* faithfulness of the functor of `f` is **Stacks 04Y5**
  (`AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces`), and the source has
  equalizers, being an algebraic stack;
* the image of `f` covers every object of `𝒳` by a singleton sieve, by **Stacks 06XH** for a
  smooth `f` (`AlgebraicGeometry.Stack.exists_etaleLocalLift`; an étale covering sieve is an
  fppf covering sieve) and by **Stacks 06QA** for a flat, locally finitely presented `f`;
* the right adjoint hypothesis on the restriction of presheaves of modules along the projections
  of the Čech nerve is `PresheafOfModules.isRightAdjoint_pushforward_of_univLE`;
* sheafification and the local-bijectivity description of local isomorphisms hold at section
  universe `u + 1` on every site whose category has objects in `Type (u + 1)` and morphisms in
  `Type u` (`AlgebraicGeometry.Stack.AlgebraicStacks.hasSheafify_succ`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.wEqualsLocallyBijective_succ`), and the module sheaves
  there have enough injectives (`AlgebraicGeometry.Stack.enoughInjectives_moduleSheaves`).

The first page and the abutment are stated with the direct and inverse images of **Stacks 06WE**,
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` and
`AlgebraicGeometry.Stack.modulePullback`, rather than those of the relative Čech construction,
`Stacks.RelativeCech.moduleDirectImage` and `Stacks.RelativeCech.moduleInverseImage`: the two
inverse images are equal
(`AlgebraicGeometry.Stack.relativeCechModuleInverseImage_eq_modulePullback`), so the two direct
images, being right adjoint to them, are isomorphic
(`AlgebraicGeometry.Stack.relativeCechModuleDirectImageIso`), and so are their right derived
functors.

## Main definitions

* `AlgebraicGeometry.Stack.HasModuleCechDirectImageSpectralSequence`: the existence of the
  spectral sequence for `f`, `g`, a topology and a module.

## Main results

* `AlgebraicGeometry.Stack.exists_moduleCechDirectImageSpectralSequence_of_cover`: the spectral
  sequence for a presentation covering its target by singleton sieves of the given topology.
* `AlgebraicGeometry.Stack.exists_etaleModuleCechDirectImageSpectralSequence`: the étale
  spectral sequence along a smooth surjective presentation.
* `AlgebraicGeometry.Stack.exists_fppfModuleCechDirectImageSpectralSequence`: the fppf spectral
  sequence along a flat, locally finitely presented, surjective presentation.
* `AlgebraicGeometry.Stack.exists_fppfModuleCechDirectImageSpectralSequence_of_isSmooth`: the fppf
  spectral sequence along a smooth surjective presentation.

## Implementation notes

The global instances `Stacks.Cohomology.SiteModules.moduleSheavesAbelian`,
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` and
`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` are switched off in this file: their
module universe is a `max` with a free universe, which leaves unification stuck at module universe
`u + 1`. The abelian structure used is Mathlib's on sheaves of modules, from the two
sheafification instances above; the instances it is built from are propositions, so it agrees with
any other such structure definitionally.

## References

* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Stack

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparison

variable {𝒜 : Type (u + 1)} [Category.{u} 𝒜] {ℬ : Type (u + 1)} [Category.{u} ℬ]
  (p : 𝒜 ⥤ BigFppfOver B S hS) (q : ℬ ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : 𝒜 ⥤ ℬ) (hF : F ⋙ q = p) (τ : SiteKind)

/-- The inverse image of sheaves of modules of the relative Čech construction is
`AlgebraicGeometry.Stack.modulePullback`: both are restriction along the functor, with the scalars
moved along the same identification of structure sheaves. -/
theorem relativeCechModuleInverseImage_eq_modulePullback :
    Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, t} B S hS p q hp hq F hF τ =
      modulePullback.{u, u + 1, u, t, u + 1, u} B S hS p q hp hq F hF (B.baseTopology τ)
        (B.baseTopology_le_topology τ) := by
  cases hF
  rfl

/-- The direct image of sheaves of modules of the relative Čech construction is isomorphic to
`AlgebraicGeometry.Stack.moduleSheafPushforward`: both are right adjoint to the same inverse
image. -/
def relativeCechModuleDirectImageIso :
    Stacks.RelativeCech.moduleDirectImage.{u, u + 1, u + 1, u, u, u + 1} B S hS p q hp hq F hF τ ≅
      moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
        (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  ((Stacks.RelativeCech.moduleInverseDirectImageAdjunction.{u, u + 1, u + 1, u, u, u + 1}
      B S hS p q hp hq F hF τ).ofNatIsoLeft
    (eqToIso (relativeCechModuleInverseImage_eq_modulePullback.{u, u + 1}
      B S hS p q hp hq F hF τ))).rightAdjointUniq
    (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
      (B.baseTopology τ) (B.baseTopology_le_topology τ))

end Comparison

section SpectralSequence

attribute [local instance] AlgebraicStacks.hasSheafify_succ
  AlgebraicStacks.wEqualsLocallyBijective_succ

variable {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)

local notation "Tp" => Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
  (CatFiberedInGroupoids.homFunctor f.hom)

/-- The structure functor of the degree `n` term of the relative Čech nerve of a 1-morphism of
algebraic stacks is fibred in groupoids. -/
theorem tupleProjection_comp_isFiberedInGroupoids_homFunctor (n : ℕ) :
    (Tp n ⋙ 𝒳.val.val.p).IsFiberedInGroupoids :=
  Stacks.RelativeCech.tupleProjection_comp_isFiberedInGroupoids B S hS 𝒰.val.val.p
    𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) 𝒰.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      f.hom.hom.w) n

/-- **The relative Čech spectral sequence of modules** for composable 1-morphisms `f : 𝒰 ⟶ 𝒳` and
`g : 𝒳 ⟶ 𝒴` of algebraic stacks, a topology `τ` and a sheaf of modules `𝓕` on `𝒳_τ` at section
universe `u + 1`: a cohomological spectral sequence of sheaves of modules on `𝒴_τ`, starting at its
first page, vanishing outside the first quadrant, with `E₁^{p,q} ≅ R^q(g ∘ fₚ)_* fₚ^*𝓕` for the
projection `fₚ` of the degree `p` term of the relative Čech nerve of `f`, and abutting to a graded
object whose degree `n ≥ 0` term is `Rⁿg_*𝓕`. All direct images are
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`, and the inverse images are
`AlgebraicGeometry.Stack.modulePullback`. -/
abbrev HasModuleCechDirectImageSpectralSequence (τ : SiteKind)
    (𝓕 : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology τ) (B.baseTopology_le_topology τ))) : Prop :=
  ∃ E : CohomologicalSpectralSequence (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) 1,
      (∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((E.page 1).X (i, j))) ∧
      (∀ i j : ℕ, Nonempty ((E.page 1).X ((i : ℤ), (j : ℤ)) ≅
        (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS (Tp i ⋙ 𝒳.val.val.p)
          𝒴.val.val.p (tupleProjection_comp_isFiberedInGroupoids_homFunctor B S hS f i)
          𝒴.val.isFiberedInGroupoids (Tp i ⋙ CatFiberedInGroupoids.homFunctor g.hom)
          (by rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p])
          (B.baseTopology τ) (B.baseTopology_le_topology τ) j).obj
          ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS (Tp i ⋙ 𝒳.val.val.p)
            𝒳.val.val.p (tupleProjection_comp_isFiberedInGroupoids_homFunctor B S hS f i)
            𝒳.val.isFiberedInGroupoids (Tp i) rfl (B.baseTopology τ)
            (B.baseTopology_le_topology τ)).obj 𝓕))) ∧
      ∃ H : ℤ → SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (B.baseTopology τ)
        (B.baseTopology_le_topology τ)),
        SpectralSequence.AbutsTo E H ∧
        ∀ n : ℕ, Nonempty (H (n : ℤ) ≅
          (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p
            𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
            (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
            (B.baseTopology τ) (B.baseTopology_le_topology τ) n).obj 𝓕)

include g in
/-- **The relative Čech spectral sequence of modules for a presentation covering its target by
singleton sieves.** If `f : 𝒰 ⟶ 𝒳` is representable by algebraic spaces and every object of `𝒳`
receives an arrow from the image of an object of `𝒰` generating a covering sieve of the topology
`τ`, then every sheaf of modules on `𝒳_τ` carries the spectral sequence
`AlgebraicGeometry.Stack.HasModuleCechDirectImageSpectralSequence` along `f` and any
`g : 𝒳 ⟶ 𝒴`. -/
theorem exists_moduleCechDirectImageSpectralSequence_of_cover (τ : SiteKind)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hcover : ∀ x : 𝒳.val.val.obj,
      ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
        Sieve.generate (Presieve.singleton α) ∈
          BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ x)
    (𝓕 : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology τ) (B.baseTopology_le_topology τ))) :
    HasModuleCechDirectImageSpectralSequence B S hS f g τ 𝓕 := by
  have : (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
    AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hrep
  have hf := Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      f.hom.hom.w
  have hg := Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      g.hom.hom.w
  have : ∀ n : ℕ, EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS (Tp n ⋙ 𝒳.val.val.p)
        (tupleProjection_comp_isFiberedInGroupoids_homFunctor B S hS f n) τ)) := fun n =>
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS _ _ _ _
  have : EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :=
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS _ _ _ _
  obtain ⟨D⟩ := Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData.{u, u + 1, u + 1,
      u + 1, u, u, u, u + 1}
    B S hS 𝒰.val.val.p 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom) τ
    𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids hf hg
    (fun x => by
      obtain ⟨z, α, hα⟩ := hcover x
      exact ⟨Presieve.singleton α, hα, by rintro y k ⟨⟩; exact ⟨z, ⟨Iso.refl _⟩⟩⟩)
    (fun n => PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{u + 1} _) 𝓕
  refine ⟨D.sequence, D.firstQuadrant, fun i j => ⟨D.pageOneIso i j ≪≫ ?_⟩, _, D.abutment,
    fun n => ⟨?_⟩⟩
  · have hfg : (Tp i ⋙ CatFiberedInGroupoids.homFunctor g.hom) ⋙ 𝒴.val.val.p =
        Tp i ⋙ 𝒳.val.val.p := by
      rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p]
    let := Stacks.RelativeCech.moduleDirectImage_additive.{u, u + 1, u + 1, u, u, u + 1} B S hS
      (Tp i ⋙ 𝒳.val.val.p) 𝒴.val.val.p
      (tupleProjection_comp_isFiberedInGroupoids_homFunctor B S hS f i)
      𝒴.val.isFiberedInGroupoids (Tp i ⋙ CatFiberedInGroupoids.homFunctor g.hom) hfg τ
    have e1 := relativeCechModuleInverseImage_eq_modulePullback.{u, u + 1} B S hS
      (Tp i ⋙ 𝒳.val.val.p) 𝒳.val.val.p
      (tupleProjection_comp_isFiberedInGroupoids_homFunctor B S hS f i)
      𝒳.val.isFiberedInGroupoids (Tp i) rfl τ
    exact (Functor.rightDerived _ j).mapIso (eqToIso (by rw [e1])) ≪≫
      (Functor.rightDerivedIsoOfIso (relativeCechModuleDirectImageIso B S hS
        (Tp i ⋙ 𝒳.val.val.p) 𝒴.val.val.p
        (tupleProjection_comp_isFiberedInGroupoids_homFunctor B S hS f i)
        𝒴.val.isFiberedInGroupoids (Tp i ⋙ CatFiberedInGroupoids.homFunctor g.hom) hfg τ) j).app _
  · let := Stacks.RelativeCech.moduleDirectImage_additive.{u, u + 1, u + 1, u, u, u + 1} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom) τ
    simp only [show ¬ ((n : ℤ) < 0) by omega, ite_false, Int.toNat_natCast]
    exact (Functor.rightDerivedIsoOfIso (relativeCechModuleDirectImageIso B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
      τ) n).app _

/-- **Stacks 072G, part (1)(b).** Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable 1-morphisms
of algebraic stacks with `f` representable by algebraic spaces, surjective and smooth. For a
sheaf of `𝒪_𝒳`-modules `𝓕` on `𝒳_étale` there is a first-quadrant spectral sequence of sheaves
of `𝒪_𝒴`-modules on `𝒴_étale`, `E₁^{p,q} = R^q(g ∘ fₚ)_* fₚ^*𝓕 ⇒ R^{p+q}g_*𝓕`, all higher
direct images computed in the étale topology. -/
theorem exists_etaleModuleCechDirectImageSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hsmooth : AlgebraicStacks.IsSmooth B S hS f)
    (𝓕 : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology .etale) (B.baseTopology_le_topology .etale))) :
    HasModuleCechDirectImageSpectralSequence B S hS f g .etale 𝓕 :=
  exists_moduleCechDirectImageSpectralSequence_of_cover B S hS f g .etale hrep
    (fun x => Stack.exists_etaleLocalLift B S hS f hsurj hsmooth x) 𝓕

/-- The fppf version of the relative Čech spectral sequence of modules along a smooth surjective
presentation. -/
theorem exists_fppfModuleCechDirectImageSpectralSequence_of_isSmooth
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hsmooth : AlgebraicStacks.IsSmooth B S hS f)
    (𝓕 : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf))) :
    HasModuleCechDirectImageSpectralSequence B S hS f g .fppf 𝓕 :=
  exists_moduleCechDirectImageSpectralSequence_of_cover B S hS f g .fppf hrep
    (fun x => by
      obtain ⟨z, α, hα⟩ := Stack.exists_etaleLocalLift B S hS f hsurj hsmooth x
      exact ⟨z, α, BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale x hα⟩) 𝓕

/-- Along a surjective, flat, locally finitely presented 1-morphism of algebraic stacks every
object of the target receives a morphism from the image of an object of the source whose
singleton generates a covering sieve of the fppf topology (Stacks 06QA). -/
theorem exists_fppfSingletonLift_of_isFlat
    (hsurj : Stack.IsSurjective B S hS f) (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) (x : 𝒳.val.val.obj) :
    ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
      Sieve.generate (Presieve.singleton α) ∈
        BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf x := by
  obtain ⟨T, m, hm, hm', hm'', z, α, hα⟩ :=
    Stack.exists_scheme_lift_of_isSurjective_isFlat_isLfp B S hS f hsurj hflat hlfp
      (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  refine ⟨z, α, ?_⟩
  refine Functor.generate_singleton_mem_inheritedTopology_of_isHomLift 𝒳.val.val.p
    (BigFppfOver.baseOverTopology B S hS .fppf) α
    (𝒳.val.isFiberedInGroupoids.isStronglyCartesian α) _ hα
    (mem_topology_of_family B S hS (I := PUnit.{u + 2}) (fun _ => T) (fun _ => m)
      (fun _ => hm) (fun _ => hm') (fun t => ⟨PUnit.unit, hm''.1 t⟩)) ?_
  rintro W u ⟨W', k, -, ⟨i⟩, rfl⟩
  exact ⟨k, rfl⟩

/-- **Stacks 072G, part (2)(b).** Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable 1-morphisms
of algebraic stacks with `f` representable by algebraic spaces, surjective, flat and locally of
finite presentation. For a sheaf of `𝒪_𝒳`-modules `𝓕` on `𝒳_fppf` there is a first-quadrant
spectral sequence of sheaves of `𝒪_𝒴`-modules on `𝒴_fppf`,
`E₁^{p,q} = R^q(g ∘ fₚ)_* fₚ^*𝓕 ⇒ R^{p+q}g_*𝓕`, all higher direct images computed in the fppf
topology. -/
theorem exists_fppfModuleCechDirectImageSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (𝓕 : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf))) :
    HasModuleCechDirectImageSpectralSequence B S hS f g .fppf 𝓕 :=
  exists_moduleCechDirectImageSpectralSequence_of_cover B S hS f g .fppf hrep
    (exists_fppfSingletonLift_of_isFlat B S hS f hsurj hflat hlfp) 𝓕

end SpectralSequence

end AlgebraicGeometry.Stack
