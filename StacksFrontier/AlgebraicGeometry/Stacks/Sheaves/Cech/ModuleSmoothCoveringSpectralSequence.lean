module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentEtaleSheafClause
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers
import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# The Čech spectral sequence of a smooth presentation for sheaves of modules (Stacks 072G)

Let `f : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks which is representable by algebraic
spaces, surjective and smooth, and let `g : 𝒳 ⟶ 𝒴` be any `1`-morphism of algebraic stacks.
For a sheaf of `𝒪_𝒳`-modules `𝓕` on the `τ`-site of `𝒳`, `τ` any of the étale, smooth, syntomic
or fppf topologies, there is a first-quadrant spectral sequence of sheaves of `𝒪_𝒴`-modules
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ^*𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in the `τ`-topology, where `fₚ : 𝒰ₚ ⟶ 𝒳` is the degree `p`
term of the relative Čech nerve of `f`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_moduleDirectImageSpectralSequenceData_of_cover`:
  the spectral sequence for a `1`-morphism representable by algebraic spaces whose image covers
  the target by singletons in the topology `τ`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_moduleDirectImageSpectralSequenceData`:
  **Stacks 072G**, parts (1)(b) and (2)(b) for a smooth surjective presentation, in every
  topology finer than the étale one.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfModuleDirectImageSpectralSequenceData`:
  **Stacks 072G**, part (2)(b), for a flat, locally finitely presented, surjective presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_moduleCechSpectralSequence`:
  the same spectral sequence with its first page and abutment written with the inverse and
  higher direct images `AlgebraicGeometry.Stack.modulePullback` and
  `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` of **Stacks 06WE**, and its convergence
  in the form `CategoryTheory.SpectralSequence.AbutsTo` that part (4) of **Stacks 0132** consumes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.moduleInverseImage_eq_modulePullback`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.moduleDirectImageIso` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.moduleDirectImageRightDerivedIso`: the inverse,
  direct and higher direct images of the relative Čech spectral sequence are those of
  **Stacks 06WE**.
* `Stacks.RelativeLeray.AbutsTo.spectralSequenceAbutsTo`: the two spellings of convergence agree.

## Implementation notes

The spectral sequence is the one of **Stacks 072E**,
`Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData`, read for the strict
presentation `homFunctor f ⋙ p_𝒳` of the source of `f`. That theorem carries five inputs beyond
its geometric ones, all of which are discharged here at the seating of the 2-category of
algebraic stacks, where the total categories have objects in `Type (u + 1)` and morphisms in
`Type u` and the modules have sections in `u + 1`:

* the pushforward of presheaves of modules along each projection of the Čech nerve is a right
  adjoint, which is `PresheafOfModules.isRightAdjoint_pushforward_of_univLE`;
* the pointwise left Kan extensions along the projections exist, because the categories of
  costructured arrows are essentially small in `u + 1`;
* sheafification and enough injectives on each term of the nerve and on `𝒳` come from
  essential smallness of the sites, `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`
  and `AlgebraicGeometry.Stack.enoughInjectives_moduleSheaves`;
* the image of `f` covers `𝒳` locally: for a smooth `f` the étale-local lifts of
  **Stacks 06XH** part (2), `AlgebraicGeometry.Stack.exists_etaleLocalLift`, which generate a
  covering sieve for every topology finer than the étale one; for a flat, locally finitely
  presented `f` the fppf-local lifts read off **Stacks 06QA**.

Faithfulness of the functor of `f` is **Stacks 04Y5** and the equalizers of the source are
part (3) of **Stacks 06WY**.

## References

* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ZeroObject

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A site whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u` admits
sheafification of abelian sheaves at section universe `u + 1`, being essentially small there. -/
theorem hasSheafify_succ {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    (J : GrothendieckTopology 𝒜) : HasSheafify J AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒜 := inferInstance
  hasSheafifyEssentiallySmallSite _ _

/-- On a site whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u`, the local
isomorphisms of abelian sheaves at section universe `u + 1` are the locally bijective
morphisms, the site being essentially small there. -/
theorem wEqualsLocallyBijective_succ {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    (J : GrothendieckTopology 𝒜) : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒜 := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

attribute [local instance] hasSheafify_succ wEqualsLocallyBijective_succ

/-- Sheaves of modules on the `τ`-site of a category fibred in groupoids whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u` have enough injectives at section universe
`u + 1`. -/
theorem enoughInjectives_moduleRingSheaf {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    (p : 𝒜 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS p hp τ)) :=
  enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p hp _ _

attribute [local instance] enoughInjectives_moduleRingSheaf
  Stacks.RelativeCech.moduleDirectImage_additive

section Cover

variable {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴) (τ : SiteKind)

/-- The relative Čech spectral sequence of **Stacks 072E** for sheaves of modules, for a
`1`-morphism `f : 𝒰 ⟶ 𝒳` of algebraic stacks which is representable by algebraic spaces and
whose image covers every object of `𝒳` by a singleton for the topology `τ`, and a further
`1`-morphism `g : 𝒳 ⟶ 𝒴` along which the higher direct images are taken. The source of `f` is
presented strictly, by `homFunctor f ⋙ p_𝒳`. -/
theorem exists_moduleDirectImageSpectralSequenceData_of_cover
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hcover : ∀ x : 𝒳.val.val.obj,
      ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
        Sieve.generate (Presieve.singleton α) ∈
          BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ x)
    (𝓕 : SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :
    Nonempty (Stacks.RelativeCech.ModulePushforwardSpectralSequenceData.{u, u + 1, u + 1, u + 1,
      u, u, u, u} B S hS (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p) 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) τ
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids (isFibredOneMorphism_homFunctor_comp B S hS f.hom)
      (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) 𝓕) := by
  have : (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hrep
  refine Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData.{u, u + 1, u + 1,
      u + 1, u, u, u, u}
    B S hS (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p) 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom) τ
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids (isFibredOneMorphism_homFunctor_comp B S hS f.hom)
    (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) ?_ ?_ 𝓕
  · intro x
    obtain ⟨z, α, hα⟩ := hcover x
    refine ⟨Presieve.singleton α, hα, ?_⟩
    rintro y k ⟨⟩
    exact ⟨z, ⟨Iso.refl _⟩⟩
  · intro n
    exact PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{u + 1}
      (F := Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) n) _

/-- **Stacks 072G, parts (1)(b) and (2)(b), for a smooth presentation.** Let `f : 𝒰 ⟶ 𝒳` and
`g : 𝒳 ⟶ 𝒴` be `1`-morphisms of algebraic stacks with `f` representable by algebraic spaces,
surjective and smooth, and let `τ` be a topology finer than the étale one (the étale, smooth,
syntomic or fppf topology). For a sheaf of `𝒪_𝒳`-modules `𝓕` on the `τ`-site of `𝒳` there is a
first-quadrant spectral sequence of sheaves of `𝒪_𝒴`-modules on the `τ`-site of `𝒴`
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ^*𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in the `τ`-topology, where `fₚ : 𝒰ₚ ⟶ 𝒳` is the degree `p`
term of the relative Čech nerve of `f`. Part (1)(b) is `τ = étale`; the smooth case of
part (2)(b) is `τ = fppf`. -/
theorem exists_moduleDirectImageSpectralSequenceData
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hsmooth : IsSmooth B S hS f)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (𝓕 : SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :
    Nonempty (Stacks.RelativeCech.ModulePushforwardSpectralSequenceData.{u, u + 1, u + 1, u + 1,
      u, u, u, u} B S hS (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p) 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) τ
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids (isFibredOneMorphism_homFunctor_comp B S hS f.hom)
      (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) 𝓕) :=
  exists_moduleDirectImageSpectralSequenceData_of_cover B S hS f g τ hrep (fun x => by
    obtain ⟨z, α, hα⟩ := Stack.exists_etaleLocalLift B S hS f hsurj hsmooth x
    exact ⟨z, α, associatedTopology_mono B S hS 𝒳.val.val.p hτ _ hα⟩) 𝓕

/-- **Stacks 072G, part (2)(b).** Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be `1`-morphisms of algebraic
stacks with `f` representable by algebraic spaces, surjective, flat and locally of finite
presentation. For a sheaf of `𝒪_𝒳`-modules `𝓕` on the fppf site of `𝒳` there is a first-quadrant
spectral sequence of sheaves of `𝒪_𝒴`-modules on the fppf site of `𝒴`
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ^*𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in the fppf topology, where `fₚ : 𝒰ₚ ⟶ 𝒳` is the degree `p`
term of the relative Čech nerve of `f`.

The covering input is the singleton form of the fppf-local lifts of **Stacks 06XH**, read off
**Stacks 06QA** (`AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isFlat_isLfp`). -/
theorem exists_fppfModuleDirectImageSpectralSequenceData
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (𝓕 : SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)) :
    Nonempty (Stacks.RelativeCech.ModulePushforwardSpectralSequenceData.{u, u + 1, u + 1, u + 1,
      u, u, u, u} B S hS (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p) 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) .fppf
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids (isFibredOneMorphism_homFunctor_comp B S hS f.hom)
      (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) 𝓕) :=
  exists_moduleDirectImageSpectralSequenceData_of_cover B S hS f g .fppf hrep (fun x => by
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
    exact ⟨k, rfl⟩) 𝓕

end Cover

/-! ### Comparison with the inverse and direct images of Stacks 06WE -/

section Comparison

variable {𝒜 : Type (u + 1)} [Category.{u} 𝒜] {ℬ : Type (u + 1)} [Category.{u} ℬ]
  (p : 𝒜 ⥤ BigFppfOver B S hS) (q : ℬ ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (F : 𝒜 ⥤ ℬ) (hF : F ⋙ q = p)
  (τ : SiteKind)

/-- The inverse image of sheaves of modules used by the relative Čech spectral sequence,
`Stacks.RelativeCech.moduleInverseImage`, is the inverse image of **Stacks 06WE**,
`AlgebraicGeometry.Stack.modulePullback`, at the topology `τ`: both are the pushforward of
sheaves of modules along `F` and the identification of the structure sheaf of the source with
the restriction of that of the target. -/
theorem moduleInverseImage_eq_modulePullback :
    Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u + 1} B S hS p q hp hq F hF
        τ =
      modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p q hp hq F hF (B.baseTopology τ)
        (B.baseTopology_le_topology τ) := by
  unfold Stacks.RelativeCech.moduleInverseImage modulePullback
  congr 1
  exact Sheaf.hom_ext (by simp [ringStructureSheafCoreHom])

/-- The direct image of sheaves of modules used by the relative Čech spectral sequence,
`Stacks.RelativeCech.moduleDirectImage`, is isomorphic to the direct image of **Stacks 06WE**,
`AlgebraicGeometry.Stack.moduleSheafPushforward`, at the topology `τ`: both are right adjoint to
the same inverse image. -/
def moduleDirectImageIso :
    Stacks.RelativeCech.moduleDirectImage.{u, u + 1, u + 1, u, u, u + 1} B S hS p q hp hq F hF
        τ ≅
      moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
        (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  (Stacks.RelativeCech.moduleInverseDirectImageAdjunction.{u, u + 1, u + 1, u, u, u + 1}
      B S hS p q hp hq F hF τ).rightAdjointUniq
    ((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
        (B.baseTopology τ) (B.baseTopology_le_topology τ)).ofNatIsoLeft
      (eqToIso (moduleInverseImage_eq_modulePullback B S hS p q hp hq F hF τ)).symm)

/-- The higher direct images of sheaves of modules used by the relative Čech spectral sequence,
the right derived functors of `Stacks.RelativeCech.moduleDirectImage`, are the higher direct
images `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` of **Stacks 06WE** at the topology
`τ`. -/
def moduleDirectImageRightDerivedIso (n : ℕ) :
    (Stacks.RelativeCech.moduleDirectImage.{u, u + 1, u + 1, u, u, u + 1} B S hS p q hp hq F hF
        τ).rightDerived n ≅
      moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS p q hp hq F hF
        (B.baseTopology τ) (B.baseTopology_le_topology τ) n :=
  Functor.rightDerivedIsoOfIso (moduleDirectImageIso B S hS p q hp hq F hF τ) n

end Comparison

/-! ### The spectral sequence in terms of the higher direct images of Stacks 06WE -/

/-- The convergence of `Stacks.RelativeLeray.AbutsTo` is the convergence
`CategoryTheory.SpectralSequence.AbutsTo` of **Stacks 01F2**: the two definitions have the same
body, so the abutment of a relative Čech spectral sequence can be fed to part (4) of
**Stacks 0132**. -/
theorem _root_.Stacks.RelativeLeray.AbutsTo.spectralSequenceAbutsTo {A : Type*} [Category A]
    [Abelian A] {r₀ : ℤ} {E : CohomologicalSpectralSequence A r₀} {H : ℤ → A}
    (h : Stacks.RelativeLeray.AbutsTo E H) : SpectralSequence.AbutsTo E H :=
  h

section Cover

variable {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴) (τ : SiteKind)

/-- **Stacks 072G, parts (1)(b) and (2)(b)**, with the first page and the abutment written with
the inverse images `AlgebraicGeometry.Stack.modulePullback` and the higher direct images
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` of **Stacks 06WE**. Let `f : 𝒰 ⟶ 𝒳` be a
`1`-morphism of algebraic stacks which is representable by algebraic spaces and whose image
covers every object of `𝒳` by a singleton for the topology `τ`, and let `g : 𝒳 ⟶ 𝒴` be a
`1`-morphism of algebraic stacks. For a sheaf of `𝒪_𝒳`-modules `𝓕` on the `τ`-site of `𝒳` there
is a spectral sequence of sheaves of `𝒪_𝒴`-modules, starting at its first page, with
`E₁^{p,q} ≅ R^q (g ∘ fₚ)_* fₚ^*𝓕` where `fₚ` is the projection of the degree `p` term of the
relative Čech nerve of `f`, vanishing outside the first quadrant, and abutting to
`R^{p+q} g_* 𝓕`. -/
theorem exists_moduleCechSpectralSequence
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hcover : ∀ x : 𝒳.val.val.obj,
      ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
        Sieve.generate (Presieve.singleton α) ∈
          BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ x)
    (𝓕 : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology τ) (B.baseTopology_le_topology τ))) :
    ∃ E : CohomologicalSpectralSequence (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) 1,
      (∀ i j : ℕ, Nonempty ((E.page 1 le_rfl).X ((i : ℤ), (j : ℤ)) ≅
        (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
          (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) i ⋙ 𝒳.val.val.p) 𝒴.val.val.p
          (Stacks.RelativeCech.tupleProjection_comp_isFiberedInGroupoids B S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p) 𝒳.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom)
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒳.val.isFiberedInGroupoids
            (isFibredOneMorphism_homFunctor_comp B S hS f.hom) i)
          𝒴.val.isFiberedInGroupoids
          (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) i ⋙ CatFiberedInGroupoids.homFunctor g.hom)
          (Stacks.RelativeCech.tupleProjection_comp_g_comp_eq B S hS 𝒳.val.val.p 𝒴.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)
            (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
              (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) i)
          (B.baseTopology τ) (B.baseTopology_le_topology τ) j).obj
          ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
            (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
              (CatFiberedInGroupoids.homFunctor f.hom) i ⋙ 𝒳.val.val.p) 𝒳.val.val.p
            (Stacks.RelativeCech.tupleProjection_comp_isFiberedInGroupoids B S hS
              (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p) 𝒳.val.val.p
              (CatFiberedInGroupoids.homFunctor f.hom)
              (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒳.val.isFiberedInGroupoids
              (isFibredOneMorphism_homFunctor_comp B S hS f.hom) i)
            𝒳.val.isFiberedInGroupoids
            (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
              (CatFiberedInGroupoids.homFunctor f.hom) i) rfl
            (B.baseTopology τ) (B.baseTopology_le_topology τ)).obj 𝓕))) ∧
      (∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((E.page 1 le_rfl).X (i, j))) ∧
      SpectralSequence.AbutsTo E (fun n : ℤ => if n < 0 then 0 else
        (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
          (B.baseTopology τ) (B.baseTopology_le_topology τ) n.toNat).obj 𝓕) := by
  obtain ⟨D⟩ := exists_moduleDirectImageSpectralSequenceData_of_cover B S hS f g τ hrep hcover 𝓕
  refine ⟨D.sequence, fun i j => ⟨D.pageOneIso i j ≪≫
    (moduleDirectImageRightDerivedIso B S hS _ _ _ _ _ _ τ j).app _ ≪≫
    eqToIso (congrArg (fun G => (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
      _ _ _ _ _ (Stacks.RelativeCech.tupleProjection_comp_g_comp_eq B S hS 𝒳.val.val.p
        𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor g.hom)
        (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
          (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) i)
      (B.baseTopology τ) (B.baseTopology_le_topology τ) j).obj (G.obj 𝓕))
      (moduleInverseImage_eq_modulePullback B S hS _ _ _ _ _ rfl τ))⟩,
    D.firstQuadrant, ?_⟩
  refine Stacks.RelativeLeray.AbutsTo.spectralSequenceAbutsTo
    (Stacks.RelativeCech.spectralSequence_abutsTo_of_iso D.sequence D.abutment fun n => ?_)
  split_ifs
  · exact Iso.refl _
  · exact (moduleDirectImageRightDerivedIso B S hS _ _ _ _ _ _ τ n.toNat).app 𝓕

end Cover

end AlgebraicGeometry.Stack.AlgebraicStacks

end
