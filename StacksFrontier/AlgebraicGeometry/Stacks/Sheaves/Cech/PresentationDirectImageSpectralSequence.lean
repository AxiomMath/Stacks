module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.SmoothCoveringSpectralSequence
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# Higher direct images along a smooth or flat presentation of an algebraic stack

Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of algebraic stacks, with `f`
representable by algebraic spaces. If `f` is surjective and smooth, then for every abelian sheaf
and for every sheaf of `𝒪_𝒳`-modules `𝓕` on the étale site of `𝒳` there is a first-quadrant
spectral sequence on the étale site of `𝒴`
`E₁^{p,q} = R^q(g ∘ fₚ)_* fₚ⁻¹𝓕 ⇒ R^{p+q} g_* 𝓕`,
in abelian sheaves, respectively in sheaves of `𝒪_𝒴`-modules, where `fₚ : 𝒰ₚ ⟶ 𝒳` is the
degree `p` term of the relative Čech nerve of `f`. If `f` is surjective, flat and locally of
finite presentation, the same holds on the fppf sites.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfLocalLift_of_isFlat`: along a surjective,
  flat, locally finitely presented `1`-morphism every object of the target is covered, for the
  fppf topology, by a single morphism from the image of an object of the source.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleDirectImageSpectralSequence`: the
  spectral sequence of abelian sheaves on the étale site, for `f` smooth and surjective.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleModuleDirectImageSpectralSequence`: the
  spectral sequence of sheaves of modules on the étale site, for `f` smooth and surjective.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfDirectImageSpectralSequence`: the
  spectral sequence of abelian sheaves on the fppf site, for `f` flat, locally of finite
  presentation and surjective.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfModuleDirectImageSpectralSequence`: the
  spectral sequence of sheaves of modules on the fppf site, for `f` flat, locally of finite
  presentation and surjective.

## Implementation notes

The four statements are instances of the relative Čech spectral sequences for higher direct
images of abelian sheaves and of sheaves of modules
(`Stacks.RelativeCech.PushforwardSpectralSequenceData`,
`Stacks.RelativeCech.ModulePushforwardSpectralSequenceData`). Their hypotheses hold because `f`
is faithful, `𝒰` has equalizers, and the image of `f` covers `𝒳` locally by singletons.

## References

* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 072D](https://stacks.math.columbia.edu/tag/072D)
* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w a

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Along a surjective, flat, locally finitely presented `1`-morphism of algebraic stacks every
object of the target receives a morphism from the image of an object of the source whose
singleton generates a covering sieve of the fppf topology. -/
alias exists_fppfLocalLift_of_isFlat := exists_fppfLocalLift_singleton

section Modules

variable {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)

/-- The relative Čech spectral sequence for higher direct images of sheaves of modules for a
`1`-morphism `f` of algebraic stacks which is representable by algebraic spaces and whose image
covers every object of the target by a singleton for the topology `τ`, along a further `1`-morphism
`g`. -/
private theorem exists_moduleDirectImageSpectralSequence_of_cover (τ : SiteKind)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hcover : ∀ x : 𝒳.val.val.obj,
      ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
        Sieve.generate (Presieve.singleton α) ∈
          BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ x)
    (𝓕 : SheafOfModules.{max (u + 1) a}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :
    Nonempty (Stacks.RelativeCech.ModulePushforwardSpectralSequenceData.{u, u + 1, u + 1, u + 1,
      u, u, u, a} B S hS 𝒰.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom) τ
      𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
        f.hom.hom.w)
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        g.hom.hom.w) 𝓕) := by
  have : (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hrep
  refine Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData.{u, u + 1, u + 1,
      u + 1, u, u, u, a} B S hS _ _ _ _ _ τ _ _ _ _ _ ?_
    (fun _ => PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE.{
      max (u + 1) a} _) 𝓕
  intro x
  obtain ⟨z, α, hα⟩ := hcover x
  refine ⟨Presieve.singleton α, hα, ?_⟩
  rintro y k ⟨⟩
  exact ⟨z, ⟨Iso.refl _⟩⟩

end Modules

section Etale

variable {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)

/-- Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of algebraic stacks and assume `f`
is representable by algebraic spaces, surjective and smooth. For an abelian sheaf `𝓕` on the étale
site of `𝒳` there is a first-quadrant spectral sequence of abelian sheaves on the étale site of `𝒴`
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ⁻¹𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in the étale topology, where `𝒰ₚ` is the degree `p` term of the
relative Čech nerve of `f`, that is the `(p+1)`-fold fibre product of `𝒰` over `𝒳`, and `fₚ` its
projection to `𝒳`. The first page, the first-quadrant vanishing and the abutment are the fields of
`Stacks.RelativeCech.PushforwardSpectralSequenceData`. -/
@[stacks 072G "part (1)(a): spectral sequence in Ab(𝒴_étale) along a smooth surjective \
presentation"]
theorem exists_etaleDirectImageSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hsmooth : IsSmooth B S hS f)
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.etale)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.PushforwardSpectralSequenceData B S hS 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) SiteKind.etale 𝓕) :=
  exists_etaleDirectImageSpectralSequenceData.{u, w, a} B S hS f g hrep hsurj hsmooth 𝓕

/-- Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of algebraic stacks and assume `f`
is representable by algebraic spaces, surjective and smooth. For a sheaf of `𝒪_𝒳`-modules `𝓕` on
the étale site of `𝒳` there is a first-quadrant spectral sequence of sheaves of `𝒪_𝒴`-modules on
the étale site of `𝒴`
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ⁻¹𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in sheaves of modules for the étale topology, where `𝒰ₚ` is the
degree `p` term of the relative Čech nerve of `f` and `fₚ` its projection to `𝒳`. The first page,
the first-quadrant vanishing and the abutment are the fields of
`Stacks.RelativeCech.ModulePushforwardSpectralSequenceData`. -/
@[stacks 072G "part (1)(b): spectral sequence in Mod(𝒴_étale, 𝒪_𝒴) along a smooth surjective \
presentation"]
theorem exists_etaleModuleDirectImageSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hsmooth : IsSmooth B S hS f)
    (𝓕 : SheafOfModules.{max (u + 1) a} (Stacks.RelativeCech.moduleRingSheaf B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.etale)) :
    Nonempty (Stacks.RelativeCech.ModulePushforwardSpectralSequenceData.{u, u + 1, u + 1, u + 1,
      u, u, u, a} B S hS 𝒰.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)
      SiteKind.etale 𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
        f.hom.hom.w)
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        g.hom.hom.w) 𝓕) :=
  exists_moduleDirectImageSpectralSequence_of_cover.{u, w, a} B S hS f g SiteKind.etale hrep
    (fun x => Stack.exists_etaleLocalLift B S hS f hsurj hsmooth x) 𝓕

end Etale

section Fppf

variable {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)

/-- Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of algebraic stacks and assume `f`
is representable by algebraic spaces, surjective, flat and locally of finite presentation. For an
abelian sheaf `𝓕` on the fppf site of `𝒳` there is a first-quadrant spectral sequence of abelian
sheaves on the fppf site of `𝒴`
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ⁻¹𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in the fppf topology, where `𝒰ₚ` is the degree `p` term of the
relative Čech nerve of `f` and `fₚ` its projection to `𝒳`. The first page, the first-quadrant
vanishing and the abutment are the fields of
`Stacks.RelativeCech.PushforwardSpectralSequenceData`. -/
@[stacks 072G "part (2)(a): spectral sequence in Ab(𝒴) along a flat, locally finitely presented, \
surjective presentation"]
theorem exists_fppfDirectImageSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.PushforwardSpectralSequenceData B S hS 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) SiteKind.fppf 𝓕) :=
  exists_fppfDirectImageSpectralSequenceData.{u, w, a} B S hS f g hrep hsurj hflat hlfp 𝓕

/-- Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of algebraic stacks and assume `f`
is representable by algebraic spaces, surjective, flat and locally of finite presentation. For a
sheaf of `𝒪_𝒳`-modules `𝓕` on the fppf site of `𝒳` there is a first-quadrant spectral sequence of
sheaves of `𝒪_𝒴`-modules on the fppf site of `𝒴`
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ⁻¹𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in sheaves of modules for the fppf topology, where `𝒰ₚ` is the
degree `p` term of the relative Čech nerve of `f` and `fₚ` its projection to `𝒳`. The first page,
the first-quadrant vanishing and the abutment are the fields of
`Stacks.RelativeCech.ModulePushforwardSpectralSequenceData`. -/
@[stacks 072G "part (2)(b): spectral sequence in Mod(𝒪_𝒴) along a flat, locally finitely \
presented, surjective presentation"]
theorem exists_fppfModuleDirectImageSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (𝓕 : SheafOfModules.{max (u + 1) a} (Stacks.RelativeCech.moduleRingSheaf B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf)) :
    Nonempty (Stacks.RelativeCech.ModulePushforwardSpectralSequenceData.{u, u + 1, u + 1, u + 1,
      u, u, u, a} B S hS 𝒰.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)
      SiteKind.fppf 𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
        f.hom.hom.w)
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        g.hom.hom.w) 𝓕) :=
  exists_moduleDirectImageSpectralSequence_of_cover.{u, w, a} B S hS f g SiteKind.fppf hrep
    (exists_fppfLocalLift_of_isFlat B S hS f hsurj hflat hlfp) 𝓕

end Fppf

end AlgebraicGeometry.Stack.AlgebraicStacks

end
