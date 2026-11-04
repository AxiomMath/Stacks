module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.SmoothCoveringSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts

/-!
# The relative Čech spectral sequence of a smooth presentation, at module coefficients

Let `c : 𝒰 ⟶ 𝒳` and `f : 𝒳 ⟶ 𝒴` be `1`-morphisms of algebraic stacks over `S`, with `c`
representable by algebraic spaces, surjective and smooth. For a sheaf of `𝒪`-modules `𝓕` on the
étale site of `𝒳` there is a first-quadrant spectral sequence of sheaves of `𝒪`-modules on the
étale site of `𝒴` whose first page is `Rᵠ(f ∘ cₚ)_* cₚ⁻¹𝓕` and which abuts to `Rᵖ⁺ᵠ f_* 𝓕`.

The source of `f` is presented strictly, by the structure functor
`CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleModuleDirectImageSpectralSequenceData`:
  the spectral sequence, as an instance of
  `Stacks.RelativeCech.ModulePushforwardSpectralSequenceData`.

## References

* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated topology of a category fibred over `(Sch/S)_{fppf}` admits sheafification of
presheaves of abelian groups at universe `u + 1`. -/
instance hasSheafify_bigFppfOverAssociatedTopology_succ {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (τ : SiteKind) :
    HasSheafify (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  hasSheafifyEssentiallySmallSite _ _

/-- For the associated topology of a category fibred over `(Sch/S)_{fppf}`, the morphisms of
presheaves of abelian groups at universe `u + 1` that become isomorphisms after sheafification are
exactly the locally bijective ones. -/
instance wEqualsLocallyBijective_bigFppfOverAssociatedTopology_succ {𝒳 : Type (u + 1)}
    [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The topology induced on a category over `(Sch/S)_{fppf}` by a Grothendieck topology `τ` on
schemes admits sheafification of presheaves of abelian groups at universe `u + 1`. -/
instance hasSheafify_stackAssociatedTopology_succ {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (τ : GrothendieckTopology B.Schemes) :
    HasSheafify (Stack.associatedTopology B S hS p τ) AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  hasSheafifyEssentiallySmallSite _ _

/-- For the topology induced on a category over `(Sch/S)_{fppf}` by a Grothendieck topology `τ`
on schemes, the morphisms of presheaves of abelian groups at universe `u + 1` that become
isomorphisms after sheafification are exactly the locally bijective ones. -/
instance wEqualsLocallyBijective_stackAssociatedTopology_succ {𝒳 : Type (u + 1)}
    [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (τ : GrothendieckTopology B.Schemes) :
    (Stack.associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Sheaves of modules on the associated site of a category fibred in groupoids at the universes of
the 2-category of algebraic stacks have enough injectives at module universe `u + 1`. -/
theorem enoughInjectives_moduleRingSheaf_succ {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS p hp τ)) :=
  enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p hp _ _

variable {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (c : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)

/-- The strict presentation of the source of `f` is fibred in groupoids. -/
theorem isFiberedInGroupoids_strict :
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p).IsFiberedInGroupoids :=
  isFiberedInGroupoids_homFunctor_comp B S hS f.hom

/-- The strict presentation of the source of `c` over the strict presentation of `𝒳` is fibred
in groupoids. -/
theorem isFiberedInGroupoids_strict₂ :
    (CatFiberedInGroupoids.homFunctor c.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
      𝒴.val.val.p).IsFiberedInGroupoids := by
  rw [CatFiberedInGroupoids.homFunctor_comp_p, CatFiberedInGroupoids.homFunctor_comp_p]
  exact 𝒰.val.isFiberedInGroupoids

/-- Let `c : 𝒰 ⟶ 𝒳` and `f : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of algebraic stacks, with `c`
representable by algebraic spaces, surjective and smooth. For a sheaf of `𝒪`-modules `𝓕` on the
étale site of `𝒳` there is a first-quadrant spectral sequence of sheaves of `𝒪`-modules on the
étale site of `𝒴` with first page `Rᵠ(f ∘ cₚ)_* cₚ⁻¹𝓕` abutting to `Rᵖ⁺ᵠ f_* 𝓕`, all higher
direct images computed in the étale topology. -/
theorem exists_etaleModuleDirectImageSpectralSequenceData
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS c.hom.hom)
    (hsurj : Stack.IsSurjective B S hS c) (hsmooth : IsSmooth B S hS c)
    (𝓕 : SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_strict B S hS f) SiteKind.etale)) :
    Nonempty (Stacks.RelativeCech.ModulePushforwardSpectralSequenceData.{u, u + 1, u + 1,
      u + 1, u, u, u, u + 1} B S hS
      (CatFiberedInGroupoids.homFunctor c.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
        𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor c.hom) (CatFiberedInGroupoids.homFunctor f.hom)
      SiteKind.etale (isFiberedInGroupoids_strict₂ B S hS c f)
      (isFiberedInGroupoids_strict B S hS f) 𝒴.val.isFiberedInGroupoids
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids
        (isFiberedInGroupoids_strict B S hS f) rfl)
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids rfl)
      𝓕) := by
  have : (CatFiberedInGroupoids.homFunctor c.hom).Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS c hrep
  have := enoughInjectives_moduleRingSheaf_succ B S hS _
    (isFiberedInGroupoids_strict B S hS f) SiteKind.etale
  have := fun n : ℕ => enoughInjectives_moduleRingSheaf_succ B S hS _
    (Stacks.RelativeCech.tupleProjection_comp_isFiberedInGroupoids B S hS _ _ _
      (isFiberedInGroupoids_strict₂ B S hS c f) (isFiberedInGroupoids_strict B S hS f)
      (Functor.isFibredOneMorphism_of_isFiberedInGroupoids
        (isFiberedInGroupoids_strict B S hS f) rfl) n) SiteKind.etale
  refine Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData.{u, u + 1, u + 1,
      u + 1, u, u, u, u + 1} B S hS _ _ _ _ _ SiteKind.etale _ _ _ _ _ ?_ ?_ 𝓕
  · intro x
    obtain ⟨z, α, hα⟩ := Stack.exists_etaleLocalLift B S hS c hsurj hsmooth x
    refine ⟨Presieve.singleton α, ?_, ?_⟩
    · rwa [CatFiberedInGroupoids.homFunctor_comp_p]
    · rintro y k ⟨⟩
      exact ⟨z, ⟨Iso.refl _⟩⟩
  · intro n
    exact PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{u + 1} _

end AlgebraicGeometry.Stack.AlgebraicStacks

end
