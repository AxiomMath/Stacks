module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasicoherentPullbackExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts

/-!
# The relative Leray spectral sequence for 1-morphisms of algebraic stacks

Let `f : 𝒳 → 𝒴` and `g : 𝒴 → 𝒵` be 1-morphisms of categories fibred in groupoids over the big
fppf site of a scheme `S` (for instance of algebraic stacks), and let `ℱ` be a module on the
associated fppf site of `𝒳`. There is a spectral sequence

`E_2^{p,q} = R^p g_*(R^q f_* ℱ)  ⟹  R^{p+q}(g ∘ f)_* ℱ`

of modules on the fppf site of `𝒵`. This is [Stacks, Tag 0734] for the morphisms of ringed topoi
`f` and `g` induce, in the form the cohomology of algebraic stacks uses it, with the direct
images of [Stacks, Tag 06WE] at section universe `u + 1`, where the library constructs them.

## Main definitions

* `AlgebraicGeometry.Stack.modulePullbackCompIso`: the inverse image along a composite is the
  composite of the inverse images.
* `AlgebraicGeometry.Stack.moduleSheafPushforwardCompIso`: the direct image along a composite is
  the composite of the direct images.

## Main results

* `AlgebraicGeometry.Stack.injective_moduleSheafPushforward_obj`: the direct image of an
  injective module is injective, because the inverse image is exact.
* `AlgebraicGeometry.Stack.exists_relativeLeraySpectralSequence_fppfModuleSheafPushforward`: the
  relative Leray spectral sequence for 1-morphisms of categories fibred in groupoids.

## Implementation notes

The source's proof of [Stacks, Tag 0734] goes through the right acyclicity of `f_*I` for an
injective `I` (Stacks 072Z and 0731 (4)). For categories fibred in groupoids a stronger and
simpler fact holds: the inverse image of [Stacks, Tag 06WE] is objectwise restriction, hence
exact, so its right adjoint `f_*` carries injectives to injectives, and the Grothendieck
spectral sequence ([Stacks, Tag 015N]) applies directly.

The library's `RingedTopos` form of [Stacks, Tag 0734],
`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence`, is stated at
`RingedTopos.{u, u, u}` and does not apply to the sites of algebraic stacks, whose objects live in
`Type (u + 1)`; this file is the instance of the same argument at the sites of stacks.

## References

* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m w

namespace AlgebraicGeometry.Stack

attribute [local instance]
  hasSheafify_fppfAssociatedTopology_succ wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  {𝒵 : Type (u + 1)} [Category.{u} 𝒵]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (r : 𝒵 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (g : 𝒴 ⥤ 𝒵) (hg : g ⋙ r = q) (hfg : (f ⋙ g) ⋙ r = p)

/-- **The inverse image along a composite is the composite of the inverse images**, for modules
on the associated fppf sites, in any module universe. Both sides are objectwise restriction
along `f ⋙ g`; once the structure functors are identified the two transports of scalars agree on
the nose. -/
def modulePullbackCompIso :
    modulePullback.{u, u + 1, u, m, u + 1, u} B S hS p r hp hr (f ⋙ g) hfg B.topology
        le_rfl ≅
      modulePullback.{u, u + 1, u, m, u + 1, u} B S hS q r hq hr g hg B.topology le_rfl ⋙
        modulePullback.{u, u + 1, u, m, u + 1, u} B S hS p q hp hq f hf B.topology le_rfl := by
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have : r.IsFibered := hr.isFibered
  have := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (B.topology.over (B.obj hS))).1
  have := ((hr.isFibredOneMorphism hg).isContinuous_and_isCocontinuous_inheritedTopology
    (B.topology.over (B.obj hS))).1
  have := Functor.isContinuous_comp f g (associatedTopology B S hS p B.topology)
    (associatedTopology B S hS q B.topology) (associatedTopology B S hS r B.topology)
  dsimp only [modulePullback]
  refine SheafOfModules.pushforwardCongr ?_ ≪≫ (SheafOfModules.pushforwardComp _ _).symm
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  simp only [Functor.sheafPushforwardContinuous, ObjectProperty.lift_map]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  simp only [Functor.comp_map, ObjectProperty.ι_map, Functor.whiskeringLeft_obj_map,
    ObjectProperty.homMk_hom, Functor.whiskerLeft_app, eqToHom_app, eqToHom_trans]

/-- **The direct image along a composite is the composite of the direct images**, for modules on
the associated fppf sites at section universe `u + 1`: both are right adjoint to the inverse image
along the composite, by `AlgebraicGeometry.Stack.modulePullbackCompIso`. -/
def moduleSheafPushforwardCompIso :
    fppfModuleSheafPushforward B S hS p r hp hr (f ⋙ g) hfg ≅
      fppfModuleSheafPushforward B S hS p q hp hq f hf ⋙
        fppfModuleSheafPushforward B S hS q r hq hr g hg :=
  ((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p r hp hr (f ⋙ g) hfg B.topology
      le_rfl).ofNatIsoLeft
        (modulePullbackCompIso.{u, u + 1} B S hS p q r hp hq hr f hf g hg hfg)).rightAdjointUniq
    ((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS q r hq hr g hg B.topology
      le_rfl).comp
      (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq f hf B.topology le_rfl))

/-- A right adjoint of a finite-limit-preserving functor carries injective objects to injective
objects, since the left adjoint then preserves monomorphisms. -/
private theorem injective_obj_of_preservesFiniteLimits_adjunction
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} [PreservesFiniteLimits L]
    (adj : L ⊣ R) (I : D) (hI : Injective I) : Injective (R.obj I) :=
  have : L.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  @Injective.injective_of_adjoint _ _ _ _ _ _ _ adj I hI

/-- **The direct image of an injective module is injective.** The inverse image of
[Stacks, Tag 06WE] is left exact (`AlgebraicGeometry.Stack.preservesFiniteLimits_modulePullback`),
hence preserves monomorphisms, and a right adjoint of a monomorphism-preserving functor preserves
injective objects. -/
theorem injective_moduleSheafPushforward_obj
    (I : SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hI : Injective I) : Injective ((fppfModuleSheafPushforward B S hS p q hp hq f hf).obj I) :=
  have := preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p q hp hq f hf
    B.topology le_rfl
  injective_obj_of_preservesFiniteLimits_adjunction
    (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq f hf B.topology le_rfl)
    I hI

/-- Modules on the associated fppf site of a category fibred in groupoids have enough injectives
at section universe `u + 1`; this is `AlgebraicGeometry.Stack.enoughInjectives_moduleSheaves`
read at the `SiteKind` spelling of the structure sheaf. -/
theorem enoughInjectives_fppfModuleSheaves :
    EnoughInjectives
      (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) :=
  enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p hp B.topology le_rfl

/-- The direct image of [Stacks, Tag 06WE] on modules on the associated fppf sites at section
universe `u + 1` is additive. -/
instance additive_fppfModuleSheafPushforward :
    (fppfModuleSheafPushforward B S hS p q hp hq f hf).Additive :=
  additive_moduleSheafPushforward.{u, u + 1, u, u + 1, u} B S hS p q hp hq f hf B.topology le_rfl

/-- The direct image of [Stacks, Tag 06WE] on modules on the associated fppf sites at section
universe `u + 1` is left exact, being a right adjoint. -/
instance preservesFiniteLimits_fppfModuleSheafPushforward :
    PreservesFiniteLimits (fppfModuleSheafPushforward B S hS p q hp hq f hf) :=
  preservesFiniteLimits_moduleSheafPushforward.{u, u + 1, u, u + 1, u} B S hS p q hp hq f hf
    B.topology le_rfl

attribute [local instance] enoughInjectives_fppfModuleSheaves

section Leray

variable
  [HasDerivedCategory
    (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))]
  [HasDerivedCategory
    (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS q hq .fppf))]
  [HasDerivedCategory
    (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS r hr .fppf))]

include hfg in
/-- **The relative Leray spectral sequence for 1-morphisms of categories fibred in groupoids.**
Let `f : 𝒳 → 𝒴` and `g : 𝒴 → 𝒵` be 1-morphisms of categories fibred in groupoids over the big
fppf site of `S`, presented with structure functors `p`, `q`, `r`, and let `K` be a bounded below
complex of modules on the associated fppf site of `𝒳`. There is a spectral sequence of modules on
the fppf site of `𝒵` with

`E_2^{a,b} = R^a g_*(R^b f_* K)`

converging to `R^{a+b}(g ∘ f)_* K`, the direct images being those of [Stacks, Tag 06WE] at
section universe `u + 1`.

This is [Stacks, Tag 0734] for the ringed topoi of categories fibred in groupoids. The proof is
the Grothendieck spectral sequence ([Stacks, Tag 015N]) for `(g ∘ f)_* ≅ g_* ∘ f_*`
(`AlgebraicGeometry.Stack.moduleSheafPushforwardCompIso`), whose acyclicity hypothesis holds
because `f_*` carries injectives to injectives
(`AlgebraicGeometry.Stack.injective_moduleSheafPushforward_obj`). -/
theorem exists_relativeLeraySpectralSequence_fppfModuleSheafPushforward
    (K : DerivedCategory.Plus
      (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))) :
    ∃ E : CohomologicalSpectralSequence
        (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS r hr .fppf)) 0,
      (∀ a b : ℤ, Nonempty ((E.page 2 zero_le_two).X (a, b) ≅
        ((fppfModuleSheafPushforward B S hS q r hq hr g hg).rightDerivedPlus a).obj
          ((DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS q hq .fppf)) b).obj
              ((fppfModuleSheafPushforward B S hS p q hp hq f hf).rightDerivedFunctorPlus.obj
                K)))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS r hr .fppf)) n).obj
            ((fppfModuleSheafPushforward B S hS p r hp hr (f ⋙ g) hfg).rightDerivedFunctorPlus.obj
              K)) := by
  have hacyclic : ∀ I : SheafOfModules.{u + 1}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf), Injective I →
      (fppfModuleSheafPushforward B S hS q r hq hr g hg).rightAcyclic
        ((fppfModuleSheafPushforward B S hS p q hp hq f hf).obj I) := fun I hI =>
    have := injective_moduleSheafPushforward_obj B S hS p q hp hq f hf I hI
    Stacks.BoundedBelowEdge.rightAcyclic_of_injective _ _
  obtain ⟨L, hL⟩ := Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp
    (fppfModuleSheafPushforward B S hS p q hp hq f hf)
    (fppfModuleSheafPushforward B S hS q r hq hr g hg) hacyclic K
  obtain ⟨E, -, h2, habuts⟩ :=
    hL _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  exact ⟨E, h2, habuts.of_nonempty_iso fun n => ⟨(DerivedCategory.Plus.homologyFunctor _ n).mapIso
    ((Functor.rightDerivedFunctorPlusNatIso
      (moduleSheafPushforwardCompIso B S hS p q r hp hq hr f hf g hg hfg)).app K).symm⟩⟩

end Leray

/-! ### Algebraic stacks, at the module universe of the schemes -/

section AlgebraicStacks

variable {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)

/-- **The inverse image along a composite of 1-morphisms of algebraic stacks is the composite of
the inverse images**, for modules on the fppf sites at the module universe `u`. -/
def fppfModulesPullbackCompIso :
    fppfModulesPullback B S hS (f ≫ g) ≅
      fppfModulesPullback B S hS g ⋙ fppfModulesPullback B S hS f :=
  modulePullbackCompIso.{u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids 𝒵.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p (f ≫ g).hom)

variable {B S hS f g}

/-- **A direct image along a composite of 1-morphisms of algebraic stacks is the composite of the
direct images**: any right adjoints `f_*`, `g_*`, `(g ∘ f)_*` of the inverse images of modules on
the fppf sites satisfy `(g ∘ f)_* ≅ f_* ⋙ g_*`, by uniqueness of adjoints and
`AlgebraicGeometry.Stack.fppfModulesPullbackCompIso`. -/
def fppfModulesPushforwardCompIsoOfAdjunction
    {Pf : fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒴}
    {Pg : fppfModules B S hS 𝒴 ⥤ fppfModules B S hS 𝒵}
    {Pfg : fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒵}
    (adjf : fppfModulesPullback B S hS f ⊣ Pf) (adjg : fppfModulesPullback B S hS g ⊣ Pg)
    (adjfg : fppfModulesPullback B S hS (f ≫ g) ⊣ Pfg) : Pf ⋙ Pg ≅ Pfg :=
  (adjg.comp adjf).rightAdjointUniq
    (adjfg.ofNatIsoLeft (fppfModulesPullbackCompIso B S hS f g))

/-- **A direct image along a 1-morphism of algebraic stacks carries injective modules to
injective modules**, because the inverse image of modules is left exact, hence preserves
monomorphisms. -/
theorem injective_obj_of_fppfModulesPullback_adjunction
    {Pf : fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒴}
    (adjf : fppfModulesPullback B S hS f ⊣ Pf) (I : fppfModules B S hS 𝒳) (hI : Injective I) :
    Injective (Pf.obj I) :=
  have := preservesFiniteLimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p
    𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    B.topology le_rfl
  injective_obj_of_preservesFiniteLimits_adjunction adjf I hI

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
