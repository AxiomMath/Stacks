module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackOfModules

/-!
# Kernels and extensions of modules with the flat base change property (Stacks 0764, part (2))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Stacks 0762** attaches to a
presheaf of `𝒪_𝒳`-modules the *flat base change property*: the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761** is an isomorphism for every arrow
`φ : x ⟶ y` of `𝒳` lying over a flat morphism of schemes `a : U ⟶ V`.

Part (2) of **Stacks 0764** says that the modules with the property form a weak Serre
subcategory, which by **Stacks 0754** asks for a zero object and for closure under cokernels,
kernels and extensions. The zero object and the cokernels are in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeColimits.lean`; this file adds
the two remaining clauses, and assembles them into the weak Serre condition.

The source's proof of part (2) runs the criterion of **Stacks 0754** and observes that
`a_{small}^*` is exact because `a` is flat, and that restriction to the small étale site is
exact. The two clauses behave differently under that split:

* The **extension** clause needs only *right* exactness of the source `F ↦ a_{small}^*(F|_{V_ét})`
  of `c_φ`, which is free: `a_{small}^*` is a left adjoint, so it preserves finite colimits, and
  restriction to the small étale site preserves them too. With the target `F ↦ F|_{U_ét}` exact,
  a short exact sequence gives a map of complexes whose upper row is exact with an epimorphism on
  the right and whose lower row is short exact; the two three-term diagram lemmas for an abelian
  category then give that `c_φ` is a monomorphism and an epimorphism at the middle term. So this
  clause is proved here outright.
* The **kernel** clause needs *left* exactness of that source functor, and no argument gives it
  for free: the inverse image of presheaves of modules below `φ` is the left adjoint of the
  direct image, hence a left Kan extension followed by a change of scalars, and left exactness of
  a left Kan extension is not formal. It is exactly the flatness input of the source — for étale
  *sheaves* of modules, `a_{small}^*` is exact when `a` is flat. So the kernel clause is proved
  here over that left exactness as a named hypothesis, and the weak Serre condition with it.

## Main results

* `AlgebraicGeometry.Stack.preservesHomology_restrictModuleToSmallEtaleFunctor`: restriction to
  the small étale site of the scheme below an object is exact, since it leaves the underlying
  presheaf of abelian groups alone up to reindexing along a functor.
* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_kernel`: **Stacks 0764** part (2), for
  presheaves of modules — the closure under kernels asked for by **Stacks 0754**, over the left
  exactness of the source of `c_φ`.
* `AlgebraicGeometry.Stack.isWeakSerreClass_flatBaseChangeModulePresheaves`: **Stacks 0764**
  part (2), for presheaves of modules — the weak Serre condition of **Stacks 0754**, over the
  same left exactness.

## Implementation notes

The ambient category of the source's part (2) is `Mod(𝒳_étale, 𝒪_𝒳)`, the étale *sheaves* of
`𝒪_𝒳`-modules. As in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeColimits.lean`, the statements
below read it in the presheaves of modules instead, which is the category
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` is stated for, and the part keys of the tags
record that. The clauses do not transfer to the sheaves: a short exact sequence of étale sheaves
of modules has an underlying presheaf sequence which need not be epimorphic on the right, the
cokernel of sheaves being the sheafification of the cokernel of presheaves, so the extension
clause below does not imply the source's.

Exactness of the restriction to the small étale site is proved through
`CategoryTheory.Functor.preservesHomology_of_map_exact` and
`CategoryTheory.Functor.reflects_exact_of_faithful`: the restriction is a reindexing along a
functor followed by a change of scalars, neither of which touches the underlying presheaf of
abelian groups, and exactness of presheaves of modules is tested there.
`PresheafOfModules.pushforward₀` being additive is
`Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.pushforward₀_additive`, which is why
that module is imported; additivity of the inverse image below `φ` is obtained from additivity
of its right adjoint through `CategoryTheory.Adjunction.left_adjoint_additive`.

The module sections live in the universe `u` of the schemes wherever the comparison map appears,
as it pins them; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleModuleComparison.lean`. The
exactness statements about the restriction alone hold at every module universe and are stated
there.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- Restriction to the small étale site of the scheme below an object of `𝒳` is additive: it is
a reindexing of the sections along a functor followed by a change of scalars, and addition of
morphisms of presheaves of modules is objectwise. -/
instance additive_restrictModuleToSmallEtaleFunctor (x : 𝒳) :
    (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x).Additive := by
  unfold restrictModuleToSmallEtaleFunctor
  infer_instance

/-- Restriction to the small étale site of the scheme below an object of `𝒳` preserves homology,
hence is exact.

A short complex of presheaves of modules is exact as soon as its image under the forgetful
functor to presheaves of abelian groups is, and that functor turns the restriction into
reindexing along a functor, which is exact because limits and colimits of presheaves of abelian
groups are computed objectwise. -/
instance preservesHomology_restrictModuleToSmallEtaleFunctor (x : 𝒳) :
    (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro T hT
  apply (PresheafOfModules.toPresheaf
    (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj).reflects_exact_of_faithful
  let := isEquivalence_overPost B S hS p hp x
  exact hT.map (PresheafOfModules.toPresheaf
      (ringStructureSheafCore B S hS p hp τ hτ).obj ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{m}).obj
      (smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
        (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x).op)

/-- Restriction to the small étale site of the scheme below an object of `𝒳` is left exact. -/
instance preservesFiniteLimits_restrictModuleToSmallEtaleFunctor (x : 𝒳) :
    PreservesFiniteLimits
      (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- Restriction to the small étale site of the scheme below an object of `𝒳` is right exact. -/
instance preservesFiniteColimits_restrictModuleToSmallEtaleFunctor (x : 𝒳) :
    PreservesFiniteColimits
      (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

section Arrow

variable {x y : 𝒳} (φ : x ⟶ y)

/-- The inverse image `a_{small}^*` of presheaves of modules below an arrow of `𝒳` is additive:
its right adjoint, the direct image along the map `a_{small}^♯` of structure sheaves, is a
reindexing followed by a change of scalars and hence additive, and a left adjoint of an additive
functor is additive. The sections of the modules may live in any universe `m` containing the
universe `u` of the schemes. -/
instance additive_pullback_smallEtaleStructureComparison_univLE [UnivLE.{u, m}] :
    (PresheafOfModules.pullback.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).Additive :=
  letI : (PresheafOfModules.pushforward.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).Additive := by
    unfold PresheafOfModules.pushforward
    infer_instance
  (PresheafOfModules.pullbackPushforwardAdjunction.{m}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).left_adjoint_additive

/-- The comparison map `c_φ` of **Stacks 06WC** at the middle term of a short exact sequence of
presheaves of modules is an isomorphism as soon as it is one at the two outer terms.

The source of `c_φ` is right exact, so the short exact sequence is carried to an exact complex
whose right-hand map is an epimorphism; the target of `c_φ` is exact, so it is carried to a short
exact sequence. The resulting map of three-term complexes is a monomorphism and an epimorphism at
the outer terms, so the two three-term diagram lemmas of an abelian category make it a
monomorphism and an epimorphism at the middle term. -/
theorem isIso_restrictModulePullbackComparison_of_shortExact
    {T : ShortComplex (PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)}
    (hT : T.ShortExact)
    (h₁ : IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ T.X₁))
    (h₃ : IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ T.X₃)) :
    IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ T.X₂) := by
  let Φ := flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ
  let Ψ := restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x
  let η := restrictModulePullbackComparisonNatTrans B E h S hS p hp τ hτ φ
  obtain ⟨hΦex, hΦepi⟩ :=
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi Φ).mp inferInstance T hT
  obtain ⟨hΨex, hΨmono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono Ψ).mp inferInstance T hT
  have : IsIso (η.app T.X₁) := h₁
  have : IsIso (η.app T.X₃) := h₃
  have hm : Mono (η.app T.X₂) :=
    ShortComplex.mono_of_mono_of_mono_of_mono (T.mapNatTrans η) hΦex hΨmono
      (inferInstanceAs (Mono (η.app T.X₁))) (inferInstanceAs (Mono (η.app T.X₃)))
  have he : Epi (η.app T.X₂) :=
    ShortComplex.epi_of_epi_of_epi_of_epi (T.mapNatTrans η) hΨex hΦepi
      (inferInstanceAs (Epi (η.app T.X₁))) (inferInstanceAs (Epi (η.app T.X₃)))
  exact isIso_of_mono_of_epi (η.app T.X₂)

/-- The comparison map `c_φ` of **Stacks 06WC** at the kernel of a morphism of presheaves of
modules is an isomorphism as soon as it is one at the source and the target, provided the source
functor of `c_φ` is left exact.

Left exactness carries the exact complex `ker α ⟶ F ⟶ G` to an exact complex and keeps the
first map a monomorphism; the target of `c_φ` is exact, so it does the same there. Then `c_φ` at
the kernel is a monomorphism because its composite with the restriction of the inclusion of the
kernel is one, and an epimorphism by the three-term diagram lemma for an abelian category. -/
theorem isIso_restrictModulePullbackComparison_kernel
    (hexact : PreservesFiniteLimits
      (flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ))
    {F G : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (α : F ⟶ G)
    (hF : IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F))
    (hG : IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ G)) :
    IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ (kernel α)) := by
  let Φ := flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ
  let Ψ := restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x
  let η := restrictModulePullbackComparisonNatTrans B E h S hS p hp τ hτ φ
  let T : ShortComplex
      (PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) :=
    ShortComplex.mk (kernel.ι α) α (kernel.condition α)
  have hTex : T.Exact := ShortComplex.exact_kernel α
  have : Φ.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  have hΦex : (T.map Φ).Exact :=
    hTex.map_of_mono_of_preservesKernel Φ inferInstance inferInstance
  have : Ψ.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  have hΨmono : Mono ((T.map Ψ).f) := inferInstanceAs (Mono (Ψ.map T.f))
  have : IsIso (η.app F) := hF
  have : IsIso (η.app G) := hG
  have e₂ : Epi ((T.mapNatTrans η).τ₂) := inferInstanceAs (Epi (η.app F))
  have m₃ : Mono ((T.mapNatTrans η).τ₃) := inferInstanceAs (Mono (η.app G))
  have he : Epi (η.app (kernel α)) :=
    ShortComplex.epi_of_mono_of_epi_of_mono (T.mapNatTrans η) hΦex hΨmono e₂ m₃
  have hm : Mono (η.app (kernel α)) := mono_of_mono_fac (η.naturality T.f).symm
  exact isIso_of_mono_of_epi (η.app (kernel α))

end Arrow

/-- **Stacks 0764, part (2), for presheaves of modules, over the left exactness of the source of
`c_φ`.** The kernel of a morphism of presheaves of `𝒪_𝒳`-modules with the flat base change
property of **Stacks 0762** has the flat base change property. This is the closure under kernels
asked for by **Stacks 0754**.

The hypothesis `hexact` is left exactness of
`AlgebraicGeometry.Stack.flatBaseChangeComparisonSource` at every arrow lying over a
flat morphism of schemes. It is the exactness of `a_{small}^*` that the source reads off
flatness of `a`; the implementation notes of this file say why no argument supplies it for the
inverse image of *presheaves* of modules. -/
theorem hasFlatBaseChangeProperty_kernel
    (hexact : ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
      PreservesFiniteLimits
        (flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ))
    {F G : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (α : F ⟶ G)
    (hF : HasFlatBaseChangeProperty B E h S hS p hp τ hτ F)
    (hG : HasFlatBaseChangeProperty B E h S hS p hp τ hτ G) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ (kernel α) := fun φ hflat =>
  isIso_restrictModulePullbackComparison_kernel B E h S hS p hp τ hτ φ (hexact φ hflat) α
    (hF φ hflat) (hG φ hflat)

/-- **Stacks 0764, part (2), for presheaves of modules, over the left exactness of the source of
`c_φ`.** The presheaves of `𝒪_𝒳`-modules with the flat base change property of **Stacks 0762**
form a weak Serre subcategory of the presheaves of `𝒪_𝒳`-modules, in the form **Stacks 0754**
gives: a strictly full subcategory containing a zero object and closed under kernels, cokernels
and extensions.

Strict fullness is
`AlgebraicGeometry.Stack.flatBaseChangeModulePresheaves`'s closure under isomorphisms, the zero
object is `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_initial`, the cokernels are
`AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_cokernel`, the extensions are
`AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_X₂_of_shortExact`, and the kernels are
`AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_kernel`, which is where the hypothesis
`hexact` enters. -/
theorem isWeakSerreClass_flatBaseChangeModulePresheaves
    (hexact : ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
      PreservesFiniteLimits
        (flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ)) :
    (flatBaseChangeModulePresheaves.{u, v, w} B E h S hS p hp τ hτ).IsWeakSerreClass := by
  have : (flatBaseChangeModulePresheaves.{u, v, w} B E h S hS p hp τ hτ).ContainsZero := by
    obtain ⟨Z, hZ⟩ := (inferInstance :
      HasZeroObject (PresheafOfModules.{u}
        (ringStructureSheafCore B S hS p hp τ hτ).obj)).zero
    exact ⟨⟨Z, hZ, hasFlatBaseChangeProperty_initial B E h S hS p hp τ hτ hZ.isInitial⟩⟩
  have : ObjectProperty.IsClosedUnderKernels
      (flatBaseChangeModulePresheaves.{u, v, w} B E h S hS p hp τ hτ) := by
    constructor
    rintro K ⟨f, k, hk, hF, hG⟩
    exact hasFlatBaseChangeProperty_of_iso B E h S hS p hp τ hτ
      (IsLimit.conePointUniqueUpToIso hk (kernelIsKernel f)).symm
      (hasFlatBaseChangeProperty_kernel B E h S hS p hp τ hτ hexact f hF hG)
  have : ObjectProperty.IsClosedUnderCokernels
      (flatBaseChangeModulePresheaves.{u, v, w} B E h S hS p hp τ hτ) := by
    constructor
    rintro Q ⟨f, k, hk, hF, hG⟩
    exact hasFlatBaseChangeProperty_of_iso B E h S hS p hp τ hτ
      (IsColimit.coconePointUniqueUpToIso hk (cokernelIsCokernel f)).symm
      (hasFlatBaseChangeProperty_cokernel B E h S hS p hp τ hτ f hF hG)
  have : ObjectProperty.IsClosedUnderExtensions
      (flatBaseChangeModulePresheaves.{u, v, w} B E h S hS p hp τ hτ) :=
    ⟨fun hT h₁ h₃ => hasFlatBaseChangeProperty_X₂_of_shortExact B E h S hS p hp τ hτ _ hT h₁ h₃⟩
  exact {}

end AlgebraicGeometry.Stack

end
