module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaCokernel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafKernels
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSmallEtaleIsoComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentWeakSerre

/-!
# The flat base change property read on sheaves of modules (Stacks 0762)

**Stacks 0762** is stated for a sheaf `ℱ` of `𝒪_𝒳`-modules on `𝒳_étale`, and the comparison map
`c_φ : a_{small}^*(ℱ|_{V_ét}) ⟶ ℱ|_{U_ét}` of **Stacks 06WC** it speaks about is the one in which
`a_{small}^*` is the pullback of *sheaves* of modules along the morphism of ringed sites `ε_a` of
**Stacks 070R (2)**.  That functor is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, the pullback of presheaves of modules
along the map `a_{small}^♯` followed by sheafification, and the comparison map out of it is the
sheafification adjunct `AlgebraicGeometry.Stack.sheafifiedRestrictComparison` of the comparison
map of presheaves of modules.

This file assembles that adjunct into a natural transformation of functors of the sheaf of
modules, which is what the closure clauses of **Stacks 0764** part (2) are about.

## Main definitions

* `AlgebraicGeometry.Stack.sheafifiedRestrictComparisonNatTrans`: the comparison map
  `c_φ : a_{small}^*(ℱ|_{V_ét}) ⟶ ℱ|_{U_ét}` of **Stacks 06WC**, read on sheaves of modules, as a
  natural transformation in `ℱ`.

## Main results

* `CategoryTheory.NatTrans.isIso_app_of_isLimit_mapCone`: a natural transformation `η : Φ ⟶ Ψ`
  which is an isomorphism at every value of a diagram, and whose two functors both carry a limit
  cone of that diagram to a limit cone, is an isomorphism at the cone point.  This is the shape of
  the kernel clause of **Stacks 0754**.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.NatTrans

/-- A natural transformation `η : Φ ⟶ Ψ` which is an isomorphism at each value of a diagram
`K : J ⥤ C`, and for which a limit cone of `K` is carried by both `Φ` and `Ψ` to a limit cone, is
an isomorphism at the cone point.

The two image cones are limits of `K ⋙ Φ` and `K ⋙ Ψ`, which `η` identifies, and the comparison
of the two cone points is `η` at the cone point by uniqueness of a map into a limit. -/
theorem isIso_app_of_isLimit_mapCone {C : Type*} [Category C] {D : Type*} [Category D]
    {J : Type*} [Category J] {Φ Ψ : C ⥤ D} (η : Φ ⟶ Ψ) {K : J ⥤ C} {c : Cone K}
    (hΦ : IsLimit (Φ.mapCone c))
    (hΨ : IsLimit (Ψ.mapCone c)) (h : ∀ j, IsIso (η.app (K.obj j))) :
    IsIso (η.app c.pt) := by
  let w : K ⋙ Φ ≅ K ⋙ Ψ := NatIso.ofComponents (fun j => let := h j; asIso (η.app (K.obj j)))
    fun f => η.naturality (K.map f)
  have key : η.app c.pt = (IsLimit.conePointsIsoOfNatIso hΦ hΨ w).hom := by
    refine hΨ.hom_ext fun j => ?_
    rw [IsLimit.conePointsIsoOfNatIso_hom_comp]
    exact (η.naturality (c.π.app j)).symm
  rw [key]
  infer_instance

end CategoryTheory.NatTrans

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- **Stacks 06WC on sheaves of modules.** The comparison map
`c_φ : a_{small}^*(ℱ|_{V_ét}) ⟶ ℱ|_{U_ét}` below an arrow `φ : z ⟶ x` of `𝒳`, as a natural
transformation from the restriction at `x` followed by the pullback of sheaves of modules along
`ε_a` to the restriction at `z`.

The components are `AlgebraicGeometry.Stack.sheafifiedRestrictComparison`, the sheafification
adjunct of the comparison map of presheaves of modules; the sheaf condition each component needs
is the one the restriction functor on sheaves of modules supplies.  Naturality is naturality of
the comparison map of presheaves of modules carried across the sheafification adjunction. -/
def sheafifiedRestrictComparisonApp {x z : 𝒳} (φ : z ⟶ x)
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ).obj
        ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).obj ℱ) ⟶
      (restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z).obj ℱ :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z)).obj)).homEquiv _ _).symm
    (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) ℱ.val)

/-- The comparison map of `AlgebraicGeometry.Stack.sheafifiedRestrictComparisonApp` is the one
`AlgebraicGeometry.Stack.sheafifiedRestrictComparison` builds. -/
theorem sheafifiedRestrictComparisonApp_eq {x z : 𝒳} (φ : z ⟶ x)
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    sheafifiedRestrictComparisonApp B E h S hS p hp φ ℱ =
      sheafifiedRestrictComparison B E h S hS p hp ℱ.val φ
        ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z).obj ℱ).isSheaf :=
  rfl

/-- **Stacks 06WC on sheaves of modules.** The comparison map
`c_φ : a_{small}^*(ℱ|_{V_ét}) ⟶ ℱ|_{U_ét}` below an arrow `φ : z ⟶ x` of `𝒳`, as a natural
transformation from the restriction at `x` followed by the pullback of sheaves of modules along
`ε_a` to the restriction at `z`.

Naturality is naturality of the comparison map of presheaves of modules carried across the
sheafification adjunction. -/
def sheafifiedRestrictComparisonNatTrans {x z : 𝒳} (φ : z ⟶ x) :
    restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ ⟶
      restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z where
  app ℱ := sheafifiedRestrictComparisonApp B E h S hS p hp φ ℱ
  naturality ℱ 𝒢 α := by
    have hnat : (PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
              (etaleTopology_le_topology B))).map
          ((SheafOfModules.forget (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x))).map
            ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).map α)) ≫
          restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B) 𝒢.val =
        restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B) ℱ.val ≫
          (SheafOfModules.forget (SmallEtale.structureSheaf E (p.obj z).left.1
              (contains_base B E h S hS p z)) ⋙
            PresheafOfModules.restrictScalars
              (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj)).map
            ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z).map α) :=
      restrictModulePullbackComparison_naturality B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) φ (F := ℱ.val) (F' := 𝒢.val) α.val
    dsimp only [sheafifiedRestrictComparisonApp, sheafifiedPullbackComparison, Functor.comp_map]
    exact Adjunction.homEquiv_naturality_right_square _ _ _ _ _ hnat

/-- The flat base change property, read on sheaves of modules. A sheaf of `𝒪_𝒳`-modules on
`𝒳_étale` *has the flat base change property* when the comparison map `c_φ` of **Stacks 06WC**,
read on sheaves of modules, is an isomorphism for every arrow `φ` of `𝒳` lying over a flat
morphism of schemes.

This is the reading of the source: the `a_{small}^*` of the source is the pullback of *sheaves*
of modules along `ε_a`, which is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, the *sheafification* of the pullback of
presheaves of modules that `AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` is stated with. -/
abbrev HasFlatBaseChangePropertySheaf
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    Prop :=
  ∀ {x z : 𝒳} (φ : z ⟶ x), Flat (B.inclusion.map (p.map φ).left) →
    IsIso ((sheafifiedRestrictComparisonNatTrans B E h S hS p hp φ).app ℱ)

/-- The flat base change property on sheaves of modules depends only on the isomorphism class of
the sheaf, the comparison map being natural in it.  This is the strict fullness asked for by
**Stacks 0754**. -/
theorem hasFlatBaseChangePropertySheaf_of_iso
    {ℱ 𝒢 : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))}
    (e : ℱ ≅ 𝒢) (hℱ : HasFlatBaseChangePropertySheaf B E h S hS p hp ℱ) :
    HasFlatBaseChangePropertySheaf B E h S hS p hp 𝒢 := by
  intro x z φ hflat
  have := hℱ φ hflat
  have hnat := (sheafifiedRestrictComparisonNatTrans B E h S hS p hp φ).naturality e.hom
  have : IsIso ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).map e.hom ≫
      (sheafifiedRestrictComparisonNatTrans B E h S hS p hp φ).app 𝒢) := by
    rw [hnat]; infer_instance
  exact IsIso.of_isIso_comp_left
    ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).map e.hom) _

/-- **The presheaf reading of the flat base change property implies the reading of
Stacks 0762 on sheaves of modules.**  If the comparison map `c_φ` of **Stacks 06WC** computed in
presheaves of modules is an isomorphism below every arrow lying over a flat morphism of schemes,
then so is the comparison map read on sheaves of modules.

The comparison map on sheaves of modules is the sheafification adjunct of the one on presheaves,
and an adjunct `η⁻¹` factors as the image of the presheaf map under sheafification followed by the
counit of the sheafification adjunction.  Sheafification carries the presheaf comparison map to an
isomorphism because it is a functor, and the counit of the sheafification adjunction is an
isomorphism, so the composite is one.

This is one half of the comparison between the two readings of **Stacks 0762**; the converse
would ask the presheaf-level pullback of the restriction to be a sheaf already. -/
theorem hasFlatBaseChangePropertySheaf_of_hasFlatBaseChangeProperty
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hℱ : HasFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ℱ.val) :
    HasFlatBaseChangePropertySheaf B E h S hS p hp ℱ := by
  intro x z φ hflat
  have := hℱ φ hflat
  change IsIso (sheafifiedRestrictComparisonApp B E h S hS p hp φ ℱ)
  -- The adjunct of `c_φ` is the image of `c_φ` under sheafification followed by the counit.
  have heq : sheafifiedRestrictComparisonApp B E h S hS p hp φ ℱ = _ :=
    Adjunction.homEquiv_counit _ _ _ _
  rw [heq]
  -- Both factors have to be named: the two sides spell the restriction to the small étale site
  -- differently, so instance search on the composite does not see the hypothesis.
  have h1 : IsIso ((PresheafOfModules.sheafification
      (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z)).obj)).map
      (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) ℱ.val)) := inferInstance
  have h2 : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z)).obj)).counit.app
      ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z).obj ℱ)) := inferInstance
  exact IsIso.comp_isIso' h1 h2

section Exactness

variable {x z : 𝒳} (φ : z ⟶ x)

/-- `a_{small}^*` read on sheaves of modules is additive, being a left adjoint of an additive
functor. -/
instance additive_sheafifiedPullbackComparison :
    (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).Additive :=
  (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ).left_adjoint_additive

/-- `a_{small}^*` read on sheaves of modules is right exact, being a left adjoint. -/
instance preservesFiniteColimits_sheafifiedPullbackComparison :
    Limits.PreservesFiniteColimits
      (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ) :=
  letI := (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ).isLeftAdjoint
  ⟨fun _ _ _ => inferInstance⟩

end Exactness

section Kernels

variable [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The source of the comparison map, restriction at `x` followed by `a_{small}^*`, is right
exact. -/
private theorem preservesFiniteColimits_restrict_comp_sheafifiedPullbackComparison (x : 𝒳)
    {z : 𝒳} (φ : z ⟶ x) :
    Limits.PreservesFiniteColimits
      (restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ) :=
  letI := preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x
  Limits.comp_preservesFiniteColimits _ _

omit [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The kernel clause of Stacks 0764 part (2), for locally quasi-coherent sheaves of modules.**
The kernel, formed in `Mod(𝒳_ét, 𝒪_𝒳)`, of a morphism of locally quasi-coherent sheaves of
`𝒪_𝒳`-modules with the flat base change property of **Stacks 0762** has the flat base change
property.

The comparison map is the component of a natural transformation from
`ℱ ↦ a_{small}^*(ℱ|_{V_ét})` to `ℱ ↦ ℱ|_{U_ét}`.  The target is exact, so it carries the kernel
fork to a limit.  So does the source: restriction to a small étale site is exact and carries the
fork to a fork of *quasi-coherent* modules there, local quasi-coherence being closed under
kernels by **Stacks 06WM** part (2), and on quasi-coherent modules `a_{small}^*` is left exact
for `a` flat, by
`AlgebraicGeometry.Stack.isLimit_mapCone_sheafifiedPullbackComparison_of_isQuasicoherentOnSite`.
With the comparison map invertible at the two terms of the fork,
`CategoryTheory.NatTrans.isIso_app_of_isLimit_mapCone` gives it invertible at the kernel. -/
theorem hasFlatBaseChangePropertySheaf_of_isLimit_kernelFork
    {M N : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))}
    (f : M ⟶ N) {k : Limits.KernelFork f} (hk : IsLimit k)
    (hM : IsLocallyQuasicoherent B E h S hS p hp M.val)
    (hN : IsLocallyQuasicoherent B E h S hS p hp N.val)
    (hfM : HasFlatBaseChangePropertySheaf B E h S hS p hp M)
    (hfN : HasFlatBaseChangePropertySheaf B E h S hS p hp N) :
    HasFlatBaseChangePropertySheaf B E h S hS p hp k.pt := by
  intro x z φ hflat
  let := preservesFiniteLimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x
  let := preservesFiniteLimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z
  have hKpt : IsLocallyQuasicoherent B E h S hS p hp k.pt.val :=
    (locallyQuasicoherent B E h S hS p hp).prop_of_isLimit_kernelFork hk hM hN
  have hK : ∀ j, ((Limits.parallelPair f 0 ⋙
      restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).obj j).IsQuasicoherentOnSite := by
    rintro (_ | _)
    · exact (isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp M).1 hM x
    · exact (isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp N).1 hN x
  have hpt : (((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).mapCone
      k).pt).IsQuasicoherentOnSite :=
    (isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp k.pt).1 hKpt x
  have h₁ : IsLimit ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).mapCone k) :=
    isLimitOfPreserves _ hk
  have h₂ : IsLimit ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).mapCone k) :=
    isLimit_mapCone_sheafifiedPullbackComparison_of_isQuasicoherentOnSite
      B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ hK hpt hflat h₁
  have h₃ : IsLimit ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z).mapCone k) :=
    isLimitOfPreserves _ hk
  refine NatTrans.isIso_app_of_isLimit_mapCone _ h₂ h₃ ?_
  rintro (_ | _)
  · exact hfM φ hflat
  · exact hfN φ hflat

/-- **The cokernel clause of Stacks 0764 part (2), on sheaves of modules.**  The cokernel,
formed in `Mod(𝒳_ét, 𝒪_𝒳)`, of a morphism of sheaves of `𝒪_𝒳`-modules with the flat base change
property has the flat base change property.

Both functors the comparison map runs between are right exact — `a_{small}^*` is a left adjoint
and restriction to a small étale site is cocontinuous — so both carry the cokernel cofork to a
colimit, and `CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone` applies. -/
theorem hasFlatBaseChangePropertySheaf_of_isColimit_cokernelCofork
    {M N : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))}
    (f : M ⟶ N) {k : Limits.CokernelCofork f} (hk : IsColimit k)
    (hfM : HasFlatBaseChangePropertySheaf B E h S hS p hp M)
    (hfN : HasFlatBaseChangePropertySheaf B E h S hS p hp N) :
    HasFlatBaseChangePropertySheaf B E h S hS p hp k.pt := by
  intro x z φ hflat
  let := preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z
  let := preservesFiniteColimits_restrict_comp_sheafifiedPullbackComparison B E h S hS p hp x φ
  have h₂ : IsColimit ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).mapCocone k) := isColimitOfPreserves _ hk
  have h₃ : IsColimit ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z).mapCocone k) :=
    isColimitOfPreserves _ hk
  refine NatTrans.isIso_app_of_isColimit_mapCocone _ _ h₂ h₃ ?_
  rintro (_ | _)
  · exact hfM φ hflat
  · exact hfN φ hflat

/-- **The zero object clause of Stacks 0764 part (2), on sheaves of modules.**  An initial sheaf
of `𝒪_𝒳`-modules — equivalently, a zero object — has the flat base change property: it is the
colimit of the empty diagram, on which the hypothesis of
`CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone` is vacuous. -/
theorem hasFlatBaseChangePropertySheaf_of_isInitial
    {ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))}
    (hℱ : IsInitial ℱ) : HasFlatBaseChangePropertySheaf B E h S hS p hp ℱ := by
  intro x z φ hflat
  let := preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z
  let := preservesFiniteColimits_restrict_comp_sheafifiedPullbackComparison B E h S hS p hp x φ
  exact NatTrans.isIso_app_of_isColimit_mapCocone _ _ (isColimitOfPreserves _ hℱ)
    (isColimitOfPreserves _ hℱ) (fun i => i.as.elim)

/-- **The extension clause of Stacks 0764 part (2), on sheaves of modules.**  In a short exact
sequence of sheaves of `𝒪_𝒳`-modules whose outer terms have the flat base change property, the
middle term has it too.

The target of the comparison map is exact and its source is right exact, which is what
`CategoryTheory.ShortComplex.isIso_app_of_shortExact`, the short five lemma against a right
exact functor, asks for. -/
theorem hasFlatBaseChangePropertySheaf_X₂_of_shortExact
    (T : ShortComplex (SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))))
    (hT : T.ShortExact)
    (h₁ : HasFlatBaseChangePropertySheaf B E h S hS p hp T.X₁)
    (h₃ : HasFlatBaseChangePropertySheaf B E h S hS p hp T.X₃) :
    HasFlatBaseChangePropertySheaf B E h S hS p hp T.X₂ := by
  intro x z φ hflat
  let := preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z
  let := preservesFiniteLimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z
  let := preservesFiniteColimits_restrict_comp_sheafifiedPullbackComparison B E h S hS p hp x φ
  exact ShortComplex.isIso_app_of_shortExact _ _
    (sheafifiedRestrictComparisonNatTrans B E h S hS p hp φ) hT (h₁ φ hflat) (h₃ φ hflat)

/-! ### `LQCoh^{fbc}(𝒪_𝒳)` as a weak Serre class in `Mod(𝒳_ét, 𝒪_𝒳)` -/

/-- `LQCoh^{fbc}(𝒪_𝒳)`: the sheaves of `𝒪_𝒳`-modules on `𝒳_étale` which are locally
quasi-coherent (**Stacks 06WJ**) and have the flat base change property (**Stacks 0762**), as an
object property. -/
abbrev locallyQuasicoherentFlatBaseChangeSheaf :
    ObjectProperty (SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :=
  fun ℱ => IsLocallyQuasicoherent B E h S hS p hp ℱ.val ∧
    HasFlatBaseChangePropertySheaf B E h S hS p hp ℱ

/-- `LQCoh^{fbc}(𝒪_𝒳)` is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_locallyQuasicoherentFlatBaseChangeSheaf :
    (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).IsClosedUnderIsomorphisms where
  of_iso e hℱ :=
    ⟨(isClosedUnderIsomorphisms_locallyQuasicoherent B E h S hS p hp).of_iso e hℱ.1,
      hasFlatBaseChangePropertySheaf_of_iso B E h S hS p hp e hℱ.2⟩

/-- `LQCoh^{fbc}(𝒪_𝒳)` contains a zero object. -/
instance containsZero_locallyQuasicoherentFlatBaseChangeSheaf :
    (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    exact ⟨Z, hZ, isLocallyQuasicoherent_of_isZero B E h S hS p hp hZ,
      hasFlatBaseChangePropertySheaf_of_isInitial B E h S hS p hp hZ.isInitial⟩

/-- `LQCoh^{fbc}(𝒪_𝒳)` is closed under cokernels in `Mod(𝒳_ét, 𝒪_𝒳)`. -/
instance isClosedUnderCokernels_locallyQuasicoherentFlatBaseChangeSheaf :
    (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    exact ⟨(locallyQuasicoherent B E h S hS p hp).prop_of_isColimit_cokernelCofork hk hM.1 hN.1,
      hasFlatBaseChangePropertySheaf_of_isColimit_cokernelCofork B E h S hS p hp f hk hM.2 hN.2⟩

/-- `LQCoh^{fbc}(𝒪_𝒳)` is closed under kernels in `Mod(𝒳_ét, 𝒪_𝒳)`. -/
instance isClosedUnderKernels_locallyQuasicoherentFlatBaseChangeSheaf :
    (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    exact ⟨(locallyQuasicoherent B E h S hS p hp).prop_of_isLimit_kernelFork hk hM.1 hN.1,
      hasFlatBaseChangePropertySheaf_of_isLimit_kernelFork B E h S hS p hp f hk hM.1 hN.1
        hM.2 hN.2⟩

/-- `LQCoh^{fbc}(𝒪_𝒳)` is closed under extensions in `Mod(𝒳_ét, 𝒪_𝒳)`. -/
instance isClosedUnderExtensions_locallyQuasicoherentFlatBaseChangeSheaf :
    (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ :=
    ⟨(locallyQuasicoherent B E h S hS p hp).prop_X₂_of_shortExact hT h₁.1 h₃.1,
      hasFlatBaseChangePropertySheaf_X₂_of_shortExact B E h S hS p hp T hT h₁.2 h₃.2⟩

/-- **Stacks 0764 part (2) and the étale half of Stacks 0771 part (2).**  The sheaves of
`𝒪_𝒳`-modules on `𝒳_étale` which are locally quasi-coherent and have the flat base change
property form a weak Serre class in `Mod(𝒳_ét, 𝒪_𝒳)` in the sense of **Stacks 0754**. -/
instance isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheaf :
    (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).IsWeakSerreClass where

end Kernels

end AlgebraicGeometry.Stack

end
