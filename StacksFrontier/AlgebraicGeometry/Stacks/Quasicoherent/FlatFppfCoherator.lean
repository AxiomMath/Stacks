module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreQuotientCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriekLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticKernelOfFlatRestrictionLargeSections
public import StacksFrontier.CategoryTheory.Abelian.CoreflectiveSubcategoryAbelian
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakSerreClassInf

/-!
# The coherator through the flat-fppf site, at module universe `u + 1`

Let `𝒳` be an algebraic stack, `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` the morphism of ringed
topoi of **Stacks 0788** (2), `g^* = g^{-1}` restriction of modules to the flat objects and
`g_!` its left adjoint (**Stacks 0789** (2)), with `g^* g_! = id`.  This file builds the
coherator `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0778** as `Q = g_! g^*` — the formula
of **Stacks 07B1** (2)(c), read as a construction — for the faithful `LQCoh^fbc` of
**Stacks 0762** at module universe `u + 1` (where the derived direct image of **Stacks 07BC**
lives), together with:

* the adjunction `i ⊣ Q` and `Q ∘ i = id` (**Stacks 0778**);
* the kernel of `Q` is the parasitic modules (**Stacks 0779** (1));
* the kernel and the cokernel of `Q 𝓕 ⟶ 𝓕` are parasitic (**Stacks 0779** (2));
* `QCoh(𝒪_𝒳)` is abelian and `Q` is exact (**Stacks 0779** (3));
* the cohomology functors `Hⁱ : D_QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 07B7**.

## The inputs

The construction is the abstract one of
`StacksFrontier/CategoryTheory/Adjunction/CoreflectorOfFullyFaithfulLeftAdjoint.lean`, and it is
parametrized here by its geometric inputs:

* an adjunction `adj : G ⊣ g^*` with invertible unit — `g_!` and **Stacks 0789** (2);
* `hQL : QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` — **Stacks 06WK**;
* `hA : g_! g^* 𝓕` is quasi-coherent for `𝓕` in `LQCoh^fbc(𝒪_𝒳)` — **Stacks 07B1** (2)(b)
  followed by **Stacks 07B0** (2);
* `hB : g_! g^* 𝓖 ⟶ 𝓖` is invertible for `𝓖` quasi-coherent — **Stacks 07B1** (2)(a);
* `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒪_𝒳)` — **Stacks 0771** (2), as an
  instance.

No declaration below carries a `@[stacks]` attribute: the tags are registered where these inputs
are discharged.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.quasicoherentModulesSucc`: `QCoh(𝒪_𝒳)` at module universe
  `u + 1`, as an object property of `Mod(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.FlatFppf.coherator`, `coheratorAdjunction`, `coheratorCompIso`.
* `AlgebraicGeometry.Stack.FlatFppf.abelianQuasicoherentModulesSucc`.
* `AlgebraicGeometry.Stack.FlatFppf.quasicoherentCohomology`: `Hⁱ : D_QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`,
  with `quasicoherentCohomologyFac`.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
* [Stacks Project, Tag 07B7](https://stacks.math.columbia.edu/tag/07B7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **`QCoh(𝒪_𝒳)` at module universe `u + 1`**: the quasi-coherent modules (**Stacks 06WG**) on
the fppf site of `𝒳`, as an object property of `Mod(𝒪_𝒳)`. -/
abbrev quasicoherentModulesSucc :
    ObjectProperty (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)

/-- The faithful `LQCoh^fbc(𝒪_𝒳)` of **Stacks 0762** at module universe `u + 1`, read on the
ambient spelling of `Mod(𝒪_𝒳)`. -/
abbrev sheafFlatBaseChangeModulesSucc :
    ObjectProperty (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
  lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳

attribute [local instance] hasSheafify_topology_largeSections
  wEqualsLocallyBijective_topology_largeSections
  isContinuous_inclusion_topology isCocontinuous_inclusion_topology

/-- **`g^*` is right exact** at module universe `u + 1` (half of **Stacks 07AS** (2)'s
exactness of `g^{-1}`): restriction of sheaves of modules along the continuous and cocontinuous
inclusion of the flat objects preserves colimits. -/
instance preservesFiniteColimits_moduleInverseImage :
    PreservesFiniteColimits (moduleInverseImage B S hS 𝒳) :=
  have : PreservesColimitsOfSize.{u + 1, u + 1} (moduleInverseImage B S hS 𝒳) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (objectProperty B S hS 𝒳).ι _
  have : PreservesColimitsOfSize.{0, 0} (moduleInverseImage B S hS 𝒳) :=
    preservesColimitsOfSize_shrink _
  inferInstance

variable {B E h S hS 𝒳}
variable {G : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
    SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)}
  (adj : G ⊣ moduleInverseImage B S hS 𝒳) [IsIso adj.unit]
  (hQL : quasicoherentModulesSucc B S hS 𝒳 ≤ sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
  (hA : ∀ F, sheafFlatBaseChangeModulesSucc B E h S hS 𝒳 F →
    quasicoherentModulesSucc B S hS 𝒳 (G.obj ((moduleInverseImage B S hS 𝒳).obj F)))
  (hB : ∀ M, quasicoherentModulesSucc B S hS 𝒳 M → IsIso (adj.counit.app M))

/-- **The coherator `Q = g_! g^* : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`** of **Stacks 0778**, by the
formula of **Stacks 07B1** (2)(c). -/
abbrev coherator :
    (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).FullSubcategory ⥤
      (quasicoherentModulesSucc B S hS 𝒳).FullSubcategory :=
  ObjectProperty.coreflectorOfLeftAdjoint G (moduleInverseImage B S hS 𝒳) _ _ hA

/-- **Stacks 0778, the adjunction**: the coherator is right adjoint to the inclusion
`QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`; its counit `Q 𝓕 ⟶ 𝓕` is the counit `g_! g^* 𝓕 ⟶ 𝓕`. -/
abbrev coheratorAdjunction : ObjectProperty.ιOfLE hQL ⊣ coherator hA :=
  ObjectProperty.coreflectorOfLeftAdjointAdjunction adj hQL hA hB

/-- **Stacks 0778, `Q ∘ i = id`.** -/
abbrev coheratorCompIso : ObjectProperty.ιOfLE hQL ⋙ coherator hA ≅ 𝟭 _ :=
  ObjectProperty.coreflectorOfLeftAdjointCompIso adj hQL hA hB

include adj in
/-- **Stacks 0779 (1)**: an object of `LQCoh^fbc(𝒪_𝒳)` is in the kernel of the coherator if and
only if it is parasitic. -/
theorem isZero_coherator_obj_iff_isParasitic
    (F : (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).FullSubcategory) :
    IsZero ((coherator hA).obj F) ↔ IsParasitic.{u, w, u + 1} B S hS 𝒳 .fppf F.obj.val := by
  have : G.IsLeftAdjoint := adj.isLeftAdjoint
  have : (moduleInverseImage B S hS 𝒳).IsRightAdjoint := adj.isRightAdjoint
  rw [ObjectProperty.isZero_coreflectorOfLeftAdjoint_obj_iff adj,
    isParasitic_iff_isZero_moduleInverseImage]

/-- `g^*` inverts the adjunction map `Q 𝓕 ⟶ 𝓕`. -/
private theorem isIso_moduleInverseImage_map_coheratorCounit
    (F : (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).FullSubcategory) :
    IsIso ((moduleInverseImage B S hS 𝒳).map
      (((coheratorAdjunction adj hQL hA hB).counit.app F).hom)) := by
  rw [ObjectProperty.coreflectorOfLeftAdjointAdjunction_counit_app_hom]
  exact ObjectProperty.isIso_map_counit_of_isIso_unit adj F.obj

include adj hB in
/-- **Stacks 0779 (2), the kernel**: the kernel of the adjunction map `Q 𝓕 ⟶ 𝓕`, computed in
`Mod(𝒪_𝒳)`, is parasitic: `g^*` preserves it, being a right adjoint, and inverts the map. -/
theorem isParasitic_of_isLimit_kernelFork_coheratorCounit
    (F : (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).FullSubcategory)
    {c : KernelFork (((coheratorAdjunction adj hQL hA hB).counit.app F).hom)} (hc : IsLimit c) :
    IsParasitic.{u, w, u + 1} B S hS 𝒳 .fppf c.pt.val := by
  have : (moduleInverseImage B S hS 𝒳).IsRightAdjoint := adj.isRightAdjoint
  have : PreservesLimitsOfSize.{0, 0} (moduleInverseImage B S hS 𝒳) :=
    adj.rightAdjoint_preservesLimits
  have := isIso_moduleInverseImage_map_coheratorCounit adj hQL hA hB F
  rw [isParasitic_iff_isZero_moduleInverseImage]
  exact KernelFork.IsLimit.isZero_of_mono (KernelFork.mapIsLimit c hc (moduleInverseImage B S hS 𝒳))

include adj hB in
/-- **Stacks 0779 (2), the cokernel**: the cokernel of the adjunction map `Q 𝓕 ⟶ 𝓕`, computed
in `Mod(𝒪_𝒳)`, is parasitic: `g^*` is exact and inverts the map. -/
theorem isParasitic_of_isColimit_cokernelCofork_coheratorCounit
    (F : (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).FullSubcategory)
    {c : CokernelCofork (((coheratorAdjunction adj hQL hA hB).counit.app F).hom)}
    (hc : IsColimit c) :
    IsParasitic.{u, w, u + 1} B S hS 𝒳 .fppf c.pt.val := by
  have : (moduleInverseImage B S hS 𝒳).IsRightAdjoint := adj.isRightAdjoint
  have := isIso_moduleInverseImage_map_coheratorCounit adj hQL hA hB F
  rw [isParasitic_iff_isZero_moduleInverseImage]
  exact CokernelCofork.IsColimit.isZero_of_epi
    (CokernelCofork.mapIsColimit c hc (moduleInverseImage B S hS 𝒳))

variable [(sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).IsWeakSerreClass]

include adj hQL hB in
/-- **`QCoh(𝒪_𝒳)` is abelian** (the abelian structure of Remark 0GQL): the coherator is a right
exact coreflector onto it from the abelian `LQCoh^fbc(𝒪_𝒳)`. -/
@[instance_reducible]
def abelianQuasicoherentModulesSucc :
    Abelian (quasicoherentModulesSucc B S hS 𝒳).FullSubcategory :=
  haveI : G.IsLeftAdjoint := adj.isLeftAdjoint
  haveI : (moduleInverseImage B S hS 𝒳).IsRightAdjoint := adj.isRightAdjoint
  ObjectProperty.abelianOfCoreflectorOfLeftAdjoint adj hQL hA hB

include adj in
omit [IsIso adj.unit] in
/-- **Stacks 0779 (3), right exactness of the coherator.** -/
theorem preservesFiniteColimits_coherator : PreservesFiniteColimits (coherator hA) :=
  ObjectProperty.preservesFiniteColimits_coreflectorOfLeftAdjoint adj hA

include adj hQL hB in
omit [(sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).IsWeakSerreClass] in
/-- **Stacks 0779 (3), left exactness of the coherator**, a right adjoint. -/
theorem preservesFiniteLimits_coherator : PreservesFiniteLimits (coherator hA) :=
  ObjectProperty.preservesFiniteLimits_coreflectorOfLeftAdjoint adj hQL hA hB

include adj in
omit [IsIso adj.unit] [(sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).IsWeakSerreClass] in
/-- The coherator preserves zero morphisms. -/
theorem preservesZeroMorphisms_coherator : (coherator hA).PreservesZeroMorphisms :=
  have : G.IsLeftAdjoint := adj.isLeftAdjoint
  have : (moduleInverseImage B S hS 𝒳).IsRightAdjoint := adj.isRightAdjoint
  ObjectProperty.preservesZeroMorphisms_coreflectorOfLeftAdjoint (G := G)
    (R := moduleInverseImage B S hS 𝒳) hA

variable [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]

variable (B S hS 𝒳) in
/-- The parasitic modules (**Stacks 0773**) at module universe `u + 1`, read on the ambient
spelling of `Mod(𝒪_𝒳)`. -/
abbrev parasiticModulesSucc :
    ObjectProperty (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
  parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf

variable (B S hS 𝒳) in
/-- **Stacks 0774** (2)(b), `AlgebraicGeometry.Stack.isSerreClass_parasiticModules`, on the
ambient spelling of `Mod(𝒪_𝒳)`. -/
instance isSerreClass_parasiticModulesSucc : (parasiticModulesSucc B S hS 𝒳).IsSerreClass :=
  isSerreClass_parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf

variable (B E h S hS 𝒳) in
/-- `Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`, the class the Verdier quotient of **Stacks 07B6**
divides by. -/
abbrev parasiticSheafFlatBaseChangeModulesSucc :
    ObjectProperty (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
  parasiticModulesSucc B S hS 𝒳 ⊓ sheafFlatBaseChangeModulesSucc B E h S hS 𝒳

include adj in
omit [(sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).IsWeakSerreClass]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))] in
/-- The coherator kills `Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`. -/
theorem isZero_coherator_obj_of_parasitic
    (M : (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳).FullSubcategory)
    (hM : parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳 M.obj) :
    IsZero ((coherator hA).obj M) :=
  (isZero_coherator_obj_iff_isParasitic adj hA M).2 hM.1

include adj hQL hB in
/-- **Stacks 07B7: `Hⁱ : D_QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`**, the descent through the Verdier quotient
`D_QCoh = D_{LQCoh^fbc}/D_{Parasitic ∩ LQCoh^fbc}` of `Q ∘ Hⁱ`. -/
def quasicoherentCohomology (n : ℤ) :
    (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Localization ⥤
      (quasicoherentModulesSucc B S hS 𝒳).FullSubcategory :=
  letI := abelianQuasicoherentModulesSucc adj hQL hA hB
  haveI := preservesFiniteColimits_coherator adj hA
  haveI := preservesFiniteLimits_coherator adj hQL hA hB
  haveI := preservesZeroMorphisms_coherator adj hA
  DerivedCategoryB.serreQuotientCohomology _ _ (coherator hA)
    (isZero_coherator_obj_of_parasitic adj hA) n

include adj hQL hB in
/-- **Stacks 07B7, the defining identity** `Hⁱ ∘ q = Q ∘ Hⁱ`. -/
def quasicoherentCohomologyFac (n : ℤ) :
    (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Q ⋙
        quasicoherentCohomology adj hQL hA hB n ≅
      DerivedCategoryB.derivedCategoryBHomology _ n ⋙ coherator hA :=
  letI := abelianQuasicoherentModulesSucc adj hQL hA hB
  haveI := preservesFiniteColimits_coherator adj hA
  haveI := preservesFiniteLimits_coherator adj hQL hA hB
  haveI := preservesZeroMorphisms_coherator adj hA
  DerivedCategoryB.serreQuotientCohomologyFac _ _ (coherator hA)
    (isZero_coherator_obj_of_parasitic adj hA) n

end AlgebraicGeometry.Stack.FlatFppf
