module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullbackUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInputs
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Coreflection
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentHasSeparator
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Transport

/-!
# The quasi-coherent direct image of an algebraic stack at module universe `u`

**Stacks 077A** at the section universe `u` of the schemes. For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks, the quasi-coherent direct image and its higher direct images are

`f_{QCoh,*} = Q ∘ f_* ∘ i` and `Rⁱf_{QCoh,*} = Q ∘ Rⁱf_* ∘ i`,

where `i : QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` is the inclusion of **Stacks 06WG**, `f_*` and `Rⁱf_*` are
the direct image of modules (**Stacks 06WE**) and its right derived functors,
`AlgebraicGeometry.Stack.fppfModulesPushforward` and
`AlgebraicGeometry.Stack.fppfModulesHigherDirectImage`, and `Q` is the coherator of
**Stacks 0781** part (2).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentInclusion`: `QCoh(𝒪_𝒳)` at module
  universe `u`, and its inclusion into `Mod(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentPullback`: **Stacks 06WH**, the inverse
  image `f^*` of quasi-coherent modules.
* `AlgebraicGeometry.Stack.AlgebraicStacks.coheratorOfSeparator` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.coheratorAdjunctionOfSeparator`: the coherator `Q`
  with its inputs of **Stacks 0778** discharged except the separator, and its adjunction `i ⊣ Q`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageOfSeparator`: `f_{QCoh,*}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageOfSeparator`:
  `Rⁱf_{QCoh,*}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentPullbackDirectImageAdjunctionOfSeparator`:
  `f^* ⊣ f_{QCoh,*}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.coherator`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.coheratorAdjunction`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage`: the canonical
  functors, with the separator supplied.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentPullbackDirectImageAdjunction`:
  **Stacks 077A**, the first assertion, `f^* ⊣ f_{QCoh,*}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesHigherDirectImageDeltaFunctor`: the
  δ-functor `{Rⁱf_*}` on modules.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageDeltaFunctorOfInputs`:
  the δ-functor `{Rⁱf_{QCoh,*}}`, from `CategoryTheory.DeltaFunctor.ofCoreflections`, over the
  inputs it consumes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.abelianQuasicoherentModulesOfInputs`: the abelian
  structure on `QCoh(𝒪_𝒳)` over the same inputs.

## Implementation notes

### The separator

The coherator is built by the special adjoint functor theorem, one of whose inputs is a separator
of `QCoh(𝒪_𝒴)`. The constructions are first made over it, as the `…OfSeparator` definitions,
and the canonical `AlgebraicGeometry.Stack.AlgebraicStacks.coherator`,
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage` apply them to
`AlgebraicGeometry.Stack.hasSeparator_quasicoherentModules`.

### The middle slot

The source composes through `LQCoh^fbc(𝒪_𝒳)` (**Stacks 0771**, **Stacks 0778**). Here the
middle slot is all of `Mod(𝒪_𝒳)`, and the coherator is the right adjoint of
`QCoh(𝒪_𝒴) ⊆ Mod(𝒪_𝒴)`. For a quasi-compact and quasi-separated `f` the direct image carries
`QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`, where the two coherators agree, being the
right adjoint of one inclusion.

### Relation to the module universe `u + 1`

The base's `AlgebraicGeometry.Stack.AlgebraicStacks.fppfQuasicoherentPushforward` and
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImageQuasicoherent` are the same
composites at module universe `u + 1`, over the coherator inputs at `u + 1`. The direct images
of modules at the two universes are related by the universe lift,
`AlgebraicGeometry.Stack.fppfModulesPushforwardULiftIso`.

**Stacks 077A** is registered at module universe `u`, where every input of the coherator is
proved: the adjunction below, the factorizations
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageIsoComposite` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageIsoComposite` through
`LQCoh^fbc`, and the cohomological δ-functor
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageDeltaFunctor`.  At
module universe `u + 1` the closure of quasi-coherence under colimits, which the coherator
inputs there rest on, goes through the essential surjectivity of `𝓕 ↦ 𝓕^a` of **Stacks 03DX**,
and the library proves that at module universe `u`.

## References

* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `QCoh(𝒪_𝒳)`, the quasi-coherent modules of **Stacks 06WG** on the fppf site of an algebraic
stack, at the module universe `u` of the schemes. -/
abbrev quasicoherentModules (𝒳 : AlgebraicStacks.{u, w} B S hS) :=
  FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

/-- The inclusion `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` at module universe `u`. -/
abbrev quasicoherentInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    quasicoherentModules B S hS 𝒳 ⥤ Stack.fppfModules B S hS 𝒳 :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **Stacks 06WH** at module universe `u`: the inverse image of modules along a 1-morphism of
algebraic stacks carries `QCoh(𝒪_𝒴)` into `QCoh(𝒪_𝒳)`, by
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_modulePullback_univ`. -/
def quasicoherentPullback : quasicoherentModules B S hS 𝒴 ⥤ quasicoherentModules B S hS 𝒳 :=
  ObjectProperty.lift _ (quasicoherentInclusion B S hS 𝒴 ⋙ fppfModulesPullback B S hS f)
    fun M => isQuasicoherentOnSite_modulePullback_univ.{u, u + 1, u, u} B S hS _ _ _ _ _
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) M.obj M.property

/-- The inverse image of quasi-coherent modules followed by the inclusion is the inclusion
followed by the inverse image of modules. -/
def quasicoherentPullbackCompInclusionIso :
    quasicoherentPullback B S hS f ⋙ quasicoherentInclusion B S hS 𝒳 ≅
      quasicoherentInclusion B S hS 𝒴 ⋙ fppfModulesPullback B S hS f :=
  ObjectProperty.liftCompιIso _ _ _

section Coherator

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- `Mod(𝒪_𝒳)` is locally `u`-small at module universe `u`. -/
theorem locallySmall_fppfModules : LocallySmall.{u} (Stack.fppfModules B S hS 𝒳) :=
  have := PresheafOfModules.locallySmall_of_essentiallySmall.{u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj
  locallySmall_of_faithful
    (SheafOfModules.forget (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf))

variable (hsep : HasSeparator (quasicoherentModules B S hS 𝒳))

/-- **The coherator `Q : Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of an algebraic stack at module universe `u`**
(**Stacks 0781** part (2)): `AlgebraicGeometry.FibredSite.moduleCoherator` with its inputs of
**Stacks 0778** discharged, except the separator `hsep`. -/
abbrev coheratorOfSeparator : Stack.fppfModules B S hS 𝒳 ⥤ quasicoherentModules B S hS 𝒳 :=
  FibredSite.moduleCoherator B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (FibredSite.closedUnderColimitsOfSize_quasicoherentModules B S hS _ _)
    (FibredSite.locallySmall_quasicoherentModules B S hS _ _) (locallySmall_fppfModules B S hS 𝒳)
    (FibredSite.wellPowered_op_quasicoherentModules B S hS _ _) hsep

/-- The coherator is right adjoint to the inclusion. -/
abbrev coheratorAdjunctionOfSeparator :
    quasicoherentInclusion B S hS 𝒳 ⊣ coheratorOfSeparator B S hS 𝒳 hsep :=
  FibredSite.moduleCoheratorAdjunction B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _ _ _ _ hsep

end Coherator

section DirectImage

variable (hsep : HasSeparator (quasicoherentModules B S hS 𝒴))

/-- **The quasi-coherent direct image `f_{QCoh,*} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)` of Stacks 077A**, at
module universe `u`: include, take the direct image of modules, and apply the coherator. -/
def quasicoherentDirectImageOfSeparator :
    quasicoherentModules B S hS 𝒳 ⥤ quasicoherentModules B S hS 𝒴 :=
  quasicoherentInclusion B S hS 𝒳 ⋙ fppfModulesPushforward B S hS f ⋙
    coheratorOfSeparator B S hS 𝒴 hsep

/-- **The higher quasi-coherent direct images `Rⁱf_{QCoh,*}` of Stacks 077A**, at module universe
`u`: the composite defining `f_{QCoh,*}` with the `i`-th higher direct image of modules in the
middle. -/
def quasicoherentHigherDirectImageOfSeparator (i : ℕ) :
    quasicoherentModules B S hS 𝒳 ⥤ quasicoherentModules B S hS 𝒴 :=
  quasicoherentInclusion B S hS 𝒳 ⋙ fppfModulesHigherDirectImage B S hS f i ⋙
    coheratorOfSeparator B S hS 𝒴 hsep

/-- The inverse image of quasi-coherent modules is left adjoint to `f_{QCoh,*}`: the composite of
the adjunction `f^* ⊣ f_*` with the coherator adjunction, restricted along the fully faithful
inclusion of `QCoh(𝒪_𝒳)`. -/
def quasicoherentPullbackDirectImageAdjunctionOfSeparator :
    quasicoherentPullback B S hS f ⊣ quasicoherentDirectImageOfSeparator B S hS f hsep :=
  Adjunction.restrictFullyFaithful
    ((coheratorAdjunctionOfSeparator B S hS 𝒴 hsep).comp
      (fppfModulesPullbackPushforwardAdjunction B S hS f))
    (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι _)
    (quasicoherentPullbackCompInclusionIso B S hS f).symm (Iso.refl _)

end DirectImage

section Canonical

/-! ### The canonical functors

The separator of `QCoh(𝒪_𝒳)` is `AlgebraicGeometry.Stack.hasSeparator_quasicoherentModules`, so
the coherator and the quasi-coherent direct images below take no further input. -/

/-- **The coherator `Q : Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of an algebraic stack** (**Stacks 0781** part (2)),
the right adjoint of the inclusion `QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`, at module universe `u`. -/
abbrev coherator (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Stack.fppfModules B S hS 𝒳 ⥤ quasicoherentModules B S hS 𝒳 :=
  coheratorOfSeparator B S hS 𝒳 (hasSeparator_quasicoherentModules B S hS 𝒳)

/-- The coherator is right adjoint to the inclusion `QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`. -/
abbrev coheratorAdjunction (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    quasicoherentInclusion B S hS 𝒳 ⊣ coherator B S hS 𝒳 :=
  coheratorAdjunctionOfSeparator B S hS 𝒳 (hasSeparator_quasicoherentModules B S hS 𝒳)

/-- **The quasi-coherent direct image `f_{QCoh,*} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)` of Stacks 077A**:
the inclusion, the direct image of modules, and the coherator. -/
abbrev quasicoherentDirectImage : quasicoherentModules B S hS 𝒳 ⥤ quasicoherentModules B S hS 𝒴 :=
  quasicoherentDirectImageOfSeparator B S hS f (hasSeparator_quasicoherentModules B S hS 𝒴)

/-- **The higher quasi-coherent direct images `Rⁱf_{QCoh,*} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)` of
Stacks 077A**: the inclusion, the `i`-th higher direct image of modules, and the coherator. -/
abbrev quasicoherentHigherDirectImage (i : ℕ) :
    quasicoherentModules B S hS 𝒳 ⥤ quasicoherentModules B S hS 𝒴 :=
  quasicoherentHigherDirectImageOfSeparator B S hS f (hasSeparator_quasicoherentModules B S hS 𝒴) i

/-- **Stacks 077A, the first assertion: `f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)` has the right adjoint
`f_{QCoh,*}`**, defined as the composite of the inclusion, the direct image of modules
(**Stacks 06WE**) and the coherator (**Stacks 0778**, **Stacks 0781** part (2)).

It holds for every 1-morphism; the source states it for quasi-compact and quasi-separated ones,
for which the direct image of a quasi-coherent module lies in `LQCoh^fbc(𝒪_𝒴)`, where the
coherator is the one of **Stacks 0778**. -/
@[stacks 077A "first assertion: f^* on quasi-coherent modules has the right adjoint \
  f_{QCoh,*} = Q ∘ f_* ∘ i, for every 1-morphism of algebraic stacks"]
def quasicoherentPullbackDirectImageAdjunction :
    quasicoherentPullback B S hS f ⊣ quasicoherentDirectImage B S hS f :=
  quasicoherentPullbackDirectImageAdjunctionOfSeparator B S hS f
    (hasSeparator_quasicoherentModules B S hS 𝒴)

end Canonical

section DeltaFunctor

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat enoughInjectives_fppfModules

/-- **The higher direct images of modules form a cohomological δ-functor** (**Stacks 010Q**) at
module universe `u`: `CategoryTheory.DeltaFunctor` of the right derived functors of
`AlgebraicGeometry.Stack.fppfModulesPushforward`. -/
def fppfModulesHigherDirectImageDeltaFunctor :
    DeltaFunctor (Stack.fppfModules B S hS 𝒳) (Stack.fppfModules B S hS 𝒴) :=
  letI := HasDerivedCategory.standard (Stack.fppfModules B S hS 𝒳)
  letI := HasDerivedCategory.standard (Stack.fppfModules B S hS 𝒴)
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (fppfModulesPushforward B S hS f)

/-- The `n`-th functor of `fppfModulesHigherDirectImageDeltaFunctor` is the `n`-th higher
direct image `fppfModulesHigherDirectImage`. -/
@[simp]
theorem fppfModulesHigherDirectImageDeltaFunctor_functor (n : ℕ) :
    (fppfModulesHigherDirectImageDeltaFunctor B S hS f).functor n =
      fppfModulesHigherDirectImage B S hS f n :=
  let := HasDerivedCategory.standard (Stack.fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (Stack.fppfModules B S hS 𝒴)
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor _ n

variable (hsep𝒳 : HasSeparator (quasicoherentModules B S hS 𝒳))
  (hsep : HasSeparator (quasicoherentModules B S hS 𝒴))
  [(lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).IsWeakSerreClass]
  (hi𝒳 : ∀ M, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
    ((quasicoherentInclusion B S hS 𝒳).obj M))
  (hi𝒴 : ∀ M, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
    ((quasicoherentInclusion B S hS 𝒴).obj M))
  [PreservesFiniteColimits
    ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coheratorOfSeparator B S hS 𝒳 hsep𝒳)]
  [PreservesFiniteColimits
    ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ coheratorOfSeparator B S hS 𝒴 hsep)]
  (hD : ∀ F, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F → ∀ n,
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
      ((fppfModulesHigherDirectImage B S hS f n).obj F))
  (hDQ : ∀ F, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F →
    IsZero ((coheratorOfSeparator B S hS 𝒳 hsep𝒳).obj F) → ∀ n,
      IsZero ((coheratorOfSeparator B S hS 𝒴 hsep).obj
        ((fppfModulesHigherDirectImage B S hS f n).obj F)))

include hi𝒳 in
/-- **`QCoh(𝒪_𝒳)` is abelian** at module universe `u` (**Stacks 06WV** part (2)): it is
coreflective in the weak Serre class `LQCoh^fbc(𝒪_𝒳)` with a right exact coreflector, by
`CategoryTheory.DeltaFunctor.abelianOfCoreflectionOnClass`. -/
@[instance_reducible]
def abelianQuasicoherentModulesOfInputs : Abelian (quasicoherentModules B S hS 𝒳) :=
  letI := (coheratorAdjunctionOfSeparator B S hS 𝒳 hsep𝒳).right_adjoint_additive
  DeltaFunctor.abelianOfCoreflectionOnClass
    (coheratorAdjunctionOfSeparator B S hS 𝒳 hsep𝒳) _ hi𝒳

include hi𝒳 hi𝒴 hD hDQ in
/-- The family `Rⁱf_{QCoh,*}` with the δ-functor structure of
`CategoryTheory.DeltaFunctor.ofCoreflections`, over the inputs it consumes: `LQCoh^fbc` is a
weak Serre class containing `QCoh` (**Stacks 0771**, **Stacks 0778**), the coherators are right
exact on it (**Stacks 0779**), the higher direct images preserve it (**Stacks 0771**), and they
carry the objects killed by the coherator to objects killed by the coherator (**Stacks 0779**,
**Stacks 0775**). -/
def quasicoherentHigherDirectImageDeltaFunctorOfInputs :
    DeltaFunctor (quasicoherentModules B S hS 𝒳) (quasicoherentModules B S hS 𝒴) :=
  letI := (coheratorAdjunctionOfSeparator B S hS 𝒳 hsep𝒳).right_adjoint_additive
  letI := (coheratorAdjunctionOfSeparator B S hS 𝒴 hsep).right_adjoint_additive
  DeltaFunctor.ofIso
    (DeltaFunctor.ofCoreflections (coheratorAdjunctionOfSeparator B S hS 𝒳 hsep𝒳) _ hi𝒳
      (coheratorAdjunctionOfSeparator B S hS 𝒴 hsep) _ hi𝒴
      (fppfModulesHigherDirectImageDeltaFunctor B S hS f) hD hDQ)
    (quasicoherentHigherDirectImageOfSeparator B S hS f hsep) (fun n ↦
      Functor.isoWhiskerLeft (quasicoherentInclusion B S hS 𝒳) (Functor.isoWhiskerRight
        (eqToIso (fppfModulesHigherDirectImageDeltaFunctor_functor B S hS f n))
        (coheratorOfSeparator B S hS 𝒴 hsep)))

end DeltaFunctor

end AlgebraicGeometry.Stack.AlgebraicStacks
