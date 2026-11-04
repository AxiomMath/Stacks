module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Pushforward of quasi-coherent modules along an affine morphism is exact

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated morphism of schemes. Pushforward of
`𝒪_X`-modules preserves quasi-coherence ([Stacks, Tag 01LC]), so it restricts to a functor
`f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. This file proves that this restriction is **exact** when `f` is
affine.

Left exactness holds with no hypothesis on `f` beyond quasi-compactness and
quasi-separatedness: `f_*` on all modules is a right adjoint, the inclusions of the
quasi-coherent modules are exact, and `QCoh(𝒪_Y) ⥤ Mod(𝒪_Y)` is fully faithful, hence reflects
limits. Right exactness is where affineness enters, through the vanishing of the higher direct
images of a quasi-coherent module along an affine morphism ([Stacks, Tag 01XC]): that vanishing
says exactly that every quasi-coherent module is right acyclic for `f_*`, and in a short exact
sequence of quasi-coherent modules both outer terms are then right acyclic, so
[Stacks, Tag 015D] makes the pushed-forward sequence short exact.

## Main definitions

* `Stacks.AlgebraicGeometry.QuasicoherentPushforward.quasicoherentPushforward` — the
  restriction `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` of `f_*` to the quasi-coherent modules.

## Main results

Both live in the namespace `Stacks.AlgebraicGeometry.QuasicoherentPushforward`.

* `preservesFiniteLimits_quasicoherentPushforward` — the restriction preserves finite limits,
  for an arbitrary quasi-compact, quasi-separated `f`.
* `preservesFiniteColimits_quasicoherentPushforward` — the restriction preserves finite
  colimits, for an affine `f`.

## Implementation notes

**No derived category appears in any statement here**, and no `HasDerivedCategory` instance is
pinned at file level or taken as an argument. Right acyclicity ([Stacks, Tag 0157] part (3)) is
nevertheless defined through the right derived functor on `D⁺`, so the proof of right exactness
needs *some* derived category of `𝒪_X`- and `𝒪_Y`-modules; it installs
`CategoryTheory.HasDerivedCategory.standard` locally inside that one proof, because that is the
model at which `Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom`
([Stacks, Tag 01XC]) is stated. Since the conclusion `PreservesFiniteColimits` does not mention
a derived category, the statement is independent of that choice and the local pin is not a
weakening.

The functor is produced as an `ObjectProperty.lift`, so that composing it with the inclusion of
the quasi-coherent modules on the target is *definitionally* the inclusion on the source
followed by `f_*` (`quasicoherentPushforward_comp_ι`, proved by `rfl`). Both exactness proofs
use that: each transports the property across the inclusion, which is legitimate because the
inclusion is fully faithful and exact.

The right-exactness proof names the direct image at the spelling
`SheafOfModules X.ringCatSheaf ⥤ SheafOfModules Y.ringCatSheaf` rather than taking
`AlgebraicGeometry.Scheme.Modules.pushforward f` at its own declared type
`X.Modules ⥤ Y.Modules`. The two are definitionally equal but carry separately declared
`Category`, `Preadditive` and `Abelian` instances, and the exactness of the inclusion of the
quasi-coherent modules — `isQuasicoherent_ι_preservesFiniteLimits` and its companion — is
stated at the first spelling only. Written at the second, `S.map (…).ι` fails to synthesize
`PreservesZeroMorphisms` for the inclusion even though `inferInstance` finds it in isolation.
Naming the functor at the first spelling and supplying its `Additive`, `PreservesFiniteLimits`
and `PreservesZeroMorphisms` instances explicitly removes the crossing, with no transparency
option.

No `@[stacks]` attribute is attached. Exactness of affine pushforward on quasi-coherent modules
is two of the four assertions of [Stacks, Tag 08D7]; the other two concern the induced functor
on the derived categories, and are not here, so an attribute on these declarations would report
an open tag as formalized.

## References

* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.AlgebraicGeometry.QuasicoherentPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **Pushforward of quasi-coherent modules.** For a quasi-compact, quasi-separated morphism
`f : X ⟶ Y` of schemes, `f_*` preserves quasi-coherence ([Stacks, Tag 01LC]), so it restricts
to a functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. -/
def quasicoherentPushforward :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ Scheme.Modules.pushforward f)
    fun M ↦ have := M.property; AlgebraicGeometry.pushforward_isQuasicoherent f M.obj

/-- Forgetting quasi-coherence identifies `quasicoherentPushforward` with pushforward of all
modules. -/
theorem quasicoherentPushforward_comp_ι :
    quasicoherentPushforward f ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι =
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ Scheme.Modules.pushforward f :=
  rfl

/-- Pushforward of all `𝒪_X`-modules preserves finite limits, being a right adjoint. -/
instance preservesFiniteLimits_pushforward :
    PreservesFiniteLimits (Scheme.Modules.pushforward f) :=
  letI : PreservesLimits (Scheme.Modules.pushforward f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  PreservesLimits.preservesFiniteLimits _

/-- Pushforward of quasi-coherent modules is additive: it is so after the faithful inclusion,
where it is pushforward of all modules. -/
instance additive_quasicoherentPushforward : (quasicoherentPushforward f).Additive where
  map_add {_ _ _ _} := (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.map_injective
    (Functor.map_add (Scheme.Modules.pushforward f))

/-- **Exactness of pushforward on quasi-coherent modules: kernels.** For a quasi-compact,
quasi-separated morphism, the restriction of `f_*` to the quasi-coherent modules preserves
finite limits. Composed with the inclusion of `QCoh(𝒪_Y)` it is the inclusion of `QCoh(𝒪_X)`
followed by `f_*`, both of which preserve finite limits, and the inclusion is fully faithful,
hence reflects them. -/
instance preservesFiniteLimits_quasicoherentPushforward :
    PreservesFiniteLimits (quasicoherentPushforward f) := by
  have h : PreservesFiniteLimits
      (quasicoherentPushforward f ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι) := by
    rw [quasicoherentPushforward_comp_ι]
    exact @comp_preservesFiniteLimits _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι (Scheme.Modules.pushforward f)
      inferInstance (preservesFiniteLimits_pushforward f)
  exact preservesFiniteLimits_of_reflects_of_preserves (quasicoherentPushforward f)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι

/-- **Exactness of pushforward on quasi-coherent modules: cokernels.** For an affine morphism,
the restriction of `f_*` to the quasi-coherent modules preserves finite colimits. Every
quasi-coherent module is right acyclic for `f_*`, because the higher direct images of a
quasi-coherent module along an affine morphism vanish ([Stacks, Tag 01XC]) and that vanishing
*is* right acyclicity for a left exact functor ([Stacks, Tag 015C] part (2)). So in a short
exact sequence of quasi-coherent modules both outer terms are right acyclic, and
[Stacks, Tag 015D] makes the pushed-forward sequence short exact; the inclusion of
`QCoh(𝒪_Y)` is faithful and so reflects short exactness, and an additive functor preserving
short exact sequences is exact. -/
instance preservesFiniteColimits_quasicoherentPushforward [IsAffineHom f] :
    PreservesFiniteColimits (quasicoherentPushforward f) := by
  let _ : HasDerivedCategory.{u + 1} (SheafOfModules X.ringCatSheaf) :=
    HasDerivedCategory.standard _
  let _ : HasDerivedCategory.{u + 1} (SheafOfModules Y.ringCatSheaf) :=
    HasDerivedCategory.standard _
  let _ : EnoughInjectives (SheafOfModules X.ringCatSheaf) :=
    IsGrothendieckAbelian.enoughInjectives
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules Y.ringCatSheaf :=
    Scheme.Modules.pushforward f
  let _ : PreservesFiniteLimits F := preservesFiniteLimits_pushforward f
  let _ : F.Additive := (inferInstance : (Scheme.Modules.pushforward f).Additive)
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  have hacyclic : ∀ M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
      F.rightAcyclic ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.obj M) := by
    intro M
    have := M.property
    exact ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F M.obj).2
      inferInstance).2 fun i hi ↦
        Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f M.obj i hi
  have hShort : ∀ S : ShortComplex
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory, S.ShortExact →
      (S.map (quasicoherentPushforward f)).ShortExact := by
    intro S hS
    have hmapped : ((S.map (quasicoherentPushforward f)).map
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι).ShortExact :=
      ((Functor.rightAcyclic_and_shortExact_map_of_shortExact F
        (S.map (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)
        (hS.map_of_exact _)).1 (hacyclic S.X₁) (hacyclic S.X₃)).2
    exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι hmapped
  have hexact : PreservesFiniteLimits (quasicoherentPushforward f) ∧
      PreservesFiniteColimits (quasicoherentPushforward f) :=
    ((Functor.exact_tfae (quasicoherentPushforward f)).out 1 4).mp hShort
  exact hexact.2

end Stacks.AlgebraicGeometry.QuasicoherentPushforward

end
