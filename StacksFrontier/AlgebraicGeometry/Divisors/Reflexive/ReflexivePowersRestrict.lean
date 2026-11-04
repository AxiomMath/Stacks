module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowers
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The reflexive powers on an open where the module is invertible

Let `X` be an integral locally Noetherian scheme, `ℱ` a coherent `𝒪_X`-module and `V ⊆ X` a
nonempty open on which `ℱ` is invertible.  Then the reflexive powers of [Stacks, Tag 0EBN] agree
on `V` with the ordinary tensor powers:

`ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}`.

This is the comparison that the proof of the colimit clause of [Stacks, Tag 0EBN] uses before it
quotes [Stacks, Tag 01PW] for the invertible module `ℱ|_V`: the source chooses `V` by
[Stacks, Tag 0AY6] and then argues on `V` with ordinary powers of an invertible module, which is
what Tag 01PW is about.  This module relates `reflexivePower` to a restriction.

The proof of the clause, `…nonempty_isColimit_reflexivePowerSystemPushforwardCocone` of
`SectionLocusColimitSections.lean`, does not in the end go through this comparison: it reads the
divisibility of the transition maps off on sections over an affine chart, which is all the
source's appeal to Tag 01PW is used for.  The comparison is what
`SectionLocusTrivialization.lean` uses to trivialize the system over the isomorphism locus `U`,
and so is still an input of the cocone itself.

The point of the proof is that the reflexive hull is invisible over `V`.  Over `V` the tensor
product `ℱ ⊗ ℱ^{[n]}` is invertible, hence reflexive, so the canonical map into its hull becomes
an isomorphism after restriction to `V` — that is
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual` — and the recursion
`ℱ^{[n + 1]} = (ℱ ⊗ ℱ^{[n]})^{∨∨}` therefore restricts to the recursion
`(ℱ|_V)^{⊗ (n + 1)} = ℱ|_V ⊗ (ℱ|_V)^{⊗ n}` with no hull.

## Main definitions

* `tensorPower ℱ n`: the ordinary tensor powers `ℱ^{⊗ n}`, indexed exactly as
  `reflexivePower` indexes the reflexive powers — the value at `0` is `𝒪_X`, the value at `1` is
  `ℱ` on the nose, and `ℱ^{⊗ (n + 2)} = ℱ ⊗ ℱ^{⊗ (n + 1)}`.  So the comparison below is an
  isomorphism of two families with the same indexing and the same two initial terms.
* `tensorSheafRestrictIso`: `(𝒜 ⊗ ℬ)|_V ≅ 𝒜|_V ⊗ ℬ|_V`, [Stacks, Tag 01CD] at an open
  immersion of schemes and at `Scheme.Modules.restrictFunctor`.
* `restrictReflexivePowerIso`: **the comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}`.**

## Main results

* `isInvertible_tensorPower`, `isCoherent_tensorPower`: every ordinary tensor power of an
  invertible module is invertible, and every positive ordinary tensor power of a coherent module
  is coherent.
* `isCoherent_reflexivePower`: every positive reflexive power of a coherent module on a locally
  Noetherian scheme is coherent.  This is the hull clause of [Stacks, Tag 0EBH] and
  [Stacks, Tag 01CE] applied along the recursion.
* `nonempty_restrictReflexivePowerIso`: **the comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}`**, as the
  statement that such an isomorphism exists; `restrictReflexivePowerIso` is the chosen one.

## Implementation notes

**Why the tensor-restriction isomorphism is rebuilt.**
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso` is the same mathematics over a ringed
space, for `Stacks.Cohomology.HigherDirectImage.moduleRestriction`.  That functor and Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` are the same pushforward along the open-image
functor of sites, differing only in the comparison of structure sheaves — the identity for the
first, `(f.appIso U).inv` for the second, and `AlgebraicGeometry.Scheme.Opens.ι_appIso` says the
latter is the identity.  They are nevertheless not definitionally equal at the transparency the
module system exposes, so the ringed-space statement cannot be read at the restriction spelling
in which `isIso_restrict_toDoubleDual` and
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_restrict` are stated, and those two are
what the proof needs.  `tensorSheafRestrictIso` is therefore assembled from the unconditional
[Stacks, Tag 01CD] (`Stacks.RingedSpace.comparisonBifunctorIso`) and Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, so no new comparison morphism is
constructed and no transparency or heartbeat escape hatch is needed.

**Why `tensorPower` is defined here and not taken from the library.**  Two ordinary tensor
powers of a module on a scheme are already in the tree, and the comparison is not a statement
about either.  `Stacks.TensorSectionPower.powObj` is left-bracketed and starts at `ℱ` in degree
`0`, so its degree `n` is the source's `ℱ^{⊗ (n + 1)}` and no term of it is the structure sheaf;
`Stacks.SheafOfModules.TensorPower.tensorPower` is indexed by `ℤ` and built from the
autoequivalence `- ⊗ ℒ`, so it is defined only for an invertible module and its positive part is
again bracketed the other way.  The reflexive powers of [Stacks, Tag 0EBN] are right-bracketed
and start at `𝒪_X`, and the comparison is an isomorphism of two families *term by term*: it has
to be stated for the ordinary powers at the same indexing and the same bracketing, which is what
`tensorPower` is.  Relating `tensorPower` to those two — a reassociation and a reindexing — is
what a consumer quoting [Stacks, Tag 01PW], which is stated for `powObj`, will need next.

**Why the statement is an isomorphism and not an equality of the two powers.**  The reflexive
hull of an invertible module is isomorphic to it, not equal to it, so `ℱ^{[n]}|_V` and
`(ℱ|_V)^{⊗ n}` are genuinely different objects of `V.Modules` and only the isomorphism holds.
The isomorphism is produced by induction, and each step consumes the previous isomorphism twice —
once as data, once through the reflexivity of the restricted tensor product that it transports —
so the recursion is carried out for the proposition `Nonempty (· ≅ ·)` and
`restrictReflexivePowerIso` is a choice of isomorphism from it.  No compatibility of the chosen
isomorphisms with the transition maps of the system is claimed, and none can be: a commuting
square is a statement about the chosen isomorphisms, and `Nonempty.some` makes no choice a proof
can see.  The colimit clause of [Stacks, Tag 0EBN] needs that compatibility, so
`StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionRestrict` rebuilds the
comparison as a recursion producing data, with computation rules, and proves the squares there.

**The hypotheses.**  Integrality and local Noetherianity of `X` are the standing hypotheses of
the source's section, and both are used: local Noetherianity through the coherence of the
reflexive powers and through `isIso_restrict_toDoubleDual`, integrality through
`AlgebraicGeometry.isReflexive_of_isInvertible`, which is stated over an integral scheme.  `V` is
required to be nonempty for the same reason: the open subscheme has to be integral for that
result to apply to `ℱ|_V`, and the empty scheme is not.  Reflexivity of `ℱ` and the rank-one
condition are *not* assumed — the comparison holds for an arbitrary coherent `ℱ` on an open where
it happens to be invertible, and the source's choice of `V` is what makes the hypothesis
available in the application.

**No `@[stacks]` attribute.**  This isomorphism is an unnamed step inside the source's proof of
[Stacks, Tag 0EBN], not a clause of that tag or of [Stacks, Tag 0EBR].  The colimit clause itself
is `…nonempty_isColimit_reflexivePowerSystemPushforwardCocone` of
`SectionLocusColimitSections.lean`, and the two registrations of Tag 0EBR, now in
`SectionLocusAffineTag.lean`, are unconditional.  Tag 01CD, Tag 01CE and Tag 0EBH are registered
where they are proved and are only used here.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
-/

@[expose] public section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive reflexiveHull toDoubleDual)
open Stacks.AlgebraicGeometry.ReflexiveEquivalence (isCoherent_doubleDual isCoherent_restrict
  isReflexive_of_iso isIso_restrict_toDoubleDual)

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

variable {X : Scheme.{u}}

/-! ### The tensor product and restriction to an open subscheme -/

/-- **[Stacks, Tag 01CD] at an open immersion of schemes**: the restriction of a tensor product
is the tensor product of the restrictions, `(𝒜 ⊗ ℬ)|_V ≅ 𝒜|_V ⊗ ℬ|_V`.

Restriction is Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which is the
spelling the reflexive-hull theory of `ReflexiveEquivalence/StalkDescent.lean` is stated in; it
is naturally isomorphic to the pullback functor, and for the pullback the statement is the
unconditional `Stacks.RingedSpace.comparisonBifunctorIso`. -/
def tensorSheafRestrictIso (V : X.Opens) (A B : X.Modules) :
    (Scheme.Modules.restrictFunctor V.ι).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨V.toScheme.toRingedSpace.presheaf, V.toScheme.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.restrictFunctor V.ι).obj A)).obj
        ((Scheme.Modules.restrictFunctor V.ι).obj B) :=
  let e₁ : (Scheme.Modules.restrictFunctor V.ι).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj B) ≅
      (Scheme.Modules.pullback V.ι).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj B) :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj B)
  let e₂ : (Scheme.Modules.pullback V.ι).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨V.toScheme.toRingedSpace.presheaf, V.toScheme.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.pullback V.ι).obj A)).obj ((Scheme.Modules.pullback V.ι).obj B) :=
    (Stacks.RingedSpace.comparisonBifunctorIso V.ι.toLRSHom.toShHom).app (A, B)
  let pulledLeft : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.sheaf) :=
    (Scheme.Modules.pullback V.ι).obj A
  let pulledRight : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.sheaf) :=
    (Scheme.Modules.pullback V.ι).obj B
  let restrictedLeft : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.sheaf) :=
    (Scheme.Modules.restrictFunctor V.ι).obj A
  let restrictedRight : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.sheaf) :=
    (Scheme.Modules.restrictFunctor V.ι).obj B
  let factorIso : (pulledLeft, pulledRight) ≅ (restrictedLeft, restrictedRight) :=
    Iso.prod ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app A).symm
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app B).symm
  let e₃ :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
        pulledLeft).obj pulledRight ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
        restrictedLeft).obj restrictedRight :=
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      V.toScheme.sheaf)).mapIso (X := (pulledLeft, pulledRight))
        (Y := (restrictedLeft, restrictedRight)) factorIso
  e₁ ≪≫ e₂ ≪≫ e₃

/-! ### The ordinary tensor powers -/

/-- **The ordinary tensor powers `ℱ^{⊗ n}`**, indexed exactly as
`Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePower` indexes the reflexive powers: the value
at `0` is `𝒪_X`, the value at `1` is `ℱ`, and `ℱ^{⊗ (n + 2)} = ℱ ⊗ ℱ^{⊗ (n + 1)}`.  Dropping the
reflexive hull from the recursion of [Stacks, Tag 0EBN] is the only difference. -/
def tensorPower (F : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | 1 => F
  | n + 2 => ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj (tensorPower F (n + 1))

/-- The zeroth ordinary tensor power is the structure sheaf. -/
@[simp]
theorem tensorPower_zero (F : X.Modules) :
    tensorPower F 0 = SheafOfModules.unit X.ringCatSheaf := rfl

/-- The first ordinary tensor power is `ℱ` itself. -/
@[simp]
theorem tensorPower_one (F : X.Modules) : tensorPower F 1 = F := rfl

/-- The recursion for the ordinary tensor powers, for `n ≥ 1`. -/
theorem tensorPower_succ_succ (F : X.Modules) (n : ℕ) :
    tensorPower F (n + 2) = ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj (tensorPower F (n + 1)) :=
  rfl

/-- **Every ordinary tensor power of an invertible module is invertible.**  This is
[Stacks, Tag 01CT] (1) along the recursion, with the structure sheaf at the index `0`. -/
theorem isInvertible_tensorPower (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) (n : ℕ) :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPower L n) := by
  have key : ∀ m : ℕ, Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPower L (m + 1)) := by
    intro m
    induction m with
    | zero => exact hL
    | succ k ih =>
        have := hL
        have := ih
        exact Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
          L (tensorPower L (k + 1))
  cases n with
  | zero => exact Stacks.SheafOfModules.isInvertible_unit X.sheaf.obj X.ringCatSheaf.property
  | succ m => exact key m

/-- The tensor product of two coherent modules is coherent, [Stacks, Tag 01CE]. -/
private theorem isCoherent_sheafTensor_obj_obj (F G : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (hG : _root_.SheafOfModules.IsCoherent G) :
    _root_.SheafOfModules.IsCoherent
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G : X.Modules) :=
  @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F G hF hG

/-- **Every positive ordinary tensor power of a coherent module is coherent**, by
[Stacks, Tag 01CE] along the recursion.  The index `0` is excluded because the structure sheaf of
a scheme is coherent only under a further hypothesis, which this statement does not need. -/
theorem isCoherent_tensorPower (L : X.Modules) (hL : _root_.SheafOfModules.IsCoherent L)
    (n : ℕ) : _root_.SheafOfModules.IsCoherent (tensorPower L (n + 1)) := by
  induction n with
  | zero => exact hL
  | succ k ih =>
      exact isCoherent_sheafTensor_obj_obj L (tensorPower L (k + 1)) hL ih

/-! ### Coherence of the reflexive powers -/

/-- **Every positive reflexive power of a coherent module is coherent.**  The recursion of
[Stacks, Tag 0EBN] is a tensor product followed by a reflexive hull, and each of the two steps
preserves coherence on a locally Noetherian scheme: the first by [Stacks, Tag 01CE], the second
by the hull clause of [Stacks, Tag 0EBH]. -/
theorem isCoherent_reflexivePower [IsLocallyNoetherian X] (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent (reflexivePower F (n + 1)) := by
  induction n with
  | zero => exact hF
  | succ k ih =>
      exact @isCoherent_doubleDual X ‹_›
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
          (reflexivePower F (k + 1)) : X.Modules)
        (isCoherent_sheafTensor_obj_obj F (reflexivePower F (k + 1)) hF ih)

/-! ### The comparison on an open where the module is invertible -/

variable (F : X.Modules) (V : X.Opens)

/-- **The comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}` for `n ≥ 1`**, the inductive step of
`nonempty_restrictReflexivePowerIso`.

In the step from `n` to `n + 1` the restriction of `ℱ ⊗ ℱ^{[n]}` is, by the inductive hypothesis
and `tensorSheafRestrictIso`, the invertible module `(ℱ|_V)^{⊗ (n + 1)}`; an invertible module on
an integral locally Noetherian scheme is reflexive, so the restriction to `V` of the canonical
map of `ℱ ⊗ ℱ^{[n]}` into its reflexive hull is an isomorphism, and that hull is `ℱ^{[n + 1]}`. -/
theorem nonempty_restrictReflexivePowerSuccIso [IsIntegral X] [IsLocallyNoetherian X]
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (n : ℕ) :
    Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1)) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)) := by
  have hVint : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have hVnoeth : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have hFV : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.restrictFunctor V.ι).obj F) :=
    @isCoherent_restrict X ‹_› V F hF
  induction n with
  | zero => exact ⟨Iso.refl _⟩
  | succ k ih =>
      obtain ⟨e⟩ := ih
      have hPcoh : _root_.SheafOfModules.IsCoherent (reflexivePower F (k + 1)) :=
        isCoherent_reflexivePower F hF k
      have hGcoh : _root_.SheafOfModules.IsCoherent
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
            (reflexivePower F (k + 1)) : X.Modules) :=
        isCoherent_sheafTensor_obj_obj F (reflexivePower F (k + 1)) hF hPcoh
      -- The restriction of `ℱ ⊗ ℱ^{[k + 1]}` is `ℱ|_V ⊗ (ℱ|_V)^{⊗ (k + 1)}`.
      let restrictedFactor : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.sheaf) :=
        (Scheme.Modules.restrictFunctor V.ι).obj F
      let restrictedPower : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.sheaf) :=
        (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (k + 1))
      let ordinaryPower : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.sheaf) :=
        tensorPower (X := V.toScheme) restrictedFactor (k + 1)
      let factorIso : (restrictedFactor, restrictedPower) ≅ (restrictedFactor, ordinaryPower) :=
        Iso.prod (Iso.refl restrictedFactor) e
      have e₂ :
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
            restrictedFactor).obj restrictedPower ≅
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
            restrictedFactor).obj ordinaryPower :=
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          V.toScheme.sheaf)).mapIso (X := (restrictedFactor, restrictedPower))
            (Y := (restrictedFactor, ordinaryPower)) factorIso
      have eG : (Scheme.Modules.restrictFunctor V.ι).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
              (reflexivePower F (k + 1)) : X.Modules) ≅
          ((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨V.toScheme.toRingedSpace.presheaf, V.toScheme.toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.restrictFunctor V.ι).obj F)).obj
            (tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (k + 1)) :=
        tensorSheafRestrictIso V F (reflexivePower F (k + 1)) ≪≫ e₂
      -- That module is the ordinary power `(ℱ|_V)^{⊗ (k + 2)}`, which is invertible, hence
      -- reflexive.
      have hinv := isInvertible_tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) hV (k + 2)
      have hpowcoh : _root_.SheafOfModules.IsCoherent
          (tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (k + 2)) :=
        isCoherent_tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) hFV (k + 1)
      have hpow := tensorPower_succ_succ ((Scheme.Modules.restrictFunctor V.ι).obj F) k
      rw [hpow] at hinv hpowcoh
      have hpowrefl : IsReflexive
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨V.toScheme.toRingedSpace.presheaf, V.toScheme.toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.restrictFunctor V.ι).obj F)).obj
            (tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (k + 1)) :
            V.toScheme.Modules) :=
        @AlgebraicGeometry.isReflexive_of_isInvertible V.toScheme hVint hVnoeth _
          hinv.toAlgebraicGeometry
      have hGrescoh : _root_.SheafOfModules.IsCoherent
          ((Scheme.Modules.restrictFunctor V.ι).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
              (reflexivePower F (k + 1)) : X.Modules)) :=
        @isCoherent_restrict X ‹_› V
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
            (reflexivePower F (k + 1)) : X.Modules) hGcoh
      have hGresrefl : IsReflexive ((Scheme.Modules.restrictFunctor V.ι).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
            (reflexivePower F (k + 1)) : X.Modules)) :=
        @isReflexive_of_iso V.toScheme hVnoeth _ _ hpowcoh hGrescoh eG.symm hpowrefl
      -- So the restriction of the canonical map into the hull is invertible.
      have hiso : IsIso ((Scheme.Modules.restrictFunctor V.ι).map
          (toDoubleDual (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
            (reflexivePower F (k + 1)) : X.Modules))) :=
        @isIso_restrict_toDoubleDual X ‹_› V
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
            (reflexivePower F (k + 1)) : X.Modules) hGcoh hGresrefl
      exact ⟨(@asIso _ _ _ _ _ hiso).symm ≪≫ eG⟩

/-- **The comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}`.**  Let `ℱ` be a coherent module on an integral
locally Noetherian scheme `X` and let `V` be a nonempty open on which `ℱ` is invertible.  Then
every reflexive power of [Stacks, Tag 0EBN] restricts on `V` to the ordinary tensor power of the
restriction, for the indexing which gives both families the structure sheaf at `0` and `ℱ` at
`1`.

This is the step the source's proof of the colimit clause of [Stacks, Tag 0EBN] makes before
quoting [Stacks, Tag 01PW] for `ℱ|_V`.  The clause itself is
`…nonempty_isColimit_reflexivePowerSystemPushforwardCocone` of
`SectionLocusColimitSections.lean`, whose argument reads the divisibility off on sections instead;
see the module documentation. -/
theorem nonempty_restrictReflexivePowerIso [IsIntegral X] [IsLocallyNoetherian X]
    [_root_.SheafOfModules.IsCoherent F] [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (n : ℕ) :
    Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F n) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) n) := by
  cases n with
  | zero => exact ⟨Scheme.Modules.restrictUnitIso V.ι⟩
  | succ m =>
      exact nonempty_restrictReflexivePowerSuccIso F V
        ‹_root_.SheafOfModules.IsCoherent F› hV m

/-- **The comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}`**, as a chosen isomorphism.  Its compatibility
with the transition maps of the system of [Stacks, Tag 0EBN] is not claimed. -/
def restrictReflexivePowerIso [IsIntegral X] [IsLocallyNoetherian X]
    [_root_.SheafOfModules.IsCoherent F] [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (n : ℕ) :
    (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F n) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) n :=
  (nonempty_restrictReflexivePowerIso F V hV n).some

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
