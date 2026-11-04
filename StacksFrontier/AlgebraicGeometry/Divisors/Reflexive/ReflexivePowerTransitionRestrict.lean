module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowersRestrict

/-!
# The system of reflexive powers restricted to an open where the module is invertible

Let `X` be an integral locally Noetherian scheme, `ℱ` a coherent `𝒪_X`-module, `V ⊆ X` a nonempty
open on which `ℱ` is invertible, and `s ∈ Γ(X, ℱ)`.  The comparison
`ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}` of
`StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowersRestrict` is a *term-by-term*
isomorphism, chosen out of a `Nonempty` and therefore with no computation rule.  The colimit
clause of [Stacks, Tag 0EBN] is about the whole system

`𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯`,

so it needs the comparison to be compatible with the transition maps.  This file rebuilds the
comparison **as data**, by a recursion with equations, and proves the commuting square at each
step.

## Main definitions

* `mulSection ℱ s 𝒢`: multiplication by `s`, `𝒢 ⟶ ℱ ⊗ 𝒢`, with source and target ascribed in
  Mathlib's `AlgebraicGeometry.Scheme.Modules` spelling.  This is
  `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom` with the one crossing between the two
  spellings of the tensor product performed once, inside a defeq-tolerant `:=`.
* `tensorPowerTransition ℱ s n`: the transitions `ℱ^{⊗ n} ⟶ ℱ^{⊗ (n + 1)}` of the ordinary
  tensor-power system, i.e. the transitions of [Stacks, Tag 0EBN] with the reflexive hull
  dropped, at the indexing of
  `Stacks.AlgebraicGeometry.ReflexivePowers.tensorPower`.
* `restrictPowerIso ℱ V hF hV n`: **the comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}` as a recursively
  defined family**, with `restrictPowerIso_zero`, `restrictPowerIso_one` and
  `restrictPowerIso_succ_succ` as its computation rules.  Unlike
  `Stacks.AlgebraicGeometry.ReflexivePowers.restrictReflexivePowerIso`, which is
  `(nonempty_restrictReflexivePowerIso …).some` and is therefore opaque, this one can be
  reasoned about.
* `restrictTensorPowerIso`, `restrictPowerSuccIso`: the two halves of the inductive step — the
  comparison of `(ℱ ⊗ ℱ^{[n + 1]})|_V` with `(ℱ|_V)^{⊗ (n + 2)}`, and that composed with the
  inverse of the restricted map into the reflexive hull.

## Main results

* `isIso_restrict_toDoubleDual_tensor_reflexivePower`: **over `V` the canonical map of
  `ℱ ⊗ ℱ^{[n + 1]}` into its reflexive hull is invertible**, given the comparison at `n + 1`.
  This is the inductive content of the construction, isolated so that the step is a one-line
  composite and the square below is provable: over `V` that tensor product is
  `(ℱ|_V)^{⊗ (n + 2)}`, which is invertible, hence reflexive, so
  `Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual` applies.
* `restrict_toDoubleDual_comp_restrictPowerSuccIso_hom`: the comparison at `n + 2` cancels the
  restricted map into the hull.
* `restrict_reflexivePowerTransition_comp_restrictPowerIso_hom`: **the commuting square at
  `n + 1`.**  The restricted transition `ℱ^{[n + 1]}|_V ⟶ ℱ^{[n + 2]}|_V`, followed by the
  comparison at `n + 2`, is the restriction of multiplication by `s` followed by the comparison
  of the tensor product.  In other words: *over `V` the transitions of the system of
  [Stacks, Tag 0EBN] are multiplication by `s`, the reflexive hull contributing nothing.*

## Implementation notes

**What the square says, and where the identification of its right-hand side is finished.**  The
right-hand side of `restrict_reflexivePowerTransition_comp_restrictPowerIso_hom` is the
*restriction of* multiplication by `s` on `X`, transported by `tensorSheafRestrictIso`, and not
`mulSection (ℱ|_V) (s|_V)`, which is what `tensorPowerTransition` of the restricted module is
built from.  Identifying the two is the left-unitor coherence of [Stacks, Tag 01CD] at the
restriction functor, and it is carried out in
`StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionMulSection`:
`restrict_mulSection` is the identification and, for every `n`,
`restrict_reflexivePowerTransition_comp_restrictPowerIso_hom'` is the resulting square against
`tensorPowerTransition (ℱ|_V) (s|_V)`.

The coherence itself is the unconditional `Stacks.RingedSpace.comparison_leftUnitor`, proved for
the *pullback* functor.  Conjugating it onto the restriction functor needs the identification of
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso V.ι` with
`Stacks.RingedSpace.pullbackObjUnitIso` conjugated by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι`, which is
`Stacks.AlgebraicGeometry.RestrictMulSection.restrictUnitIso_eq`; its proof transposes both
sides along `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, where both become the
structure morphism `(V.ι)^♯`.  `Stacks.RingedSpace.pullbackAdjunction`, which
`comparison_leftUnitor` is proved over, *is* Mathlib's `pullbackPushforwardAdjunction` at this
spelling, by `rfl`.

**Why the comparison is rebuilt instead of reused.**  The inductive step consumes the comparison
at `n + 1` twice, once as data and once through the reflexivity of the restricted tensor product
that it transports, which is why `ReflexivePowersRestrict.lean` carries the recursion for the
proposition `Nonempty (· ≅ ·)`.  A commuting square is a statement about the chosen
isomorphisms, so it cannot be proved for a choice made by `Nonempty.some`.  Isolating the
invertibility of the restricted map into the hull as
`isIso_restrict_toDoubleDual_tensor_reflexivePower` makes the recursion produce data with no
loss: the step is then literally `(asIso …).symm ≪≫ restrictTensorPowerIso`, and both of its
factors are available to a proof.

**No `@[stacks]` attribute.**  Nothing here is a clause of a tag.  The colimit clause of
[Stacks, Tag 0EBN] is proved in `SectionLocusColimitSections.lean`, and the two registrations of
[Stacks, Tag 0EBR], in `SectionLocusAffineTag.lean`, carry no hypothesis beyond the source's
own.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive reflexiveHull toDoubleDual)
open Stacks.AlgebraicGeometry.ReflexiveEquivalence (isCoherent_doubleDual isCoherent_restrict
  isReflexive_of_iso isIso_restrict_toDoubleDual)

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable {X : Scheme.{u}}

/-! ### Multiplication by a global section, ascribed at `Scheme.Modules` -/

/-- **Multiplication by a global section `s` of `ℱ`**, `𝒢 ⟶ ℱ ⊗ 𝒢`, with source and target
ascribed in Mathlib's `AlgebraicGeometry.Scheme.Modules` spelling rather than at the monoidal
product of `Stacks.SheafOfModules.OnSpace.monoidal`.  The two are equal by `rfl`, but a composite
mixing them is not type-correct at `implicit` transparency, so `rw` refuses a goal containing one;
the crossing happens once here, inside a defeq-tolerant `:=`. -/
def mulSection (F : X.Modules) (s : F.sections) (G : X.Modules) :
    G ⟶ ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G)) : X.Modules) :=
  mulSectionHom X.toRingedSpace (F.unitHomEquiv.symm s)

/-- The transition out of degree `n + 1` of the system of [Stacks, Tag 0EBN], written as
multiplication by `s` followed by the map into the hull, both ascribed at `X.Modules`. -/
theorem reflexivePowerTransition_succ' (F : X.Modules) (s : F.sections) (n : ℕ) :
    reflexivePowerTransition F s (n + 1) =
      mulSection F s (reflexivePower F (n + 1)) ≫
        toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) :
          X.Modules) := rfl

/-! ### The transitions of the ordinary tensor-power system -/

/-- **The transition maps of the ordinary tensor-power system** `𝒪_X →ˢ ℱ →ˢ ℱ^{⊗ 2} → ⋯`:
multiplication by `s`, with no reflexive hull.  This is the system
`Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePowerTransition` becomes on an open where `ℱ`
is invertible. -/
def tensorPowerTransition (F : X.Modules) (s : F.sections) :
    (n : ℕ) → (tensorPower F n ⟶ tensorPower F (n + 1))
  | 0 => F.unitHomEquiv.symm s
  | n + 1 => mulSection F s (tensorPower F (n + 1))

/-- The transition out of degree `0` is the morphism `𝒪_X ⟶ ℱ` determined by `s`. -/
theorem tensorPowerTransition_zero (F : X.Modules) (s : F.sections) :
    tensorPowerTransition F s 0 = F.unitHomEquiv.symm s := rfl

/-- The transition out of degree `n + 1` is multiplication by `s`. -/
theorem tensorPowerTransition_succ (F : X.Modules) (s : F.sections) (n : ℕ) :
    tensorPowerTransition F s (n + 1) = mulSection F s (tensorPower F (n + 1)) := rfl

/-! ### The comparison as a recursively defined family -/

variable (F : X.Modules) (V : X.Opens)

/-- `(ℱ ⊗ ℱ^{[n + 1]})|_V ≅ (ℱ|_V)^{⊗ (n + 2)}`, assembled from [Stacks, Tag 01CD] at the open
immersion and the comparison at `n + 1`. -/
def restrictTensorPowerIso {n : ℕ}
    (e : (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1)) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)) :
    (Scheme.Modules.restrictFunctor V.ι).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) : X.Modules) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 2) :=
  tensorSheafRestrictIso V F (reflexivePower F (n + 1)) ≪≫
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      V.toScheme.sheaf)).mapIso
        (X := ((Scheme.Modules.restrictFunctor V.ι).obj F,
          (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1))))
        (Y := ((Scheme.Modules.restrictFunctor V.ι).obj F,
          tensorPower (X := V.toScheme) ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)))
        (Iso.prod (Iso.refl ((Scheme.Modules.restrictFunctor V.ι).obj F)) e)

/-- **Over `V` the canonical map of `ℱ ⊗ ℱ^{[n + 1]}` into its reflexive hull is invertible**,
given the comparison at `n + 1`: over `V` that tensor product is the invertible, hence reflexive,
module `(ℱ|_V)^{⊗ (n + 2)}`. -/
theorem isIso_restrict_toDoubleDual_tensor_reflexivePower [IsIntegral X] [IsLocallyNoetherian X]
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (n : ℕ)
    (e : (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1)) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) : X.Modules))) :=
  have hVint : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have hVnoeth : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have hFV : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.restrictFunctor V.ι).obj F) :=
    @isCoherent_restrict X ‹_› V F hF
  have hPcoh : _root_.SheafOfModules.IsCoherent (reflexivePower F (n + 1)) :=
    isCoherent_reflexivePower F hF n
  have hGcoh : _root_.SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) : X.Modules) :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F
      (reflexivePower F (n + 1)) hF hPcoh
  have hpowcoh : _root_.SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((V.toScheme.toRingedSpace)).presheaf,
        ((V.toScheme.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.restrictFunctor V.ι).obj F))).obj
          ((tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)))) :
        V.toScheme.Modules) :=
    isCoherent_tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) hFV (n + 1)
  have hinv : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((V.toScheme.toRingedSpace)).presheaf,
        ((V.toScheme.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.restrictFunctor V.ι).obj F))).obj
          ((tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)))) :
        V.toScheme.Modules) :=
    isInvertible_tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) hV (n + 2)
  have hpowrefl : IsReflexive
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((V.toScheme.toRingedSpace)).presheaf,
        ((V.toScheme.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.restrictFunctor V.ι).obj F))).obj
          ((tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)))) :
        V.toScheme.Modules) :=
    @AlgebraicGeometry.isReflexive_of_isInvertible V.toScheme hVint hVnoeth _
      hinv.toAlgebraicGeometry
  have hGrescoh : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.restrictFunctor V.ι).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) : X.Modules)) :=
    @isCoherent_restrict X ‹_› V
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) : X.Modules) hGcoh
  have hGresrefl : IsReflexive ((Scheme.Modules.restrictFunctor V.ι).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) : X.Modules)) :=
    @isReflexive_of_iso V.toScheme hVnoeth _ _ hpowcoh hGrescoh
      (restrictTensorPowerIso F V e).symm hpowrefl
  @isIso_restrict_toDoubleDual X ‹_› V
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) : X.Modules)
      hGcoh hGresrefl

/-- The inductive step of `restrictPowerIso`, as data: cancel the hull against
`isIso_restrict_toDoubleDual_tensor_reflexivePower` and compose with the comparison of the
tensor product. -/
def restrictPowerSuccIso [IsIntegral X] [IsLocallyNoetherian X]
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (n : ℕ)
    (e : (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1)) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)) :
    (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 2)) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 2) :=
  (@asIso _ _ _ _ _ (isIso_restrict_toDoubleDual_tensor_reflexivePower F V hF hV n e)).symm ≪≫
    restrictTensorPowerIso F V e

/-- **The comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}` as a recursively defined family**, so that it
has computation rules and a commuting square against the transition maps can be stated for it. -/
def restrictPowerIso [IsIntegral X] [IsLocallyNoetherian X]
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F)) :
    (n : ℕ) → ((Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F n) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) n)
  | 0 => Scheme.Modules.restrictUnitIso V.ι
  | 1 => Iso.refl _
  | n + 2 => restrictPowerSuccIso F V hF hV n (restrictPowerIso hF hV (n + 1))

/-- At `0` the comparison is the identification `𝒪_X|_V ≅ 𝒪_V`. -/
theorem restrictPowerIso_zero [IsIntegral X] [IsLocallyNoetherian X]
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F)) :
    restrictPowerIso F V hF hV 0 = Scheme.Modules.restrictUnitIso V.ι := rfl

/-- At `1` the comparison is the identity: both families have `ℱ` at `1` on the nose. -/
theorem restrictPowerIso_one [IsIntegral X] [IsLocallyNoetherian X]
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F)) :
    restrictPowerIso F V hF hV 1 = Iso.refl _ := rfl

/-- The recursion defining the comparison, for `n ≥ 1`. -/
theorem restrictPowerIso_succ_succ [IsIntegral X] [IsLocallyNoetherian X]
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F)) (n : ℕ) :
    restrictPowerIso F V hF hV (n + 2) =
      restrictPowerSuccIso F V hF hV n (restrictPowerIso F V hF hV (n + 1)) := by
  rw [restrictPowerIso]

/-! ### The hull is invisible on the transition maps -/

/-- **The comparison at `n + 2` cancels the restricted map into the reflexive hull.**  This is
the one computation rule the inductive step has, and the commuting square is read off it. -/
theorem restrict_toDoubleDual_comp_restrictPowerSuccIso_hom [IsIntegral X]
    [IsLocallyNoetherian X] (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F)) (n : ℕ)
    (e : (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1)) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)) :
    (Scheme.Modules.restrictFunctor V.ι).map
        (toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) :
          X.Modules)) ≫
      (restrictPowerSuccIso F V hF hV n e).hom = (restrictTensorPowerIso F V e).hom :=
  (@asIso _ _ _ _ _
    (isIso_restrict_toDoubleDual_tensor_reflexivePower F V hF hV n e)).hom_inv_id_assoc _

/-- **The square at `n + 1`, with the hull cancelled.**  Over `V` the transition
`ℱ^{[n + 1]} ⟶ ℱ^{[n + 2]}` of the system of [Stacks, Tag 0EBN] is, after the comparison,
the restriction of multiplication by `s`: the canonical map into the reflexive hull becomes
invertible on `V` and is cancelled by the comparison at `n + 2`. -/
theorem restrict_reflexivePowerTransition_comp_restrictPowerIso_hom [IsIntegral X]
    [IsLocallyNoetherian X] (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (s : F.sections) (n : ℕ) :
    (Scheme.Modules.restrictFunctor V.ι).map (reflexivePowerTransition F s (n + 1)) ≫
        (restrictPowerIso F V hF hV (n + 2)).hom =
      (Scheme.Modules.restrictFunctor V.ι).map (mulSection F s (reflexivePower F (n + 1))) ≫
        (restrictTensorPowerIso F V (restrictPowerIso F V hF hV (n + 1))).hom := by
  rw [restrictPowerIso_succ_succ, reflexivePowerTransition_succ']
  refine Eq.trans (congrArg
    (fun g => g ≫ (restrictPowerSuccIso F V hF hV n (restrictPowerIso F V hF hV (n + 1))).hom)
    ((Scheme.Modules.restrictFunctor V.ι).map_comp
      (mulSection F s (reflexivePower F (n + 1)))
      (toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj ((reflexivePower F (n + 1)))) :
        X.Modules)))) ?_
  exact (Category.assoc _ _ _).trans (congrArg
    (fun g => (Scheme.Modules.restrictFunctor V.ι).map
      (mulSection F s (reflexivePower F (n + 1))) ≫ g)
    (restrict_toDoubleDual_comp_restrictPowerSuccIso_hom F V hF hV n
      (restrictPowerIso F V hF hV (n + 1))))

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
