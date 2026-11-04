module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModuleDirectSum
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FiniteTypeDominating.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.RelativeSpecQcohEquivalence.FiniteType
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative spectrum of a graded algebra sheaf, and the single module it carries

Let `X` be a scheme and `𝓑` a sheaf of graded `𝒪_X`-algebras with commutative homogeneous
multiplication, concentrated in nonnegative degrees and with quasi-coherent homogeneous pieces.
The proof of [Stacks, Tag 0897] passes from a graded `𝓑`-module `M` to a **single** module `F'`
on `X' = Spec_X(⨁ₙ 𝓑ₙ)` with `π_* F' ≅ ∐ₙ Mₙ`, and uses that `F'` is coherent. This file carries
out that passage for an arbitrary `𝓑`, so that nothing about it has to be redone at each graded
algebra a consumer happens to have.

## Main definitions

* `Stacks.GradedProperCohomology.baseChangeModule`: **`F'`**, the module on the relative spectrum
  of a quasi-coherent algebra sheaf `𝒜` attached to a quasi-coherent
  `AlgebraSheaf.ringSheaf 𝒜`-module by [Stacks, Tag 01SB], together with `baseChangeModuleIso`,
  the defining identification `π_* F' ≅ N` inside the category of quasi-coherent
  `AlgebraSheaf.ringSheaf 𝒜`-modules.
* `Stacks.GradedProperCohomology.pushforwardBaseChangeModuleIso`: that identification read as an
  isomorphism of `𝒪_X`-modules, `N ≅ π_* F'`.
* `Stacks.GradedProperCohomology.totalQcoh`: the total module `⨁ₙ Mₙ` of a graded `𝓑`-module,
  packaged as a quasi-coherent module over the ungraded realization of `𝓑`.
* `Stacks.GradedProperCohomology.gradedBaseChangeModule`: `F'` for a graded module, and
  `gradedCoprodPushforwardIso`: **`∐ₙ Mₙ ≅ π_* F'`** — the datum `ε` that the uniform vanishing
  of `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_coprodIso` consumes.

## Main results

* `Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver`: the relative spectrum of
  an algebra sheaf of finite type over a locally Noetherian scheme is locally Noetherian.
* `Stacks.GradedProperCohomology.isFiniteType_baseChangeModule` and
  `isCoherent_baseChangeModule`: `F'` is of finite type, and — over a locally Noetherian `X'` —
  coherent.
* `Stacks.GradedProperCohomology.isQuasicoherent_ungradedSheaf`: the total module of a graded
  module whose homogeneous pieces have quasi-coherent coproduct and whose negative pieces vanish
  is quasi-coherent over the ungraded realization. Finite type of that total module is not
  restated — it is `SheafOfModules.GradedModule.isFiniteType_ungradedSheaf`, used directly.
* `Stacks.GradedProperCohomology.isCoherent_gradedBaseChangeModule`: **`F'` is coherent**, from
  the graded module's own hypotheses alone.

## What was and was not missing

The implementation notes of `StacksFrontier/AlgebraicGeometry/GradedProperCohomology/Basic.lean`
record, as the reason its own base change is a binder, that

> the *ungraded* realization of a `SheafOfModules.GradedModule` as a module over the ungraded
> realization of its graded algebra

is absent. **That is false, and was already known to be false**: the realization is
`SheafOfModules.GradedModule.ungradedSheaf`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedRealizationModule.lean`), its underlying
`𝒪_X`-module is the coproduct `∐ₙ Mₙ` by
`SheafOfModules.GradedModule.coprodIsoUngradedSheaf`, it is of finite type when the graded module
is by `SheafOfModules.GradedModule.isFiniteType_ungradedSheaf`, and the ungraded realization of
the *algebra* as a quasi-coherent algebra sheaf is `Stacks.RelativeSpec.gradedAlgebraSheaf` with
`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf`. The implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/CohomologyGradedReesBaseChange.lean` say as much
("once claimed here to be absent, which was false").

What was genuinely missing is this file: the assembly of those pieces into `X'`, `π`, `F'` and
`ε` **for an arbitrary graded algebra sheaf**. It existed only for the Rees algebra `⨁ₙ ℐⁿ` of an
ideal sheaf, spread over
`StacksFrontier/AlgebraicGeometry/FormalFunctions/CohomologyGradedReesBaseChange.lean`,
`StacksFrontier/AlgebraicGeometry/FormalFunctions/ReesBaseChangeCoherent.lean` and `StacksFrontier/AlgebraicGeometry/FormalFunctions/ReesCmpAssembly.lean`, and the Rees algebra is the one case
the fibre-side instance of [Stacks, Tag 0897] needed by [Stacks, Tag 0D2M] cannot use. Those Rees
declarations are now the instantiations of the ones here, so there is one copy of each statement
and not two.

## Implementation notes

The commutativity of the homogeneous multiplication appears twice, in the two shapes the library
asks for it: as the explicit argument `hc` that `Stacks.RelativeSpec.gradedAlgebraSheaf` takes,
and as the class `SheafOfModules.GradedAlgebra.IsCommutative` that
`SheafOfModules.GradedModule.ungradedSheaf` resolves by instance search. They are the same
statement — `Stacks.GradedProperCohomology.isCommutative_of_heq` builds the instance from the
argument — but both are taken, because an instance argument cannot be used to *build* the
algebra sheaf appearing in the surrounding types without fixing a proof term for it.

`Stacks.RelativeSpec.AlgebraSheaf.ringSheaf (Stacks.RelativeSpec.gradedAlgebraSheaf X 𝓑 hc)` is
`SheafOfModules.GradedAlgebra.ungradedSheaf 𝓑` on the nose
(`Stacks.RelativeSpec.ringSheaf_gradedAlgebraSheaf`), so the total module is literally a module
over the sheaf of rings that [Stacks, Tag 01SB] is stated with and no transport appears.

Quasi-coherence of the coproduct `∐ₙ Mₙ` is a hypothesis rather than a consequence of
quasi-coherence of the pieces. The index type is `ℕ`, which does not lie in the module universe,
so the step needs a shrinking of the index type, and the lemma that performs it —
`Stacks.Cohomology.FormalFunctions.isQuasicoherent_coprod_of_small` — sits downstream of this
file. A caller holding the pieces quasi-coherent applies it there; both consumers in the tree
do.

**No `@[stacks]` attribute is attached.** Every statement here is an instance of a tag already
carried in its own generality — [Stacks, Tag 01LX] is
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`, [Stacks, Tag 01SB] is
`Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward`,
[Stacks, Tag 01XZ] is
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType` — and
tagging a specialisation would weaken the tag.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.FiniteTypeDominating

universe u

namespace Stacks.GradedProperCohomology

/-! ### The relative spectrum of a quasi-coherent algebra sheaf -/

section AlgebraSheaf

variable {X : Scheme.{u}} (𝒜 : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent 𝒜]

/-- **The relative spectrum of an algebra sheaf of finite type over a locally Noetherian scheme
is locally Noetherian.** The structure morphism is locally of finite type
(`Stacks.AlgebraicGeometry.FiniteTypeDominating.locallyOfFiniteType_relativeSpecOver`), and
[Stacks, Tag 01T6] carries local Noetherianness along a morphism locally of finite type. -/
theorem isLocallyNoetherian_relativeSpecOver [IsLocallyNoetherian X]
    (hft : AlgebraSheaf.IsFiniteType 𝒜) :
    IsLocallyNoetherian (relativeSpecOver 𝒜).left :=
  @AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian _ _ (relativeSpecOver 𝒜).hom
    (locallyOfFiniteType_relativeSpecOver 𝒜 hft) ‹IsLocallyNoetherian X›

variable (N : (SheafOfModules.isQuasicoherent (AlgebraSheaf.ringSheaf 𝒜)).FullSubcategory)

/-- **`F'`: the module on the relative spectrum of `𝒜` whose direct image is `N`.** This is
[Stacks, Tag 01SB] at the relative spectrum,
`Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence`, applied to a quasi-coherent
`𝒜`-module — the "existence clause used by [Stacks, Tag 0897]" of that file, with the module
extracted from the full subcategory. -/
def baseChangeModule : (relativeSpecOver 𝒜).left.Modules :=
  ((relativeSpecQcohEquivalence 𝒜).inverse.obj N).obj

/-- `F'` is quasi-coherent, being the image of an object of the quasi-coherent full
subcategory. -/
theorem isQuasicoherent_baseChangeModule : (baseChangeModule 𝒜 N).IsQuasicoherent :=
  ((relativeSpecQcohEquivalence 𝒜).inverse.obj N).property

/-- **`π_* F' ≅ N`**, the defining property of `F'`, inside the category of quasi-coherent
`AlgebraSheaf.ringSheaf 𝒜`-modules: the counit of the equivalence of [Stacks, Tag 01SB]. -/
def baseChangeModuleIso :
    (relativeSpecQcohEquivalence 𝒜).functor.obj
        ((relativeSpecQcohEquivalence 𝒜).inverse.obj N) ≅ N :=
  (relativeSpecQcohEquivalence 𝒜).counitIso.app N

/-- **`F'` is of finite type** when `N` is. Finite type transports across [Stacks, Tag 01SB] by
`Stacks.AffineAlgebraEquivalence.isFiniteType_inverse_obj`. -/
theorem isFiniteType_baseChangeModule (hft : N.obj.IsFiniteType) :
    (baseChangeModule 𝒜 N).IsFiniteType :=
  isFiniteType_inverse_obj 𝒜 N hft

/-- **`F'` is coherent**: quasi-coherent and of finite type on a locally Noetherian relative
spectrum, which is [Stacks, Tag 01XZ]. -/
theorem isCoherent_baseChangeModule [IsLocallyNoetherian (relativeSpecOver 𝒜).left]
    (hft : N.obj.IsFiniteType) : (baseChangeModule 𝒜 N).IsCoherent :=
  have := isQuasicoherent_baseChangeModule 𝒜 N
  have := isFiniteType_baseChangeModule 𝒜 N hft
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **The functor of [Stacks, Tag 01SB] is the direct image**, after restriction of scalars
along the structure map of the algebra sheaf. The equality holds because
`Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence_functor_obj_obj` and
`Stacks.AlgebraicGeometry.AffineQcohPushforward.restrictScalars_pushforwardModules` are both
`rfl`, and the two restrictions of scalars compose to the one along `π^♯` by
`Stacks.AffineAlgebraEquivalence.structureMap_comp_pushforwardRingIso`. -/
theorem restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj
    (G : (SheafOfModules.isQuasicoherent (relativeSpec 𝒜).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap 𝒜)).obj
        ((relativeSpecQcohEquivalence 𝒜).functor.obj G).obj =
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeSpecToBase 𝒜)).obj G.obj := by
  have hmap : AlgebraSheaf.structureMap 𝒜 ≫ (pushforwardRingIso 𝒜).inv =
      (relativeSpecToBase 𝒜).toRingCatSheafHom :=
    (Iso.comp_inv_eq _).2 (structureMap_comp_pushforwardRingIso 𝒜).symm
  show (SheafOfModules.restrictScalars
      (AlgebraSheaf.structureMap 𝒜 ≫ (pushforwardRingIso 𝒜).inv)).obj
    ((Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules
      (relativeSpecToBase 𝒜).base (relativeSpec 𝒜).ringCatSheaf).obj G.obj) = _
  exact congrArg (fun α => (SheafOfModules.restrictScalars α).obj _) hmap

/-- **`N ≅ π_* F'` as `𝒪_X`-modules.** The defining property `baseChangeModuleIso` of `F'` is an
isomorphism of `AlgebraSheaf.ringSheaf 𝒜`-modules; restricting scalars along the structure map of
`𝒜` turns it into one of `𝒪_X`-modules, and
`restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj` identifies the restricted direct
image with the direct image of `𝒪_X`-modules. -/
def pushforwardBaseChangeModuleIso :
    (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap 𝒜)).obj N.obj ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeSpecOver 𝒜).hom).obj
        (baseChangeModule 𝒜 N) :=
  ((SheafOfModules.restrictScalars (AlgebraSheaf.structureMap 𝒜)).mapIso
      ((ObjectProperty.ι _).mapIso (baseChangeModuleIso 𝒜 N))).symm ≪≫
    eqToIso (restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj 𝒜 _)

end AlgebraSheaf

/-! ### The graded case -/

section Graded

variable {X : Scheme.{u}} (𝓑 : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (𝓑.piece i).val.obj W) (b : (𝓑.piece j).val.obj W),
    HEq ((𝓑.mul i j).app W a b) ((𝓑.mul j i).app W b a))

/-- The commutativity hypothesis that `Stacks.RelativeSpec.gradedAlgebraSheaf` takes as an
argument is the field of the class that `SheafOfModules.GradedModule.ungradedSheaf` resolves by
instance search. -/
theorem isCommutative_of_heq
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (𝓑.piece i).val.obj W)
      (b : (𝓑.piece j).val.obj W), HEq ((𝓑.mul i j).app W a b) ((𝓑.mul j i).app W b a)) :
    𝓑.IsCommutative := ⟨hc⟩

variable [𝓑.IsCommutative] (M : SheafOfModules.GradedModule.{u, u, u} 𝓑)

/-- **The total module `⨁ₙ Mₙ` of a graded `𝓑`-module is quasi-coherent over the ungraded
realization of `𝓑`**, as soon as the coproduct of its homogeneous pieces is quasi-coherent and
its negative pieces vanish.

The `𝒪_X`-module underlying the total module is that coproduct
(`SheafOfModules.GradedModule.coprodIsoUngradedSheaf`), and quasi-coherence passes from the
restriction of scalars to the module itself by [Stacks, Tag 0H88]
(`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars`), whose
hypothesis that the realization is quasi-coherent as an `𝒪_X`-module is what `hB` supplies. -/
theorem isQuasicoherent_ungradedSheaf
    (hB : ((SheafOfModules.restrictScalars 𝓑.ungradedStructureMap).obj
      (SheafOfModules.unit 𝓑.ungradedSheaf)).IsQuasicoherent)
    (hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) :
    (SheafOfModules.GradedModule.ungradedSheaf M).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars
    𝓑.ungradedStructureMap hB (SheafOfModules.GradedModule.ungradedSheaf M)
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (SheafOfModules.GradedModule.coprodIsoUngradedSheaf M hneg) hcop)

variable [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X 𝓑 hc)]

/-- The total module `⨁ₙ Mₙ`, packaged as a quasi-coherent module over the sheaf of rings of
`Stacks.RelativeSpec.gradedAlgebraSheaf`, i.e. in the form [Stacks, Tag 01SB] consumes. The sheaf
of rings *is* the ungraded realization of `𝓑`
(`Stacks.RelativeSpec.ringSheaf_gradedAlgebraSheaf`), so no transport appears. -/
def totalQcoh
    (hB : ((SheafOfModules.restrictScalars 𝓑.ungradedStructureMap).obj
      (SheafOfModules.unit 𝓑.ungradedSheaf)).IsQuasicoherent)
    (hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) :
    (SheafOfModules.isQuasicoherent
      (AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X 𝓑 hc))).FullSubcategory :=
  ⟨SheafOfModules.GradedModule.ungradedSheaf M,
    isQuasicoherent_ungradedSheaf 𝓑 M hB hcop hneg⟩

/-- **`F'` for a graded module**: the module on `X' = Spec_X(⨁ₙ 𝓑ₙ)` whose direct image is the
total module `⨁ₙ Mₙ`. -/
def gradedBaseChangeModule
    (hB : ((SheafOfModules.restrictScalars 𝓑.ungradedStructureMap).obj
      (SheafOfModules.unit 𝓑.ungradedSheaf)).IsQuasicoherent)
    (hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) :
    (relativeSpecOver (gradedAlgebraSheaf X 𝓑 hc)).left.Modules :=
  baseChangeModule (gradedAlgebraSheaf X 𝓑 hc) (totalQcoh 𝓑 hc M hB hcop hneg)

/-- **`F'` is coherent**, from the graded module's own hypotheses: its pieces quasi-coherent, its
negative pieces zero, and the graded module of finite type, over a locally Noetherian relative
spectrum. -/
theorem isCoherent_gradedBaseChangeModule
    [IsLocallyNoetherian (relativeSpecOver (gradedAlgebraSheaf X 𝓑 hc)).left]
    (hB : ((SheafOfModules.restrictScalars 𝓑.ungradedStructureMap).obj
      (SheafOfModules.unit 𝓑.ungradedSheaf)).IsQuasicoherent)
    (hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) (hft : M.IsFiniteType) :
    (gradedBaseChangeModule 𝓑 hc M hB hcop hneg).IsCoherent :=
  isCoherent_baseChangeModule (gradedAlgebraSheaf X 𝓑 hc) (totalQcoh 𝓑 hc M hB hcop hneg)
    (SheafOfModules.GradedModule.isFiniteType_ungradedSheaf M hft)

/-- **`ε : ∐ₙ Mₙ ≅ π_* F'`.** The coproduct comparison
`SheafOfModules.GradedModule.coprodIsoUngradedSheaf` followed by the `𝒪_X`-module form
`pushforwardBaseChangeModuleIso` of the defining property of `F'`.

This is the datum the uniform vanishing
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_coprodIso` consumes, and
with it the only inputs that remain for the fibre-side instance of [Stacks, Tag 0897] part (2)
are geometric: `f' : X' ⟶ Spec R` proper over a Noetherian `R`, and ampleness of `π^* ℒ`. -/
def gradedCoprodPushforwardIso
    (hB : ((SheafOfModules.restrictScalars 𝓑.ungradedStructureMap).obj
      (SheafOfModules.unit 𝓑.ungradedSheaf)).IsQuasicoherent)
    (hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) :
    (∐ fun n : ℕ => M.piece (n : ℤ)) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward
        (relativeSpecOver (gradedAlgebraSheaf X 𝓑 hc)).hom).obj
          (gradedBaseChangeModule 𝓑 hc M hB hcop hneg) :=
  SheafOfModules.GradedModule.coprodIsoUngradedSheaf M hneg ≪≫
    pushforwardBaseChangeModuleIso (gradedAlgebraSheaf X 𝓑 hc) (totalQcoh 𝓑 hc M hB hcop hneg)

end Graded

end Stacks.GradedProperCohomology

end
