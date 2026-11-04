module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSubmodule

/-!
# Strict transforms under a blowup

Let `S` be a scheme, let `ℐ` be a quasi-coherent sheaf of ideals on `S`, and let
`b : S' ⟶ S` be the blowup of `S` in `ℐ` (`Stacks.Blowup.blowUpToBase`), with exceptional
ideal sheaf `ℐ·𝒪_{S'}` (`Stacks.Blowup.exceptionalIdeal`) and exceptional divisor `E` its
closed subscheme. For a scheme `X` over `S` via `f : X ⟶ S` one forms the cartesian square

```
X ×_S S' --pr_{S'}--> S'
   |                   |
 pr_X                  b
   |                   |
   v                   v
   X -------f--------> S
```

and the closed subset `pr_{S'}⁻¹ E` of `X ×_S S'`. The *strict transform* of a quasi-coherent
`𝒪_X`-module `ℱ` is the quotient of `pr_X^* ℱ` by the submodule of its sections supported on
`pr_{S'}⁻¹ E`, and the *strict transform of `X`* is the closed subscheme of `X ×_S S'` cut out
by the corresponding ideal of sections of `𝒪_{X ×_S S'}`.

## Main definitions

* `Stacks.Blowup.blowUpPullback` is `X ×_S S'`, with projections
  `Stacks.Blowup.blowUpPullbackToSource` and `Stacks.Blowup.blowUpPullbackToBlowUp`.
* `Stacks.Blowup.exceptionalPullbackSet` is the closed subset `pr_{S'}⁻¹ E` of `X ×_S S'`, and
  `Stacks.Blowup.exceptionalPullbackCompl` its open complement.
* `Stacks.Blowup.strictTransformSheaf` is the strict transform of an `𝒪_X`-module.
* `Stacks.Blowup.strictTransformIdeal` is the ideal of sections of the structure sheaf
  supported on `pr_{S'}⁻¹ E`.
* `Stacks.Blowup.strictTransform` is the strict transform of `X`, the closed subscheme of
  `X ×_S S'` cut out by that ideal, and `Stacks.Blowup.strictTransformι` its closed
  immersion into `X ×_S S'`.

## Main results

* `AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule_unit_eq_ker`: on any scheme, the
  ideal of sections of the structure sheaf supported on a subset `Z` is the kernel of the
  restriction map to any open whose points are exactly the points outside `Z`.
* `Stacks.Blowup.isClosed_exceptionalPullbackSet`: the subset `pr_{S'}⁻¹ E` is closed.
* `Stacks.Blowup.exceptionalPullbackSet_eq_preimage_support`: it is the preimage of the support
  of `ℐ` under `X ×_S S' ⟶ S`, equivalently of the support of the exceptional ideal under
  `pr_{S'}`.
* `Stacks.Blowup.strictTransformIdeal_eq_ker`: the defining ideal of the strict transform is the
  kernel ideal sheaf of the inclusion of the complement of `pr_{S'}⁻¹ E`.
* `Stacks.Blowup.ideal_strictTransformIdeal_le` and
  `Stacks.Blowup.ideal_strictTransformIdeal_of_quasiCompact`: the defining ideal on an affine
  open is contained in, and under quasi-compactness of that inclusion equal to, the module of
  supported sections there.

## Implementation notes

The module quotient is expressed as the cokernel of the canonical inclusion of the
supported-sections submodule, which is
`AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule` (Stacks tag 084L). Mathlib
presents quasi-coherent ideal sheaves as compatible families of ideals on affine opens, so the
ideal of supported sections is assembled with `Scheme.IdealSheafData.ofIdeals` from the
supported-sections submodule of the structure sheaf, and the closed subscheme is obtained from
it by `Scheme.IdealSheafData.subscheme`.

The ideal of the resulting `IdealSheafData` on an affine open is always contained in the module
of supported sections there, and equals it when the complement of `pr_{S'}⁻¹ E` is retrocompact
(Stacks tag 07ZP): the defining ideal is the kernel ideal sheaf of the inclusion `j` of that
complement, and `QuasiCompact j` is retrocompactness of the complement.

The strict transform of a module is defined for any `𝒪_X`-module `ℱ`; the source states it for
quasi-coherent `ℱ`, a hypothesis the construction does not use.

## References

* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- On a scheme `T`, the ideal of sections of the structure sheaf over `U` supported on a subset
`Z` is the kernel of the restriction map to an open subscheme `V` whose points are exactly the
points of `T` outside `Z`. -/
public theorem supportedSectionsSubmodule_unit_eq_ker {T : Scheme.{u}} (Z : Set T) {V : T.Opens}
    (hV : (V : Set T) = Zᶜ) (U : T.Opens) :
    (supportedSectionsSubmodule Z
      (_root_.SheafOfModules.unit T.ringCatSheaf)).toSubmodule.obj (op U) =
      RingHom.ker ((Scheme.Opens.ι V).app U).hom := by
  obtain ⟨W, i, hWset, hker⟩ : ∃ (W : T.Opens) (i : op U ⟶ op W),
      (W : Set T) = (U : Set T) ∩ Zᶜ ∧
        RingHom.ker ((Scheme.Opens.ι V).app U).hom = RingHom.ker (T.presheaf.map i).hom := by
    refine ⟨V.ι ''ᵁ (V.ι ⁻¹ᵁ U),
      (homOfLE (x := V.ι ''ᵁ V.ι ⁻¹ᵁ U) (Set.image_preimage_subset _ _)).op, ?_, ?_⟩
    · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        TopologicalSpace.Opens.coe_inf, hV]
      exact Set.inter_comm _ _
    · rw [Scheme.Opens.ι_app]
      rfl
  rw [hker]
  refine SetLike.ext fun s ↦
    Iff.trans (mem_supportedSectionsSubmodule_iff_map_eq_zero Z _ i hWset s) ?_
  exact Iff.rfl

end AlgebraicGeometry.SheafOfModules

namespace Stacks.Blowup

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℐ : S.IdealSheafData)

/-- The base change `X ×_S S'` of a scheme `X` over `S` along the blowup of `S` in `ℐ`. -/
abbrev blowUpPullback : Scheme.{u} := pullback f (blowUpToBase ℐ)

/-- The projection of `X ×_S S'` to `X`, denoted `pr_X`. -/
abbrev blowUpPullbackToSource : blowUpPullback f ℐ ⟶ X := pullback.fst f (blowUpToBase ℐ)

/-- The projection of `X ×_S S'` to the blowup `S'`, denoted `pr_{S'}`. -/
abbrev blowUpPullbackToBlowUp : blowUpPullback f ℐ ⟶ blowUp ℐ := pullback.snd f (blowUpToBase ℐ)

/-- The inverse image `pr_{S'}⁻¹ E` of the exceptional divisor in `X ×_S S'`, as a subset. -/
abbrev exceptionalPullbackSet : Set (blowUpPullback f ℐ) :=
  (blowUpPullbackToBlowUp f ℐ).base ⁻¹' (exceptionalIdeal ℐ).support

/-- The inverse image of the exceptional divisor is closed. -/
theorem isClosed_exceptionalPullbackSet : IsClosed (exceptionalPullbackSet f ℐ) :=
  (exceptionalIdeal ℐ).support.isClosed.preimage (blowUpPullbackToBlowUp f ℐ).continuous

/-- The open complement of `pr_{S'}⁻¹ E` in `X ×_S S'`. -/
def exceptionalPullbackCompl : (blowUpPullback f ℐ).Opens :=
  ⟨(exceptionalPullbackSet f ℐ)ᶜ, (isClosed_exceptionalPullbackSet f ℐ).isOpen_compl⟩

/-- The underlying set of `exceptionalPullbackCompl` is the complement of `pr_{S'}⁻¹ E`. -/
@[simp]
theorem coe_exceptionalPullbackCompl :
    (exceptionalPullbackCompl f ℐ : Set (blowUpPullback f ℐ)) =
      (exceptionalPullbackSet f ℐ)ᶜ :=
  rfl

/-- The inverse image of the exceptional divisor is the preimage of the support of `ℐ` along
`X ×_S S' ⟶ S' ⟶ S`; since the square is cartesian this is also the preimage of the support
of `ℐ` along `X ×_S S' ⟶ X ⟶ S`. -/
theorem exceptionalPullbackSet_eq_preimage_support :
    exceptionalPullbackSet f ℐ =
      (blowUpPullbackToBlowUp f ℐ ≫ blowUpToBase ℐ).base ⁻¹' ℐ.support := by
  rw [exceptionalPullbackSet, exceptionalIdeal, Scheme.IdealSheafData.support_comap]
  rfl

/-- The strict transform of an `𝒪_X`-module `ℱ` along the blowup of the base in `ℐ`: the
quotient of the pullback of `ℱ` to `X ×_S S'` by the submodule of sections supported on the
inverse image of the exceptional divisor. -/
@[stacks 080D "strict transform of a module"]
abbrev strictTransformSheaf (ℱ : X.Modules) : (blowUpPullback f ℐ).Modules :=
  cokernel (SheafOfModules.supportedSectionsSubmodule (exceptionalPullbackSet f ℐ)
    ((Scheme.Modules.pullback (blowUpPullbackToSource f ℐ)).obj ℱ)).ι

/-- The quasi-coherent ideal of sections of `𝒪_{X ×_S S'}` supported on the inverse image of
the exceptional divisor, assembled from its modules of sections over the affine opens of
`X ×_S S'`. -/
@[stacks 080D "ideal of the strict transform of a scheme"]
def strictTransformIdeal : (blowUpPullback f ℐ).IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    (SheafOfModules.supportedSectionsSubmodule (exceptionalPullbackSet f ℐ)
      (SheafOfModules.unit (blowUpPullback f ℐ).ringCatSheaf)).toSubmodule.obj (op U.1)

/-- The defining ideal of the strict transform is the kernel ideal sheaf of the inclusion of the
complement of `pr_{S'}⁻¹ E`: a section of the structure sheaf is supported on `pr_{S'}⁻¹ E`
exactly when it restricts to zero off it. -/
theorem strictTransformIdeal_eq_ker :
    strictTransformIdeal f ℐ = (Scheme.Opens.ι (exceptionalPullbackCompl f ℐ)).ker := by
  rw [strictTransformIdeal, Scheme.Hom.ker]
  exact congrArg Scheme.IdealSheafData.ofIdeals
    (funext fun U ↦ SheafOfModules.supportedSectionsSubmodule_unit_eq_ker _ rfl U.1)

/-- On an affine open, the defining ideal of the strict transform is contained in the module of
sections supported on `pr_{S'}⁻¹ E`. -/
theorem ideal_strictTransformIdeal_le (U : (blowUpPullback f ℐ).affineOpens) :
    (strictTransformIdeal f ℐ).ideal U ≤
      (SheafOfModules.supportedSectionsSubmodule (exceptionalPullbackSet f ℐ)
        (SheafOfModules.unit (blowUpPullback f ℐ).ringCatSheaf)).toSubmodule.obj (op U.1) :=
  Scheme.IdealSheafData.ideal_ofIdeals_le _ _

/-- On an affine open, the defining ideal of the strict transform consists of exactly the
sections supported on `pr_{S'}⁻¹ E`, as soon as the inclusion of the complement of
`pr_{S'}⁻¹ E` is quasi-compact — equivalently, as soon as that complement is retrocompact. -/
theorem ideal_strictTransformIdeal_of_quasiCompact
    [QuasiCompact (Scheme.Opens.ι (exceptionalPullbackCompl f ℐ))]
    (U : (blowUpPullback f ℐ).affineOpens) :
    (strictTransformIdeal f ℐ).ideal U =
      (SheafOfModules.supportedSectionsSubmodule (exceptionalPullbackSet f ℐ)
        (SheafOfModules.unit (blowUpPullback f ℐ).ringCatSheaf)).toSubmodule.obj (op U.1) := by
  rw [strictTransformIdeal_eq_ker, Scheme.Hom.ker_apply]
  exact (SheafOfModules.supportedSectionsSubmodule_unit_eq_ker _ rfl U.1).symm

/-- The strict transform of `X` along the blowup of the base in `ℐ`: the closed subscheme of
`X ×_S S'` cut out by the ideal of sections supported on the inverse image of the exceptional
divisor. -/
@[stacks 080D "strict transform of a scheme"]
abbrev strictTransform : Scheme.{u} := (strictTransformIdeal f ℐ).subscheme

/-- The inclusion of the strict transform of `X` into `X ×_S S'`. -/
def strictTransformι : strictTransform f ℐ ⟶ blowUpPullback f ℐ :=
  (strictTransformIdeal f ℐ).subschemeι

/-- The inclusion of the strict transform of `X` into `X ×_S S'` is a closed immersion. -/
instance : IsClosedImmersion (strictTransformι f ℐ) :=
  inferInstanceAs (IsClosedImmersion (strictTransformIdeal f ℐ).subschemeι)

end Stacks.Blowup

end
