module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 01VH and 0891: relatively ample invertible modules, and quasi-affine morphisms

Stacks Tag 01VH defines an invertible `𝒪_X`-module `L` to be *ample relative to* `f : X ⟶ S`
when `f` is quasi-compact and, for every affine open `V ⊆ S`, the restriction of `L` to
`f⁻¹(V)` is ample. Stacks Tag 0891 says that `𝒪_X` is relatively ample for `f` precisely when
`f` is quasi-affine, and that is what this file proves, alongside the definition.

## Main definitions

* `Stacks.RelativeAmple.IsRelativelyAmple`: **Stacks Tag 01VH**, relative ampleness.
* `Stacks.RelativeAmple.tensorPowModuleIsoUnitModule`: every integer tensor power of a module
  isomorphic to `𝒪_X` is isomorphic to `𝒪_X`.
* `Stacks.RelativeAmple.pullbackUnitModuleIso`: `f^* 𝒪_S ≅ 𝒪_X` for a morphism of schemes.

## Main results

* `Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule`: a scheme is quasi-affine
  if and only if some (hence any) invertible module isomorphic to `𝒪_X` is ample. This is
  Stacks Tag 01QE freed from the requirement that the module be `𝒪_X` on the nose, which is what
  makes it applicable to a pullback of `𝒪_S`.
* `Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff`: **Stacks Tag 0891.** `𝒪_X` is ample
  relative to `f : X ⟶ S` if and only if the preimage of every affine open of `S` is a
  quasi-affine scheme — that is, if and only if `f` is quasi-affine.
* `Stacks.RelativeAmple.quasiCompact_of_forall_isQuasiAffine_preimage`: a morphism whose affine
  preimages are quasi-affine is quasi-compact, which is why the quasi-compactness clause of
  Tag 01VH costs nothing on the right-hand side of Tag 0891.
* `Stacks.RelativeAmple.isRelativelyAmple_iff`, `IsRelativelyAmple.quasiCompact` and
  `IsRelativelyAmple.isAmple_preimage`: the defining conditions, usable without unfolding.
* `Stacks.RelativeAmple.isRelativelyAmple_unitModule_id`: the predicate is satisfiable.

## The route

Tag 01QE is `Stacks.Ample.isQuasiAffine_iff_isAmple`, already proved in the repository for
`𝒪_X` itself. Tag 0891 needs it for `U.ι^* 𝒪_X`, which is only *isomorphic* to `𝒪_U`, and
ampleness is not known in the repository to depend only on the isomorphism class of the module.
The gap is closed without that general fact: `Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers`
asks exactly for a `Stacks.Ample.NonvanishingBasis` in each tensor degree, and
`AlgebraicGeometry.SheafOfModules.tensorPowIsoUnit` identifies every tensor power of a
unit-isomorphic module with the unit, so `Stacks.Ample.NonvanishingBasis.ofIso` transports the
basis `1` of `𝒪_U` into every degree.

The isomorphism `U.ι^* 𝒪_X ≅ 𝒪_U` is `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`, and
the invertibility of `U.ι^* 𝒪_X` that the ampleness predicate needs as an instance is Tag 0B8L in
the form `Stacks.InvertiblePullback.isInvertibleModule_restrict`.

Quasi-compactness of `f` is *implied* by the right-hand side of Tag 0891 rather than assumed:
a quasi-affine scheme is quasi-compact, and
`AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen` reduces quasi-compactness of `f` to
compactness of the affine preimages.

## Implementation notes

**Ampleness of the restriction, not of a restriction functor.** The restriction of `L` to the
open subscheme `f⁻¹(V)` is taken as the module pullback along the open immersion
`(f ⁻¹ᵁ V).ι`, which is the form Stacks Tag 01VH is stated in and the form Tag 0B8L supplies
invertibility for. `AlgebraicGeometry.Scheme.Modules.restrictFunctor` is isomorphic to it
(`Scheme.Modules.restrictFunctorIsoPullback`) and has better definitional behaviour on sections,
but nothing here looks at sections.

**Monoidal instances are local.** The statement of
`AlgebraicGeometry.SheafOfModules.tensorPowIsoUnit` mentions `𝟙_`, so
`Stacks.SheafInternalHom.monoidalCategory` and `braidedCategory` — deliberately `def`s — are
brought in as local instances in the one section that uses it, exactly as
`StacksFrontier/AlgebraicGeometry/AmpleWire/Basic.lean` does. Nothing in the
`IsRelativelyAmple` interface needs them.

**Compactness of an open subscheme.** `CompactSpace V.toScheme` and `CompactSpace ↥(V : Set X)`
are the same type up to unfolding but instance search does not bridge them, so
`quasiCompact_of_forall_isQuasiAffine_preimage` converts with an explicit term rather than
`infer_instance`.

## What is not done

Only Tag 0891 is proved about relative ampleness. Tag 01VJ — that relative ampleness may be
checked on an affine open covering of the base rather than on every affine open — is not here,
and it is what Tag 0C4K needs in order to get a single tensor-power threshold out of
quasi-compactness of the base; its proof in the source goes through relative `Proj`. The
stability of relative ampleness under restriction of the base to an open is also not stated.

## References

* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [EGA II, Definition 4.6.1]
* [EGA II, Proposition 5.1.6]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RelativeAmple

/-! ### Tensor powers of a module isomorphic to the structure sheaf -/

section Monoidal

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

/-- **Every integer tensor power of an invertible module isomorphic to `𝒪_X` is isomorphic to
`𝒪_X`.** This is `AlgebraicGeometry.SheafOfModules.tensorPowIsoUnit` read through the
identification of `𝒪_X` with the monoidal unit of `X.Modules`. -/
def tensorPowModuleIsoUnitModule (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (e : L ≅ Stacks.Ample.unitModule X) (n : ℤ) :
    Stacks.Ample.tensorPowModule X L n ≅ Stacks.Ample.unitModule X :=
  AlgebraicGeometry.SheafOfModules.tensorPowIsoUnit X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L
      (e ≪≫ Stacks.Ample.unitModuleIsoTensorUnit X) n ≪≫
    (Stacks.Ample.unitModuleIsoTensorUnit X).symm

end Monoidal

/-- A nowhere-vanishing global basis of every tensor power of an invertible module isomorphic to
`𝒪_X`: the basis `1` of `𝒪_X`, transported along
`Stacks.RelativeAmple.tensorPowModuleIsoUnitModule`. -/
def unitLikeTensorPowBasis (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (e : L ≅ Stacks.Ample.unitModule X) (n : ℤ) :
    Stacks.Ample.NonvanishingBasis (Stacks.Ample.tensorPowModule X L n) :=
  (Stacks.Ample.unitBasis X).ofIso (tensorPowModuleIsoUnitModule X L e n).symm

/-- **Stacks Tag 01QE for any module isomorphic to the structure sheaf.** A scheme is
quasi-affine if and only if an invertible module isomorphic to `𝒪_X` is ample.

`Stacks.Ample.isQuasiAffine_iff_isAmple` is the case `L = 𝒪_X`; the point of the present form is
that it applies to a pullback of a structure sheaf, which is isomorphic to `𝒪_X` but not equal
to it. No general invariance of ampleness under isomorphism of modules is used: the only
hypothesis of `Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers` is a global basis in each tensor
degree, and that is transported degreewise. -/
@[ega "II 5.1.2" "more general", ega "II 5.1.4" "special case", ega "II 6.6.13" "more general"]
theorem isQuasiAffine_iff_isAmple_of_iso_unitModule (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (e : L ≅ Stacks.Ample.unitModule X) :
    X.IsQuasiAffine ↔ Stacks.Ample.IsAmple X L :=
  Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers X (Stacks.Ample.tensorPowModule X L)
    (unitLikeTensorPowBasis X L e)

/-- **The pullback of the structure sheaf along a morphism of schemes is the structure sheaf**,
`f^* 𝒪_S ≅ 𝒪_X`. This is `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso` for the
underlying morphism of ringed spaces. -/
def pullbackUnitModuleIso {X S : Scheme.{u}} (f : X ⟶ S) :
    (modulePullback f.toLRSHom.toShHom).obj (Stacks.Ample.unitModule S) ≅
      Stacks.Ample.unitModule X :=
  RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f.toLRSHom.toShHom

/-! ### Tag 01VH: relative ampleness -/

/-- **Stacks Tag 01VH.** An invertible `𝒪_X`-module `L` is *ample relative to* `f : X ⟶ S` when
`f` is quasi-compact and, for every affine open `V` of `S`, the restriction of `L` to the open
subscheme `f⁻¹(V)` is ample. The restriction is the module pullback along the open immersion of
`f⁻¹(V)`, whose invertibility is Stacks Tag 0B8L, and ampleness is Stacks Tag 01PS. -/
@[stacks 01VH, ega "II 4.6.1"]
def IsRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] : Prop :=
  QuasiCompact f ∧ ∀ V : S.Opens, IsAffineOpen V →
    Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L)

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The defining conditions of relative ampleness, usable without unfolding the definition. -/
theorem isRelativelyAmple_iff :
    IsRelativelyAmple f L ↔ QuasiCompact f ∧ ∀ V : S.Opens, IsAffineOpen V →
      Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
        ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) := Iff.rfl

/-- A relatively ample module is ample relative to a quasi-compact morphism. -/
theorem IsRelativelyAmple.quasiCompact (h : IsRelativelyAmple f L) : QuasiCompact f := h.1

/-- The restriction of a relatively ample module to the preimage of an affine open of the base
is ample. -/
theorem IsRelativelyAmple.isAmple_preimage (h : IsRelativelyAmple f L) (V : S.Opens)
    (hV : IsAffineOpen V) :
    Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) := h.2 V hV

/-! ### Tag 0891: quasi-affine morphisms -/

/-- A morphism whose preimages of affine opens are quasi-affine schemes is quasi-compact: a
quasi-affine scheme is quasi-compact, and quasi-compactness of a morphism may be checked on
affine opens of the target. -/
theorem quasiCompact_of_forall_isQuasiAffine_preimage {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ V : S.Opens, IsAffineOpen V → (f ⁻¹ᵁ V).toScheme.IsQuasiAffine) :
    QuasiCompact f := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro V hV
  rw [isCompact_iff_compactSpace]
  exact (h V hV).toCompactSpace

/-- **Stacks Tag 0891.** The structure sheaf `𝒪_X` is ample relative to `f : X ⟶ S` if and only
if the preimage under `f` of every affine open of `S` is a quasi-affine scheme — that is, if and
only if `f` is quasi-affine.

The quasi-compactness clause of Tag 01VH is not an extra condition on the right-hand side: it
follows from quasi-affineness of the affine preimages by
`Stacks.RelativeAmple.quasiCompact_of_forall_isQuasiAffine_preimage`. On each preimage the
equivalence is Tag 01QE applied to `(f ⁻¹ᵁ V).ι^* 𝒪_X`, which
`Stacks.RelativeAmple.pullbackUnitModuleIso` identifies with the structure sheaf of the open
subscheme. -/
@[stacks 0891, ega "II 5.1.6" "(a) <=> (c')"]
theorem isRelativelyAmple_unitModule_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    IsRelativelyAmple f (Stacks.Ample.unitModule X) ↔
      ∀ V : S.Opens, IsAffineOpen V → (f ⁻¹ᵁ V).toScheme.IsQuasiAffine :=
  ⟨fun h V hV => (isQuasiAffine_iff_isAmple_of_iso_unitModule _ _
      (pullbackUnitModuleIso (f ⁻¹ᵁ V).ι)).mpr (h.2 V hV),
    fun h => ⟨quasiCompact_of_forall_isQuasiAffine_preimage f h, fun V hV =>
      (isQuasiAffine_iff_isAmple_of_iso_unitModule _ _ (pullbackUnitModuleIso (f ⁻¹ᵁ V).ι)).mp
        (h V hV)⟩⟩

/-- **The structure sheaf is ample relative to the identity.** Recorded because it witnesses
that `Stacks.RelativeAmple.IsRelativelyAmple` is satisfiable: the predicate is not vacuous, and
Tag 0891 above is not a proof that nothing is relatively ample. -/
theorem isRelativelyAmple_unitModule_id (Y : Scheme.{u}) :
    IsRelativelyAmple (𝟙 Y) (Stacks.Ample.unitModule Y) := by
  rw [isRelativelyAmple_unitModule_iff]
  intro V hV
  rw [show (𝟙 Y) ⁻¹ᵁ V = V by simp]
  have : IsAffine V.toScheme := hV
  infer_instance

end Stacks.RelativeAmple

end
