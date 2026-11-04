module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPresentation
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QcohShortExact.QcohExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree

/-!
# Functoriality for quasi-coherent modules: the covering set of Stacks 01LA

Stacks 01LA is a *section* tag — `\section{Functoriality for quasi-coherent modules}` of the
chapter on schemes. Its own mathematical content is the ten-item enumeration with which it
opens: for a scheme `X`, the category `QCoh(𝒪_X)` inherits from the affine case
(Section 26.7) the good properties listed there, "since the property of being quasi-coherent is
local on `X`". The section tag therefore belongs on the declarations that carry
those ten items, and this module places it there.

The section also contains three labelled lemmas, which carry their own tags and are no part of
this registration: 01LC (pushforward along a quasi-compact quasi-separated morphism, already
proved), 01LD (the closed-immersion criterion) and 02V0 (compositions of immersions). The same
reading is already recorded in `StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.General`,
whose docstring calls 01LB "item (5) of the enumeration of 01LA".

## The section's ten items, and where each lives

* Item (1), quasi-coherence against the restrictions to the affine opens being sheaves `M^~`,
  is `isQuasicoherent_iff_forall_isAffineOpen_exists_tilde` below.
* Item (2), quasi-coherence against the restrictions to an affine open covering, is
  `isQuasicoherent_iff_forall_restrict` below.
* Item (3), direct sums, is
  `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma`.
* Item (4), colimits, is
  `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`.
* Item (5), kernels and cokernels, is the pair
  `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` and
  `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`. The item carries
  the sub-label 01LB, under which the same pair is already recorded.
* Item (6), two out of three in a short exact sequence, is the triple
  `Stacks.AlgebraicGeometry.QcohExtension.isQuasicoherent_X₂_of_shortExact` together with
  `isQuasicoherent_X₁_of_shortExact` and `isQuasicoherent_X₃_of_shortExact` below, which supply
  the two outer cases on an arbitrary scheme.
* Item (7), pullbacks, is
  `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback`.
* Item (8), tensor products, is `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj`.
* Item (9), the tensor, symmetric and exterior algebras, is the triple
  `Stacks.SheafOfModules.isQuasicoherent_tensorAlgebraSheaf_of_isQuasicoherent`,
  `isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent` and
  `isQuasicoherent_exteriorAlgebraSheaf_of_isQuasicoherent`.
* Item (10), the internal hom out of a module of finite presentation, is
  `Stacks.AlgebraicGeometry.InternalHomModules.isQuasicoherent_sheafHomModules`.

## Main results

* `Stacks.AlgebraicGeometry.FunctorialityQcoh.isQuasicoherent_iff_forall_isAffineOpen_exists_tilde`
  is item (1).
* `Stacks.AlgebraicGeometry.FunctorialityQcoh.isQuasicoherent_iff_forall_restrict` is item (2).
* `Stacks.AlgebraicGeometry.FunctorialityQcoh.isQuasicoherent_X₁_of_shortExact` and
  `isQuasicoherent_X₃_of_shortExact` complete item (6) on an arbitrary scheme; its middle case
  was already available there.

Items (3), (4), (5), (7), (8), (9) and the middle case of (6) are proved elsewhere in the
library for an arbitrary scheme, so the tag is recorded on them rather than restating them.

## Implementation notes

The covering set is spread over nine modules, so the tag cannot be written as an attribute at
every point of definition; `add_to_stacks` records it against the declarations proved
elsewhere, exactly as `StacksFrontier.Topology.Sheaves.Modules.LocallyFreeSection` does for the
section tag 01C5.

Items (1) and (2) are stated as the source states them, as criteria quantified over affine
opens. Both directions of each hold with no affineness used in the forward direction, which is
restriction along an open immersion; the affine hypothesis is kept because it is the source's.

Item (9) is registered on the ringed-space statements. A scheme is a ringed space, so these
cover the scheme-level assertion the section makes; the three algebras enter as the package
`SheafOfModules.TensorExteriorSymmetricAlgebras`, which is constructed unconditionally by
`SheafOfModules.ringedSpaceAlgebras` and is the shape in which the library's 01CL already sits.

## References

* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe w u

namespace Stacks.AlgebraicGeometry.FunctorialityQcoh

variable {X : Scheme.{u}}

/-! ### Item (1): recognising quasi-coherence from the sheaves `M^~` on affine opens -/

/-- **[Stacks, Tag 01LA], item (1).** A sheaf of `𝒪_X`-modules `F` is quasi-coherent if and
only if the restriction of `F` to each affine open `U = Spec Γ(X, U)` is of the form `M^~` for
some `Γ(X, U)`-module `M`.

Forwards, the module is `Γ(F, U)` and the isomorphism is
`Stacks.Modules.tildeIsoRestrictFromSpec`. Backwards, `M^~` is quasi-coherent, hence so is the
restriction of `F` to `Spec Γ(X, U)`; transporting along `hU.isoSpec.hom ≫ hU.fromSpec = U.ι`
makes the restriction of `F` to `U` quasi-coherent, and quasi-coherence is local on `X`. -/
@[stacks 01LA "the section's item (1): a sheaf of modules is quasi-coherent exactly when its \
restriction to each affine open `U = Spec Γ(X, U)` is the sheaf associated to a \
`Γ(X, U)`-module"]
theorem isQuasicoherent_iff_forall_isAffineOpen_exists_tilde (F : X.Modules) :
    F.IsQuasicoherent ↔
      ∀ (U : X.Opens) (hU : IsAffineOpen U),
        ∃ M : ModuleCat.{u} Γ(X, U),
          Nonempty (tilde (R := Γ(X, U)) M ≅ F.restrict hU.fromSpec) := by
  refine ⟨fun _ U hU ↦
    ⟨ModuleCat.of Γ(X, U) Γ(F, U), ⟨Stacks.Modules.tildeIsoRestrictFromSpec F hU⟩⟩,
    fun h ↦ QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens F fun V ↦ ?_⟩
  obtain ⟨U, hU : IsAffineOpen U⟩ := V
  obtain ⟨M, ⟨e⟩⟩ := h U hU
  have : (F.restrict hU.fromSpec).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso e inferInstance
  have iso : (F.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ F.restrict U.ι :=
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app F
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso iso inferInstance

/-! ### Item (2): quasi-coherence is affine-local -/

/-- **[Stacks, Tag 01LA], item (2).** A sheaf of `𝒪_X`-modules `F` is quasi-coherent if and
only if the restriction of `F` to each of the members of an affine open covering of `X` is
quasi-coherent.

Forwards this is restriction along an open immersion, which preserves quasi-coherence;
backwards it is `Stacks.Modules.isQuasicoherent_of_restrict`, the locality of
quasi-coherence. -/
@[stacks 01LA "the section's item (2): a sheaf of modules is quasi-coherent exactly when its \
restriction to each member of an affine open covering is quasi-coherent"]
theorem isQuasicoherent_iff_forall_restrict {I : Type w} (F : X.Modules)
    (U : I → X.affineOpens) (hU : ⨆ i, (U i : X.Opens) = ⊤) :
    F.IsQuasicoherent ↔ ∀ i, (F.restrict (U i : X.Opens).ι).IsQuasicoherent :=
  ⟨fun _ i ↦ Scheme.Modules.isQuasicoherent_restrictFunctor (U i : X.Opens).ι F,
    fun h ↦ Stacks.Modules.isQuasicoherent_of_restrict F (fun i ↦ (U i : X.Opens)) hU h⟩

/-! ### Item (6): the two outer cases on an arbitrary scheme -/

/-- **[Stacks, Tag 01LA], item (6), the kernel case.** Let
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of `𝒪_X`-modules on an arbitrary scheme `X`.
If `F₂` and `F₃` are quasi-coherent then so is `F₁`, being the kernel of `F₂ ⟶ F₃`. -/
@[stacks 01LA "the section's item (6), the kernel case on an arbitrary scheme: in a short exact \
sequence, if the last two terms are quasi-coherent then so is the first"]
theorem isQuasicoherent_X₁_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₂ : S.X₂.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₁.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hS.fIsKernel)
    (QcohLimits.isQuasicoherent_kernel S.g)

/-- **[Stacks, Tag 01LA], item (6), the cokernel case.** Let
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of `𝒪_X`-modules on an arbitrary scheme `X`.
If `F₁` and `F₂` are quasi-coherent then so is `F₃`, being the cokernel of `F₁ ⟶ F₂`. -/
@[stacks 01LA "the section's item (6), the cokernel case on an arbitrary scheme: in a short \
exact sequence, if the first two terms are quasi-coherent then so is the last"]
theorem isQuasicoherent_X₃_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) (h₂ : S.X₂.IsQuasicoherent) :
    S.X₃.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hS.gIsCokernel)
    (QuasicoherentColimits.isQuasicoherent_cokernel S.f)

end Stacks.AlgebraicGeometry.FunctorialityQcoh

/-! ### The rest of the covering set

The remaining items of the enumeration are proved elsewhere in the library, for an arbitrary
scheme in every case, so the section tag is recorded on those declarations. -/

add_to_stacks 01LA "the section's item (3): any direct sum of quasi-coherent modules is \
quasi-coherent" Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma
add_to_stacks 01LA "the section's item (4): any colimit of quasi-coherent modules is \
quasi-coherent" Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
add_to_stacks 01LA "the section's item (5) = Tag 01LB, the kernel half: the kernel of a \
morphism of quasi-coherent modules is quasi-coherent"
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel
add_to_stacks 01LA "the section's item (5) = Tag 01LB, the cokernel half: the cokernel of a \
morphism of quasi-coherent modules is quasi-coherent"
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
add_to_stacks 01LA "the section's item (6), the extension case on an arbitrary scheme: in a \
short exact sequence, if the two outer terms are quasi-coherent then so is the middle one"
  Stacks.AlgebraicGeometry.QcohExtension.isQuasicoherent_X₂_of_shortExact
add_to_stacks 01LA "the section's item (7): the pullback of a quasi-coherent module along a \
morphism of schemes is quasi-coherent"
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
add_to_stacks 01LA "the section's item (8): the tensor product of two quasi-coherent modules \
is quasi-coherent" AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj
add_to_stacks 01LA "the section's item (9), the tensor algebra of a quasi-coherent module is \
quasi-coherent" Stacks.SheafOfModules.isQuasicoherent_tensorAlgebraSheaf_of_isQuasicoherent
add_to_stacks 01LA "the section's item (9), the symmetric algebra of a quasi-coherent module \
is quasi-coherent"
  Stacks.SheafOfModules.isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent
add_to_stacks 01LA "the section's item (9), the exterior algebra of a quasi-coherent module is \
quasi-coherent"
  Stacks.SheafOfModules.isQuasicoherent_exteriorAlgebraSheaf_of_isQuasicoherent
add_to_stacks 01LA "the section's item (10): the internal hom from a module of finite \
presentation into a quasi-coherent module is quasi-coherent"
  Stacks.AlgebraicGeometry.InternalHomModules.isQuasicoherent_sheafHomModules

end
