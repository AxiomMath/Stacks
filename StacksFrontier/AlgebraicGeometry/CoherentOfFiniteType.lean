module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Affine
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Basis
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.ProperMapping
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentIffFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-coherent module of finite type on a locally Noetherian scheme is coherent

This is [Stacks, Tag 01XZ] in the direction *into* coherence: implication (2) ⇒ (1) of the
characterisation of coherent modules on a locally Noetherian scheme. Together with the
implications out of (1), which hold on any ringed space and are
[Stacks, Tag 01BW], it gives the equivalence of (1) and (2), and together with
[Stacks, Tag 01BZ] — formalized as
`Stacks.SheafOfModules.isCoherent_iff_isFinitePresentation`, whose hypothesis is coherence of the
structure sheaf and so is discharged here — also the equivalence with (3), finite presentation.

The proof is the source's, organised so that the Noetherian hypothesis enters once. Coherence is
checked on the affine opens (`isCoherent_of_basis`), and over an affine open the relations among
finitely many sections are finitely generated because the ring of sections is Noetherian
(`isFiniteType_kernel_free_isAffineOpen`).

Two consequences of [Stacks, Tag 01Y1] follow, in the form the dévissage of
[Stacks, Tag 02O5] consumes: a quasi-coherent submodule and a quasi-coherent quotient of a
coherent module are coherent. The submodule case needs the extra observation that the kernel of a
morphism from a module of finite type to an arbitrary quasi-coherent module is of finite type
(`isFiniteType_kernel_of_isQuasicoherent`), applied to the projection onto the cokernel.

## Main results

* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType`:
  **[Stacks, Tag 01XZ], (2) ⇒ (1)**, for the coherence predicate
  `SheafOfModules.IsCoherent`, and
  `stacksIsCoherent_of_isQuasicoherent_of_isFiniteType` for the other one.
* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isQuasicoherent_and_isFiniteType`
  and `isCoherent_iff_isFinitePresentation`: **[Stacks, Tag 01XZ], (1) ⇔ (2) ⇔ (3)**.
* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit`: the structure sheaf of a
  locally Noetherian scheme is coherent.
* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isFiniteType_kernel_free`: over any open of a
  locally Noetherian scheme, the relations among finitely many sections of a quasi-coherent
  module are locally finitely generated. No finiteness of the module is assumed.
* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent` and
  `isCoherent_of_epi_of_isQuasicoherent`: **[Stacks, Tag 01Y1]** — a quasi-coherent submodule and
  a quasi-coherent quotient of a coherent module are coherent.
* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_higherDirectImage_of_isAffineHom`:
  **[Stacks, Tag 02O5] for an affine morphism with locally Noetherian target**, with the
  remaining hypothesis of
  `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_of_isAffineHom`
  discharged down to quasi-coherence and finiteness of type of the direct image.

## Implementation notes

**No `@[stacks 01XZ]` tag is placed.** Tag 01XZ is a five-way equivalence; conditions (4) and (5)
are not stated here, so the covering set of the tag is not present. What is proved is
(1) ⇔ (2) ⇔ (3). Conditions (4) and (5) live in
`StacksFrontier/AlgebraicGeometry/CoherentTFAE/Basic.lean` as
`Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn`, and (2) ⇒ (4) is proved there as
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType`; the
tag can be placed once those are assembled with the implications proved here.

**The predicate is written `_root_.SheafOfModules.IsCoherent` throughout, and that is not
cosmetic**: inside the `Stacks.` namespace the unqualified name and the dot notation both resolve
to the other coherence constant of this branch, with no error anywhere. See the implementation
notes of `StacksFrontier/AlgebraicGeometry/ProperMapping/CoherenceClosure.lean`.

Several instance arguments are supplied positionally rather than left to synthesis. The reason is
uniform: `AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, so a lemma stated
for a general site, applied to `X.Modules`, asks for `Epi`, `IsFiniteType` or `HasKernel`
instances at the `SheafOfModules _` spelling, while the hypotheses in context carry the
`X.Modules` one. The two are definitionally equal, so passing the term works; synthesis does not
see through the `def`.

`HasDerivedCategory.standard` is made a local instance, as it is in
`StacksFrontier/AlgebraicGeometry/ProperMapping.lean`: the statement of
`isCoherent_higherDirectImage_of_isAffineHom` must name the same derived category as the theorem
of that file whose hypothesis it discharges. Nothing else in this file mentions a derived
category.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01BZ](https://stacks.math.columbia.edu/tag/01BZ)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/
@[expose] public section

open CategoryTheory Limits TopologicalSpace SheafOfModules
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.CoherentOfFiniteType

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-! ### Relations among finitely many sections -/

/-- **The relations among finitely many sections of a quasi-coherent module over an arbitrary
open of a locally Noetherian scheme are locally finitely generated.** -/
theorem isFiniteType_kernel_free (Q : X.Modules) [Q.IsQuasicoherent] (U : X.Opens)
    {A : Type u} [Finite A]
    (φ : (free A : SheafOfModules.{u} (X.ringCatSheaf.over U)) ⟶ Q.over U) :
    (kernel φ).IsFiniteType :=
  isFiniteType_kernel_free_of_basis (fun V => IsAffineOpen V)
    (fun _W _x hx => Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx)
    (fun V hV B hB ψ => @isFiniteType_kernel_free_isAffineOpen X _ Q _ V hV B hB ψ) U φ

/-! ### Coherence of a quasi-coherent module of finite type -/

/-- **Stacks 01XZ, (2) ⇒ (1).** On a locally Noetherian scheme a quasi-coherent module of finite
type is coherent. -/
theorem isCoherent_of_isQuasicoherent_of_isFiniteType (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] : _root_.SheafOfModules.IsCoherent F :=
  isCoherent_of_basis F (fun V => IsAffineOpen V)
    (fun _W _x hx => Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx)
    fun V hV B hB ψ => @isFiniteType_kernel_free_isAffineOpen X _ F _ V hV B hB ψ

/-- **Stacks 01XZ, (2) ⇒ (1)** for the second coherence predicate of this branch. -/
theorem stacksIsCoherent_of_isQuasicoherent_of_isFiniteType (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] : Stacks.SheafOfModules.IsCoherent F :=
  Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent
    (isCoherent_of_isQuasicoherent_of_isFiniteType F)

/-- **Stacks 01XZ, (1) ⇔ (2).** -/
theorem isCoherent_iff_isQuasicoherent_and_isFiniteType (F : X.Modules) :
    _root_.SheafOfModules.IsCoherent F ↔ F.IsQuasicoherent ∧ F.IsFiniteType := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · exact ⟨@_root_.isQuasicoherent_of_isCoherent _ _ _ F h,
      @_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ F h⟩
  · have := h₁
    have := h₂
    exact isCoherent_of_isQuasicoherent_of_isFiniteType F

/-! ### The structure sheaf, and finite presentation -/

/-- **The structure sheaf of a locally Noetherian scheme is coherent.** -/
theorem isCoherent_unit : _root_.SheafOfModules.IsCoherent (unit.{u} X.ringCatSheaf) :=
  @isCoherent_of_isQuasicoherent_of_isFiniteType X _ (unit.{u} X.ringCatSheaf)
    isQuasicoherent_unit isFiniteType_unit

/-- **Stacks 01XZ, (1) ⇔ (3).** On a locally Noetherian scheme a module is coherent if and only
if it is of finite presentation; this is [Stacks, Tag 01BZ] together with coherence of the
structure sheaf. -/
theorem isCoherent_iff_isFinitePresentation (F : X.Modules) :
    _root_.SheafOfModules.IsCoherent F ↔ F.IsFinitePresentation :=
  have : Stacks.SheafOfModules.IsCoherent (unit.{u} X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent isCoherent_unit
  (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff F).trans
    (Stacks.SheafOfModules.isCoherent_iff_isFinitePresentation X.ringCatSheaf F)

/-! ### Submodules and quotients: Stacks 01Y1 -/

/-- The kernel of a morphism from a module of finite type to a quasi-coherent module on a
locally Noetherian scheme is of finite type. -/
theorem isFiniteType_kernel_of_isQuasicoherent {M Q : X.Modules} [M.IsFiniteType]
    [Q.IsQuasicoherent] (ψ : M ⟶ Q) : (kernel ψ).IsFiniteType := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have hloc : ∀ i, ((kernel ψ).over (σ.X i)).IsFiniteType := fun i => by
    have hfin : Finite (σ.generators i).I := (hσ.isFiniteType i).finite
    have h1 : (kernel ((σ.generators i).π ≫ ψ.over (σ.X i))).IsFiniteType :=
      @isFiniteType_kernel_free X _ Q _ (σ.X i) (σ.generators i).I hfin _
    have h2 : (kernel (ψ.over (σ.X i))).IsFiniteType :=
      Stacks.SheafOfModules.isFiniteType_kernel_of_epi_comp (σ.generators i).π _ h1
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (M := kernel (ψ.over (σ.X i))) (N := (kernel ψ).over (σ.X i))
      (Stacks.SheafOfModules.overKernelIso ψ (σ.X i)).symm
  exact Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop (kernel ψ) σ.X
    σ.coversTop hloc

/-- A quasi-coherent submodule of a quasi-coherent module of finite type on a locally Noetherian
scheme is of finite type. -/
theorem isFiniteType_of_mono_of_isQuasicoherent {G F : X.Modules} [G.IsQuasicoherent]
    [F.IsQuasicoherent] [F.IsFiniteType] (ι : G ⟶ F) [Mono ι] : G.IsFiniteType := by
  have h1 : (kernel (cokernel.π ι)).IsFiniteType :=
    isFiniteType_kernel_of_isQuasicoherent (cokernel.π ι)
  have h2 : IsIso (Abelian.factorThruImage ι) := Abelian.isIso_factorThruImage ι
  exact @Stacks.SheafOfModules.isFiniteType_of_iso.{u} _ _ _ _ _ _ _ _ _
    (@asIso _ _ _ _ (Abelian.factorThruImage ι) h2).symm h1

/-- **Stacks 01Y1, submodules.** A quasi-coherent submodule of a coherent module on a locally
Noetherian scheme is coherent.

This carries the tag, and with the quotient statement below 01Y1's covering set is complete. The
source (coherent.tex:2364) states exactly two assertions — "Any quasi-coherent submodule of `F`
is coherent. Any quasi-coherent quotient module of `F` is coherent." — and one declaration is
tagged for each. Both are proved here, so the attribute is not an over-claim. -/
@[stacks 01Y1 "quasi_coherent_submodule", ega "I 9.6.4" "submodule, B = O_X"]
theorem isCoherent_of_mono_of_isQuasicoherent {G F : X.Modules} [G.IsQuasicoherent]
    (hF : _root_.SheafOfModules.IsCoherent F) (ι : G ⟶ F) [Mono ι] :
    _root_.SheafOfModules.IsCoherent G :=
  have ⟨_, _⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType F).1 hF
  have : G.IsFiniteType := isFiniteType_of_mono_of_isQuasicoherent ι
  isCoherent_of_isQuasicoherent_of_isFiniteType G

/-- **Stacks 01Y1, quotients.** A quasi-coherent quotient of a coherent module on a locally
Noetherian scheme is coherent. This is the second of 01Y1's two assertions; see the submodule
statement above for why the tag is complete here. -/
@[stacks 01Y1 "quasi_coherent_quotient", ega "I 9.6.4" "quotient, B = O_X"]
theorem isCoherent_of_epi_of_isQuasicoherent {F Q : X.Modules} [Q.IsQuasicoherent]
    (hF : _root_.SheafOfModules.IsCoherent F) (p : F ⟶ Q) [Epi p] :
    _root_.SheafOfModules.IsCoherent Q :=
  have ⟨_, hft⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType F).1 hF
  have : Q.IsFiniteType :=
    @Stacks.SheafOfModules.isFiniteType_of_epi'.{u} _ _ _ _ _ _ _ _ _ p hft ‹Epi p›
  isCoherent_of_isQuasicoherent_of_isFiniteType Q

/-! ### The affine case of the proper mapping theorem -/

/-- **[Stacks, Tag 02O5] for an affine morphism with locally Noetherian target**, with the
remaining hypothesis of
`Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_of_isAffineHom`
discharged: all that is needed of the direct image is that it is quasi-coherent and of finite
type. -/
theorem isCoherent_higherDirectImage_of_isAffineHom {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] (F : Y.Modules) (hF : _root_.SheafOfModules.IsCoherent F)
    [((Scheme.Modules.pushforward f).obj F).IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj F).IsFiniteType] (p : ℤ) :
    _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  ProperMapping.isCoherent_higherDirectImage_of_isAffineHom f F hF
    (isCoherent_of_isQuasicoherent_of_isFiniteType _) p

end Stacks.AlgebraicGeometry.CoherentOfFiniteType

end
