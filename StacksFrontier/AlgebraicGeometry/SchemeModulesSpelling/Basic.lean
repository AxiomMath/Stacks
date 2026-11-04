module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingGradedHom
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Basic

/-!
# Sheaves of modules on a scheme and on its underlying ringed space

An `𝒪_X`-module on a scheme `X` is written in two ways in this repository: as an object of
`AlgebraicGeometry.Scheme.Modules X`, which is `SheafOfModules X.ringCatSheaf`, and as an object
of `SheafOfModules (structureSheafRing
X.toRingedSpace)`, the spelling the tensor product of Stacks Tag 01CB and the graded section
calculus of Stacks Tags 0B5L and 0B5M are built over. The two sheaves of rings are the same term
(`Stacks.TensorSheafSpellingIso.structureSheafRing_eq_ringCatSheaf`), so the two categories are
the same type; but `AlgebraicGeometry.Scheme.Modules` is a `def`, so instance search crosses
neither direction on its own.

This file crosses it, once: finite type, finite presentation, quasi-coherence and invertibility
transport, the nonvanishing open of Stacks Tag 01CY is the same open subset on both sides, and
the tensor product sheaf is the monoidal product.

## Main results

* `Stacks.SchemeModulesSpelling.toModules` and `Stacks.SchemeModulesSpelling.ofModules`: the two
  identity coercions, with `Stacks.SchemeModulesSpelling.modules_eq` and
  `Stacks.SchemeModulesSpelling.hom_eq` recording that objects and morphisms are literally the
  same.
* `Stacks.SchemeModulesSpelling.isFiniteType_iff`,
  `Stacks.SchemeModulesSpelling.isFinitePresentation_iff` and
  `Stacks.SchemeModulesSpelling.isQuasicoherent_iff`: the three Mathlib finiteness predicates are
  the same proposition in both spellings, with `scoped instance`s crossing each direction.
* `Stacks.SchemeModulesSpelling.isInvertible_algebraicGeometry` and
  `Stacks.SchemeModulesSpelling.isInvertible_stacks`: the two parallel copies of the invertibility
  class of Stacks Tag 01CS, `Stacks.SheafOfModules.IsInvertible` and
  `AlgebraicGeometry.SheafOfModules.IsInvertible`, imply each other; at a scheme this identifies
  `Stacks.Ample.IsInvertibleModule` with the hypothesis the graded section calculus asks for.
* `Stacks.SchemeModulesSpelling.nonvanishingLocus_eq` and
  `Stacks.SchemeModulesSpelling.nonvanishingOpen_eq`: the `X_s` of Stacks Tag 01CY computed from
  the ringed space is the `X_s` of the scheme.
* `Stacks.SchemeModulesSpelling.tensorSheaf_eq` and
  `Stacks.SchemeModulesSpelling.tensorSheafIsoMonoidal`: the tensor product sheaf of Stacks
  Tag 05NA at the section-site spelling is Tag 01CB's, and is the monoidal product on `X.Modules`.
* `Stacks.SchemeModulesSpelling.sectionRingGradedRing`,
  `Stacks.SchemeModulesSpelling.sectionRingGradingGradedRing`,
  `Stacks.SchemeModulesSpelling.sectionModuleModule`,
  `Stacks.SchemeModulesSpelling.sectionModuleDecomposition`,
  `Stacks.SchemeModulesSpelling.sectionModuleGradedSMul` and
  `Stacks.SchemeModulesSpelling.gradedHomAwayModule`: the algebraic structures of the graded
  section calculus of Stacks Tags 01CU, 0B5L and 0B5M, at the structure-sheaf spelling of a
  scheme. Each is a `scoped instance` restating a global instance that instance search does not
  reach, because its hypothesis is stated over `TensorSheafification.structureSheaf`.

## Implementation notes

**All transports are `scoped instance`s**, as
`Stacks.NonvanishingSpelling.isInvertible_toRingedSpace` already is: a consumer turns them on
with `open scoped Stacks.SchemeModulesSpelling`, and a file that does not is untouched. The
finiteness transports come in both directions and their conclusions have the same class head as
their hypotheses, so scoping is what keeps that pair out of every importing file.

A hypothesis about an object of `X.Modules` must name the sheaf of rings, as in
`[SheafOfModules.IsFiniteType (R := X.ringCatSheaf) M]`: in an instance binder the universe
arguments of the Mathlib classes are solved before the type of `M` is looked at, and
`AlgebraicGeometry.Scheme.Modules` being a `def` they then default to `0`.

The two invertibility classes are parallel copies with the same two fields over the same
monoidal structure on presheaves of modules, so the transport is a repackaging of the
tensor-functor data; the two `TensorLeftUniversal` structures are distinct constants, which is
why the transport is a theorem and not `rfl`.

The `𝒪_{X,x}`-module structure on a stalk is named at the ringed-space spelling in Stacks Tag
01CB and at the scheme spelling elsewhere; both names are Mathlib's instance
(`Stacks.SheafOfModules.stalkModule_eq`, which is `rfl`), and transporting the submodule
`𝔪_x · M_x` across an equality of `Module` instances is done by substituting that equality in
`mem_maximalIdeal_smul_congr` rather than by rewriting, since the ambient term is not
type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe v u w

namespace Stacks.SchemeModulesSpelling

/-! ### Invertibility -/

section Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- The invertibility class of Stacks Tag 01CS in the `Stacks.SheafOfModules` copy implies the
one in the `AlgebraicGeometry.SheafOfModules` copy: a tensor functor satisfying the one
universal property satisfies the other, the two being the same two conditions. -/
theorem isInvertible_algebraicGeometry (h : Stacks.SheafOfModules.IsInvertible O hO L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible O hO L :=
  h.toAlgebraicGeometry

/-- The converse of `isInvertible_algebraicGeometry`: the two copies of the invertibility class
of Stacks Tag 01CS are equivalent. -/
theorem isInvertible_stacks (h : AlgebraicGeometry.SheafOfModules.IsInvertible O hO L) :
    Stacks.SheafOfModules.IsInvertible O hO L :=
  .ofAlgebraicGeometry O hO L h

end Invertible

variable (X : Scheme.{u})

/-! ### The two categories of modules -/

/-- The category of `𝒪_X`-modules on a scheme is the category of sheaves of modules over the
structure sheaf of rings of its underlying ringed space, in the packaging of Stacks Tag 01CB. -/
theorem modules_eq : X.Modules = SheafOfModules.{u} (structureSheafRing X.toRingedSpace) := rfl

/-- An `𝒪_X`-module in the ringed-space packaging of Stacks Tag 01CB, read as an object of
`X.Modules`. This is the identity. -/
abbrev toModules (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) : X.Modules := M

/-- An object of `X.Modules`, read as a sheaf of modules over the structure sheaf of rings of the
underlying ringed space. This is the identity. -/
abbrev ofModules (M : X.Modules) : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) := M

/-- Morphisms of `𝒪_X`-modules are the same in the two spellings. -/
theorem hom_eq (M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (M ⟶ N) = (toModules X M ⟶ toModules X N) := rfl

/-! ### Finiteness, quasi-coherence and invertibility at a scheme -/

section Properties

variable (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- Finite type in the sense of Stacks Tag 01B4 is the same condition in the two spellings. -/
theorem isFiniteType_iff :
    SheafOfModules.IsFiniteType (R := structureSheafRing X.toRingedSpace) M ↔
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf) (toModules X M) := Iff.rfl

/-- Finite presentation in the sense of Stacks Tag 01BN is the same condition in the two
spellings. -/
theorem isFinitePresentation_iff :
    SheafOfModules.IsFinitePresentation (R := structureSheafRing X.toRingedSpace) M ↔
      SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (toModules X M) := Iff.rfl

/-- Quasi-coherence in the sense of Stacks Tag 01BD is the same condition in the two
spellings. -/
theorem isQuasicoherent_iff :
    SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) M ↔
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (toModules X M) := Iff.rfl

/-- Finite type, transported to `X.Modules`. -/
scoped instance isFiniteType_toModules
    [SheafOfModules.IsFiniteType (R := structureSheafRing X.toRingedSpace) M] :
    SheafOfModules.IsFiniteType (R := X.ringCatSheaf) (toModules X M) := ‹_›

/-- Finite type, transported from `X.Modules`. -/
scoped instance isFiniteType_ofModules
    [SheafOfModules.IsFiniteType (R := X.ringCatSheaf) (toModules X M)] :
    SheafOfModules.IsFiniteType (R := structureSheafRing X.toRingedSpace) M := ‹_›

/-- Finite presentation, transported to `X.Modules`. -/
scoped instance isFinitePresentation_toModules
    [SheafOfModules.IsFinitePresentation (R := structureSheafRing X.toRingedSpace) M] :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (toModules X M) := ‹_›

/-- Finite presentation, transported from `X.Modules`. -/
scoped instance isFinitePresentation_ofModules
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (toModules X M)] :
    SheafOfModules.IsFinitePresentation (R := structureSheafRing X.toRingedSpace) M := ‹_›

/-- Quasi-coherence, transported to `X.Modules`. -/
scoped instance isQuasicoherent_toModules
    [SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) M] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (toModules X M) := ‹_›

/-- Quasi-coherence, transported from `X.Modules`. -/
scoped instance isQuasicoherent_ofModules
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (toModules X M)] :
    SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) M := ‹_›

/-- Invertibility of Stacks Tag 01CS, transported from the hypothesis the graded section
calculus of Stacks Tags 0B5L and 0B5M asks for to the class `Stacks.Ample.IsInvertibleModule`
that the scheme-level ampleness files are written over. -/
scoped instance isInvertibleModule_toModules
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M] :
    Stacks.Ample.IsInvertibleModule X (toModules X M) :=
  isInvertible_algebraicGeometry _ _ _ ‹_›

/-- Invertibility of Stacks Tag 01CS, transported from `Stacks.Ample.IsInvertibleModule` to the
hypothesis the graded section calculus asks for. -/
scoped instance isInvertible_ofModules [Stacks.Ample.IsInvertibleModule X (toModules X M)] :
    Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  isInvertible_stacks _ _ _ ‹_›

end Properties

/-! ### The instances of the graded section calculus -/

section GradedCalculus

open Stacks.SheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf

variable (M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property M]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- The graded ring structure on the section ring `⨁ₙ Γ(X, M^{⊗ n})`. -/
scoped instance sectionRingGradedRing : DirectSum.GCommRing
    (fun n : ℕ => (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) M
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :=
  Stacks.SheafOfModules.sectionRingGradedRing (sectionSiteRing X) (sectionSiteSheaf X) M

/-- The section ring is internally graded by its homogeneous summands. -/
scoped instance sectionRingGradingGradedRing :
    GradedRing (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) M) :=
  Stacks.SheafOfModules.sectionRingGradingGradedRing (sectionSiteRing X) (sectionSiteSheaf X) M

/-- The section ring acts on the section module `⨁ₙ Γ(X, N ⊗ M^{⊗ n})`. -/
scoped instance sectionModuleModule :
    Module (sectionRing (sectionSiteRing X) (sectionSiteSheaf X) M)
      (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) M N) :=
  Stacks.SheafOfModules.sectionModuleModule (sectionSiteRing X) (sectionSiteSheaf X) M N

/-- The section module decomposes into its homogeneous summands. -/
scoped instance sectionModuleDecomposition : DirectSum.Decomposition
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) M N) :=
  Stacks.SheafOfModules.sectionModuleDecomposition (sectionSiteRing X) (sectionSiteSheaf X) M N

/-- The action of the section ring on the section module adds degrees. -/
scoped instance sectionModuleGradedSMul : SetLike.GradedSMul
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) M)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) M N) :=
  Stacks.SheafOfModules.sectionModuleGradedSMul (sectionSiteRing X) (sectionSiteSheaf X) M N

/-- The degree-zero homogeneous localization of the section ring acts on the localization of the
graded Hom module through its embedding into the full localization. Mathlib keeps this
`Module.compHom` action out of instance search, and `Stacks.SheafOfModules.homAtNonvanishingOpen`
is a submodule over it, so it has to be in scope for that submodule to have an additive
structure at all. -/
scoped instance gradedHomAwayModule (F G : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) (s : M.sections) :
    Module (HomogeneousLocalization.Away
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) M)
        (homogeneousSection X M s))
      (LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) M)
        (homogeneousSection X M s) (gradedHom X M F G)) :=
  Module.compHom (R := Localization.Away (homogeneousSection X M s))
    (LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) M)
      (homogeneousSection X M s) (gradedHom X M F G))
    (algebraMap (HomogeneousLocalization.Away
      (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) M)
      (homogeneousSection X M s))
      (Localization.Away (homogeneousSection X M s)))

end GradedCalculus

/-! ### The nonvanishing open -/

section Nonvanishing

variable (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The `𝒪_{X,x}`-module structure on a stalk used in Stacks Tag 01CB is Mathlib's, which is
the one `Stacks.ModuleStalk.maximalSmul` is stated over. -/
theorem stalkModule_eq (x : X) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace M.val x =
      Stacks.ModuleStalk.stalkModule (toModules X M) x :=
  Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace M.val x

/-- Membership of `I · M` is unchanged by an equality of the module structures involved. -/
private theorem mem_maximalIdeal_smul_congr {R N : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup N] {i j : Module R N} (h : i = j) (m : N) :
    m ∈ (I • (⊤ : @Submodule R N _ _ i)) ↔ m ∈ (I • (⊤ : @Submodule R N _ _ j)) := by
  subst h; exact Iff.rfl

/-- **The two spellings of the nonvanishing locus of Stacks Tag 01CY agree.** The locus computed
from the underlying ringed space of a scheme, for a restriction-compatible family of sections, is
the locus computed from the scheme for the global section that family names. -/
theorem nonvanishingLocus_eq (s : M.sections) :
    Stacks.SheafOfModules.nonvanishingLocus M s =
      Stacks.Ample.nonvanishingLocus (toModules X M) (s.eval (op ⊤)) := by
  ext x
  exact not_congr (mem_maximalIdeal_smul_congr
    (IsLocalRing.maximalIdeal (ringStalk X.toRingedSpace x)) (stalkModule_eq X M x)
    (grpGerm X.toRingedSpace M.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))))

/-- **The two spellings of the nonvanishing open `X_s` of Stacks Tag 01CY agree.** This is the
form the consumers need: the open subset that the graded section calculus of Stacks Tags 0B5L and
0B5M restricts to is the `X.Opens` that affineness and quasi-compactness are stated for. -/
theorem nonvanishingOpen_eq
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M] (s : M.sections) :
    Stacks.SheafOfModules.nonvanishingOpen M s =
      Stacks.NonvanishingOpen.nonvanishingOpen X (toModules X M) (s.eval (op ⊤)) :=
  Opens.ext (nonvanishingLocus_eq X M s)

end Nonvanishing

/-! ### The tensor product -/

section Tensor

variable (A B : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The tensor product sheaf of Stacks Tag 05NA, over the section site of a scheme, is the one of
Stacks Tag 01CB over the underlying ringed space. -/
theorem tensorSheaf_eq :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Stacks.SheafOfModules.sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((Stacks.SheafOfModules.sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((Stacks.SheafOfModules.sectionSiteSheaf X))⟩).obj (A)).obj (B)) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (A)).obj (B)) := rfl

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

/-- The monoidal product of two `𝒪_X`-modules is the tensor product sheaf at the spelling the
graded section calculus of Stacks Tags 0B5L and 0B5M uses. -/
def tensorSheafIsoMonoidal :
    toModules X A ⊗ toModules X B ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Stacks.SheafOfModules.sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((Stacks.SheafOfModules.sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((Stacks.SheafOfModules.sectionSiteSheaf X))⟩).obj (A)).obj (B)) :=
  Stacks.TensorSheafSpellingIso.monoidalTensorIso X A B

end Tensor

end Stacks.SchemeModulesSpelling

end
