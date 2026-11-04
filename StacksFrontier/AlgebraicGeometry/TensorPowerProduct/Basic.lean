module

public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtensionAffineCover.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0890: an ample sheaf stays ample after tensoring with a sheaf whose powers have sections

Let `X` be a scheme and `L`, `M` invertible `𝒪_X`-modules. If `L` is ample and the nonvanishing
opens `X_t`, for `t` a global section of a positive tensor power of `M`, cover `X`, then
`L ⊗ M` is ample ([Stacks, Tag 0890], [EGA II, Proposition 4.5.6(ii)]).

## Main definitions

* `Stacks.SheafOfModules.Invertible.tensorInterchange`: the braided interchange
  `(A ⊗ B) ⊗ (D ⊗ E) ≅ (A ⊗ D) ⊗ (B ⊗ E)` of the sheaf tensor product.
* `Stacks.SheafOfModules.Invertible.tensorPowerProductIso`:
  `(L ⊗ M)^{⊗ n} ≅ L^{⊗ n} ⊗ M^{⊗ n}` for `n : ℕ`.
* `AlgebraicGeometry.Scheme.Modules.tensorProductModule`: the tensor product of two modules on a
  scheme, ascribed at `X.Modules`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAmple_tensor_of_power_sections_cover`: **Tag 0890**.
* `AlgebraicGeometry.Scheme.Modules.isInvertible_tensorProductModule`: Tag 01CT part (1) at the
  ascribed spelling, so that instance search finds it.

## Implementation notes

The source argument is one line: given `x ∈ X`, pick `n ≥ 1` and `s ∈ Γ(X, L^{⊗ n})` with
`x ∈ X_s` and `X_s` affine (ampleness of `L`), and `m ≥ 1` and `t ∈ Γ(X, M^{⊗ m})` with
`x ∈ X_t` (the cover). Then `s^m t^n ∈ Γ(X, (L ⊗ M)^{⊗ nm})`, its nonvanishing open is
`X_s ⊓ X_t`, and that is affine by [Stacks, Tag 01PV] applied with the affine open `X_s`.

`Stacks.SheafOfModules.Invertible.sectionPow'` raises a global section of `L^{⊗ n}` to a global
section of `L^{⊗ nm}` directly, with `nonvanishingLocus_sectionPow'` saying the nonvanishing locus
does not move; the two exponents `nm` and `mn` are identified by `sectionsCongr`, which also does
not move it. The product of a
section of `L^{⊗ nm}` and a section of `M^{⊗ nm}` is `Stacks.SheafOfModules.tensorSections`,
whose nonvanishing locus is the intersection of the two by `nonvanishingLocus_tensorSections`.
The sheaf that product lives on is identified with a tensor power of `L ⊗ M` by
`tensorPowerProductIso`, an induction on `n` whose step is the braided interchange above, built
from the associator `Stacks.SheafOfModules.Invertible.tensorProductAssociator`, the braiding
`Stacks.SheafOfModules.Invertible.tensorProductBraiding` and the left unitor
`Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor`.

**Why `tensorProductModule` exists.** Instance search re-infers an object's type from the
declared return type of the definition that produced it, and
`Stacks.SheafOfModules.Tensor.sheafTensor` returns a
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf _)`, not an `X.Modules`. So
`AlgebraicGeometry.Scheme.Modules.isInvertible_tensorPower` — which is stated for `M : Y.Modules`
and is what makes the nonvanishing locus of a section of a tensor power nameable — is never tried
against a tensor product written with `sheafTensor`. An `abbrev` with return type
`Y.Modules` fixes that, and being reducible it changes no statement: `IsAmple X
(tensorProductModule X L M)` and `IsAmple X (((sheafTensor _).obj L).obj M)` are the same
proposition.

The two local instances below supply sheafification of abelian-group-valued presheaves on the
site of opens of a scheme; without them the tensor powers of Tag 01CU cannot be formed over a
scheme at all.

## References

* [Stacks Project, Tag 0890](https://stacks.math.columbia.edu/tag/0890)
* [EGA II, Proposition 4.5.6(ii)]
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe u v w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The interchange isomorphism of the sheaf tensor product**,
`(A ⊗ B) ⊗ (D ⊗ E) ≅ (A ⊗ D) ⊗ (B ⊗ E)`: reassociate so that `B` and `D` become adjacent, swap
them by the braiding, and reassociate back. -/
noncomputable def tensorInterchange
    (A B D E : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
            A).obj B)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          D).obj E)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
            A).obj D)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          B).obj E)) :=
  tensorProductAssociator O hO A B
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        D).obj E)
    ≪≫
    tensorProductIso O hO (Iso.refl A) (tensorProductAssociator O hO B D E).symm ≪≫
    tensorProductIso O hO (Iso.refl A)
      (tensorProductIso O hO (tensorProductBraiding O hO B D) (Iso.refl E)) ≪≫
    (tensorProductAssociator O hO A
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          D).obj B) E).symm ≪≫
    tensorProductIso O hO (tensorProductAssociator O hO A D B).symm (Iso.refl E) ≪≫
    tensorProductAssociator O hO
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        A).obj D) B
      E

/-- **The tensor powers of a tensor product of invertible sheaves split**,
`(L ⊗ M)^{⊗ n} ≅ L^{⊗ n} ⊗ M^{⊗ n}` for a natural number `n`.

At `n = 0` both sides are the structure sheaf, the right one after the left unitor. The step
reads `(L ⊗ M)^{⊗ (n+1)}` as `(L ⊗ M)^{⊗ n} ⊗ (L ⊗ M)` by Tag 01CU's successor comparison,
applies the inductive hypothesis, interchanges the two middle factors, and recombines
`L^{⊗ n} ⊗ L` and `M^{⊗ n} ⊗ M` by the same successor comparison. -/
noncomputable def tensorPowerProductIso
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO M] :
    (n : ℕ) →
      tensorPower O hO
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
            L).obj M)
          (n : ℤ) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (tensorPower O hO L (n : ℤ))).obj (tensorPower O hO M (n : ℤ))
  | 0 => (tensorProductLeftUnitor O hO
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).symm
  | n + 1 =>
      (tensorPowerSuccIso O hO
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
            L).obj M) (n : ℤ)).symm ≪≫
        tensorProductIso O hO (tensorPowerProductIso L M n) (Iso.refl _) ≪≫
        tensorInterchange O hO (tensorPower O hO L (n : ℤ)) (tensorPower O hO M (n : ℤ)) L M ≪≫
        tensorProductIso O hO (tensorPowerSuccIso O hO L (n : ℤ))
          (tensorPowerSuccIso O hO M (n : ℤ))

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- Abelian-group-valued presheaves on a scheme admit sheafification. -/
noncomputable local instance (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- For abelian-group-valued presheaves on a scheme, the morphisms inverted by sheafification
are exactly the locally bijective ones. -/
noncomputable local instance (X : Scheme.{u}) :
    (Opens.grothendieckTopology (X : Type u)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The tensor product of two modules on a scheme, ascribed at `Y.Modules`. Reducible, so it is
the same object as `((Stacks.SheafOfModules.Tensor.sheafTensor _).obj A).obj B`; the point
of the ascription is that instance search reads the declared return type, and the tensor functor's
is the generic `SheafOfModules` spelling. -/
noncomputable abbrev tensorProductModule (Y : Scheme.{u}) (A B : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property A] : Y.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.toRingedSpace.sheaf).obj A).obj B

/-- **Tag 01CT part (1) at the ascribed spelling**: the tensor product of two invertible modules
on a scheme is invertible, as an instance on `tensorProductModule`. This restates
`Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible` at the spelling instance search can
reach. -/
public instance isInvertible_tensorProductModule (Y : Scheme.{u}) (A B : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property A]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property B] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property (tensorProductModule Y A B) :=
  Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property A B

/-- **Stacks Project, Tag 0890.** Let `L` and `M` be invertible modules on a scheme `X`. If `L`
is ample and the nonvanishing opens of the global sections of the positive tensor powers of `M`
cover `X`, then `L ⊗ M` is ample.

At a point `x`, ampleness of `L` gives `n ≥ 1` and `s ∈ Γ(X, L^{⊗ n})` with `x ∈ X_s` and `X_s`
affine, and the cover gives `m ≥ 1` and `t ∈ Γ(X, M^{⊗ m})` with `x ∈ X_t`. The section
`s^m ⊗ t^n` of `(L ⊗ M)^{⊗ nm}`, read through `tensorPowerProductIso`, has nonvanishing open
`X_s ⊓ X_t`, which contains `x` and is affine by Tag 01PV. -/
@[stacks 0890, ega "II 4.5.6" "(ii)"]
theorem isAmple_tensor_of_power_sections_cover (X : Scheme.{u}) (L M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (hL : IsAmple X L)
    (hcover : ∀ x : X, ∃ m : ℕ, 1 ≤ m ∧
      ∃ t : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property M (m : ℤ)).sections,
        x ∈ nonvanishingOpen (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property M (m : ℤ)) t) :
    IsAmple X (tensorProductModule X L M) := by
  have hloc : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => X.isLocalRing z
  refine ⟨hL.1, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, haff⟩ := hL.2 x
  obtain ⟨m, hm, t, ht⟩ := hcover x
  have hk : 1 ≤ n * m := by simpa using Nat.mul_le_mul hn hm
  let qL := sectionPow' L s m
  let qM := sectionsCongr X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property M (Nat.mul_comm m n) (sectionPow' M t n)
  let e := (tensorPowerProductIso X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L M (n * m)).symm
  have h1 := Stacks.SheafOfModules.nonvanishingLocus_sectionsMap X.toRingedSpace e
    (Stacks.SheafOfModules.tensorSections _ _ qL qM)
  have h2 : Stacks.SheafOfModules.nonvanishingLocus
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L ((n * m : ℕ) : ℤ))).obj
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property M ((n * m : ℕ) : ℤ)))
        (Stacks.SheafOfModules.tensorSections _ _ qL qM)
      = Stacks.SheafOfModules.nonvanishingLocus _ qL
        ∩ Stacks.SheafOfModules.nonvanishingLocus _ qM :=
    Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ qL qM
  have h3 : Stacks.SheafOfModules.nonvanishingLocus _ qL
      = Stacks.SheafOfModules.nonvanishingLocus _ s :=
    nonvanishingLocus_sectionPow' L s m hm
  have h4 : Stacks.SheafOfModules.nonvanishingLocus _ qM
      = Stacks.SheafOfModules.nonvanishingLocus _ t :=
    (nonvanishingLocus_sectionsCongr M (Nat.mul_comm m n) (sectionPow' M t n)).trans
      (nonvanishingLocus_sectionPow' M t n hn)
  have hloci : Stacks.SheafOfModules.nonvanishingLocus _
        (_root_.SheafOfModules.sectionsMap e.hom
          (Stacks.SheafOfModules.tensorSections _ _ qL qM))
      = Stacks.SheafOfModules.nonvanishingLocus _ s
        ∩ Stacks.SheafOfModules.nonvanishingLocus _ t :=
    h1.trans (h2.trans (by rw [h3, h4]))
  refine ⟨n * m, hk, _root_.SheafOfModules.sectionsMap e.hom
    (Stacks.SheafOfModules.tensorSections _ _ qL qM), ?_, ?_⟩
  · have hmem : x ∈ Stacks.SheafOfModules.nonvanishingLocus _
        (_root_.SheafOfModules.sectionsMap e.hom
          (Stacks.SheafOfModules.tensorSections _ _ qL qM)) := by
      rw [hloci]; exact ⟨hs, ht⟩
    exact hmem
  · have hEq : Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (tensorProductModule X L M) ((n * m : ℕ) : ℤ))
        (_root_.SheafOfModules.sectionsMap e.hom
          (Stacks.SheafOfModules.tensorSections _ _ qL qM))
        = Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ s ⊓
          Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ t :=
      TopologicalSpace.Opens.ext hloci
    exact Eq.mpr (congrArg IsAffineOpen hEq)
      (isAffineOpen_inf_nonvanishingOpen _ t _ haff)

end AlgebraicGeometry.Scheme.Modules

end
