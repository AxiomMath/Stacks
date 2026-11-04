module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ampleness over the actual tensor powers, and Stacks Tag 01QE unconditionally

`Stacks.Ample.IsAmpleForPowers X pow` takes the family of tensor powers as an explicit parameter
`pow : ℤ → X.Modules`, independently of any construction of Stacks Tag 01CU; and
`Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers` proves Tag 01QE conditionally on a
`Stacks.Ample.NonvanishingBasis` in each degree. The integer tensor powers are available as
`AlgebraicGeometry.SheafOfModules.tensorPow`, and the sibling file `UnitStalk.lean` constructs
the basis for `𝒪_X`.

`AlgebraicGeometry.SheafOfModules.tensorPow` does *not* carry the Tag 01CU attribute: that
attribute is on `Stacks.SheafOfModules.TensorPower.tensorPower`, a second construction of the
same powers over the other class realising Tag 01CS. The two agree in every integer degree by
`Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow`, and on a scheme by
`Stacks.PowerFamilyBridge.tensorPowerModuleIso`.

This file joins the three. It defines ampleness over the real tensor powers, shows the wiring is
insensitive to the choice of construction, proves that every tensor power of `𝒪_X` is `𝒪_X`, and
concludes Tag 01QE **with no hypothesis beyond the scheme**.

## Main definitions

* `Stacks.Ample.IsInvertibleModule X L`: invertibility of an `𝒪_X`-module, with the sheaf
  condition on the structure presheaf of rings supplied, so that it can be used as an instance
  binder on a scheme.
* `Stacks.Ample.tensorPowModule X L n`: the `n`-th tensor power of an invertible `𝒪_X`-module,
  as an object of `X.Modules`.
* `Stacks.Ample.IsAmple X L`: **ampleness, over the actual integer tensor powers of `L`.** This
  is `IsAmpleForPowers X (tensorPowModule X L)`.

## Main results

* `Stacks.Ample.isAmple_iff_isAmpleForPowers`: ampleness agrees with `IsAmpleForPowers` for
  *any* family isomorphic degreewise to the tensor powers. This is the soundness of the wiring:
  the parameter of `IsAmpleForPowers` has been instantiated with a construction of the tensor
  powers, and no other construction would give a different predicate.
* `Stacks.Ample.isAmple_iff_isOpen`: ampleness in the literal shape of Tag 01PS, with the
  nonvanishing locus carrying its own openness witness. Unconditional.
* `AlgebraicGeometry.SheafOfModules.isInvertible_unit`: **the structure sheaf is invertible**, on
  an arbitrary site. An instance.
* `AlgebraicGeometry.SheafOfModules.tensorPowIsoUnit`: every integer tensor power of a sheaf of
  modules isomorphic to the structure sheaf is isomorphic to the structure sheaf.
* `Stacks.Ample.unitTensorPowBasis`: a nowhere-vanishing global basis of every tensor power of
  `𝒪_X`, by transporting the basis `1` of the sibling file along the above.
* `Stacks.Ample.isQuasiAffine_iff_isAmple`: **Stacks Tag 01QE.** A scheme is quasi-affine if and
  only if its structure sheaf is ample. No hypothesis.

## The hypothesis that was removed, and how

`Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers` carries `b : ∀ n : ℤ, NonvanishingBasis (pow n)`,
which is not part of Tag 01QE: there the sheaf is `𝒪_X`, its powers are `𝒪_X` again, and the
section is `1`. Discharging it took two independent pieces.

**The stalk comparison** is the sibling file `UnitStalk.lean`; its module documentation describes
it. It gives `NonvanishingBasis (unitModule X)` — the one construction that
`Stacks.Ample.NonvanishingBasis.ofIso` propagates everywhere.

**The powers of `𝒪_X` are `𝒪_X`** is this file. It is proved abstractly, for any object of any
monoidal category isomorphic to the unit: `Stacks.TensorPowers.natTensorPowIsoUnit` is a two-line
induction and `Stacks.TensorPowers.intTensorPowIsoUnit` splits on the sign. The input that makes
it apply is that `𝒪_X` is invertible, so that `tensorPow` is defined on it at all; that is
`Stacks.TensorPowers.isEquivalence_tensorLeft_of_iso_unit`, which is Mathlib's
`MonoidalCategory.leftUnitorNatIso` transported along the repository's
`isInvertible_iff_isEquivalence_tensorLeft`. The chosen inverse of the unit is then isomorphic to
the unit by its own defining isomorphism composed with a unitor.

So Tag 01QE below is the literal biconditional of the source with nothing assumed, and the
scheme-theoretic half remains the one proved in the conditional file, against Mathlib's
quasi-affine API rather than through `Proj`.

## Implementation notes

**Local monoidal instances.** `Stacks.SheafInternalHom.monoidalCategory` and `braidedCategory`
are deliberately `def`s, so they are brought in with `attribute [local instance]` inside the two
sections whose statements mention `⊗` or `𝟙_`. Everything in the `Stacks.Ample` namespace below
is stated without them — `tensorPowModule`, `IsAmple` and Tag 01QE need no monoidal instance to
elaborate, which is the point of routing through `tensorPow` rather than through `⊗` directly.
`Stacks.Ample.unitModuleIsoTensorUnit` and `Stacks.Ample.unitTensorPowIso` are the two
exceptions, and they are confined to their own section.

**`IsInvertibleModule` is an `abbrev`.** It has to be reducible: `IsInvertible` is a class, and
an instance supplied for the unfolded form must be found for the abbreviated one and the other
way round. `Stacks.Ample.isInvertibleModule_unit` is stated at `X.ringCatSheaf` rather than at
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf _`, even though the two are
  equal by `rfl`, because
instance search does not unfold `structureSheaf` and so would not match the general instance
against the spelling a consumer writes.

## References

* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)

## What is not done

Openness of the nonvanishing locus is not proved here, so ampleness is phrased with the open set
produced existentially; `isAmple_iff_isOpen` records that this is equivalent to the bundled shape
and not a weakening. Tag 01CY is available elsewhere in the repository — its openness clause as
`Stacks.NonvanishingOpen.isOpen_nonvanishingLocus` (`../NonvanishingOpen/Basic.lean`), which
`Stacks.NonvanishingOpen.isAmple_iff_nonvanishingOpen` uses to restate ampleness with the locus
bundled as an open rather than produced existentially. Ampleness is not shown to
depend only on the isomorphism class of `L`: that needs the tensor powers to be functorial in
`L`, which would be a comparison of two chosen tensor inverses and is not built here. Tag 01PT
(`L` ample if and only if `L ^⊗ n` is, for `n ≥ 1`) is not proved here, nor Tag 01Q3 or Tag 01Q1.
Tag 01Q2 — a positive twist of the structure sheaf of `Proj(S)` pulls back to an invertible ample
module along an open immersion of a quasi-compact scheme — is proved, as
`Stacks.AlgebraicGeometry.ProjAmpleTwist.exists_isAmple_pullback_twistingSheaf`; it is the
implication that runs out of `Proj`, so it supplies none of the opposite direction. The graded
ring of Tag 01CV is still absent, so nothing about the morphism to `Proj` is stated.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Limits
  Stacks.SheafOfModules.TensorSheafification TopologicalSpace
open Opposite

universe v u w

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Every natural-number tensor power of an object isomorphic to the monoidal unit is
isomorphic to the unit. -/
noncomputable def natTensorPowIsoUnit {L : C} (e : L ≅ 𝟙_ C) :
    (n : ℕ) → natTensorPow L n ≅ 𝟙_ C
  | 0 => Iso.refl _
  | n + 1 =>
      whiskerRightIso (natTensorPowIsoUnit e n) L ≪≫ whiskerLeftIso (𝟙_ C) e ≪≫ λ_ (𝟙_ C)

/-- Every integer tensor power of an object isomorphic to the monoidal unit is isomorphic to the
unit, provided the chosen inverse is too. -/
noncomputable def intTensorPowIsoUnit {L L' : C} (e : L ≅ 𝟙_ C) (e' : L' ≅ 𝟙_ C) :
    (n : ℤ) → intTensorPow L L' n ≅ 𝟙_ C
  | .ofNat k => natTensorPowIsoUnit e k
  | .negSucc k => natTensorPowIsoUnit e' (k + 1)

/-- Tensoring on the left with an object isomorphic to the unit is an equivalence: it is
isomorphic to the identity functor, by Mathlib's left unitor as a natural isomorphism. -/
theorem isEquivalence_tensorLeft_of_iso_unit {L : C} (e : L ≅ 𝟙_ C) :
    (tensorLeft L).IsEquivalence :=
  Functor.isEquivalence_of_iso ((curriedTensor C).mapIso e ≪≫ leftUnitorNatIso C).symm

end Stacks.TensorPowers

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

section Unit

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

/-- A sheaf of modules isomorphic to the structure sheaf is invertible. -/
theorem isInvertible_of_iso_unit (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    (e : L ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) : IsInvertible 𝒪 h𝒪 L :=
  (isInvertible_iff_isEquivalence_tensorLeft 𝒪 h𝒪 L).mpr
    (Stacks.TensorPowers.isEquivalence_tensorLeft_of_iso_unit e)

/-- **The structure sheaf, as a module over itself, is invertible.** -/
instance isInvertible_unit :
    IsInvertible 𝒪 h𝒪 (_root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) :=
  isInvertible_of_iso_unit 𝒪 h𝒪 _ (unitIso 𝒪 h𝒪).symm

/-- The chosen tensor inverse of a sheaf of modules isomorphic to the structure sheaf is itself
isomorphic to the structure sheaf: its defining isomorphism `L ⊗ L⁻¹ ≅ 𝒪` becomes
`𝒪 ⊗ L⁻¹ ≅ 𝒪`, and a unitor finishes. -/
noncomputable def tensorInvIsoUnit (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    [IsInvertible 𝒪 h𝒪 L] (e : L ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :
    tensorInv 𝒪 h𝒪 L ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  (λ_ (tensorInv 𝒪 h𝒪 L)).symm ≪≫ whiskerRightIso e.symm (tensorInv 𝒪 h𝒪 L) ≪≫
    tensorInvMulIso 𝒪 h𝒪 L

/-- **Every integer tensor power of a sheaf of modules isomorphic to the structure sheaf is
isomorphic to the structure sheaf.** -/
noncomputable def tensorPowIsoUnit (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    [IsInvertible 𝒪 h𝒪 L] (e : L ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)))
    (n : ℤ) : tensorPow 𝒪 h𝒪 L n ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  Stacks.TensorPowers.intTensorPowIsoUnit e (tensorInvIsoUnit 𝒪 h𝒪 L e) n

end Unit

end AlgebraicGeometry.SheafOfModules

namespace Stacks.Ample

open AlgebraicGeometry.SheafOfModules

/-- Invertibility of an `𝒪_X`-module on a scheme: the repository's `IsInvertible` with the sheaf
condition on the structure presheaf of rings supplied. Deliberately an `abbrev`, so that an
instance proved in either spelling is found in the other. -/
abbrev IsInvertibleModule (X : Scheme.{u}) (L : X.Modules) : Prop :=
  IsInvertible X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- `𝒪_X` is an invertible `𝒪_X`-module. -/
instance isInvertibleModule_unit (X : Scheme.{u}) : IsInvertibleModule X (unitModule X) :=
  isInvertible_unit X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- **The integer tensor powers of an invertible `𝒪_X`-module**, Stacks Tag 01CU, read as a
family `ℤ → X.Modules`. This is the family that `Stacks.Ample.IsAmpleForPowers` was written to
be instantiated at. -/
noncomputable def tensorPowModule (n : ℤ) : X.Modules :=
  tensorPow X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n

/-- The first tensor power is `L`. -/
noncomputable def tensorPowModuleOneIso : tensorPowModule X L 1 ≅ L :=
  tensorPowOneIso X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- The zeroth tensor power is `𝒪_X`. -/
noncomputable def tensorPowModuleZeroIso : tensorPowModule X L 0 ≅ unitModule X :=
  tensorPowZeroIso X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- **The addition law for the powers**, `L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, in the tensor-product
spelling that needs no monoidal instance to state. This is what makes
`Stacks.Ample.tensorPowModule` recognisably the family of tensor powers of `L` rather than an
arbitrary family of modules; `AlgebraicGeometry.SheafOfModules.tensorPow_natCast` records that
in nonnegative degree the identification with the iterated tensor product is definitional. -/
noncomputable def tensorPowModuleAddIso (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj
        ((tensorPowModule X L n))).obj ((tensorPowModule X L m))) ≅
      tensorPowModule X L (n + m) :=
  tensorPowAddIsoSheaf X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n m

/-- Every tensor power of an invertible `𝒪_X`-module is invertible. -/
instance isInvertibleModule_tensorPowModule (n : ℤ) :
    IsInvertibleModule X (tensorPowModule X L n) :=
  isInvertible_tensorPow X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n

/-- **Stacks Tag 01PS.** An invertible `𝒪_X`-module `L` is *ample* when `X` is quasi-compact and
every point of `X` lies in an affine nonvanishing locus of a global section of a positive tensor
power of `L`. The tensor powers are Stacks Tag 01CU's, through
`Stacks.Ample.tensorPowModule`; the affine open is produced existentially rather than by
bundling the nonvanishing locus with the openness theorem of Tag 01CY, and
`Stacks.Ample.isAmple_iff_isOpen` proves with no hypothesis that this is equivalent to the
bundled shape.

Tag 01PS is registered on `AlgebraicGeometry.Scheme.Modules.IsAmple`, the spelling of the tag
this repository's own statement of 01PS uses; `Stacks.AmpleBridge.isAmple_iff_isAmple`
proves with no hypothesis that this predicate is that same condition, so the tag is not
registered twice. -/
def IsAmple : Prop := IsAmpleForPowers X (tensorPowModule X L)

/-- **The wiring is sound.** Ampleness agrees with `Stacks.Ample.IsAmpleForPowers` applied to any
family isomorphic in each degree to the tensor powers, so instantiating the parameter of
`IsAmpleForPowers` with `Stacks.Ample.tensorPowModule` privileges no construction of the powers.
-/
theorem isAmple_iff_isAmpleForPowers (pow : ℤ → X.Modules)
    (e : ∀ n : ℤ, tensorPowModule X L n ≅ pow n) : IsAmple X L ↔ IsAmpleForPowers X pow :=
  isAmpleForPowers_congr e

/-- An invertible `𝒪_X`-module `L` is ample if and only if `Stacks.Ample.IsAmpleForPowers` holds
for the family of tensor powers `Stacks.Ample.tensorPowModule X L`. -/
theorem isAmple_iff : IsAmple X L ↔ IsAmpleForPowers X (tensorPowModule X L) := Iff.rfl

/-- **Ampleness in the literal shape of Stacks Tag 01PS**, where the nonvanishing locus carries
its own openness witness. The equivalence holds with no hypothesis. -/
theorem isAmple_iff_isOpen : IsAmple X L ↔ CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
    ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      ∃ ho : IsOpen (nonvanishingLocus (tensorPowModule X L (n : ℤ)) s),
        x ∈ nonvanishingLocus (tensorPowModule X L (n : ℤ)) s ∧ IsAffineOpen ⟨_, ho⟩ :=
  isAmpleForPowers_iff_isOpen X (tensorPowModule X L)

/-- A scheme carrying an ample invertible module is quasi-compact. -/
theorem IsAmple.compactSpace (h : IsAmple X L) : CompactSpace X := h.1

/-
`AlgebraicGeometry.Scheme.Modules.IsAmple.compactSpace`
(`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean:144`) is declared with the same statement text
and the same proof `h.1` as `Stacks.Ample.IsAmple.compactSpace` above, and is NOT a duplicate of
it. The two `IsAmple` predicates are different constants, carrying different invertibility
hypotheses, so the two lemmas are about different objects. Asking the elaborator for `rfl`
between them:

  Type mismatch
    Stacks.Ample.IsAmple.compactSpace
  has type
    ∀ (X : AlgebraicGeometry.Scheme) (L : X.Modules) [inst : Stacks.Ample.IsInvertibleModule X L],
      Stacks.Ample.IsAmple X L → CompactSpace ↥X
  but is expected to have type
    ∀ {X : AlgebraicGeometry.Scheme} {L : X.Modules}
      [inst : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf ⋯ L],
      AlgebraicGeometry.Scheme.Modules.IsAmple X L → CompactSpace ↥X

`Stacks.Ample.IsAmple` (`AmpleWire/Basic.lean:239`) asks for
`Stacks.Ample.IsInvertibleModule X L`; `AlgebraicGeometry.Scheme.Modules.IsAmple`
(`Ample/Defs.lean:118`) asks for
`AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf _ L`, and takes `X` and
`L` implicitly where this one takes them explicitly. Identifying the two lemmas therefore means
first identifying the two invertibility predicates and the two ampleness predicates built on
them — the Tag 01PS fork — which is a merge of definitions, not a deletion of a lemma.
-/

/-- Every point lies in an affine nonvanishing locus of a section of a positive tensor power. -/
theorem IsAmple.exists_affine_nonvanishingLocus (h : IsAmple X L) (x : X) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤), ∃ U : X.Opens,
      (U : Set X) = nonvanishingLocus (tensorPowModule X L (n : ℤ)) s ∧ x ∈ U ∧
        IsAffineOpen U := h.2 x

section Monoidal

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

/-- `𝒪_X` is the monoidal unit of `X.Modules`. -/
noncomputable def unitModuleIsoTensorUnit (Y : Scheme.{u}) :
    unitModule Y ≅ 𝟙_ (SheafOfModules.{u}
      (structureSheaf Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y))) :=
  (unitIso Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)).symm

/-- **Every tensor power of `𝒪_X` is `𝒪_X`**, which is what Stacks Tag 01QE uses silently when
it says that the ampleness condition for `𝒪_X` is about global sections of `𝒪_X`. -/
noncomputable def unitTensorPowIso (Y : Scheme.{u}) (n : ℤ) :
    unitModule Y ≅ tensorPowModule Y (unitModule Y) n :=
  unitModuleIsoTensorUnit Y ≪≫
    (tensorPowIsoUnit Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
      (unitModule Y) (unitModuleIsoTensorUnit Y) n).symm

end Monoidal

/-- **A nowhere-vanishing global basis of every tensor power of `𝒪_X`.** The basis `1` of
`Stacks.Ample.unitBasis`, transported along `Stacks.Ample.unitTensorPowIso`. -/
noncomputable def unitTensorPowBasis (Y : Scheme.{u}) (n : ℤ) :
    NonvanishingBasis (tensorPowModule Y (unitModule Y) n) :=
  (unitBasis Y).ofIso (unitTensorPowIso Y n)

/-- **Stacks Tag 01QE, unconditionally.** A scheme is quasi-affine if and only if its structure
sheaf is ample. The hypothesis `∀ n, NonvanishingBasis (pow n)` of
`Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers`, which is not part of the source, is discharged
by `Stacks.Ample.unitTensorPowBasis`: its two ingredients are the identification of the stalk of
`𝒪_X` as an abelian group with `𝒪_{X,x}` as a ring, in the sibling file, and the identification
of every tensor power of `𝒪_X` with `𝒪_X`, above. -/
@[stacks 01QE, ega "II 5.1.2" "more general", ega "II 6.6.13"]
theorem isQuasiAffine_iff_isAmple (Y : Scheme.{u}) :
    Y.IsQuasiAffine ↔ IsAmple Y (unitModule Y) :=
  isQuasiAffine_iff_isAmpleForPowers Y _ (unitTensorPowBasis Y)

/-- The forward half of Stacks Tag 01QE. -/
theorem isAmple_unitModule_of_isQuasiAffine (Y : Scheme.{u}) (h : Y.IsQuasiAffine) :
    IsAmple Y (unitModule Y) := (isQuasiAffine_iff_isAmple Y).mp h

/-- The converse half of Stacks Tag 01QE. -/
theorem isQuasiAffine_of_isAmple_unitModule (Y : Scheme.{u}) (h : IsAmple Y (unitModule Y)) :
    Y.IsQuasiAffine := (isQuasiAffine_iff_isAmple Y).mpr h

/-- **The structure sheaf of an affine scheme is ample.** Recorded because it witnesses that
`Stacks.Ample.IsAmple` is satisfiable: the predicate is not vacuous, and the biconditional above
is not a proof that nothing is ample. -/
@[sga "6 II 2.2.10" "Clause a)"]
theorem isAmple_unitModule_of_isAffine (Y : Scheme.{u}) [IsAffine Y] :
    IsAmple Y (unitModule Y) :=
  isAmple_unitModule_of_isQuasiAffine Y inferInstance

end Stacks.Ample

end
