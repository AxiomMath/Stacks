module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartFactor
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartLinearForm
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.IdealSheafLiftSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.PullbackTautologicalSection
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.ChartHom

/-! # The pairing of `𝒪(1)` with `𝒪(-1)` and the scalar identity of Tag 0B3V clause 3

* linearity and evaluation of `sectionMulNegOne`, `v` on the canonical section of `π^*ker q`,
* the scalar identity and the vanishing of the ratio of a kernel section along `σ`,
* functions on the base reachable from upstairs, and unit multiples of generators.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.ProjectiveBundleSplitting
open Stacks.SheafOfModules (tensorSectionsAt)
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

/-! ### The pairing of an invertible module with its inverse is linear in the first slot -/

/-- **The product of a section of `L` with a section of `L^{⊗ -1}` is linear in the first
factor.** `Stacks.SheafOfModules.Invertible.sectionMulNegOne` is the evaluation pairing
`L ⊗ L^{⊗ -1} ≅ 𝒪_X` read on a product section
(`Stacks.ProjectiveBundleConormal.invertibleEvaluation_tensorSectionsAt`), so the scalar passes
out of the product section by
`Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_smul_left` and then through the
pairing, which is a morphism of modules.

This is what turns a ratio identity between degree-one sections into an identity between
functions. It was once the only property of the pairing available;
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso` below now evaluates
`sectionMulNegOne` on a named pair as well. -/
theorem sectionMulNegOne_smul_left {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (V : X.Opens) (r : Γ(X, V)) (a : Γ(L, V))
    (t : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1), V)) :
    Stacks.SheafOfModules.Invertible.sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op V)
        (r • a) t =
      ((𝟙_ X.Modules).smul r).asHom.hom
        (Stacks.SheafOfModules.Invertible.sectionMulNegOne X.presheaf X.ringCatSheaf.2 L
          (op V) a t) := by
  refine Eq.trans (invertibleEvaluation_tensorSectionsAt L V (r • a) t).symm ?_
  refine Eq.trans (congrArg ((invertibleEvaluation L).hom.val.app (op V))
    (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_smul_left X.presheaf
      X.ringCatSheaf.2 (op V) L
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
      r a t)) ?_
  refine Eq.trans (((invertibleEvaluation L).hom.val.app (op V)).hom.map_smul r _) ?_
  exact congrArg (fun z : Γ(𝟙_ X.Modules, V) => ((𝟙_ X.Modules).smul r).asHom.hom z)
    (invertibleEvaluation_tensorSectionsAt L V a t)

/-- `Stacks.ProjectiveBundleConormal.sectionMulNegOne_smul_left` with the value of the unscaled
product named, so that the conclusion is a product of two functions on `V`.

The scalar action on the sections of the monoidal unit is multiplication in `Γ(X, V)` by
definition; naming the unscaled product is what lets the statement be written with `*` without a
type ascription, the sections of `𝟙_ X.Modules` not being read at the `Γ(X, V)` spelling that
carries the `Mul` instance. -/
theorem sectionMulNegOne_smul_left_eq_mul {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (V : X.Opens) (r g : Γ(X, V)) (a : Γ(L, V))
    (t : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1), V))
    (hg : Stacks.SheafOfModules.Invertible.sectionMulNegOne X.presheaf X.ringCatSheaf.2 L
      (op V) a t = g) :
    Stacks.SheafOfModules.Invertible.sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op V)
        (r • a) t = r * g :=
  (sectionMulNegOne_smul_left L V r a t).trans (congrArg (fun z : Γ(X, V) => r * z) hg)

/-! ### The pairing of an invertible module with its inverse, evaluated -/

section Evaluate

open Stacks.SheafOfModules.Invertible (sectionMulNegOne tensorPower tensorPowerOneIso
  tensorPowerSuccIso tensorPowerReindex tensorProductIso)
open Stacks.ProjBundleInverseBaseChange (negOneMulIso negOneMulIso_hom_tensorSectionsAt)

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
  (V : X.Opens)

/-- **The two crossings between the monoidal tensor product of sheaves of modules and the tensor
product sheaf of [Stacks, Tag 01CA] are the same isomorphism.**
`Stacks.SheafOfModules.tensorObjIso` is built from the sheafification counit on each factor
followed by the monoidality comparison of sheafification;
`AlgebraicGeometry.SheafOfModules.tensorIso` is the same thing assembled as a component of
`Stacks.SheafInternalHom.tensorLeftIso`. The two localized monoidal structures they are stated
over differ only in their unit comparison — `Stacks.SheafOfModules.monoidalCategory` takes
`Stacks.SheafOfModules.sheafifyUnitIso` where `Stacks.SheafInternalHom.monoidalCategory` takes
`CategoryTheory.Iso.refl` — so the tensor products, and these crossings, agree.

**The two `Iso` structures are not definitionally equal and their `inv` fields are not either**
(`rfl` on either is rejected, and on the bare `Iso`s the kernel spends the whole
heartbeat budget before rejecting). Their `hom` fields *are*, so
`CategoryTheory.Iso.ext` reduces the comparison to a `rfl` that costs nothing. -/
theorem tensorObjIso_eq_tensorIso (A B : X.Modules) :
    Stacks.SheafOfModules.tensorObjIso X.presheaf X.ringCatSheaf.2 A B =
      AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf X.ringCatSheaf.2 A B := by
  apply Iso.ext
  rfl

/-- **The two spellings of "the monoidal unit of sheaves of modules is the structure sheaf" are
the same isomorphism.** Both are the sheafification counit at
`SheafOfModules.unit`; as with `Stacks.ProjectiveBundleConormal.tensorObjIso_eq_tensorIso` only
the `hom` fields are definitionally equal, so `CategoryTheory.Iso.ext` is what compares them. -/
theorem sheafifyUnitIso_eq_unitIso :
    Stacks.SheafOfModules.sheafifyUnitIso X.presheaf X.ringCatSheaf.2 =
      AlgebraicGeometry.SheafOfModules.unitIso X.presheaf X.ringCatSheaf.2 := by
  apply Iso.ext
  rfl

/-- **The unit crossing of `Stacks.ProjBundleInverseBaseChange.negOneMulIso` is undone by the
one `Stacks.SheafOfModules.sheafifyUnitIso` performs**, read on a section: the two are the same
isomorphism (`Stacks.ProjectiveBundleConormal.sheafifyUnitIso_eq_unitIso`) and an isomorphism
cancels its own inverse. -/
theorem sheafifyUnitIso_hom_unitIso_inv
    (z : (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.presheaf X.ringCatSheaf.2)).val.obj (op V)) :
    (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf X.ringCatSheaf.2).hom.val.app (op V)
        ((AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
          X.ringCatSheaf.2).inv.val.app (op V) z) = z :=
  Eq.trans
    (congrArg (fun φ => φ.val.app (op V)
        ((AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
          X.ringCatSheaf.2).inv.val.app (op V) z))
      (congrArg Iso.hom (sheafifyUnitIso_eq_unitIso (X := X))))
    (Stacks.SheafOfModules.hom_val_app_inv_val_app
      (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf X.ringCatSheaf.2) (op V) z)

/-- **The product of a section of `L` with a section of `L^{⊗ -1}` is the successor comparison of
[Stacks, Tag 01CU] on the product section, with the factors exchanged.** This *evaluates*
`Stacks.SheafOfModules.Invertible.sectionMulNegOne` on a named pair, which the development did
not do: the pairing was characterised only by linearity
(`Stacks.ProjectiveBundleConormal.sectionMulNegOne_smul_left`) and by the identification with
Tag 01CU's coherent multiplication
(`Stacks.SheafOfModules.Invertible.sectionMulNegOne_eq_coherent`).

`Stacks.SheafOfModules.Invertible.sectionMulNegOne` is
`Stacks.SheafOfModules.Invertible.tensorPowerMulIsoNegOne` applied to the product section, and
that isomorphism is a four-fold composite which splits on a section by `rfl`; the braiding is
`Stacks.SheafOfModules.tensorSections_braidingAt`, the functorial step is
`Stacks.SheafOfModules.tensorSections_tensorProductIsoAt`, and the identification `L^{⊗ 1} ≅ L`
cancels against its inverse. -/
theorem sectionMulNegOne_eq_tensorPowerSucc (b : Γ(L, V))
    (t : Γ(tensorPower X.presheaf X.ringCatSheaf.2 L (-1), V)) :
    sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op V) b t =
      (tensorPowerReindex X.presheaf X.ringCatSheaf.2 L
          (show (-1 : ℤ) + 1 = 0 by omega)).hom.val.app (op V)
        ((tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L (-1)).hom.val.app (op V)
          (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V)
            (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L t b)) := by
  refine congrArg (fun z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).obj
          (L))).val.obj (op V) =>
      (tensorPowerReindex X.presheaf X.ringCatSheaf.2 L
          (show (-1 : ℤ) + 1 = 0 by omega)).hom.val.app (op V)
        ((tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L (-1)).hom.val.app (op V) z)) ?_
  refine Eq.trans (congrArg
    (fun z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 L 1))).val.obj (op V) =>
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (Iso.refl (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)))
          (tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L)).hom.val.app (op V) z)
    (Stacks.SheafOfModules.tensorSections_braidingAt X.presheaf X.ringCatSheaf.2 (op V)
      (tensorPower X.presheaf X.ringCatSheaf.2 L 1)
      (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
      ((tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L).inv.val.app (op V) b) t)) ?_
  refine Eq.trans (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.presheaf
    X.ringCatSheaf.2 (op V)
    (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
    (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
    (tensorPower X.presheaf X.ringCatSheaf.2 L 1) L
    (Iso.refl (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)))
    (tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L) t
    ((tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L).inv.val.app (op V) b)) ?_
  exact congrArg
    (fun z : L.val.obj (op V) =>
      tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V)
        (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L t z)
    (Stacks.SheafOfModules.hom_val_app_inv_val_app
      (tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L) (op V) b)

/-- `Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_tensorPowerSucc` read against the right
trivialisation `Stacks.ProjBundleInverseBaseChange.negOneMulIso`, whose own section formula
`Stacks.ProjBundleInverseBaseChange.negOneMulIso_hom_tensorSectionsAt` stops at the same
successor comparison. The crossing of the two units is
`Stacks.ProjectiveBundleConormal.sheafifyUnitIso_hom_unitIso_inv`; the identification of the
reindexed zeroth power with the monoidal unit is `eqToHom` of an equality of definitionally
equal objects, hence the identity. -/
theorem sectionMulNegOne_eq_negOneMulIso_tensorIso (b : Γ(L, V))
    (t : Γ(tensorPower X.presheaf X.ringCatSheaf.2 L (-1), V)) :
    sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op V) b t =
      (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf X.ringCatSheaf.2).hom.val.app (op V)
        ((negOneMulIso X.presheaf X.ringCatSheaf.2 L).hom.val.app (op V)
          ((AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf X.ringCatSheaf.2
              (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V)
              (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L t b))) := by
  refine Eq.trans (sectionMulNegOne_eq_tensorPowerSucc L V b t) ?_
  refine Eq.trans ?_ (congrArg
    (fun z => (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf X.ringCatSheaf.2).hom.val.app
      (op V) z)
    (negOneMulIso_hom_tensorSectionsAt X.presheaf X.ringCatSheaf.2 L (op V) t b)).symm
  exact (sheafifyUnitIso_hom_unitIso_inv V _).symm

/-- **The product of a section of `L` with a section of `L^{⊗ -1}` is the left-hand side of the
hypothesis `hup` of `Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app`.**

This is what lets a pairing produced for `hup` be *used* as a value of
`Stacks.SheafOfModules.Invertible.sectionMulNegOne`, which is the form in which the source half
of [Stacks, Tag 0B3V] clause 3 pins its section of `ℐ(σ)`
(`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt`). It is
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso_tensorIso` with the crossing
replaced by the one `hup` is stated with,
`Stacks.ProjectiveBundleConormal.tensorObjIso_eq_tensorIso`. -/
theorem sectionMulNegOne_eq_negOneMulIso (b : Γ(L, V))
    (t : Γ(tensorPower X.presheaf X.ringCatSheaf.2 L (-1), V)) :
    sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op V) b t =
      (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf X.ringCatSheaf.2).hom.val.app (op V)
        ((negOneMulIso X.presheaf X.ringCatSheaf.2 L).hom.val.app (op V)
          ((Stacks.SheafOfModules.tensorObjIso X.presheaf X.ringCatSheaf.2
              (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V)
              (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L t b))) :=
  Eq.trans (sectionMulNegOne_eq_negOneMulIso_tensorIso L V b t)
    (congrArg
      (fun z => (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf X.ringCatSheaf.2).hom.val.app
          (op V)
        ((negOneMulIso X.presheaf X.ringCatSheaf.2 L).hom.val.app (op V) z))
      (PresheafOfModules.hom_congr_apply
        (congrArg SheafOfModules.Hom.val
          (congrArg Iso.inv
            (tensorObjIso_eq_tensorIso (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L)))
        (op V)
        (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V)
          (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L t b))).symm

end Evaluate

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)

/-! ### `v` on the canonical section of `π^*ker q` -/

/-- **`v` on the canonical section of `π^*ker q` attached to `k` is the degree-one tautological
section of `ι k`.** The map `v` of [Stacks, Tag 0B3V] clause 3 is `π^*(ι)` followed by the
tautological map, so on the unit of `π^* ⊣ π_*` at `k` the first factor is the unit at `ι k` by
`AlgebraicGeometry.Scheme.Modules.unit_app_val_app_naturality`, and what is left is
`Stacks.ProjectiveBundleConormal.tautologicalSectionOver` at `ι k`.

This is the identification that lets the ratio identity of the chart — which is about the
degree-one sections attached to elements of `Γ(ℰ, W)` — speak about `v`, whose arguments are
sections of `π^*ker q`. -/
theorem kernelTautologicalMap_unitSection (W : X.Opens) (k : Γ(kernel Q.q, W)) :
    (kernelTautologicalMap E Q).val.app (op ((bundle E).toBase ⁻¹ᵁ W))
        (unitSection (bundle E).toBase (kernel Q.q) W k) =
      tautologicalSectionOver E W ((kernel.ι Q.q).val.app (op W) k) :=
  (SheafOfModules.comp_val_app_apply
      ((Scheme.Modules.pullback (bundle E).toBase).map (kernel.ι Q.q))
      (tautologicalMap E (symPieces E)) (op ((bundle E).toBase ⁻¹ᵁ W))
      (unitSection (bundle E).toBase (kernel Q.q) W k)).trans
    (congrArg ((tautologicalMap E (symPieces E)).val.app
        (op ((bundle E).toBase ⁻¹ᵁ W)))
      (Scheme.Modules.unit_app_val_app_naturality (bundle E).toBase (kernel.ι Q.q) W k))

/-- `Stacks.ProjectiveBundleConormal.kernelTautologicalMap_unitSection` restricted to an open `V`
of `𝐏(ℰ)` below `π⁻¹W`, which is where the chart computation of clause 3 reads it: `𝒪(-1)` has no
nonzero section on the whole of `π⁻¹W`, so the product section has to be taken on a chart, and
then so does this factor. Restriction passes through `v` by naturality. -/
theorem kernelTautologicalMap_res_unitSection (W : X.Opens)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (k : Γ(kernel Q.q, W)) :
    (kernelTautologicalMap E Q).val.app (op V)
        (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
          (homOfLE hV).op (unitSection (bundle E).toBase (kernel Q.q) W k)) =
      (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
        (tautologicalSectionOver E W ((kernel.ι Q.q).val.app (op W) k)) :=
  (PresheafOfModules.naturality_apply (kernelTautologicalMap E Q).val (homOfLE hV).op
        (unitSection (bundle E).toBase (kernel Q.q) W k)).trans
    (congrArg ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op)
      (kernelTautologicalMap_unitSection E Q W k))

/-! ### The scalar identity -/

/-- **The scalar identity for the untwisted tautological map on a product section.** Let `V` be an
open of `𝐏(ℰ)`, `z` a section of `π^*ker q` and `w` a section of `𝒪(-1)` there, and suppose the
degree-one section `v(z)` is `g` times a reference section `b` of `𝒪(1)`. Then `ṽ` on the product
section determined by `z` and `w` is `g` times the product of `b` with `w`.

This is the step clause 3's chart computation turns on. By
`Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_tensorSectionsAt` the left-hand side
is the multiplication of `v(z)` with `w`, and
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_smul_left_eq_mul` factors the scalar out of it:
both sides are sections of the structure sheaf of `𝐏(ℰ)`, and no sheaf-of-modules comparison is
involved.

The reference section `b` is an arbitrary section of `𝒪(1)` and not a value of `v`: the reference
the chart supplies is the degree-one section of the frame section `s`, which does not lie in
`ker q`. -/
theorem kernelTautologicalMapTwisted_tensorSectionsAt_eq_mul
    (V : (bundle E).scheme.Opens)
    (z : Γ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q), V))
    (w : Γ(inverseTautologicalTwist E, V))
    (b : Γ(tautologicalTwist E (symPieces E), V))
    (g g₀ : Γ((bundle E).scheme, V))
    (hz : (kernelTautologicalMap E Q).val.app (op V) z =
      ((tautologicalTwist E (symPieces E)).smul g).asHom.hom b)
    (hg₀ : Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
        (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E)) (op V) b w = g₀) :
    (kernelTautologicalMapTwisted E Q).val.app (op V)
        (tensorSectionsAt (bundle E).scheme.presheaf (bundle E).scheme.ringCatSheaf.2 (op V)
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E) z w) =
      g * g₀ :=
  (kernelTautologicalMapTwisted_tensorSectionsAt E Q V z w).trans
    ((congrArg (fun a : Γ(tautologicalTwist E (symPieces E), V) =>
          Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
            (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E)) (op V) a w)
        hz).trans
      (sectionMulNegOne_smul_left_eq_mul (tautologicalTwist E (symPieces E)) V g g₀ b w hg₀))

/-! ### The ratio of a kernel section vanishes on the section -/

variable {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)

include hσ e hqe in
/-- **The ratio of a kernel section against a frame section is killed by `σ`.** Let `W` carry a
frame `eL` for `𝓛` and a section `s` of `ℰ` at which the chart's linear form `p = eL ∘ q` takes
the value `1`, let `V` be an open of `𝐏(ℰ)` with `V ≤ π⁻¹W` and `W ≤ σ⁻¹V`, and let `k` be a
section of `ker q` over `W`. If the degree-one section of `ι k` is, on `V`, the function `g` times
the degree-one section of `s`, then `σ` pulls `g` back to `0` on `W`.

This is the computation clause 3 of [Stacks, Tag 0B3V] turns on, read upstairs on `𝐏(ℰ)` instead
of through the chart of `Proj`: `g` is the affine coordinate `ι k / ι s` of the affine bundle
`𝐀(ker p)`, and the statement says the point named by `σ|_W` is the origin — the same content as
`Stacks.ProjectiveBundleConormal.chartHomEquiv_chartSection_mk_ι` at an element of `ker p`, but
in the vocabulary of the twist rather than of `HomogeneousLocalization`.

Three known facts and no new mathematics. Pulling back along `σ` is semilinear
(`AlgebraicGeometry.Scheme.Modules.pullbackSection_smul`), so the function becomes `σ`'s `appLE`
of it; `Stacks.ProjectiveBundleConormal.hom_pullbackSection_tautologicalMap` computes the pullback
of a degree-one section through `e` as `q` of the element it is attached to; and `q (ι k) = 0`
because `ι` is the kernel inclusion. What is left is the frame: `eL` carries `q s` to `1`, so it
cancels the generator off both sides. -/
theorem appLE_eq_zero_of_tautologicalSectionOver_eq_smul
    {W : X.Opens} (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (hWV : W ≤ σ ⁻¹ᵁ V)
    (k : Γ(kernel Q.q, W)) (g : Γ((bundle E).scheme, V))
    (hg : (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
          (tautologicalSectionOver E W ((kernel.ι Q.q).val.app (op W) k)) =
        ((tautologicalTwist E (symPieces E)).smul g).asHom.hom
          ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
            (tautologicalSectionOver E W s))) :
    σ.appLE V W hWV g = 0 := by
  have hres : ∀ m : Γ(E, W),
      Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E)) V W hWV
          ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
            (tautologicalSectionOver E W m)) =
        Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
          ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
          (tautologicalSectionOver E W m) := fun m =>
    Scheme.Modules.pullbackSection_res σ (tautologicalTwist E (symPieces E)) hV W hWV
      (tautologicalSectionOver E W m)
  have hA : Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
        ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
        (tautologicalSectionOver E W ((kernel.ι Q.q).val.app (op W) k)) =
      (((Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E))).smul
          (σ.appLE V W hWV g)).asHom.hom
        (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
          ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
          (tautologicalSectionOver E W s)) :=
    (hres ((kernel.ι Q.q).val.app (op W) k)).symm.trans
      (((congrArg (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
              V W hWV) hg).trans
          (Scheme.Modules.pullbackSection_smul σ (tautologicalTwist E (symPieces E)) V W hWV g
            ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
              (tautologicalSectionOver E W s)))).trans
        (congrArg (fun y : Γ((Scheme.Modules.pullback σ).obj
              (tautologicalTwist E (symPieces E)), W) =>
            (((Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E))).smul
              (σ.appLE V W hWV g)).asHom.hom y)
          (hres s)))
  have hq0 : Q.q.val.app (op W) ((kernel.ι Q.q).val.app (op W) k) = 0 :=
    (SheafOfModules.comp_val_app_apply (kernel.ι Q.q) Q.q (op W) k).symm.trans
      (congrArg (fun φ : kernel Q.q ⟶ Q.L => φ.val.app (op W) k) (kernel.condition Q.q))
  have hB : (0 : Γ(Q.L, W)) =
      (Q.L.smul (σ.appLE V W hWV g)).asHom.hom (Q.q.val.app (op W) s) :=
    hq0.symm.trans
      ((hom_pullbackSection_tautologicalMap E Q hσ e hqe W
            ((kernel.ι Q.q).val.app (op W) k)).symm.trans
        ((congrArg (e.hom.val.app (op W)) hA).trans
          ((((e.hom.val.app (op W))).hom.map_smul (σ.appLE V W hWV g) _).trans
            (congrArg (fun y : Γ(Q.L, W) => (Q.L.smul (σ.appLE V W hWV g)).asHom.hom y)
              (hom_pullbackSection_tautologicalMap E Q hσ e hqe W s)))))
  refine Eq.symm (Eq.trans (map_zero eL).symm ?_)
  refine Eq.trans (congrArg eL hB) ?_
  refine Eq.trans (eL.map_smul (σ.appLE V W hWV g) (Q.q.val.app (op W) s)) ?_
  refine Eq.trans (congrArg (fun y : Γ(X, W) => σ.appLE V W hWV g • y) hs) ?_
  simp

include hσ e hqe in
/-- **`σ` kills the value of the untwisted tautological map on a product section built from a
kernel section.** The two halves above, multiplied: the value is the ratio times the reference
product by
`Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_tensorSectionsAt_eq_mul`, `σ`'s
`appLE` is a ring map, and the ratio goes to `0` by
`Stacks.ProjectiveBundleConormal.appLE_eq_zero_of_tautologicalSectionOver_eq_smul`.

So the product `v(π^*k) · w` of [Stacks, Tag 0B3V] clause 3 — the section of `𝒪_{𝐏(ℰ)}` that
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_val_app_tensorSectionsAt` asks for a
preimage of in `ℐ(σ)` — vanishes on the section, which is exactly the condition for such a
preimage to exist.

The identification of `v` on the canonical section is
`Stacks.ProjectiveBundleConormal.kernelTautologicalMap_res_unitSection`; it is passed in as `hzk`
rather than used here, so that the statement applies to any `z` representing that section. -/
theorem appLE_kernelTautologicalMapTwisted_tensorSectionsAt_eq_zero
    {W : X.Opens} (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (hWV : W ≤ σ ⁻¹ᵁ V)
    (k : Γ(kernel Q.q, W))
    (z : Γ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q), V))
    (w : Γ(inverseTautologicalTwist E, V)) (g g₀ : Γ((bundle E).scheme, V))
    (hzk : (kernelTautologicalMap E Q).val.app (op V) z =
      (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
        (tautologicalSectionOver E W ((kernel.ι Q.q).val.app (op W) k)))
    (hz : (kernelTautologicalMap E Q).val.app (op V) z =
      ((tautologicalTwist E (symPieces E)).smul g).asHom.hom
        ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
          (tautologicalSectionOver E W s)))
    (hg₀ : Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
        (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E)) (op V)
        ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
          (tautologicalSectionOver E W s)) w = g₀) :
    σ.appLE V W hWV
        ((kernelTautologicalMapTwisted E Q).val.app (op V)
          (tensorSectionsAt (bundle E).scheme.presheaf (bundle E).scheme.ringCatSheaf.2 (op V)
            ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
            (inverseTautologicalTwist E) z w)) = 0 := by
  refine Eq.trans (congrArg (σ.appLE V W hWV)
    (kernelTautologicalMapTwisted_tensorSectionsAt_eq_mul E Q V z w
      ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
        (tautologicalSectionOver E W s)) g g₀ hz hg₀)) ?_
  refine Eq.trans ((σ.appLE V W hWV).hom.map_mul g g₀) ?_
  refine Eq.trans (congrArg (fun y : Γ(X, W) => y * σ.appLE V W hWV g₀)
    (appLE_eq_zero_of_tautologicalSectionOver_eq_smul E Q hσ e hqe eL s hs V hV hWV k g
      (hzk.symm.trans hz))) ?_
  exact zero_mul _

/-! ### The functions on the base reachable from upstairs -/

include hσ in
/-- **A section of `π` splits `AlgebraicGeometry.Scheme.Hom.appLE` on functions.** For an open `V`
of `𝐏(ℰ)` with `V ≤ π⁻¹W` and `W ≤ σ⁻¹V`, pulling a function on `W` up to `V` along `π` and back
down along `σ` returns it.

The whole content is `σ ≫ π = 𝟙 X`: the composite of the two restriction maps is
`AlgebraicGeometry.Scheme.Hom.appLE` of `σ ≫ π` by
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`, and `appLE` of the identity is restriction along
`W ≤ W`, which is the identity. The inequality carried by `appLE` depends on the morphism, so the
substitution of `hσ` happens on a morphism quantified over rather than by rewriting.

This is the one place the section hypothesis enters the reachability statement
`Stacks.ProjectiveBundleConormal.exists_hom_pullbackSection_tautologicalChart_eq`: it is what
makes *every* function on `W` the restriction along `σ` of a function upstairs, and hence every
scalar multiple of a pulled-back section again a pulled-back section. -/
theorem appLE_appLE_toBase (W : X.Opens) (V : (bundle E).scheme.Opens)
    (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (hWV : W ≤ σ ⁻¹ᵁ V) (a : Γ(X, W)) :
    σ.appLE V W hWV ((bundle E).toBase.appLE W V hV a) = a := by
  have key : ∀ k : X ⟶ X, k = 𝟙 X → ∀ hk : W ≤ k ⁻¹ᵁ W, k.appLE W W hk a = a := by
    rintro k rfl hk
    have h1 : (𝟙 X : X ⟶ X).appLE W W hk a
        = X.presheaf.map (homOfLE (le_rfl : W ≤ W)).op a := rfl
    refine h1.trans ?_
    refine Eq.trans (congrArg (fun φ : op W ⟶ op W => X.presheaf.map φ a)
      (Subsingleton.elim (homOfLE (le_rfl : W ≤ W)).op (𝟙 (op W)))) ?_
    exact congrArg (fun φ : Γ(X, W) ⟶ Γ(X, W) => φ a) (X.presheaf.map_id (op W))
  refine Eq.trans (CommRingCat.comp_apply ((bundle E).toBase.appLE W V hV)
    (σ.appLE V W hWV) a).symm ?_
  refine Eq.trans (congrArg (fun φ : Γ(X, W) ⟶ Γ(X, W) => φ a)
    (Scheme.Hom.appLE_comp_appLE σ (bundle E).toBase W V W hV hWV)) ?_
  exact key (σ ≫ (bundle E).toBase) hσ _

include hσ in
/-- **A scalar multiple of a pulled-back section is again a pulled-back section.** Multiplying a
section of a module over `V` by the function `π^♯a` and pulling the result back along `σ` is
multiplying the pullback by `a`.

Pulling back is semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`
(`AlgebraicGeometry.Scheme.Modules.pullbackSection_smul`), and
`Stacks.ProjectiveBundleConormal.appLE_appLE_toBase` says `σ`'s `appLE` returns `a`. The module is
a variable; the consumer applies it at `𝒪(1)`. -/
theorem pullbackSection_smul_appLE_toBase (M : (bundle E).scheme.Modules) (W : X.Opens)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (hWV : W ≤ σ ⁻¹ᵁ V)
    (a : Γ(X, W)) (b : Γ(M, V)) :
    Scheme.Modules.pullbackSection σ M V W hWV
        ((M.smul ((bundle E).toBase.appLE W V hV a)).asHom.hom b) =
      (((Scheme.Modules.pullback σ).obj M).smul a).asHom.hom
        (Scheme.Modules.pullbackSection σ M V W hWV b) :=
  (Scheme.Modules.pullbackSection_smul σ M V W hWV
      ((bundle E).toBase.appLE W V hV a) b).trans
    (congrArg (fun r : Γ(X, W) =>
        (((Scheme.Modules.pullback σ).obj M).smul r).asHom.hom
          (Scheme.Modules.pullbackSection σ M V W hWV b))
      (appLE_appLE_toBase E hσ W V hV hWV a))

/-! ### A unit multiple of a generator is a generator -/

section Generator

open Stacks.SheafOfModules.TensorStalkRingedSpace IsLocalRing TopologicalSpace

/-- **A unit multiple of a section generating at every point of an open generates there too.**
If the germ of `t` at every point of `V ≤ U` escapes `𝔪_y M_y` and `r` is a unit on `V`, then the
germ of `r · t|_V` escapes it as well: germs do not see the restriction
(`TopCat.Presheaf.germ_res_apply`), the germ of a scalar multiple is the multiple of the germs
(`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul`), a ring map carries a unit
to a unit, and `Stacks.SheafOfModules.smul_notMem_maximalIdeal_smul_top_iff` is the local-algebra
statement that a unit multiple escapes `𝔪 M` exactly when the vector does.

Nothing is assumed of `M`: not invertibility, not quasi-coherence. The section being scaled is a
variable `b` named by the equation `hb`, in the idiom of this module's implementation notes.

This is the germ condition the hypothesis `hup` of
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` needs of the witness
of `Stacks.ProjectiveBundleConormal.hom_pullbackSection_smul_tautologicalSectionOver`, the unit
there being `π^♯(eL c)`. -/
theorem notMem_maximalIdeal_smul_top_smul_of_isUnit {Y : AlgebraicGeometry.RingedSpace.{u, u}}
    [∀ x : Y.carrier, IsLocalRing (ringStalk Y x)]
    (M : _root_.SheafOfModules.{u} (structureSheafRing Y))
    {U V : Opens Y.carrier} (hVU : V ≤ U) (t : M.val.obj (op U))
    (ht : ∀ (y : Y.carrier) (hy : y ∈ V), grpGerm Y M.val y U (hVU hy) t ∉
      maximalIdeal (ringStalk Y y) • (⊤ : Submodule (ringStalk Y y) (grpStalk Y M.val y)))
    (r : Y.presheaf.obj (op V)) (hr : IsUnit r)
    (b : M.val.obj (op V)) (hb : b = r • M.val.restrictₛₗ (homOfLE hVU).op t)
    (y : Y.carrier) (hy : y ∈ V) :
    grpGerm Y M.val y V hy b ∉
      maximalIdeal (ringStalk Y y) • (⊤ : Submodule (ringStalk Y y) (grpStalk Y M.val y)) := by
  have hres : grpGerm Y M.val y V hy (M.val.restrictₛₗ (homOfLE hVU).op t)
      = grpGerm Y M.val y U (hVU hy) t :=
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.val.presheaf (homOfLE hVU) y hy t
  have hgr : grpGerm Y M.val y V hy b
      = ringGerm Y y V hy r • grpGerm Y M.val y U (hVU hy) t :=
    (congrArg (grpGerm Y M.val y V hy) hb).trans
      ((stalkModule_germ_smul Y M.val y V hy r (M.val.restrictₛₗ (homOfLE hVU).op t)).trans
        (congrArg (fun z => ringGerm Y y V hy r • z) hres))
  refine fun hmem => (Stacks.SheafOfModules.smul_notMem_maximalIdeal_smul_top_iff
    (ringGerm Y y V hy r) (grpGerm Y M.val y U (hVU hy) t)).mpr
      ⟨IsUnit.map (ringGerm Y y V hy) hr, ht y hy⟩ ?_
  exact hgr ▸ hmem

/-- **A frame sends a section pairing to the unit section to a unit.** Let `ψ : ℳ ⊗ 𝒩 ≅ 𝒪_Y` be a
trivialisation, let `c` be a section of `ℳ` over `V` pairing with some section of `𝒩` to the unit
section, and let `eM` be any identification of `Γ(ℳ, V)` with `Γ(Y, V)`. Then `eM c` is a unit.

Pairing to the unit section makes `d ↦ d · c` a bijection
(`Stacks.SheafOfModules.bijective_smul_of_tensorPairing_eq_unitSection` at `V ≤ V`, the
restriction along `le_rfl` removed by `Stacks.ProjectiveBundleConormal.val_map_le_refl`), and a
generator has unit image under any frame
(`Stacks.SheafOfModules.Invertible.isUnit_linearEquiv_of_surjective_smul`).

This is how the chart computation of [Stacks, Tag 0B3V] clause 3 learns that the scalar `eL c`
determined by its downstairs pairing is invertible, which is what makes the witness of
`Stacks.ProjectiveBundleConormal.hom_pullbackSection_smul_tautologicalSectionOver` generate
`𝒪(1)` on the chart, as the upstairs hypothesis `hup` requires of it. -/
theorem isUnit_linearEquiv_of_tensorPairing_eq_unitSection {Y : Scheme.{u}} (M N : Y.Modules)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj (M)).obj (N)) ≅
      _root_.SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
    (V : Y.Opens) (eM : Γ(M, V) ≃ₗ[Γ(Y, V)] Γ(Y, V)) (c : Γ(M, V)) (w : N.val.obj (op V))
    (hc : Stacks.SheafOfModules.tensorPairing ψ V c w =
      Stacks.SheafOfModules.unitSection Y.toRingedSpace V) :
    IsUnit (eM c) := by
  refine Stacks.SheafOfModules.Invertible.isUnit_linearEquiv_of_surjective_smul eM fun m => ?_
  obtain ⟨d, hd⟩ := (Stacks.SheafOfModules.bijective_smul_of_tensorPairing_eq_unitSection
    ψ V c w hc V le_rfl).surjective m
  exact ⟨d, Eq.trans (congrArg (fun z : Γ(M, V) => d • z) (val_map_le_refl M V c)).symm hd⟩

end Generator

end Stacks.ProjectiveBundleConormal

end
