module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistModuleMultiplication
public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Basic
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Locality
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Absolute

/-!
# Twists on a `Proj` covered by the standard opens of degree one

Let `S` be a graded ring, `M` a graded `S`-module and `X = Proj S`.  Stacks Tag 01MT assumes
that `X` is *covered by the standard opens `D₊(f)` with `f ∈ S₁`* — generation of `S` by `S₁`
over `S₀` is offered only as an example of that hypothesis — and concludes that every twist
`𝒪_X(n)` is invertible and that the three canonical maps of the section are isomorphisms:

* Equation 01MO, `𝒪_X(n) ⊗ 𝒪_X(m) ⟶ 𝒪_X(n + m)`;
* Equation 03GJ, `𝒪_X(n) ⊗ ℱ(m) ⟶ ℱ(n + m)` for an arbitrary `𝒪_X`-module `ℱ`;
* Equation 01MQ, `M̃(n) = M̃ ⊗ 𝒪_X(n) ⟶ M(n)̃`.

It then records the two identifications those isomorphisms induce,
`𝒪_X(1)^{⊗ n} ≅ 𝒪_X(n)` and `M̃ ⊗_{𝒪_X} 𝒪_X(n) = M̃(n) ≅ M(n)̃`.

This file proves all of that from the source's own hypothesis.  What it does not do is the
remainder of the tag, the two simplified global-sections maps; see the section below.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.ratioLocus_one_eq_top`: the degree-one
  covering hypothesis puts the whole of `Proj S` inside Tag 01MU's locus `W₁`.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf`: every
  `𝒪_X(n)` is invertible.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isIso_twistMultiplicationMap`: Equation
  01MO is an isomorphism, in all integer degrees.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isIso_twistSheafMultiplicationMap`:
  Equation 03GJ is an isomorphism, for every sheaf of `𝒪_X`-modules.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isIso_moduleTwistMap`: Equation 01MQ is an
  isomorphism, for every graded `S`-module; `moduleTwistIso` is the isomorphism it induces.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.nonempty_tensorPowModule_iso_twistingSheaf`:
  the identification `𝒪_X(1)^{⊗ n} ≅ 𝒪_X(n)` induced by Equation 01MO, for every `n : ℤ`.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isIso_moduleTwistMap_of_ratioLocus_eq_top`
  is the global form of Tag 01MU's comparison assertion on which the previous result rests: as
  soon as `W_d = Proj S`, the comparison `M̃ ⊗ 𝒪(dn) ⟶ M(dn)̃` is an isomorphism on all of
  `Proj S`.

## The hypothesis, and why it is not generation in degree one

The library already had the three global statements under the *stronger* hypothesis
`Algebra.adjoin (𝒮 0) (𝒮 1) = ⊤`
(`Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_adjoin_degree_one`,
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin`).  That
hypothesis implies this one — it is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.iSup_basicOpen_degreeOne_eq_top` — and not
conversely, so those statements are strictly weaker than the source's and are not what Tag 01MT
asserts.  The results here are stated at the source's own printed hypothesis,
`DegreeOneCover`, which is what lets them carry the tag.

The route is uniform: `DegreeOneCover` says the standard opens of the degree-one elements cover,
hence Tag 01MU's ratio locus `W₁` is everything
(`Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_iSup_basicOpen_eq_top`), and at
`d = 1` every integer is a multiple of `d`, so the `W_d`-local results of Tag 01MU apply in
every degree with no divisibility side condition.

## What this file does not cover of Tag 01MT

Tag 01MT has one further clause, which is **not** formalized here and which no declaration below
claims:

* the two simplified global-sections maps that the tag's statement ends with, Equation 0AG3
  `M_n ⟶ Γ(X, M̃(n))` and Equation 0AG4 `M ⟶ ⨁ n, Γ(X, M̃(n))`, obtained by transporting
  Equations 0AG2 and 01MR along `moduleTwistIso`.  Equation 0AG4 is a map of *graded*
  `S`-modules, so stating it needs the `S`-module structure on `⨁ n, Γ(X, M̃(n))` and the
  compatibility of that action with the grading as well; none of that is done here.
  `moduleTwistIso` is the transport those two maps would be taken along, so this file supplies
  their input and stops there.

One point of precision about the clause that *is* claimed for the tensor powers.
`nonempty_tensorPowModule_iso_twistingSheaf` asserts that an isomorphism
`𝒪_X(1)^{⊗ n} ≅ 𝒪_X(n)` exists, and the witness is built out of Equation 01MO: in degree one it
*is* Equation 01MO at `(n, 1)` (`twistMulIso`), and the general degree is reached by iterating
that step upwards and cancelling the autoequivalence `twistRight` downwards.  No single
canonical comparison morphism `𝒪_X(1)^{⊗ n} ⟶ 𝒪_X(n)` is named and then shown invertible,
because the tensor power of Tag 01CU is an iterate of an autoequivalence rather than a literal
`n`-fold product; the statement is therefore `Nonempty`-valued.

## References

* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.GradedLocalization
open Stacks.GradedModule (shiftedGrading)

namespace Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover

universe u w t

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Tag 01MT's hypothesis:** `Proj S` is covered by the standard opens `D₊(f)` of the
homogeneous elements `f` of degree one.

This is weaker than generation of `S` by `S₁` over `S₀`, which the source offers as an example
of it; see the module docstring. -/
public abbrev DegreeOneCover : Prop :=
  (⨆ f : 𝒮 1, AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S)) = ⊤

/-- **Under Tag 01MT's hypothesis, Tag 01MU's ratio locus `W₁` is all of `Proj S`.**

A degree-one element `f` gives the pair `(f, 1)` with `deg f = deg 1 + 1`, so `D₊(f) ⊆ W₁`; this
is `Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_iSup_basicOpen_eq_top` at `d = 1`.
Every `W_d`-local statement of Tag 01MU is therefore available globally at `d = 1`, and at
`d = 1` the degrees `dn` of Tag 01MU range over all of `ℤ`. -/
public theorem ratioLocus_one_eq_top (hcover : DegreeOneCover 𝒮) :
    ProjShared.ratioLocus 𝒮 1 = ⊤ :=
  ProjShared.ratioLocus_eq_top_of_iSup_basicOpen_eq_top 𝒮 hcover

/-! ### Invertibility of the twists -/

/-- **Stacks 01MT: the sheaves `𝒪_X(n)` are invertible.**

The trivializing sections are the ratios `(f/1)^n` on the standard opens `D₊(f)` with
`f ∈ S₁`, assembled by
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_ratioLocus_eq_top`
at `d = 1`. -/
@[stacks 01MT "the sheaves 𝒪_X(n) are invertible", ega "II 3.2.5" "Second assertion"]
public theorem isInvertible_twistingSheaf (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).presheaf
      (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.2 (twistingSheaf 𝒮 n) := by
  have h := isInvertible_twistingSheaf_of_ratioLocus_eq_top 𝒮 (ratioLocus_one_eq_top 𝒮 hcover) n
  rwa [Nat.cast_one, one_mul] at h

/-! ### Equation 01MO: multiplication of two twists -/

/-- **Stacks 01MT: Equation 01MO `𝒪_X(n) ⊗ 𝒪_X(m) ⟶ 𝒪_X(n + m)` is an isomorphism**, for all
integers `n` and `m`.

This is
`Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top` at
`k = 1`; the only work is the substitution of `1 * n` for `n`, which has to be done after
`revert` because the index occurs in the type of the morphism. -/
@[stacks 01MT "equation 01MO is an isomorphism"]
public theorem isIso_twistMultiplicationMap (hcover : DegreeOneCover 𝒮) (n m : ℤ) :
    IsIso (twistMultiplicationMap 𝒮 n m) := by
  have key := TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top 𝒮 (k := 1)
    (ratioLocus_one_eq_top 𝒮 hcover) n m
  revert key
  rw [Nat.cast_one, one_mul, one_mul]
  exact id

/-- The isomorphism `𝒪_X(n) ⊗ 𝒪_X(m) ≅ 𝒪_X(n + m)` of Equation 01MO. -/
public def twistMultiplicationIso (hcover : DegreeOneCover 𝒮) (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((twistingSheaf 𝒮 n))).obj ((twistingSheaf 𝒮 m))) ≅
      twistingSheaf 𝒮 (n + m) :=
  @asIso _ _ _ _ (twistMultiplicationMap 𝒮 n m) (isIso_twistMultiplicationMap 𝒮 hcover n m)

/-! ### Equation 03GJ: multiplication of a twist with the twist of an arbitrary module -/

/-- **Stacks 01MT: Equation 03GJ `𝒪_X(n) ⊗ ℱ(m) ⟶ ℱ(n + m)` is an isomorphism**, for every
sheaf of `𝒪_X`-modules `ℱ` and all integers `n` and `m`.

The source deduces this clause from the Equation 01MO clause, and so does the proof: by
construction
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap` is the composite of
the inverse associator, the braiding on `𝒪(n) ⊗ ℱ` tensored with `𝒪(m)`, the associator, and
`𝟙 ℱ ⊗ (Equation 01MO)`.  The first three factors are isomorphisms unconditionally, and the
fourth is one because the native tensor bifunctor maps the product of two isomorphisms to an
isomorphism. -/
@[stacks 01MT "equation 03GJ is an isomorphism"]
public theorem isIso_twistSheafMultiplicationMap (hcover : DegreeOneCover 𝒮)
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) (n m : ℤ) :
    IsIso (twistSheafMultiplicationMap 𝒮 F n m) := by
  have h := isIso_twistMultiplicationMap 𝒮 hcover n m
  let tensorProduct := Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf,
        (AlgebraicGeometry.Proj 𝒮).toRingedSpace.IsSheaf⟩)
  have map_prod_isIso {A B C D : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))} (f : A ⟶ B) (g : C ⟶ D)
      (hf : IsIso f) (hg : IsIso g) : IsIso (tensorProduct.map ((f, g) : (A, C) ⟶ (B, D))) :=
    (tensorProduct.mapIso (Iso.prod (@asIso _ _ _ _ f hf) (@asIso _ _ _ _ g hg))).isIso_hom
  change IsIso (_ ≫ _ ≫ _ ≫ _)
  beta_reduce
  exact IsIso.comp_isIso' (Iso.isIso_inv _)
    (IsIso.comp_isIso' (map_prod_isIso _ _ (Iso.isIso_hom _) inferInstance)
      (IsIso.comp_isIso' (Iso.isIso_hom _) (map_prod_isIso _ _ inferInstance h)))

/-! ### The tensor powers `𝒪_X(1)^{⊗ n} ≅ 𝒪_X(n)` -/

/-- Invertibility of `𝒪_X(n)`, in the `Stacks.Ample.IsInvertibleModule` spelling that the
tensor powers of Tag 01CU are indexed by.

`isInvertible_twistingSheaf` proves the same thing, but assembled from the trivializations by a
dual-sheaf argument on the ratio locus; the tensor-power development needs the statement with
the sheaf condition supplied as `Stacks.SheafInternalHom.isSheaf_structureRingPresheaf`, which
is what `Stacks.AlgebraicGeometry.TwistMapsInvertible` produces from a pointwise local
trivialization. -/
@[ega "II 2.5.8" "special case", ega "II 2.6.1" "more general", ega "II 8.7.8" "special case"]
public theorem isInvertibleModule_twistingSheaf (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twistingSheaf 𝒮 n) :=
  TwistMapsInvertible.isInvertibleModule_of_forall_exists_restrict_isoUnit _
    fun x => TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf 𝒮 (d := 1)
      (n := n) (c := n) (by simp)
      ((ratioLocus_one_eq_top 𝒮 hcover).ge (TopologicalSpace.Opens.mem_top x))

/-- Equation 01MO at `(n, 1)` as an isomorphism, in the functor spelling: tensoring `𝒪_X(n)` on
the right by `𝒪_X(1)` gives `𝒪_X(n + 1)`. -/
public def twistMulIso (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    (ProjTwistPowers.twistRight 𝒮).obj (twistingSheaf 𝒮 n) ≅ twistingSheaf 𝒮 (n + 1) :=
  @asIso _ _ _ _ (twistMultiplicationMap 𝒮 n 1) (isIso_twistMultiplicationMap 𝒮 hcover n 1)

/-- **Under Tag 01MT's hypothesis, tensoring by `𝒪_X(1)` is an autoequivalence of
`𝒪_X`-modules.** -/
public theorem isEquivalence_twistRight (hcover : DegreeOneCover 𝒮) :
    (ProjTwistPowers.twistRight 𝒮).IsEquivalence :=
  let : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).presheaf
      (ProjTwistPowers.projSheafCond 𝒮) (twistingSheaf 𝒮 1) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        (AlgebraicGeometry.Proj 𝒮).presheaf (ProjTwistPowers.projSheafCond 𝒮)
        (twistingSheaf 𝒮 1)).mpr (isInvertibleModule_twistingSheaf 𝒮 hcover 1)
  Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _

/-- **Stacks 01MT: the induced identification `𝒪_X(1)^{⊗ n} ≅ 𝒪_X(n)`**, for every integer `n`,
at the canonical integral tensor power `Stacks.Ample.tensorPowModule` of Tag 01CU.

Both families are carried one degree by the autoequivalence `twistRight` — the tensor powers by
the addition law of Tag 01CU, the twists by Equation 01MO at `(n, 1)` — and they agree in degree
one, so `Stacks.AlgebraicGeometry.ProjTwistPowers.nonempty_iso_of_shift` identifies them in
every degree, negative ones included, with no separate argument.

The library already had this under the stronger hypothesis
`Algebra.adjoin (𝒮 0) (𝒮 1) = ⊤`, as
`Stacks.AlgebraicGeometry.ProjTwistPowers.nonempty_tensorPowModule_iso_twistingSheaf`; this is
the same statement at the source's own printed hypothesis. -/
@[stacks 01MT "the induced identification 𝒪_X(1)^{⊗ n} ≅ 𝒪_X(n)", ega "II 2.5.14" "(2.5.14.2)"]
public theorem nonempty_tensorPowModule_iso_twistingSheaf (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    letI := isInvertibleModule_twistingSheaf 𝒮 hcover 1
    Nonempty (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twistingSheaf 𝒮 1) n ≅
      twistingSheaf 𝒮 n) :=
  let := isInvertibleModule_twistingSheaf 𝒮 hcover 1
  let := isEquivalence_twistRight 𝒮 hcover
  ProjTwistPowers.nonempty_iso_of_shift (ProjTwistPowers.twistRight 𝒮)
    (fun m => Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twistingSheaf 𝒮 1) m)
    (fun m => twistingSheaf 𝒮 m) (fun m => ProjTwistPowers.twistPowSuccIso 𝒮 m)
    (fun m => twistMulIso 𝒮 hcover m) (k := 1)
    (Stacks.Ample.tensorPowModuleOneIso (AlgebraicGeometry.Proj 𝒮) (twistingSheaf 𝒮 1)) n

/-! ### Equation 01MQ: comparison with the shifted graded module -/

variable {M : Type u} [AddCommGroup M] [Module S M] {τ : Type t} [SetLike τ M]
  [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- **Tag 01MU's comparison assertion, globally on `Proj S` once `W_d` is everything.**

`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_moduleTwistMap` states this for
the restriction of the comparison to an open contained in the ratio locus; when the ratio locus
is all of `Proj S` the statement can be made about the comparison itself.  The argument is the
one `Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top`
runs for Equation 01MO: every point lies on some `D₊(fg)` with `deg f = deg g + d`, the
comparison is a stalk isomorphism there, and a morphism of sheaves that is a stalk isomorphism
at every point is an isomorphism. -/
public theorem isIso_moduleTwistMap_of_ratioLocus_eq_top {d : ℕ}
    (hd : ProjShared.ratioLocus 𝒮 d = ⊤) (n : ℤ) :
    IsIso (ProjShifted.moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n)) := by
  have hstalk : ∀ x : ↑↑(AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((SheafOfModules.toSheaf (structureSheafRing
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
          (ProjShifted.moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n))).hom) := by
    intro x
    have hx : x ∈ ProjShared.ratioLocus 𝒮 d := by rw [hd]; trivial
    obtain ⟨e, f, g, hf, hg, hfx, hgx⟩ := (ProjShared.mem_ratioLocus_iff 𝒮 d x).mp hx
    have hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (f * g) := fun hmul =>
      (x.isPrime.mem_or_mem hmul).elim hfx hgx
    exact ModuleTwistIso.isIso_stalkFunctor_map_moduleTwist 𝒮 𝒨 hf hg
      (mul_comm (n : ℤ) (d : ℤ)) hx'
  have h := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    ((SheafOfModules.toSheaf (structureSheafRing
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
      (ProjShifted.moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n)))
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (SheafOfModules.toSheaf
    (structureSheafRing (AlgebraicGeometry.Proj
      𝒮).toRingedSpace)) h
    (PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
      (R := structureSheafRing (AlgebraicGeometry.Proj 𝒮).toRingedSpace))

/-- **Stacks 01MT: Equation 01MQ `M̃ ⊗ 𝒪_X(n) ⟶ M(n)̃` is an isomorphism**, for every graded
`S`-module `M` and every integer `n`.

`isIso_moduleTwistMap_of_ratioLocus_eq_top` at `d = 1`. -/
@[stacks 01MT "equation 01MQ is an isomorphism", ega "II 2.5.15", ega "II 3.2.8"]
public theorem isIso_moduleTwistMap (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    IsIso (ProjShifted.moduleTwistMap 𝒮 𝒨 n) := by
  have key := isIso_moduleTwistMap_of_ratioLocus_eq_top 𝒮 𝒨 (d := 1)
    (ratioLocus_one_eq_top 𝒮 hcover) n
  revert key
  rw [Nat.cast_one, one_mul]
  exact id

/-- **Stacks 01MT: the induced isomorphism `M̃ ⊗_{𝒪_X} 𝒪_X(n) = M̃(n) ≅ M(n)̃`.** -/
@[stacks 01MT "the induced isomorphism M̃ ⊗ 𝒪_X(n) ≅ M(n)~"]
public def moduleTwistIso (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((associatedModuleSheaf 𝒮 𝒨))).obj ((twistingSheaf 𝒮 n))) ≅
      associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n) :=
  @asIso _ _ _ _ (ProjShifted.moduleTwistMap 𝒮 𝒨 n) (isIso_moduleTwistMap 𝒮 𝒨 hcover n)

end Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover

end
