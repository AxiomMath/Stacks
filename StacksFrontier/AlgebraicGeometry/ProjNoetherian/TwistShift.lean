module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorRingedSpace
public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.TwistComparison
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpen
public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.ApparatusBridge
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections

/-!
# Shifting a twist by a multiple of a degree whose ratio locus is everything

Let `A` be a graded ring, `X = Proj A` and `d` a natural number whose *ratio locus*
`Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒜 d` — the union of the standard opens `D₊(fg)`
with `deg f = deg g + d`, Tag 01MU's second description of the invertible locus `W_d` — is all of
`X`. This file records the three consequences that hypothesis has for the twists `𝒪_X(dn)`, and
produces such a `d` for a Noetherian `A`.

The first is Tag 01MU's comparison `M̃ ⊗_{𝒪_X} 𝒪_X(dn) ⟶ M(dn)~` read globally rather than
restricted to an open: the general form
`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_moduleTwistMap` restricts to the
opens of the ratio locus, and with the locus equal to `⊤` the restriction functor can be dropped
altogether. The second specializes it to the graded module `A(q)`, giving the multiplication
isomorphism `𝒪_X(q) ⊗ 𝒪_X(dn) ≅ 𝒪_X(q + dn)` for an **arbitrary** integer `q`, not only a
multiple of `d`. The third tensors that with an arbitrary sheaf of `𝒪_X`-modules `ℱ` and uses
associativity of the tensor product of sheaves of modules to get `(ℱ(q))(dn) ≅ ℱ(q + dn)`.

Finally, a Noetherian `A` admits a positive `d` divisible by any prescribed positive `d₀` with
`ratioLocus 𝒜 d = ⊤`, obtained from the common degree of a finite standard-open cover of the
quasi-compact space `Proj A` and then multiplied up along divisibility.

## Main results

* `Stacks.AlgebraicGeometry.ProjNoetherianTwistShift.isIso_moduleTwistMap_of_ratioLocus_eq_top`:
  **the global comparison.** If `ratioLocus 𝒜 d = ⊤` then `moduleTwistMap 𝒜 𝒨 (d * n)` is an
  isomorphism on all of `Proj A`, for every graded module `𝒨` and every `n : ℤ`.
* `Stacks.AlgebraicGeometry.ProjNoetherianTwistShift.twistingSheafTensorIso`:
  `𝒪_X(q) ⊗ 𝒪_X(dn) ≅ 𝒪_X(q + dn)`, for every `q n : ℤ`.
* `Stacks.AlgebraicGeometry.ProjNoetherianTwistShift.twistSheafOfModulesShiftIso`:
  `(ℱ(q))(dn) ≅ ℱ(q + dn)` for every sheaf of `𝒪_X`-modules `ℱ` and all `q n : ℤ`.
* `Stacks.AlgebraicGeometry.ProjNoetherianTwistShift.exists_pos_ratioLocus_eq_top`: for a
  Noetherian `A` and every positive `d₀` there is a positive `d` with `d₀ ∣ d`,
  `Proj.degreeOpen 𝒜 d = ⊤` and `ratioLocus 𝒜 d = ⊤`.

## The route

The comparison is obtained through stalks, exactly as
`Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top` is for
the multiplication map, and for the same reason: `moduleTwistMap` is a morphism out of a
*sheafified* tensor product, and nothing in this repository says that restriction to an open
commutes with that sheafification, so the proof never restricts the tensor product. With
`ratioLocus 𝒜 d = ⊤` every point of `Proj A` lies in some `D₊(fg)` with `deg f = deg g + d`, so
`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_stalkFunctor_map_moduleTwist` — which carries no
divisibility hypothesis on the left factor — makes the comparison a stalk isomorphism
everywhere; `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` turns that into an isomorphism of
abelian sheaves and `SheafOfModules.toSheaf` reflects isomorphisms.

The multiplication isomorphism is the comparison at `𝒨 = twistGrading 𝒜 q`, which is how the
source obtains it: `𝒪_X(q)` *is* `associatedModuleSheaf 𝒜 (twistGrading 𝒜 q)` by definition, so
the only work is identifying the target `associatedModuleSheaf 𝒜 (A(q)(dn))` with
`𝒪_X(q + dn)`, which is `associatedModuleSheaf_shiftedGrading_twistGrading`.

For the module-level form, `twistSheafOfModules 𝒜 ℱ c` is *equal* to the tensor product
`ℱ ⊗ 𝒪_X(c)` that `moduleTwistMap` uses, by
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistSheafOfModules_eq_tensorSheaf`. So
`(ℱ(q))(dn)` is `(ℱ ⊗ 𝒪(q)) ⊗ 𝒪(dn)`, and the isomorphism is the associator of
`Stacks.SheafOfModules.OnSpace.monoidal` followed by the multiplication isomorphism above tensored on the left with
`ℱ`. Both steps are literally at the right type: no `eqToIso` is needed anywhere in that
composite, because the two spellings of the twist agree on the nose.

## Implementation notes

* `associatedModuleSheaf_congr` is the transport along an equality of gradings. It is needed
  because the two instances `[DirectSum.Decomposition 𝒨]` carried by the two spellings of the
  grading of `A(q)(c)` are genuinely different terms —
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGradingDecomposition` is an
  `IsInternal.chooseDecomposition` while `Stacks.GradedModule.shiftedGradingDecomposition`
  transports the given one — so `congrArg` does not apply. It holds by `rfl` after `subst`
  because the construction of `associatedModuleSheaf` never uses those instances as data: the
  grading enters only through the local predicate cutting out the sections and through
  `Prop`-valued membership proofs.
* Functoriality of `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` in its arguments
  is `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMapIso`, recorded in
  `StacksFrontier/AlgebraicGeometry/Scheme/QuasiCoherent/TildeTensorSections.lean`; it is used here
  at `Iso.refl` in the left argument.
* The `VAdd ℕ ℤ` action is the scoped `Stacks.GradedLocalization.instVAddNatInt`, the one
  `Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap` is stated with; without opening that
  namespace the `SetLike.GradedSMul 𝒜 𝒨` hypothesis of the variable block does not elaborate.
* `exists_pos_ratioLocus_eq_top` carries the hypothesis `0 < d₀`. It is not removable: for
  `d₀ = 0` the two requirements `0 ∣ d` and `0 < d` are contradictory.

## What is not done

* **No stacks attribute is attached here.** Tag 01MU's covering set spans several files and the
  tags are placed elsewhere in that covering set; the statements here are the conditional global
  forms that `StacksFrontier/AlgebraicGeometry/ModuleTwistIso/Basic.lean` records as absent.
* Nothing is proved about the inverse morphisms: `twistingSheafTensorIso` and
  `twistSheafOfModulesShiftIso` are produced from `asIso` and from the associativity
  constraint, with no formula for either direction on sections.
* No coherence is stated for `twistSheafOfModulesShiftIso`: neither naturality in the twisting
  index nor any compatibility with a third shift.
* The hypothesis `ratioLocus 𝒜 d = ⊤` is *not* discharged for any particular graded ring here
  beyond `exists_pos_ratioLocus_eq_top`; in particular the degree `d` it produces is the common
  degree of some cover and is not computed.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShifted
open Stacks.GradedLocalization
open Stacks.GradedModule (shiftedGrading)

namespace Stacks.AlgebraicGeometry.ProjNoetherianTwistShift

universe u w t

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A M : Type u} {σ : Type w} {τ : Type t} [CommRing A] [AddCommGroup M] [Module A M]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-! ### The comparison map on all of `Proj A` -/

/-- **Tag 01MU's comparison assertion, globally.** If the ratio locus of `d` is all of `Proj A`
— the union of the standard opens `D₊(fg)` with `deg f = deg g + d`, which for `d = 1` is the
usual hypothesis that `A` is generated in degree one — then for every graded `A`-module `M` and
every integer `n` the canonical comparison `M̃ ⊗_{𝒪_X} 𝒪_X(dn) ⟶ M(dn)~` is an isomorphism of
sheaves of modules on the whole of `Proj A`.

The unconditional global statement is false for a general graded ring; that is exactly why Tag
01MU introduces the open `W_d`. The proof goes through stalks, as the multiplication-map
analogue `Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top`
does: the hypothesis puts every point of `Proj A` in some `D₊(fg)`, and
`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_stalkFunctor_map_moduleTwist` is a stalkwise
isomorphism there with no hypothesis on the left factor. -/
theorem isIso_moduleTwistMap_of_ratioLocus_eq_top {d : ℕ}
    (hd : ProjShared.ratioLocus 𝒜 d = ⊤) (n : ℤ) :
    IsIso (moduleTwistMap 𝒜 𝒨 ((d : ℤ) * n)) := by
  have hstalk : ∀ x : ↑↑(AlgebraicGeometry.Proj 𝒜).toRingedSpace.toPresheafedSpace,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((SheafOfModules.toSheaf (structureSheafRing
          (AlgebraicGeometry.Proj 𝒜).toRingedSpace)).map
          (moduleTwistMap 𝒜 𝒨 ((d : ℤ) * n))).hom) := by
    intro x
    have hx : x ∈ ProjShared.ratioLocus 𝒜 d := by rw [hd]; trivial
    obtain ⟨e, f, g, hf, hg, hfx, hgx⟩ := (ProjShared.mem_ratioLocus_iff 𝒜 d x).mp hx
    have hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒜 (f * g) := fun hmul =>
      (x.isPrime.mem_or_mem hmul).elim hfx hgx
    exact ModuleTwistIso.isIso_stalkFunctor_map_moduleTwist 𝒜 𝒨 hf hg
      (mul_comm (n : ℤ) (d : ℤ)) hx'
  have h := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    ((SheafOfModules.toSheaf (structureSheafRing
      (AlgebraicGeometry.Proj 𝒜).toRingedSpace)).map (moduleTwistMap 𝒜 𝒨 ((d : ℤ) * n)))
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (SheafOfModules.toSheaf
    (structureSheafRing (AlgebraicGeometry.Proj 𝒜).toRingedSpace)) h
    (PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
      (R := structureSheafRing (AlgebraicGeometry.Proj 𝒜).toRingedSpace))

/-! ### Transporting the associated sheaf along an equality of gradings -/

omit [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒜 𝒨] in
/-- Equal gradings have equal associated sheaves, *whatever* decomposition and graded-action
instances the two sides carry. The instances have to be allowed to differ because the two
spellings of the grading of a twice-shifted module come with unrelated ones; the statement is
nevertheless closed by `rfl` after substituting, since `associatedModuleSheaf` uses the grading
only through the local predicate cutting out its sections and through `Prop`-valued membership
proofs, never as data. -/
lemma associatedModuleSheaf_congr (𝒩 𝒩' : ℤ → τ)
    [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
    [DirectSum.Decomposition 𝒩'] [SetLike.GradedSMul 𝒜 𝒩'] (h : 𝒩 = 𝒩') :
    associatedModuleSheaf 𝒜 𝒩 = associatedModuleSheaf 𝒜 𝒩' := by
  subst h
  rfl

/-- **`A(q)(c)` and `A(q + c)` have the same associated sheaf.** The gradings agree by
`Stacks.AlgebraicGeometry.ModuleTwistIso.shiftedGrading_twistGrading` — one is `A_{i + c + q}`
and the other `A_{i + (q + c)}` — and the decomposition instances the two sides carry are
irrelevant by `associatedModuleSheaf_congr`. This is what identifies the target of the
comparison map at the graded module `A(q)` with the twisting sheaf `𝒪_X(q + c)`. -/
lemma associatedModuleSheaf_shiftedGrading_twistGrading (q c : ℤ) :
    associatedModuleSheaf 𝒜 (shiftedGrading (twistGrading (S := A) 𝒜 q) c) =
      twistingSheaf 𝒜 (q + c) :=
  associatedModuleSheaf_congr 𝒜 _ _ (ModuleTwistIso.shiftedGrading_twistGrading 𝒜 q c)

/-! ### The multiplication isomorphism between the twists -/

/-- **`𝒪_X(q) ⊗ 𝒪_X(dn) ≅ 𝒪_X(q + dn)`**, for an arbitrary integer `q` and every `n : ℤ`, as
soon as the ratio locus of `d` is all of `Proj A`. Only the right-hand factor's index has to be
a multiple of `d`.

This is `isIso_moduleTwistMap_of_ratioLocus_eq_top` at the graded module `A(q)`, which is how
the source obtains the multiplication maps for an arbitrary left index: the left-hand factor
`associatedModuleSheaf 𝒜 (twistGrading 𝒜 q)` *is* `𝒪_X(q)` by definition, and the target is
`𝒪_X(q + dn)` by `associatedModuleSheaf_shiftedGrading_twistGrading`. The tensor product is the
one `moduleTwistMap` is stated over, namely
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
noncomputable def twistingSheafTensorIso {d : ℕ} (hd : ProjShared.ratioLocus 𝒜 d = ⊤) (q n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((AlgebraicGeometry.Proj
        𝒜).toRingedSpace)).presheaf, (((AlgebraicGeometry.Proj
        𝒜).toRingedSpace)).IsSheaf⟩).obj ((twistingSheaf 𝒜 q))).obj
        ((twistingSheaf 𝒜 ((d : ℤ) * n)))) ≅
      twistingSheaf 𝒜 (q + (d : ℤ) * n) :=
  haveI := isIso_moduleTwistMap_of_ratioLocus_eq_top 𝒜 (twistGrading (S := A) 𝒜 q) hd n
  asIso (moduleTwistMap 𝒜 (twistGrading (S := A) 𝒜 q) ((d : ℤ) * n)) ≪≫
    eqToIso (associatedModuleSheaf_shiftedGrading_twistGrading 𝒜 q ((d : ℤ) * n))

/-! ### Functoriality of the tensor product sheaf in its right argument -/

/-! ### Shifting the twist of an arbitrary sheaf of modules -/

/-- **`(ℱ(q))(dn) ≅ ℱ(q + dn)`** for every sheaf of `𝒪_X`-modules `ℱ` and all `q n : ℤ`, as soon
as the ratio locus of `d` is all of `Proj A`.

`twistSheafOfModules 𝒜 ℱ c` is the tensor product `ℱ ⊗ 𝒪_X(c)` — *equal* to it, by
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistSheafOfModules_eq_tensorSheaf` — so the
left-hand side is `(ℱ ⊗ 𝒪_X(q)) ⊗ 𝒪_X(dn)`. Re-bracketing it with the associator of
`Stacks.SheafOfModules.OnSpace.monoidal` and then applying `twistingSheafTensorIso` inside the
right-hand factor gives `ℱ ⊗ 𝒪_X(q + dn)`, which is the right-hand side.

The re-bracketing is the associator of the monoidal structure of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal`, whose tensor product *is*
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` and whose tensor product of morphisms
*is* `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap`, both by `rfl`. Taking it there
rather than at `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafAssociator` is what makes
this isomorphism have a *coherence*: naturality in the middle factor, read off
`CategoryTheory.MonoidalCategory.associator_naturality`. The Tag 01CB associator carries no such
coherence and cannot cheaply be given one: it is an `eqToIso` transport of the Tag 05NA associator
along two *nested* identifications of tensor products, and a statement comparing it with a monoidal
associator forces the elaborator to settle both nestings at once, which exhausts the default
heartbeat budget. -/
noncomputable def twistSheafOfModulesShiftIso {d : ℕ} (hd : ProjShared.ratioLocus 𝒜 d = ⊤)
    (F : SheafOfModules.{u} (ProjTwistFunctor.projRingSheaf 𝒜)) (q n : ℤ) :
    twistSheafOfModules 𝒜 (twistSheafOfModules 𝒜 F q) ((d : ℤ) * n) ≅
      twistSheafOfModules 𝒜 F (q + (d : ℤ) * n) :=
  letI : MonoidalCategory (SheafOfModules.{u} (ProjTwistFunctor.projRingSheaf 𝒜)) :=
    Stacks.SheafOfModules.OnSpace.monoidal (AlgebraicGeometry.Proj 𝒜).toRingedSpace
  MonoidalCategory.associator F (twistingSheaf 𝒜 q) (twistingSheaf 𝒜 ((d : ℤ) * n)) ≪≫
    Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMapIso (Iso.refl F)
      (twistingSheafTensorIso 𝒜 hd q n)

/-! ### A good degree for a Noetherian graded ring -/

/-- **A Noetherian graded ring has a good degree in every divisibility class.** For every
positive `d₀` there is a positive multiple `d` of `d₀` whose degree open `U_d = ⋃_{f ∈ 𝒜 d}
D₊(f)` is all of `Proj A`, and whose ratio locus is therefore all of `Proj A` too — which is the
hypothesis of `isIso_moduleTwistMap_of_ratioLocus_eq_top`, `twistingSheafTensorIso` and
`twistSheafOfModulesShiftIso`. The `degreeOpen` conclusion is stated alongside because it is the
stronger of the two and consumers ask for it directly.

`Stacks.AlgebraicGeometry.ProjCoherentII.exists_pos_degreeOpen_eq_top` supplies one positive
`d₁` with `U_{d₁} = ⊤`, from quasi-compactness of `Proj A`; `AlgebraicGeometry.Proj
.degreeOpen_le_of_dvd` makes the degree opens grow along divisibility, so `d = d₀ d₁` works; and
`Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_iSup_basicOpen_eq_top` converts the
cover into the ratio locus, a homogeneous `f` of degree `d` contributing the pair `(f, 1)`.

The hypothesis `0 < d₀` is not removable: for `d₀ = 0` the requirements `0 ∣ d` and `0 < d` are
contradictory. -/
theorem exists_pos_ratioLocus_eq_top [IsNoetherianRing A] (d₀ : ℕ) (hd₀ : 0 < d₀) :
    ∃ d : ℕ, 0 < d ∧ d₀ ∣ d ∧ AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤ ∧
      ProjShared.ratioLocus 𝒜 d = ⊤ := by
  obtain ⟨d₁, hd₁, htop⟩ := ProjCoherentII.exists_pos_degreeOpen_eq_top 𝒜
  have hcover : AlgebraicGeometry.Proj.degreeOpen 𝒜 (d₀ * d₁) = ⊤ :=
    top_le_iff.mp (htop.ge.trans
      (AlgebraicGeometry.Proj.degreeOpen_le_of_dvd 𝒜 (Dvd.intro_left _ rfl)
        (Nat.mul_pos hd₀ hd₁)))
  exact ⟨d₀ * d₁, Nat.mul_pos hd₀ hd₁, Dvd.intro _ rfl, hcover,
    ProjShared.ratioLocus_eq_top_of_iSup_basicOpen_eq_top 𝒜 hcover⟩

end Stacks.AlgebraicGeometry.ProjNoetherianTwistShift

end
