module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.QcohPresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Characterization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteLocallyFree
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.CanonicalSheafCertificate
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Twisting an object of the derived category by an invertible module

Let `X` be a scheme and `ℒ` an invertible `𝒪_X`-module. For `E` in `D(𝒪_X)` the object
`E ⊗ ℒ` of chapter 42 of the Stacks Project is the derived tensor product `E ⊗^L_{𝒪_X} ℒ[0]`.
Since `ℒ` is flat, `ℒ[0]` is K-flat, so on a complex `P` it is computed by the termwise tensor
product `P^n ⊗_{𝒪_X} ℒ`; and it commutes with derived pullback, by Stacks 079U and because the
derived pullback of the K-flat complex `ℒ[0]` is the termwise pullback `(f^*ℒ)[0]`.

These facts together show that twisting by `ℒ` preserves the condition of Stacks 0F9E (1)
under which the Chern classes of `E` are defined: an envelope `f : Y ⟶ X` with `Lf^*E`
represented by a locally bounded complex `P` of finite locally free `𝒪_Y`-modules gives the
same envelope with `Lf^*(E ⊗ ℒ)` represented by `P ⊗ f^*ℒ`, which is again locally bounded and
finite locally free, of the same ranks. This is the reduction used in the proof of Stacks 0FAF.

## Main definitions

* `Stacks.Chow.derivedTwist` — the twist `E ⊗^L ℒ[0]` of an object `E` of `D(𝒪_X)`.
* `Stacks.Chow.twistComplex` — the termwise twist `P^n ⊗ ℒ` of a complex of `𝒪_X`-modules.
* `Stacks.Chow.EnvelopePresentation.twist` — the twist of an envelope presentation of `E`, an
  envelope presentation of `E ⊗ ℒ` on the same envelope.

## Main results

* `Stacks.Chow.derivedTwistQIso` — `Q(P) ⊗^L ℒ[0] ≅ Q(P ⊗ ℒ)`.
* `Stacks.Chow.derivedPullbackDerivedTwistIso` — `Lf^*(E ⊗^L ℒ[0]) ≅ Lf^*E ⊗^L (f^*ℒ)[0]`.
* `Stacks.Chow.isLocallyBoundedFiniteLocallyFree_twistComplex` — the termwise twist of a locally
  bounded complex of finite locally free modules is one again.
* `Stacks.Chow.isFiniteLocallyFreeOfRank_restrict_tensor` — on an open where `M` is finite
  locally free of rank `r`, so is `M ⊗ ℒ`.
* `Stacks.Chow.hasDefinedChernClasses_derivedTwist` — if the Chern classes of `E` are defined,
  so are those of `E ⊗ ℒ`.
* `Stacks.Chow.isPerfect_derivedTwist` — if `E` is perfect, so is `E ⊗ ℒ`.

## Implementation notes

The derived tensor product is `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`,
the one Stacks 079U (`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`) is
stated for, and the termwise tensor product is its underlying
`Stacks.SheafOfModules.Tensor.sheafTensor`, so that the comparison of the derived tensor
product with a K-flat right factor applies without transport.

## References

* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

-- The standard model of the derived category is the one `Stacks.Chow.EnvelopePresentation` and
-- the derived pullback are stated at; the priority beats the locally small model, which is a
-- global instance.
attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing StacksDraft.KFlat.modulePullback

/-! ### The twist of an object and of a complex -/

section Twist

variable {X : Scheme.{u}}

/-- The complex `ℒ[0]`: the `𝒪_X`-module `ℒ` placed in degree zero. -/
abbrev singleZero (L : X.Modules) : CochainComplex X.Modules ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L

/-- **The twist of an object of `D(𝒪_X)` by an `𝒪_X`-module**: the derived tensor product
`E ⊗^L_{𝒪_X} ℒ[0]`. For an invertible `ℒ` this is the object `E ⊗ ℒ` of Stacks 0FAF. -/
def derivedTwist (E : DerivedCategory X.Modules) (L : X.Modules) : DerivedCategory X.Modules :=
  ((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj (singleZero L))

/-- The twist is functorial in the object of `D(𝒪_X)`: an isomorphism `E ≅ E'` induces an
isomorphism of twists. -/
def derivedTwistMapIso {E E' : DerivedCategory X.Modules} (e : E ≅ E') (L : X.Modules) :
    derivedTwist E L ≅ derivedTwist E' L :=
  ((derivedTensorProductFunctor X.sheaf).mapIso e).app _

/-- Tensoring on the right with a fixed `𝒪_X`-module, `M ↦ M ⊗_{𝒪_X} ℒ`. -/
def twistFunctor (L : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj L

/-- Tensoring on the right with a fixed module is additive. -/
instance (L : X.Modules) : (twistFunctor L).Additive :=
  RingedSpace.sheafTensor_flip_additive X.toRingedSpace L

/-- **The termwise twist of a complex**: the complex `n ↦ P^n ⊗_{𝒪_X} ℒ`, with the
differentials `d ⊗ 1`. -/
def twistComplex (P : CochainComplex X.Modules ℤ) (L : X.Modules) : CochainComplex X.Modules ℤ :=
  ((twistFunctor L).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- The terms of the termwise twist are the tensor products of the terms. -/
theorem twistComplex_X (P : CochainComplex X.Modules ℤ) (L : X.Modules) (n : ℤ) :
    (twistComplex P L).X n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (P.X n)).obj L :=
  rfl

end Twist

/-! ### Invertible modules are flat and of rank one -/

section Invertible

variable {X : Scheme.{u}}

/-- **An invertible module on a scheme is flat**: its stalks are invertible modules over the
local rings, hence flat. -/
theorem isFlat_of_isInvertible (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) L :=
  Stacks.SheafOfModules.isFlat_of_isInvertible (X := X.toRingedSpace) L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ h)

/-- **`ℒ[0]` is K-flat for an invertible `ℒ`**: a flat module in a single degree is K-flat, the
base case of Stacks 06YQ. -/
theorem kFlat_singleZero (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace (singleZero L) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat X.sheaf L
    (isFlat_of_isInvertible L) 0

/-- **An invertible module on a scheme is finite locally free of rank one**, by Stacks 0B8M:
the stalks of the structure sheaf of a scheme are local rings. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 := by
  obtain ⟨q, hq, hr⟩ :=
    ((Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one_algebraicGeometry
      (X := X.toRingedSpace) L).mp h).exists_isFiniteLocallyFreeOfRankData
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u} ⟨q, hq, hr⟩

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
theorem isInvertible_pullback {Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L h

end Invertible

/-! ### Tensor products of finite locally free modules -/

section TensorRank

variable {X : Scheme.{u}}

/-- **A tensor product of finite locally free modules of ranks `r` and `s` is finite locally
free of rank `r * s`**: on the common refinement of two families of local bases the tensor
product is free on the product of the two index types. -/
@[sga "6 I 6.12" "Clause a), special case"]
theorem isFiniteLocallyFreeOfRank_tensor {M N : X.Modules} {r s : ℕ}
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N s) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) (r * s) := by
  obtain ⟨qM, hqM, hrM⟩ := hM.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨qN, hqN, hrN⟩ := hN.exists_isFiniteLocallyFreeOfRankData
  -- `Stacks.SheafOfModules.localGeneratorsDataTensor` asks for the local freeness of the two
  -- factors at `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, the sheaf of rings the native
  -- tensor product is stated at; `X.ringCatSheaf` is that sheaf but not reducibly so, so the
  -- two hypotheses are seated at the spelling instance search uses.
  let : _root_.SheafOfModules.LocalGeneratorsData.IsLocallyFreeData
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) qM := hqM
  let : _root_.SheafOfModules.LocalGeneratorsData.IsLocallyFreeData
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) qN := hqN
  refine AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
    ⟨Stacks.SheafOfModules.localGeneratorsDataTensor X.sheaf qM qN,
      Stacks.SheafOfModules.isLocallyFreeData_localGeneratorsDataTensor X.sheaf qM qN,
      fun z => ?_⟩
  obtain ⟨i, j, -⟩ := z
  exact ⟨((hrM i).some.prodCongr (hrN j).some).trans finProdFinEquiv⟩

/-- A tensor product of finite locally free modules is finite locally free. -/
theorem isFiniteLocallyFree_tensor {M N : X.Modules}
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) :=
  Stacks.SheafOfModules.isFiniteLocallyFree_tensor X.sheaf hM hN

/-- The tensor product of isomorphisms of `𝒪_X`-modules. -/
def sheafTensorMapIso {M M' N N' : X.Modules} (e : M ≅ M') (e' : N ≅ N') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M').obj N' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).mapIso e).app N ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M').mapIso e'

/-- **Pullback commutes with tensor products**, Stacks 01CD:
`f^*(M ⊗_{𝒪_X} N) ≅ f^*M ⊗_{𝒪_Y} f^*N`. -/
def sheafTensorPullbackIso {Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    (Scheme.Modules.pullback f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
        ((Scheme.Modules.pullback f).obj M)).obj ((Scheme.Modules.pullback f).obj N) :=
  Cohomology.DerivedPullbackTensor.comparisonAppIso f.toLRSHom.toShHom M N

/-- Restriction along an open immersion commutes with tensor products: it is the pullback. -/
def sheafTensorRestrictIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj
        ((Scheme.Modules.restrictFunctor f).obj M)).obj
        ((Scheme.Modules.restrictFunctor f).obj N) :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app _ ≪≫ sheafTensorPullbackIso f M N ≪≫
    sheafTensorMapIso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
      ((Scheme.Modules.restrictFunctorIsoPullback f).app N).symm

/-- **Twisting by an invertible module preserves the rank on an open**: on an open subscheme
`U` on which `M` is finite locally free of rank `r`, so is `M ⊗_{𝒪_X} ℒ`. -/
theorem isFiniteLocallyFreeOfRank_restrict_tensor (U : X.Opens) (M L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {r : ℕ} (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor U.ι).obj M) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor U.ι).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj L)) r := by
  have := isInvertible_pullback U.ι L
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor U.ι).obj L) 1 :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm
      (isFiniteLocallyFreeOfRank_one_of_isInvertible _)
  have h' := isFiniteLocallyFreeOfRank_tensor h hL
  rw [mul_one] at h'
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (sheafTensorRestrictIso U.ι M L).symm h'

/-- The rank statement of `isFiniteLocallyFreeOfRank_restrict_tensor` with the restriction to
`U` taken in the ringed-space spelling of `Stacks.Chow.IsFiniteLocallyFreeOfRankLT`. -/
theorem isFiniteLocallyFreeOfRank_restrictModules_tensor (U : X.Opens) (M L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {r : ℕ} (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((RingedSpace.restrictModules X.toRingedSpace U).obj M) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((RingedSpace.restrictModules X.toRingedSpace U).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj L)) r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app _).symm
    (isFiniteLocallyFreeOfRank_restrict_tensor U M L
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
        ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app M) h))

/-- **The termwise twist of a locally bounded complex of finite locally free modules by an
invertible module is again locally bounded and finite locally free.** Each term `P^n ⊗ ℒ` is a
tensor product of finite locally free modules, and on an open where `P^n` restricts to zero so
does `P^n ⊗ ℒ`, restriction commuting with tensor products. -/
theorem isLocallyBoundedFiniteLocallyFree_twistComplex {P : CochainComplex X.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    IsLocallyBoundedFiniteLocallyFree (twistComplex P L) := by
  refine ⟨fun n => isFiniteLocallyFree_tensor (hP.1 n)
      (@AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ _ _ _
        L 1 (isFiniteLocallyFreeOfRank_one_of_isInvertible L)), fun x => ?_⟩
  obtain ⟨U₀, hx, lo, hi, hbd⟩ := hP.2 x
  let U : X.Opens := U₀
  refine ⟨U₀, hx, lo, hi, fun n hn => ?_⟩
  have h0 : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj (P.X n)) :=
    (hbd n hn).of_iso
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app
        (P.X n)).symm
  exact ((CochainComplex.KFlatBifunctor.isZero_obj_obj_of_isZero
      (Stacks.SheafOfModules.Tensor.sheafTensor U.toScheme.sheaf) h0 _).of_iso
      (sheafTensorRestrictIso U.ι (P.X n) L)).of_iso
    ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app _)

end TensorRank

/-! ### The derived twist of a complex and of a derived pullback -/

section Derived

variable {X : Scheme.{u}}

/-- **The twist of a complex by an invertible module is computed termwise**:
`Q(P) ⊗^L ℒ[0] ≅ Q(P ⊗ ℒ)`. The complex `ℒ[0]` is K-flat, so the derived tensor product with
it is the total tensor complex, and the total complex of `P ⊗ ℒ[0]` is the termwise tensor
product. -/
def derivedTwistQIso (P : CochainComplex X.Modules ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    derivedTwist (DerivedCategory.Q.obj P) L ≅ DerivedCategory.Q.obj (twistComplex P L) :=
  (canonicalDerivedTensorProduct X.sheaf).comparisonRight P (singleZero L)
      (kFlat_singleZero L) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) P L)

/-- **Derived pullback commutes with twisting by an invertible module**: for `f : Y ⟶ X`,

`Lf^*(E ⊗^L ℒ[0]) ≅ Lf^*E ⊗^L (f^*ℒ)[0]`.

This is Stacks 079U at the pair `(E, ℒ[0])`, followed by the identification of `Lf^*(ℒ[0])`
with `(f^*ℒ)[0]`: the complex `ℒ[0]` is K-flat, so its derived pullback is the termwise
pullback. -/
def derivedPullbackDerivedTwistIso {Y : Scheme.{u}} (f : Y ⟶ X)
    (E : DerivedCategory X.Modules) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    (derivedPullback f.toLRSHom.toShHom).obj (derivedTwist E L) ≅
      derivedTwist ((derivedPullback f.toLRSHom.toShHom).obj E)
        ((Scheme.Modules.pullback f).obj L) :=
  (Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f.toLRSHom.toShHom).app
      (E, DerivedCategory.Q.obj (singleZero L)) ≪≫
    ((derivedTensorProductFunctor Y.sheaf).obj
      ((derivedPullback f.toLRSHom.toShHom).obj E)).mapIso
      (Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom (singleZero L)
          (kFlat_singleZero L) ≪≫
        DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.pullback f) (ComplexShape.up ℤ) 0).app L))

end Derived

/-! ### Twisting preserves the condition of Stacks 0F9E (1) -/

section Envelope

variable {X : Scheme.{u}}

/-- **The twist of an envelope presentation.** If `f : Y ⟶ X` is an envelope with `Lf^*E`
represented by the locally bounded complex `P` of finite locally free modules, then the same
envelope has `Lf^*(E ⊗ ℒ)` represented by the termwise twist `P ⊗ f^*ℒ`. -/
def EnvelopePresentation.twist {E : DerivedCategory X.Modules} (H : EnvelopePresentation E)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    EnvelopePresentation (derivedTwist E L) :=
  have := isInvertible_pullback H.f L
  { Y := H.Y
    f := H.f
    envelope := H.envelope
    P := twistComplex H.P ((Scheme.Modules.pullback H.f).obj L)
    locallyBounded := isLocallyBoundedFiniteLocallyFree_twistComplex H.locallyBounded _
    representation := ⟨derivedPullbackDerivedTwistIso H.f E L ≪≫
      derivedTwistMapIso H.representation.some _ ≪≫ derivedTwistQIso H.P _⟩ }

/-- The twisted presentation lives on the same scheme. -/
@[simp]
theorem EnvelopePresentation.twist_Y {E : DerivedCategory X.Modules}
    (H : EnvelopePresentation E) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    (H.twist L).Y = H.Y :=
  rfl

/-- The twisted presentation uses the same envelope. -/
theorem EnvelopePresentation.twist_f {E : DerivedCategory X.Modules}
    (H : EnvelopePresentation E) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    (H.twist L).f = H.f :=
  rfl

/-- The complex of the twisted presentation is the termwise twist by the pullback of `ℒ`. -/
theorem EnvelopePresentation.twist_P {E : DerivedCategory X.Modules}
    (H : EnvelopePresentation E) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    (H.twist L).P = twistComplex H.P ((Scheme.Modules.pullback H.f).obj L) :=
  rfl

/-- **If the Chern classes of `E` are defined, so are those of `E ⊗ ℒ`** for an invertible
`𝒪_X`-module `ℒ`: twist an envelope presentation of `E`. -/
theorem hasDefinedChernClasses_derivedTwist {E : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    HasDefinedChernClasses (derivedTwist E L) :=
  let ⟨H⟩ := hE
  ⟨H.twist L⟩

end Envelope

/-! ### Twisting preserves perfectness -/

section Perfect

variable {X : Scheme.{u}}

/-- **`ℒ[0]` is perfect for an invertible `ℒ`**: it is a bounded complex of finite locally free
modules. -/
theorem isPerfect_singleZero (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (DerivedCategory.Q.obj (singleZero L)) := by
  refine Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_boundedFiniteLocallyFree X _
    ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · have hL : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L :=
      (isFiniteLocallyFreeOfRank_one_of_isInvertible L).isFiniteLocallyFree
    exact Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso.{u, u, u}
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).symm
  · exact Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_of_isZero X _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 L n hn)

/-- **Twisting by an invertible module preserves perfectness**: `ℒ[0]` is perfect, and the
derived tensor product of two perfect objects is perfect (Stacks 09J5). -/
theorem isPerfect_derivedTwist {E : DerivedCategory X.Modules}
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (derivedTwist E L) :=
  RingedSpace.isPerfect_canonicalDerivedTensorProduct X.toRingedSpace E _ hE
    (isPerfect_singleZero L)

end Perfect

end Stacks.Chow

end
