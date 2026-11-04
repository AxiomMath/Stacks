module

public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionSetup
public import StacksFrontier.CategoryTheory.Shift.ShiftSequenceZigzagTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# The isomorphisms of [Stacks, Tag 0A1F] on objects with quasi-coherent cohomology

In the situation of [Stacks, Tag 0DJQ] — `S` Noetherian, `f : X ⟶ S` locally of finite type,
`E` perfect, `𝒢` a bounded complex of coherent modules flat over `S` with support proper over
`S`, and `K = Rf_*(E ⊗^𝐋 𝒢)` — this file constructs, for every `M ∈ D(𝒪_S)` with quasi-coherent
cohomology and every `i`, an isomorphism

`H^i(S, K ⊗^𝐋_{𝒪_S} M) ≅ H^i(X, E ⊗^𝐋_{𝒪_X} (𝒢 ⊗^𝐋_{𝒪_X} Lf^*M))`,

natural in `M` and compatible with the connecting morphisms of every triangle whose vertices have
quasi-coherent cohomology.

## Construction

Both sides are `H^0` of a functor `D(𝒪_S) ⥤ D(Γ(S, 𝒪_S))` composed with the shift, so by
`CategoryTheory.Functor.zigzagShiftTransport` it suffices to give a zigzag of natural
transformations in degree zero, each leg invertible at objects with quasi-coherent cohomology.
Write `N = E ⊗^𝐋 𝒢` and choose a quasi-compact open `U ⊇ Z`, `ι : U ⟶ X`, `g = ι ≫ f`
(`Stacks.Cohomology.ExtProjectionSetup.exists_supportOpen`).  The common target is
`M ↦ H^0RΓ(S, Rg_*(N_U ⊗^𝐋 Lg^*M))` and the legs are

* `H^0RΓ(S, K ⊗^𝐋 M) ⟶ H^0RΓ(S, Rg_*(N_U ⊗^𝐋 Lg^*M))`, the projection formula for `g`
  (`Stacks.Cohomology.SupportedProjectionFormula.forwardLeg`);
* `H^0RΓ(X, E ⊗^𝐋 (𝒢 ⊗^𝐋 Lf^*M)) ≅ H^0RΓ(X, N ⊗^𝐋 Lf^*M) ≅ H^0RΓ(S, Rf_*(N ⊗^𝐋 Lf^*M)) ⟶
  H^0RΓ(S, Rg_*(N_U ⊗^𝐋 Lg^*M))`: associativity, Leray ([Stacks, Tag 0D5W]) and the projection
  formula for `ι` (`Stacks.Cohomology.SupportedProjectionFormula.backwardLeg`).

No compatibility of either leg with the shift is used: the connecting morphisms are compatible
because they are the degree-zero functors applied to shifted morphisms.

## Main results

* `CategoryTheory.Functor.homologySequenceδ_leftComp`: the connecting morphism of
  `π ⋙ H` at a triangle is that of `H` at the image triangle.
* `Stacks.Cohomology.ExtProjectionDegreeIso.degreeIso`, its naturality `degreeIso_naturality`
  and `degreeIso_comp_homologySequenceδ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Pretriangulated
open StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedSectionsOverOpen derivedPreimageSections derivedSectionsPushforwardIso)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.SupportedProjectionFormula
  (DX HasQuasicoherentCohomology legTarget forwardLeg backwardLeg)

universe u

namespace Stacks.Cohomology.ExtProjectionDegreeIso

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
  (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)

/-- `N = E ⊗^𝐋 𝒢`. -/
abbrev Nobj : DX X := Stacks.Cohomology.ExtProjectionFormula.derivedTensorG E G

/-- `K = Rf_*N`. -/
abbrev Kobj : DX S := (derivedPushforward f.toLRSHom.toShHom).obj (Nobj E G)

/-- Global sections over `S`, valued in `Γ(S, 𝒪_S)`-modules. -/
abbrev sectionsS :
    DX S ⥤ DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤))) :=
  derivedSectionsOverOpen S.toRingedSpace ⊤

/-- `H^0` on `D(Γ(S, 𝒪_S))`. -/
abbrev H0 := DerivedCategory.homologyFunctor
  (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤))) 0

/-- **The left-hand side before `H^0`**: `M ↦ RΓ(S, K ⊗^𝐋 M)`. -/
abbrev baseSide :
    DX S ⥤ DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤))) :=
  (derivedTensorProductFunctor S.toRingedSpace.sheaf).obj (Kobj f E G) ⋙ sectionsS (S := S)

/-- `M ↦ 𝒢 ⊗^𝐋 Lf^*M`, the source of the flat identification of [Stacks, Tag 08DE]. -/
abbrev pullbackTensorG : DX S ⥤ DX X :=
  derivedPullback f.toLRSHom.toShHom ⋙
    (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (DerivedCategory.Q.obj G)

/-- **The right-hand side before `H^0`**: `M ↦ RΓ(X, E ⊗^𝐋 (𝒢 ⊗^𝐋 Lf^*M))`, read as a complex of
`Γ(S, 𝒪_S)`-modules. -/
abbrev sourceSide :
    DX S ⥤ DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤))) :=
  pullbackTensorG f G ⋙ (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E ⋙
    derivedPreimageSections f.toLRSHom.toShHom ⊤

/-- The associator `(E ⊗^𝐋 𝒢) ⊗^𝐋 L ≅ E ⊗^𝐋 (𝒢 ⊗^𝐋 L)`. -/
abbrev assocIso (L : DX X) :=
  Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator X.toRingedSpace.sheaf
    (canonicalDerivedTensorProduct X.toRingedSpace.sheaf) E (DerivedCategory.Q.obj G) L

variable (U : X.Opens) {T : Set X} (hT : IsClosed T) (hTU : T ⊆ U)
  (hN : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
    (structureSheafRing X.toRingedSpace) T (Nobj E G))

/-- The common target of the two legs: `M ↦ H^0RΓ(S, Rg_*(N_U ⊗^𝐋 Lg^*M))`. -/
abbrev legTargetH0 := legTarget f U (Nobj E G) ⋙ sectionsS (S := S) ⋙ H0 (S := S)

include hT hTU hN in
/-- **The first leg**: `H^0RΓ(S, K ⊗^𝐋 M) ⟶ H^0RΓ(S, Rg_*(N_U ⊗^𝐋 Lg^*M))`. -/
def alphaLeg : baseSide f E G ⋙ H0 (S := S) ⟶ legTargetH0 f E G U :=
  Functor.whiskerRight (forwardLeg f U hT hTU (Nobj E G) hN) (sectionsS (S := S) ⋙ H0 (S := S))

/-- **Associativity as an isomorphism of functors**:
`(E ⊗^𝐋 𝒢) ⊗^𝐋 - ≅ E ⊗^𝐋 (𝒢 ⊗^𝐋 -)`. -/
def assocNatIso :
    (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (Nobj E G) ≅
      (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (DerivedCategory.Q.obj G) ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E :=
  NatIso.ofComponents (fun L => assocIso E G L) (fun φ =>
    Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_right
      X.toRingedSpace.sheaf (canonicalDerivedTensorProduct X.toRingedSpace.sheaf) E
      (DerivedCategory.Q.obj G) φ)

/-- First factor of the second leg: associativity, `E ⊗^𝐋 (𝒢 ⊗^𝐋 L) ≅ (E ⊗^𝐋 𝒢) ⊗^𝐋 L`. -/
def betaLegAssoc :
    sourceSide f E G ⟶
      (derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (Nobj E G)) ⋙
          derivedPreimageSections f.toLRSHom.toShHom ⊤ :=
  Functor.whiskerLeft (derivedPullback f.toLRSHom.toShHom)
    (Functor.whiskerRight (assocNatIso E G).inv (derivedPreimageSections f.toLRSHom.toShHom ⊤))

/-- Second factor of the second leg: Leray, `RΓ(X, -) ≅ RΓ(S, Rf_*(-))` ([Stacks, Tag 0D5W]). -/
def betaLegLeray :
    (derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (Nobj E G)) ⋙
          derivedPreimageSections f.toLRSHom.toShHom ⊤ ⟶
      (derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (Nobj E G) ⋙
          derivedPushforward f.toLRSHom.toShHom) ⋙ sectionsS (S := S) :=
  Functor.whiskerLeft (derivedPullback f.toLRSHom.toShHom ⋙
      (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (Nobj E G))
    (derivedSectionsPushforwardIso f.toLRSHom.toShHom ⊤).inv

include hT hTU hN in
/-- The second leg before `H^0`, at `𝒢 ⊗^𝐋 Lf^*(-)`: associativity, Leray and the projection
formula for `ι`. -/
def betaLegSections : sourceSide f E G ⟶ legTarget f U (Nobj E G) ⋙ sectionsS (S := S) :=
  betaLegAssoc f E G ≫ betaLegLeray f E G ≫
    Functor.whiskerRight (backwardLeg f U hT hTU (Nobj E G) hN) (sectionsS (S := S))

/-! ### The right-hand side through a model of `𝒢 ⊗^𝐋 Lf^*(-)`

The right-hand side is written through a functor `R : D(𝒪_S) ⥤ D(𝒪_X)` with a shift structure
and an isomorphism `R ≅ 𝒢 ⊗^𝐋 Lf^*(-)`; the shift structure of `R` is the one the connecting
morphisms are taken with. -/

/-- `D(𝒪_Y)` at the spelling of the derived tensor product, the domain of `K ⊗^𝐋 -`. -/
abbrev DT (Y : Scheme.{u}) := Stacks.DerivedTensor.RingedSite.DerivedModules Y.toRingedSpace.sheaf

variable (R : DT S ⥤ DT X) [R.CommShift ℤ] (μ : R ≅ pullbackTensorG f G)

/-- `RΓ(X, E ⊗^𝐋 -)`, read as complexes of `Γ(S, 𝒪_S)`-modules. -/
abbrev sourceSections :=
  (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E ⋙
    derivedPreimageSections f.toLRSHom.toShHom ⊤

/-- **The right-hand side through `R`, before `H^0`**: `M ↦ RΓ(X, E ⊗^𝐋 R(M))`. -/
abbrev sourceSideR :
    DX S ⥤ DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤))) :=
  R ⋙ sourceSections f E

include hT hTU hN in
/-- **The second leg**: `H^0RΓ(X, E ⊗^𝐋 R(M)) ≅ H^0RΓ(X, E ⊗^𝐋 (𝒢 ⊗^𝐋 Lf^*M)) ⟶
H^0RΓ(S, Rg_*(N_U ⊗^𝐋 Lg^*M))`. -/
def betaLeg : sourceSideR f E R ⋙ H0 (S := S) ⟶ legTargetH0 f E G U :=
  Functor.whiskerRight
    (Functor.whiskerRight μ.hom (sourceSections f E) ≫ betaLegSections f E G U hT hTU hN)
    (H0 (S := S))

/-! ### Invertibility of the legs -/

/-- Objects with quasi-coherent cohomology are stable under shifts. -/
theorem hasQuasicoherentCohomology_shift {Y : Scheme.{u}} {M : DX Y}
    (hM : HasQuasicoherentCohomology M) (n : ℤ) : HasQuasicoherentCohomology (M⟦n⟧) := fun j =>
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor _ 0).shiftIso n j (n + j) rfl).app M).symm (hM (n + j))

variable [QuasiCompact U.ι] [QuasiSeparated U.ι] [QuasiCompact (U.ι ≫ f)]
  [QuasiSeparated (U.ι ≫ f)] (hNq : HasQuasicoherentCohomology (Nobj E G))

omit [QuasiCompact U.ι] [QuasiSeparated U.ι] in
include hNq in
/-- The first leg is invertible at every `M` with quasi-coherent cohomology. -/
theorem isIso_alphaLeg_app (M : DX S) (hM : HasQuasicoherentCohomology M) :
    IsIso ((alphaLeg f E G U hT hTU hN).app M) := by
  have := Stacks.Cohomology.SupportedProjectionFormula.isIso_forwardLeg_app f U hT hTU hN hNq M hM
  dsimp only [alphaLeg, Functor.whiskerRight_app]
  infer_instance

omit [R.CommShift ℤ] [QuasiCompact (U.ι ≫ f)] [QuasiSeparated (U.ι ≫ f)] in
include hNq in
/-- The second leg is invertible at every `M` with quasi-coherent cohomology. -/
theorem isIso_betaLeg_app (M : DX S) (hM : HasQuasicoherentCohomology M) :
    IsIso ((betaLeg f E G U hT hTU hN R μ).app M) := by
  have := Stacks.Cohomology.SupportedProjectionFormula.isIso_backwardLeg_app f U hT hTU hN hNq M hM
  have hμ : IsIso ((Functor.whiskerRight μ.hom (sourceSections f E)).app M) :=
    ((sourceSections f E).mapIso (μ.app M)).isIso_hom
  dsimp only [betaLeg, betaLegSections, betaLegAssoc, betaLegLeray, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-! ### The degree-`i` morphisms -/

/-- `H^0(S, -)` with its shift sequence `H^n(S, -)`. -/
abbrev baseCohomology := sectionsS (S := S) ⋙ H0 (S := S)

/-- `H^0(X, E ⊗^𝐋 -)` with its shift sequence `H^n(X, E ⊗^𝐋 -)`, as `Γ(S, 𝒪_S)`-modules. -/
abbrev sourceCohomology := sourceSections f E ⋙ H0 (S := S)

/-- The common target of the two legs, as a functor on `D(𝒪_S)` at the spelling of the derived
tensor product. -/
abbrev legTargetT : DT S ⥤ ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤)) :=
  legTargetH0 f E G U

/-- `K ⊗^𝐋 -`, at the spelling of the derived tensor product. -/
abbrev tensorK : DT S ⥤ DT S := (derivedTensorProductFunctor S.toRingedSpace.sheaf).obj (Kobj f E G)

/-- The first leg, as a transformation of functors on `DT S`. -/
def alphaT : tensorK f E G ⋙ baseCohomology (S := S) ⟶ legTargetT f E G U :=
  alphaLeg f E G U hT hTU hN

/-- The second leg, as a transformation of functors on `DT S`. -/
def betaT : R ⋙ sourceCohomology f E ⟶ legTargetT f E G U :=
  betaLeg f E G U hT hTU hN R μ

omit [R.CommShift ℤ] [QuasiCompact (U.ι ≫ f)] [QuasiSeparated (U.ι ≫ f)] in
include hNq in
/-- `betaT` is invertible at every `M` with quasi-coherent cohomology. -/
theorem isIso_betaT_app (M : DT S) (hM : HasQuasicoherentCohomology (M : DX S)) :
    IsIso ((betaT f E G U hT hTU hN R μ).app M) :=
  isIso_betaLeg_app f E G U hT hTU hN R μ hNq M hM

omit [QuasiCompact U.ι] [QuasiSeparated U.ι] in
include hNq in
/-- `alphaT` is invertible at every `M` with quasi-coherent cohomology. -/
theorem isIso_alphaT_app (M : DT S) (hM : HasQuasicoherentCohomology (M : DX S)) :
    IsIso ((alphaT f E G U hT hTU hN).app M) :=
  isIso_alphaLeg_app f E G U hT hTU hN hNq M hM

/-- **The degree-`i` morphism** `H^i(S, K ⊗^𝐋 M) ⟶ H^i(X, E ⊗^𝐋 R(M))`, at an object `M` at which
the second leg is invertible after shifting by `i`. -/
def degreeMap (i : ℤ) (M : DT S) (hM : IsIso ((betaT f E G U hT hTU hN R μ).app (M⟦i⟧))) :
    ((baseCohomology (S := S)).shift i).obj ((tensorK f E G).obj M) ⟶
      ((sourceCohomology f E).shift i).obj (R.obj M) :=
  haveI := hM
  Functor.compZigzagTransport (tensorK f E G) (baseCohomology (S := S)) R (sourceCohomology f E)
    (alphaT f E G U hT hTU hN) (betaT f E G U hT hTU hN R μ) i M

omit [QuasiCompact U.ι] [QuasiSeparated U.ι] [QuasiCompact (U.ι ≫ f)]
  [QuasiSeparated (U.ι ≫ f)] in
/-- The degree-`i` morphism at `M` is an isomorphism when both legs are invertible at `M⟦i⟧`. -/
theorem isIso_degreeMap (i : ℤ) (M : DT S) (hα : IsIso ((alphaT f E G U hT hTU hN).app (M⟦i⟧)))
    (hM : IsIso ((betaT f E G U hT hTU hN R μ).app (M⟦i⟧))) :
    IsIso (degreeMap f E G U hT hTU hN R μ i M hM) :=
  Functor.isIso_compZigzagTransport _ _ _ _ _ _ i M

omit [QuasiCompact U.ι] [QuasiSeparated U.ι] [QuasiCompact (U.ι ≫ f)]
  [QuasiSeparated (U.ι ≫ f)] in
/-- The degree-`i` morphisms are natural in `M`. -/
theorem degreeMap_naturality (i : ℤ) {M M' : DT S} (φ : M ⟶ M')
    (hM : IsIso ((betaT f E G U hT hTU hN R μ).app (M⟦i⟧)))
    (hM' : IsIso ((betaT f E G U hT hTU hN R μ).app (M'⟦i⟧))) :
    ((baseCohomology (S := S)).shift i).map ((tensorK f E G).map φ) ≫
        degreeMap f E G U hT hTU hN R μ i M' hM' =
      degreeMap f E G U hT hTU hN R μ i M hM ≫ ((sourceCohomology f E).shift i).map (R.map φ) :=
  Functor.compZigzagTransport_naturality (tensorK f E G) (baseCohomology (S := S)) R
    (sourceCohomology f E) (alphaT f E G U hT hTU hN) (betaT f E G U hT hTU hN R μ) i φ

omit [QuasiCompact U.ι] [QuasiSeparated U.ι] [QuasiCompact (U.ι ≫ f)]
  [QuasiSeparated (U.ι ≫ f)] in
/-- **The degree-`i` morphisms commute with the connecting morphisms** of `H^*(S, -)` at the image
under `K ⊗^𝐋 -` of a triangle, and of `H^*(X, E ⊗^𝐋 -)` at its image under `R`. -/
theorem degreeMap_comp_homologySequenceδ (T : Triangle (DT S)) (i j : ℤ) (h : i + 1 = j)
    (h₃ : IsIso ((betaT f E G U hT hTU hN R μ).app (T.obj₃⟦i⟧)))
    (h₁ : IsIso ((betaT f E G U hT hTU hN R μ).app (T.obj₁⟦j⟧))) :
    degreeMap f E G U hT hTU hN R μ i T.obj₃ h₃ ≫
        (sourceCohomology f E).homologySequenceδ (R.mapTriangle.obj T) i j h =
      (baseCohomology (S := S)).homologySequenceδ ((tensorK f E G).mapTriangle.obj T) i j h ≫
        degreeMap f E G U hT hTU hN R μ j T.obj₁ h₁ :=
  Functor.compZigzagTransport_comp_homologySequenceδ (tensorK f E G) (baseCohomology (S := S)) R
    (sourceCohomology f E) (alphaT f E G U hT hTU hN) (betaT f E G U hT hTU hN R μ) T i j h

end Stacks.Cohomology.ExtProjectionDegreeIso

end
