module

public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionFormulaBoundary
public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionFormulaQuasiCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualExtTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHomFunctorial
import StacksCore.Tactic.StacksAttribute

/-!
# A projection formula for `Ext`, with boundary maps

Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of finite type, `E` a perfect object
of `D(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with support
proper over `S` — the situation of [Stacks, Tag 0DJR], with `K = Rf_* RSheafHom(E, 𝒢)`.
[Stacks, Tag 08ID] asserts isomorphisms

`H^i(S, K ⊗^L_{𝒪_S} ℱ) ⟶ Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`,

functorial in the quasi-coherent `𝒪_S`-module `ℱ` and compatible with the boundary maps of short
exact sequences of quasi-coherent modules.  This file proves it, with
`Ext^i_{𝒪_X}(E, N) = Hom_{D(𝒪_X)}(E, N[i])` and with the boundary map on the right the Yoneda
composition with the connecting morphism of the distinguished triangle of the short exact
sequence of complexes `0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0`.

## Main results

* `Stacks.Cohomology.ExtPerfectProjection.sheafHomIsoTensorDual`: `RSheafHom(E, 𝒢) ≅ E^∨ ⊗^L 𝒢`
  ([Stacks, Tag 08DQ]).
* `Stacks.Cohomology.ExtPerfectProjection.extIso_qcoh_boundary`: **[Stacks, Tag 08ID]**.

## Implementation notes

The proof is the source's: with `E^∨` the dual of [Stacks, Tag 08DQ],
`K = Rf_* RSheafHom(E, 𝒢) ≅ Rf_*(E^∨ ⊗^L 𝒢)`, and
`Ext^i(E, N) ≅ H^i(X, E^∨ ⊗^L N)`, so the assertion is [Stacks, Tag 0A1F] applied to `E^∨` and
`𝒢` (`Stacks.Cohomology.ExtProjectionFormulaBoundary.extCohomologyIso_qcoh_boundary`).  The two
rewrites are made compatible with connecting morphisms by producing the degree-`i` isomorphisms
from degree-zero ones evaluated at shifted objects
(`CategoryTheory.Functor.shiftSequenceTransport`): the first from `K ≅ Rf_*(E^∨ ⊗^L 𝒢)`, the second
from the fourth assertion of [Stacks, Tag 08DQ], `H⁰(X, M ⊗^L E^∨) = Hom(E, M)`
(`Stacks.Cohomology.PerfectDualExt.extIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Pretriangulated StrictlyPerfect
open Stacks.Cohomology.ExtProjectionDegreeIso (Kobj Nobj tensorK sectionsS H0 sourceSections DT)
open Stacks.Cohomology.ExtProjectionAssembly (ModS qcModules Ψ)

universe u

namespace Stacks.Cohomology.ExtPerfectProjection

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
  (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)

/-- **`RSheafHom(E, 𝒢) ≅ E^∨ ⊗^L 𝒢` for a perfect `E`**: the third assertion of
[Stacks, Tag 08DQ] at `𝒢`, read through the commutativity of the derived tensor product. -/
def sheafHomIsoTensorDual
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    Stacks.Cohomology.PerfectInternalHomPushforward.derivedSheafHomObj (X := X) E G ≅
      Nobj (X := X) (Stacks.Cohomology.PerfectDualExt.dual (X := X.toRingedSpace) E) G :=
  ((Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace X.toRingedSpace E hE).app
      (DerivedCategory.Q.obj G)).symm ≪≫
    ((Stacks.Cohomology.PerfectDualExt.tensorSwapIso
      (Stacks.Cohomology.PerfectDualExt.dual (X := X.toRingedSpace) E)).app
      (DerivedCategory.Q.obj G)).symm

/-- `K = Rf_* RSheafHom(E, 𝒢) ≅ Rf_*(E^∨ ⊗^L 𝒢)`. -/
def pushforwardKIso (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.sheafHomPushforwardK (X := X) f E G ≅
      Kobj f (Stacks.Cohomology.PerfectDualExt.dual (X := X.toRingedSpace) E) G :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom).mapIso
    (sheafHomIsoTensorDual E G hE)

/-- `K ⊗^L -` on `D(𝒪_S)`, for `K = Rf_* RSheafHom(E, 𝒢)`. -/
abbrev tensorSheafHomK : DT S ⥤ DT S :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
    (Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.sheafHomPushforwardK (X := X) f E G)

/-- `K ⊗^L - ≅ K' ⊗^L -` for `K' = Rf_*(E^∨ ⊗^L 𝒢)`. -/
def tensorKIso (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    tensorSheafHomK f E G ≅
      tensorK f (Stacks.Cohomology.PerfectDualExt.dual (X := X.toRingedSpace) E) G :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.toRingedSpace.sheaf).mapIso
    (pushforwardKIso f E G hE)

/-- The isomorphism `K ⊗^L - ≅ K' ⊗^L -` commutes with the shift by `ℤ`. -/
instance natTransCommShift_tensorKIso_hom
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    NatTrans.CommShift (tensorKIso f E G hE).hom ℤ :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    S.toRingedSpace.sheaf).commShift₂.commShift_map (pushforwardKIso f E G hE).hom

/-- **`K ⊗^L - ≅ K' ⊗^L -` is compatible with the connecting morphisms of `H^i(S, -)`**: for every
triangle `T` of `D(𝒪_S)` the connecting morphisms of `H⁰ ∘ RΓ(S, -)` at the images of `T` under
`K ⊗^L -` and `K' ⊗^L -` correspond.  The isomorphism commutes with the shift because the derived
tensor product commutes with the shift in both variables ([Stacks, Tag 06YU]). -/
theorem tensorKIso_homologySequenceδ
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (T : Triangle (DT S)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (H0 (S := S)).homologySequenceδ ((sectionsS (S := S)).mapTriangle.obj
        ((tensorSheafHomK f E G).mapTriangle.obj T)) n₀ n₁ h ≫
      (DerivedCategory.homologyFunctor _ n₁).map ((sectionsS (S := S)).map
        ((tensorKIso f E G hE).hom.app T.obj₁)) =
    (DerivedCategory.homologyFunctor _ n₀).map ((sectionsS (S := S)).map
        ((tensorKIso f E G hE).hom.app T.obj₃)) ≫
      (H0 (S := S)).homologySequenceδ ((sectionsS (S := S)).mapTriangle.obj
        ((tensorK f (Stacks.Cohomology.PerfectDualExt.dual (X := X.toRingedSpace) E)
          G).mapTriangle.obj T)) n₀ n₁ h :=
  ((H0 (S := S)).homologySequenceδ_naturality ((sectionsS (S := S)).mapTriangle.map
    ((Functor.mapTriangleIso (tensorKIso f E G hE)).hom.app T)) n₀ n₁ h).symm

open Stacks.Cohomology.PerfectDualExt (forgetLift extIso extIso_hom_app_comp_homologySequenceδ)

/-- **[Stacks, Tag 08ID], as isomorphisms of functors.**  For every `i` an isomorphism, natural
in the quasi-coherent `𝒪_S`-module `ℱ`, from `H^i(S, K ⊗^L ℱ)` (with its scalars forgotten and
lifted to the universe of morphisms of `D(𝒪_X)`) to `Hom_{D(𝒪_X)}(E, (𝒢 ⊗ f^*ℱ)[i])`, carrying the
connecting morphisms of a short exact sequence of quasi-coherent modules on the left to Yoneda
composition with the connecting morphism of the triangle of
`0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0` on the right. -/
theorem exists_extIso_functor [IsNoetherian S] [LocallyOfFiniteType f]
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : PerfectPushforward.FlatProperSupportComplex f G) :
    ∃ Φ : ∀ i : ℤ, (qcModules S).ι ⋙ DerivedCategory.singleFunctor (ModS S) 0 ⋙
          tensorSheafHomK f E G ⋙ sectionsS (S := S) ⋙ DerivedCategory.homologyFunctor _ i ⋙
          forgetLift (Y := S.toRingedSpace) ≅
        (qcModules S).ι ⋙ Ψ f G ⋙ DerivedCategory.Q ⋙ shiftFunctor _ i ⋙
          preadditiveCoyoneda.obj (op E),
      ∀ (T : ShortComplex (ModS S)) (hT : T.ShortExact) (h₁ : qcModules S T.X₁)
        (h₃ : qcModules S T.X₃) (i : ℤ),
        (Φ i).hom.app ⟨T.X₃, h₃⟩ ≫
          (preadditiveCoyoneda.obj (op E)).homologySequenceδ
            (DerivedCategory.triangleOfSES
              (Stacks.Cohomology.ExtProjectionFormulaBoundary.shortExact_Ψ f G hG T hT))
            i (i + 1) rfl =
        (forgetLift (Y := S.toRingedSpace)).map ((H0 (S := S)).homologySequenceδ
            ((sectionsS (S := S)).mapTriangle.obj
              ((tensorSheafHomK f E G).mapTriangle.obj hT.singleTriangle)) i (i + 1) rfl) ≫
          (Φ (i + 1)).hom.app ⟨T.X₁, h₁⟩ := by
  have hE' : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E := hE
  have hD : RingedSpace.IsPerfect (X := X.toRingedSpace)
      (Stacks.Cohomology.PerfectDualExt.dual (X := X.toRingedSpace) E) :=
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace E hE'
  obtain ⟨Φ', hΦ'⟩ := Stacks.Cohomology.ExtProjectionFormulaBoundary.extCohomologyIso_qcoh_boundary
    f (Stacks.Cohomology.PerfectDualExt.dual (X := X.toRingedSpace) E) G hD hG
  refine ⟨fun i =>
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft ((qcModules S).ι ⋙ DerivedCategory.singleFunctor (ModS S) 0)
        (Functor.isoWhiskerRight (tensorKIso f E G hE')
          (sectionsS (S := S) ⋙ DerivedCategory.homologyFunctor _ i)) ≪≫ Φ' i)
      (forgetLift (Y := S.toRingedSpace)) ≪≫
    Functor.isoWhiskerLeft ((qcModules S).ι ⋙ Ψ f G ⋙ DerivedCategory.Q)
      (extIso f.toLRSHom.toShHom E hE' i), ?_⟩
  intro T hT h₁ h₃ i
  have hβ := extIso_hom_app_comp_homologySequenceδ f.toLRSHom.toShHom E hE'
    (DerivedCategory.triangleOfSES
      (Stacks.Cohomology.ExtProjectionFormulaBoundary.shortExact_Ψ f G hG T hT)) i (i + 1) rfl
  rw [Functor.homologySequenceδ_leftComp] at hβ
  have h3 := hΦ' T hT h₁ h₃ i
  have h4 := tensorKIso_homologySequenceδ f E G hE' hT.singleTriangle i (i + 1) rfl
  have inner := (Category.assoc _ _ _).trans ((whisker_eq _ h3).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker h4.symm _).trans (Category.assoc _ _ _))))
  have step := ((forgetLift (Y := S.toRingedSpace)).map_comp _ _).symm.trans
    ((congrArg (forgetLift (Y := S.toRingedSpace)).map inner).trans
      ((forgetLift (Y := S.toRingedSpace)).map_comp _ _))
  exact (Category.assoc _ _ _).trans ((whisker_eq _ hβ).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker step _).trans (Category.assoc _ _ _))))

/-- **[Stacks, Tag 08ID].**  Let `S` be a Noetherian scheme, `f : X ⟶ S` locally of finite type,
`E` a perfect object of `D(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over
`S`, with support proper over `S`, and let `K = Rf_* RSheafHom(E, 𝒢)` as in [Stacks, Tag 0DJR].
Then there are isomorphisms

`Φᵢ : H^i(S, K ⊗^L_{𝒪_S} ℱ) ⟶ Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ) = Hom_{D(𝒪_X)}(E, (𝒢 ⊗ f^*ℱ)[i])`,

functorial in the quasi-coherent `𝒪_S`-module `ℱ` (a natural isomorphism of functors on
quasi-coherent modules for every `i`), compatible with boundary maps: for a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_S`-modules with `ℱ₁`, `ℱ₃` quasi-coherent and every class `y` in
`H^i(S, K ⊗^L ℱ₃)`,

`Φᵢ₊₁(∂ y) = Φᵢ(y) ∘ δ`,

where `∂ : H^i(S, K ⊗^L ℱ₃) ⟶ H^{i+1}(S, K ⊗^L ℱ₁)` is the connecting morphism of the
distinguished triangle `K ⊗^L ℱ₁ → K ⊗^L ℱ₂ → K ⊗^L ℱ₃ → (K ⊗^L ℱ₁)[1]` (the image under
`K ⊗^L -` of the triangle of the sequence) and `δ : 𝒢 ⊗ f^*ℱ₃ ⟶ (𝒢 ⊗ f^*ℱ₁)[1]` is the
connecting morphism of the distinguished triangle of the short exact sequence of complexes
`0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0`, composed as an element of `Ext¹`.

`H^i(S, -)` is the `i`-th cohomology of the unbounded derived global sections; it is a group of
`Γ(S, 𝒪_S)`-modules, read as an abelian group and lifted to the universe of the morphism groups of
`D(𝒪_X)`.  `f^*` is the pullback of modules and `𝒢 ⊗ f^*ℱ` the complex with terms
`𝒢^p ⊗ f^*ℱ`. -/
@[stacks 08ID "the functorial isomorphisms for every i, Ext^i read as Hom_{D(O_X)}(E, -[i]), and \
their compatibility with the boundary maps of every short exact sequence of quasi-coherent \
modules (with ℱ₂ an arbitrary O_S-module): the class of a boundary is the Yoneda composite \
with the connecting morphism of the triangle of 0 → G ⊗ f^*F₁ → G ⊗ f^*F₂ → G ⊗ f^*F₃ → 0; \
H^i(S, -) is H^i of unbounded RΓ(S, -) with its Γ(S, O_S)-module structure forgotten"]
theorem extIso_qcoh_boundary [IsNoetherian S] [LocallyOfFiniteType f]
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : PerfectPushforward.FlatProperSupportComplex f G) :
    ∃ Φ : ∀ i : ℤ, (qcModules S).ι ⋙ DerivedCategory.singleFunctor (ModS S) 0 ⋙
          tensorSheafHomK f E G ⋙ sectionsS (S := S) ⋙ DerivedCategory.homologyFunctor _ i ⋙
          forgetLift (Y := S.toRingedSpace) ≅
        (qcModules S).ι ⋙ Ψ f G ⋙ DerivedCategory.Q ⋙ shiftFunctor _ i ⋙
          preadditiveCoyoneda.obj (op E),
      ∀ (T : ShortComplex (ModS S)) (hT : T.ShortExact) (h₁ : qcModules S T.X₁)
        (h₃ : qcModules S T.X₃) (i : ℤ)
        (y : ((qcModules S).ι ⋙ DerivedCategory.singleFunctor (ModS S) 0 ⋙
          tensorSheafHomK f E G ⋙ sectionsS (S := S) ⋙ DerivedCategory.homologyFunctor _ i ⋙
          forgetLift (Y := S.toRingedSpace)).obj ⟨T.X₃, h₃⟩),
        (Φ (i + 1)).hom.app ⟨T.X₁, h₁⟩
            ((forgetLift (Y := S.toRingedSpace)).map ((H0 (S := S)).homologySequenceδ
              ((sectionsS (S := S)).mapTriangle.obj
                ((tensorSheafHomK f E G).mapTriangle.obj hT.singleTriangle)) i (i + 1) rfl) y) =
          ((Φ i).hom.app ⟨T.X₃, h₃⟩ y : E ⟶ _) ≫
            (DerivedCategory.triangleOfSESδ
              (Stacks.Cohomology.ExtProjectionFormulaBoundary.shortExact_Ψ f G hG T hT))⟦i⟧' ≫
            (shiftFunctorAdd' _ 1 i (i + 1) (by omega)).inv.app _ := by
  obtain ⟨Φ, hΦ⟩ := exists_extIso_functor f E G hE hG
  refine ⟨Φ, fun T hT h₁ h₃ i y => ?_⟩
  have h := ConcreteCategory.congr_hom (hΦ T hT h₁ h₃ i) y
  exact h.symm.trans (preadditiveCoyoneda_homologySequenceδ_apply _ i (i + 1) rfl _)

end Stacks.Cohomology.ExtPerfectProjection

end
