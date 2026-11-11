module

public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.DerivedPullbackTensorFlat
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartConsequences

/-!
# `f^!` of a Cohen–Macaulay morphism of constant relative dimension

Let `S` be Noetherian and `f : X ⟶ Y` a Cohen–Macaulay morphism of `AlgebraicGeometry.FTS S`
of relative dimension `d`. Then `f^!𝒪_Y` has a single nonzero cohomology sheaf
`ω_{X/Y} = H^{-d}(f^!𝒪_Y)` and `f^!𝒪_Y ≅ ω_{X/Y}[d]` ([Stacks, Tag 0BV8]); combined with
`f^!K ≅ Lf^*K ⊗ᴸ f^!𝒪_Y` ([Stacks, Tag 0B6U] (e)) this gives `f^!K ≅ Lf^*K ⊗ᴸ ω_{X/Y}[d]`,
which is the content of [Stacks, Tag 0C10].

## Main definitions

* `Stacks.Duality.relativeDualizingSheaf` — `ω_{X/Y} = H^{-d}(f^!𝒪_Y)`.
* `Stacks.Duality.relativeDualizingSheafShift` — `ω_{X/Y}[d]` as an object of `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.isZero_homology_relativeDualizingComplexObj_of_ne` — `H^i(f^!𝒪_Y) = 0` for
  `i ≠ -d`.
* `Stacks.Duality.nonempty_relativeDualizingComplexObj_iso_shift` — `f^!𝒪_Y ≅ ω_{X/Y}[d]`.
* `Stacks.Duality.exists_homology_upperShriek_comp_iso_pullback_tensor_of_iso` — given `μ_{f,K}`
  and that `ω_Y^•` is dualizing on a connected Cohen–Macaulay `Y`:
  `ω_X = f^*ω_Y ⊗ ω_{X/Y}` for the unique nonzero cohomology sheaves.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open DerivedPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- The relative dualizing sheaf `ω_{X/Y} = H^{-d}(f^!𝒪_Y)` of a morphism of `FTS S` in
relative dimension `d`, with `f^!` computed at the compactification `j`. -/
abbrev relativeDualizingSheaf (d : ℕ) : X.left.Modules :=
  (DerivedCategory.homologyFunctor X.left.Modules (-(d : ℤ))).obj (relativeDualizingComplexObj f j)

/-- For a Cohen–Macaulay morphism of relative dimension `d` the cohomology sheaves of `f^!𝒪_Y`
vanish outside degree `-d`. -/
theorem isZero_homology_relativeDualizingComplexObj_of_ne
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    (i : ℤ) (hi : i ≠ -(d : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (relativeDualizingComplexObj f j)) := by
  have h := (isCohenMacaulay_iff_flat_and_fibers f.left (isLocallyNoetherian_fiber_left f)).mp hCM
  have : Flat f.left := h.1
  have := locallyOfFinitePresentation_left f
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun x => ?_
  have hx : x ∈ relativeDimensionOpen f.left h.2 d := by
    rw [mem_relativeDimensionOpen]
    exact_mod_cast (relativeDimensionFunction_apply f.left h.2 x).symm.trans (hd x)
  exact Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict _ _ x hx
    (isZero_restrict_homology_relativeDimensionOpen (upperShriekStructureSheafCharts f j) hCM h.2
      d i hi)

/-- **`f^!𝒪_Y ≅ ω_{X/Y}[d]`** for a Cohen–Macaulay morphism of relative dimension `d`: the
complex `f^!𝒪_Y` is concentrated in degree `-d`. The isomorphism `L = f^!𝒪_Y[-d] ≅ M[0]` with a
complex in degree `0` is chosen, and `M` is then identified with `H⁰(L) = ω_{X/Y}` through the
cohomology of that same isomorphism, so the composite `L ≅ H⁰(L)[0]` induces the identity on
`H⁰`. -/
def relativeDualizingComplexObjIsoShift
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞)) :
    relativeDualizingComplexObj f j ≅
      ((DerivedCategory.singleFunctor X.left.Modules 0).obj (relativeDualizingSheaf f j d))⟦
        (d : ℤ)⟧ := by
  let E := relativeDualizingComplexObj f j
  let L := E⟦-(d : ℤ)⟧
  have hzL : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj L) := fun i hi =>
    (isZero_homology_relativeDualizingComplexObj_of_ne f j hCM d hd (i + -(d : ℤ))
      (by omega)).of_iso (Dualizing.homologyShiftObjIso E i (-(d : ℤ)))
  have : L.IsGE 0 := (DerivedCategory.isGE_iff L 0).2 fun i hi => hzL i (by omega)
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 fun i hi => hzL i (by omega)
  let hM := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L 0
  let M := hM.choose
  let eL : L ≅ (DerivedCategory.singleFunctor X.left.Modules 0).obj M := hM.choose_spec.some
  let eM : M ≅ relativeDualizingSheaf f j d :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.left.Modules 0).app M).symm ≪≫
      (DerivedCategory.homologyFunctor X.left.Modules 0).mapIso eL.symm ≪≫
      Dualizing.homologyShiftObjIso E 0 (-(d : ℤ)) ≪≫
      eqToIso (congrArg (fun n => (DerivedCategory.homologyFunctor X.left.Modules n).obj E)
        (zero_add _))
  exact ((shiftFunctorCompIsoId _ (-(d : ℤ)) (d : ℤ) (by omega)).app E).symm ≪≫
    (shiftFunctor _ (d : ℤ)).mapIso (eL ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eM)

/-- **`f^!𝒪_Y ≅ ω_{X/Y}[d]`** for a Cohen–Macaulay morphism of relative dimension `d`: the
complex `f^!𝒪_Y` is concentrated in degree `-d`. -/
theorem nonempty_relativeDualizingComplexObj_iso_shift
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞)) :
    Nonempty (relativeDualizingComplexObj f j ≅
      ((DerivedCategory.singleFunctor X.left.Modules 0).obj (relativeDualizingSheaf f j d))⟦
        (d : ℤ)⟧) :=
  ⟨relativeDualizingComplexObjIsoShift f j hCM d hd⟩

/-- `ω_{X/Y}[d]` as an object of `D_QCoh(𝒪_X)`, for a Cohen–Macaulay morphism of relative
dimension `d`; its cohomology is quasi-coherent because it is isomorphic to `f^!𝒪_Y`. -/
def relativeDualizingSheafShift
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞)) :
    quasiCoherentDerivedCategory X.left :=
  ⟨((DerivedCategory.singleFunctor X.left.Modules 0).obj (relativeDualizingSheaf f j d))⟦
      (d : ℤ)⟧, fun i => by
    obtain ⟨e⟩ := nonempty_relativeDualizingComplexObj_iso_shift f j hCM d hd
    exact (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.left.Modules i).mapIso e)
      (((upperShriek f j).obj (derivedStructureSheaf Y.left)).property i)⟩

/-- The isomorphism `f^!𝒪_Y ≅ ω_{X/Y}[d]` in `D_QCoh(𝒪_X)`, from
`relativeDualizingComplexObjIsoShift`. -/
def upperShriekStructureSheafIsoRelativeDualizingSheafShift
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞)) :
    (upperShriek f j).obj (derivedStructureSheaf Y.left) ≅
      relativeDualizingSheafShift f j hCM d hd :=
  ObjectProperty.isoMk _ (relativeDualizingComplexObjIsoShift f j hCM d hd)

/-- `f^!𝒪_Y ≅ ω_{X/Y}[d]` in `D_QCoh(𝒪_X)`. -/
theorem nonempty_upperShriek_structureSheaf_iso_relativeDualizingSheafShift
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞)) :
    Nonempty ((upperShriek f j).obj (derivedStructureSheaf Y.left) ≅
      relativeDualizingSheafShift f j hCM d hd) :=
  ⟨upperShriekStructureSheafIsoRelativeDualizingSheafShift f j hCM d hd⟩

/-- **`f^!K ≅ Lf^*K ⊗ᴸ ω_{X/Y}[d]`, from the comparison `μ_{f,K}`.** For a Cohen–Macaulay
morphism of relative dimension `d`, the inverse of a given isomorphism
`μ : Lf^*K ⊗ᴸ f^!𝒪_Y ≅ f^!K` (the map `μ_{f,K}` of [Stacks, Tag 0B6U] (e)) followed by
`Lf^*K ⊗ᴸ -` applied to `upperShriekStructureSheafIsoRelativeDualizingSheafShift`. -/
def upperShriekIsoPullbackTensorShiftOfIso
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    (K : quasiCoherentDerivedCategory Y.left)
    (μ : ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K)).obj
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≅ (upperShriek f j).obj K) :
    (upperShriek f j).obj K ≅
      ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K)).obj
          (relativeDualizingSheafShift f j hCM d hd) :=
  μ.symm ≪≫ ((quasiCoherentDerivedTensor X.left).obj
    ((quasiCoherentDerivedPullback' f.left).obj K)).mapIso
      (upperShriekStructureSheafIsoRelativeDualizingSheafShift f j hCM d hd)

/-- **`f^!K ≅ Lf^*K ⊗ᴸ ω_{X/Y}[d]`, from the comparison `μ_{f,K}`.** For a Cohen–Macaulay
morphism of relative dimension `d`, an isomorphism `Lf^*K ⊗ᴸ f^!𝒪_Y ≅ f^!K` (the map `μ_{f,K}`
of [Stacks, Tag 0B6U] (e)) composed with `f^!𝒪_Y ≅ ω_{X/Y}[d]`. -/
theorem nonempty_upperShriek_iso_pullback_tensor_shift_of_iso
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    (K : quasiCoherentDerivedCategory Y.left)
    (μ : ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K)).obj
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≅ (upperShriek f j).obj K) :
    Nonempty ((upperShriek f j).obj K ≅
      ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K)).obj
          (relativeDualizingSheafShift f j hCM d hd)) :=
  ⟨upperShriekIsoPullbackTensorShiftOfIso f j hCM d hd K μ⟩

/-- **The relative dualizing complexes over a common base**, as an isomorphism: for
`f ≫ πY = πX` and a given `μ : Lf^*ω_Y ⊗ᴸ f^!𝒪_Y ≅ f^!ω_Y`, the composition isomorphism
`(f ≫ πY)^! ≅ f^! ∘ πY^!` on `D⁺_QCoh` at `ω_T`, followed by
`upperShriekIsoPullbackTensorShiftOfIso`. -/
def upperShriekCompIsoPullbackTensorShiftOfIso
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj)
    (μ : ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj ((upperShriek πY jY).obj ωT))).obj
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≅
        (upperShriek f j).obj ((upperShriek πY jY).obj ωT)) :
    (upperShriek πX jX).obj ωT ≅
      ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj ((upperShriek πY jY).obj ωT))).obj
          (relativeDualizingSheafShift f j hCM d hd) := by
  subst hπ
  exact (ObjectProperty.ι _).mapIso ((upperShriekCompIso f πY j jY jX).app ⟨ωT, hωT⟩) ≪≫
    upperShriekIsoPullbackTensorShiftOfIso f j hCM d hd _ μ

/-- **The relative dualizing complexes over a common base.** Let `πY : Y ⟶ T` and `πX : X ⟶ T`
be morphisms of `FTS S` with `f ≫ πY = πX`, let `ω_T ∈ D⁺_QCoh(𝒪_T)` and put
`ω_Y = πY^! ω_T`, `ω_X = πX^! ω_T`. If `f` is Cohen–Macaulay of relative dimension `d`, an
isomorphism `μ : Lf^*ω_Y ⊗ᴸ f^!𝒪_Y ≅ f^!ω_Y` gives `ω_X ≅ Lf^*ω_Y ⊗ᴸ ω_{X/Y}[d]`, through the
composition isomorphism `(f ≫ πY)^! ≅ f^! ∘ πY^!` on `D⁺_QCoh`. -/
theorem nonempty_upperShriek_comp_iso_pullback_tensor_shift_of_iso
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj)
    (μ : ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj ((upperShriek πY jY).obj ωT))).obj
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≅
        (upperShriek f j).obj ((upperShriek πY jY).obj ωT)) :
    Nonempty ((upperShriek πX jX).obj ωT ≅
      ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj ((upperShriek πY jY).obj ωT))).obj
          (relativeDualizingSheafShift f j hCM d hd)) :=
  ⟨upperShriekCompIsoPullbackTensorShiftOfIso f j hCM d hd πY πX hπ jY jX ωT hωT μ⟩

/-- The cohomology sheaves of `N` placed in degree `j` vanish outside degree `j`. -/
private theorem isZero_homology_singleFunctor_of_ne {Z : Scheme.{u}} (N : Z.Modules) (j k : ℤ)
    (hk : k ≠ j) :
    IsZero ((DerivedCategory.homologyFunctor Z.Modules k).obj
      ((DerivedCategory.singleFunctor Z.Modules j).obj N)) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) j N k hk).of_iso
    ((DerivedCategory.homologyFunctor Z.Modules k).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ Z.Modules j).app N) ≪≫
      (DerivedCategory.homologyFunctorFactors Z.Modules k).app _)

/-- An object isomorphic to `N[0]` shifted by `a` and then by `b` has vanishing cohomology
outside degree `-(a + b)`, and its cohomology in degree `-(a + b)` is `N`. -/
theorem isZero_homology_and_nonempty_iso_of_iso_shift_shift_single {Z : Scheme.{u}}
    (E : DerivedCategory Z.Modules) (N : Z.Modules) (a b : ℤ)
    (e : E ≅ (((DerivedCategory.singleFunctor Z.Modules 0).obj N)⟦a⟧)⟦b⟧) :
    (∀ i : ℤ, i ≠ -(a + b) → IsZero ((DerivedCategory.homologyFunctor Z.Modules i).obj E)) ∧
      Nonempty ((DerivedCategory.homologyFunctor Z.Modules (-(a + b))).obj E ≅ N) := by
  have key : ∀ i : ℤ, (DerivedCategory.homologyFunctor Z.Modules i).obj E ≅
      (DerivedCategory.homologyFunctor Z.Modules (i + b + a)).obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj N) := fun i =>
    (DerivedCategory.homologyFunctor Z.Modules i).mapIso e ≪≫
      Dualizing.homologyShiftObjIso _ i b ≪≫ Dualizing.homologyShiftObjIso _ (i + b) a
  refine ⟨fun i hi => ?_, ⟨key _ ≪≫ eqToIso (congrArg (fun n =>
      (DerivedCategory.homologyFunctor Z.Modules n).obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj N)) (by omega : -(a + b) + b + a = 0)) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Z.Modules 0).app N⟩⟩
  refine IsZero.of_iso ?_ (key i)
  exact isZero_homology_singleFunctor_of_ne N 0 (i + b + a) (by omega)

/-- **The cohomology sheaves of complexes related by a Cohen–Macaulay twist.** Let `f` be
Cohen–Macaulay of relative dimension `d`, `ω_Y` a dualizing complex on a connected Cohen–Macaulay
`Y`, and `ω_X ≅ Lf^*ω_Y ⊗ᴸ ω_{X/Y}[d]`. Then `ω_Y` and `ω_X` are concentrated in single degrees
`m` and `m - d`, and their cohomology sheaves there satisfy `ω_X ≅ f^*ω_Y ⊗ ω_{X/Y}`. -/
theorem exists_homology_iso_pullback_tensor_of_iso_shift
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    (ωY : quasiCoherentDerivedCategory Y.left) (ωX : quasiCoherentDerivedCategory X.left)
    [ConnectedSpace Y.left] (hY : AlgebraicGeometry.IsCohenMacaulay Y.left)
    (hωY : IsDualizingComplex ωY.obj)
    (eX : ωX ≅ ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj ωY)).obj
          (relativeDualizingSheafShift f j hCM d hd)) :
    ∃ m : ℤ,
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
        ωY.obj)) ∧
      (∀ i : ℤ, i ≠ m - d → IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj
        ωX.obj)) ∧
      Nonempty ((DerivedCategory.homologyFunctor X.left.Modules (m - d)).obj ωX.obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
          ((Scheme.Modules.pullback f.left).obj
            ((DerivedCategory.homologyFunctor Y.left.Modules m).obj ωY.obj))).obj
          (relativeDualizingSheaf f j d)) := by
  obtain ⟨m, -, -, ⟨eY⟩⟩ := exists_coherent_cohenMacaulay_iso_single_of_connected _ hωY hY
  have h := (isCohenMacaulay_iff_flat_and_fibers f.left (isLocallyNoetherian_fiber_left f)).mp hCM
  have : Flat f.left := h.1
  let M := (DerivedCategory.homologyFunctor Y.left.Modules m).obj ωY.obj
  let W := relativeDualizingSheaf f j d
  have hW : IsFlatOver f.left.toLRSHom.toShHom W :=
    isFlatOver_homology_of_isCohenMacaulay (upperShriekStructureSheafCharts f j) hCM _
  obtain ⟨eT⟩ := nonempty_derivedTensor_derivedPullback_single_iso f.left m M W hW
  let B := (DerivedCategory.singleFunctor X.left.Modules 0).obj W
  let E := (derivedPullback f.left).obj ωY.obj
  let hcs : ((derivedTensor X.left).obj E).CommShift ℤ :=
    (Stacks.Cohomology.TorAmplitude.derTensor X.left.toRingedSpace).commShift_right E
  let e3 : ((derivedTensor X.left).obj E).obj (B⟦(d : ℤ)⟧) ≅
      ((((derivedTensor X.left).obj ((derivedPullback f.left).obj
        ((DerivedCategory.singleFunctor Y.left.Modules m).obj M))).obj B))⟦(d : ℤ)⟧ :=
    ((Functor.commShiftIso (self := hcs) ((derivedTensor X.left).obj E) (d : ℤ))).app B ≪≫
      (shiftFunctor _ (d : ℤ)).mapIso
        ((((derivedTensor X.left).flip.obj B)).mapIso ((derivedPullback f.left).mapIso eY))
  let N := ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
    ((Scheme.Modules.pullback f.left).obj M)).obj W
  have := isZero_homology_and_nonempty_iso_of_iso_shift_shift_single _ N (-m) (d : ℤ)
    ((ObjectProperty.ι _).mapIso eX ≪≫ e3 ≪≫ (shiftFunctor _ (d : ℤ)).mapIso
      (eT ≪≫ ((DerivedCategory.singleFunctors X.left.Modules).shiftIso (-m) m 0
        (by omega)).symm.app N))
  rw [show -(-m + (d : ℤ)) = m - d by omega] at this
  refine ⟨m, fun i hi => ?_, this.1, this.2⟩
  exact (isZero_homology_singleFunctor_of_ne M m i hi).of_iso
    ((DerivedCategory.homologyFunctor Y.left.Modules i).mapIso eY)

/-- **The dualizing modules of Cohen–Macaulay schemes over a common base.** In the situation of
`nonempty_upperShriek_comp_iso_pullback_tensor_shift_of_iso`, suppose moreover that `Y` is
connected and Cohen–Macaulay and that `ω_Y^• = πY^! ω_T` is a dualizing complex. Then for some
`m` the complex `ω_Y^•` is concentrated in degree `m`, the complex `ω_X^• = πX^! ω_T` is
concentrated in degree `m - d`, and `H^{m-d}(ω_X^•) ≅ f^*H^m(ω_Y^•) ⊗_{𝒪_X} ω_{X/Y}`. -/
theorem exists_homology_upperShriek_comp_iso_pullback_tensor_of_iso
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (d : ℕ)
    (hd : ∀ x : X.left,
      topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj)
    [ConnectedSpace Y.left] (hY : AlgebraicGeometry.IsCohenMacaulay Y.left)
    (hωY : IsDualizingComplex ((upperShriek πY jY).obj ωT).obj)
    (μ : ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj ((upperShriek πY jY).obj ωT))).obj
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≅
        (upperShriek f j).obj ((upperShriek πY jY).obj ωT)) :
    ∃ m : ℤ,
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
        ((upperShriek πY jY).obj ωT).obj)) ∧
      (∀ i : ℤ, i ≠ m - d → IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj
        ((upperShriek πX jX).obj ωT).obj)) ∧
      Nonempty ((DerivedCategory.homologyFunctor X.left.Modules (m - d)).obj
          ((upperShriek πX jX).obj ωT).obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
          ((Scheme.Modules.pullback f.left).obj
            ((DerivedCategory.homologyFunctor Y.left.Modules m).obj
              ((upperShriek πY jY).obj ωT).obj))).obj (relativeDualizingSheaf f j d)) := by
  obtain ⟨eX⟩ := nonempty_upperShriek_comp_iso_pullback_tensor_shift_of_iso f j hCM d hd πY πX
    hπ jY jX ωT hωT μ
  exact exists_homology_iso_pullback_tensor_of_iso_shift f j hCM d hd _ _ hY hωY eX

end Stacks.Duality

end
