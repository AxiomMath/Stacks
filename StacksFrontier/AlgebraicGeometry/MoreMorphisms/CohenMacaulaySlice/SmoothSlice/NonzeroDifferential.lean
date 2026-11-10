module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.Algebra
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EffectiveCartierSlice
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Slicing a smooth morphism by a hypersurface through a point

Let `f : X ⟶ S` be smooth at `x : X` and let `h` be an element of the maximal ideal of
`𝒪_{X, x}` whose differential is nonzero in the residue-field fibre `Ω_{X/S, x} ⊗ κ(x)` of the
relative differentials.  Then `h` is the germ at `x` of a global section of an affine open
neighbourhood `U` of `x`, its zero scheme `V(h) ⊆ U` is an effective Cartier divisor through
`x`, and `V(h) ⟶ S` is smooth.  This is Stacks tag 057C.

## This file

This file contains the definition of `HasNonzeroRelativeDifferential` and the facts about it
that do not involve the slice: independence of the representative, nonvanishing in the
scheme-theoretic fibre and on affine representatives, and the commutative algebra of a quotient
`A ⧸ (a)` by an element with nonzero differential (regularity, formal smoothness, and formal
smoothness of the stalk map of a closed subscheme cut out by such an element).  The slice itself
and Stacks tag 057C are in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SmoothSlice.SmoothDivisor`.

## Main definitions

* `Stacks.AlgebraicGeometry.HasNonzeroRelativeDifferential`: the hypothesis that the
  differential of a germ is nonzero in the residue-field fibre of the relative differentials.

## Main results

* `Stacks.AlgebraicGeometry.exists_smooth_effectiveCartierDivisor_of_nonzero_differential`:
  Stacks tag 057C, the smooth hypersurface slice through the prescribed point.

## Implementation notes

The fibre cotangent space of the source is the residue-field fibre `Ω_{X/S, x} ⊗ κ(x)` of the
stalk of the relative differentials;  the source's identification of it with the corresponding
space of the scheme-theoretic fibre `X_s` is
`Stacks.FiberCotangentAssembly.fiberDifferentialsTensorIdentification` (tag 01V9), and the
proof transports the hypothesis across it to apply regularity of the fibre local ring.

The nonzero differential is tested on one representative of the germ;  the value does not
depend on the choice, so the existential hypothesis also holds for every representative.  The
zero scheme is specified by its principal ideals on every affine open of the chosen affine
neighbourhood;  this records the equation, not merely its support.

One ring, one group and one point are each spelled more than one way below, and instance
search and `rw` unfold none of the identifications:  `Scheme.Modules.presheaf M` is
`M.val.presheaf`, the ring `Γ(X, U)` acting on sections is reached through `X.ringCatSheaf`
rather than `X.presheaf`, and the carrier of `U.toScheme` is the subtype `↥U`.  Every one of
these holds by definition and none of them reducibly, so a general lemma stated at one
spelling neither applies nor rewrites at another, and the scalar action on a stalk that is
visible from a hypothesis need not be the one visible in the goal.

The remedy used throughout is the one of
`StacksFrontier/AlgebraicGeometry/PullbackTensor/Basic.lean`:  the instance of each general lemma
that is needed is stated as a closed equation of its own, with every argument spelled out, and
rewritten with;  a scalar action or module structure whose spelling instance search cannot
reach is named on the spot;  and a step whose goal is not type-correct at reducible
transparency is composed in term mode rather than rewritten.  The closed equations are
`Stacks.AlgebraicGeometry.Modules.germ_smul`,
`Stacks.AlgebraicGeometry.Modules.smul_restrict_ι`,
`Stacks.AlgebraicGeometry.Modules.germ_stalkMap_restrictStalkNatIso`,
`Stacks.AlgebraicGeometry.presheaf_map_comp_eq`,
`Stacks.AlgebraicGeometry.presheaf_map_comp` and
`Stacks.AlgebraicGeometry.appTop_comp_map`.

## References

* [Stacks Project, Tag 057C](https://stacks.math.columbia.edu/tag/057C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry

universe u

/-- A germ has nonzero relative differential in the residue-field fibre of
the sheaf of differentials. -/
public def HasNonzeroRelativeDifferential {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (h : X.presheaf.stalk x) : Prop :=
  ∃ (W : X.Opens) (hxW : x ∈ W) (a : Γ(X, W)),
    ((TopCat.Presheaf.germ X.presheaf W x hxW).hom a = h) ∧
      (letI : Module (X.presheaf.stalk x)
          (SmoothAtJacobian.relativeDifferentialStalk f x) :=
            SmoothAtJacobian.relativeDifferentialStalkModule f x
       letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
         (X.residue x).hom.toAlgebra
       TensorProduct.tmul (X.presheaf.stalk x) (1 : X.residueField x)
         (show SmoothAtJacobian.relativeDifferentialStalk f x from
           ((TopCat.Presheaf.germ
             (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials
               (inverseImageStructureMap f)).val.presheaf W x hxW)).hom
             ((AlgebraicGeometry.SheafOfModules.universalDerivation
               (inverseImageStructureMap f)).d a)) ≠ 0)

private theorem differential_germ_eq_of_germ_eq
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U V : X.Opens) (hxU : x ∈ U) (hxV : x ∈ V)
    (a : Γ(X, U)) (b : Γ(X, V))
    (hab : (X.presheaf.germ U x hxU).hom a = (X.presheaf.germ V x hxV).hom b) :
    (TopCat.Presheaf.germ (Scheme.Hom.relativeDifferentials f).val.presheaf
      U x hxU).hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
    (TopCat.Presheaf.germ (Scheme.Hom.relativeDifferentials f).val.presheaf
      V x hxV).hom ((Scheme.Hom.universalRelativeDerivation f).d b) := by
  let M := Scheme.Hom.relativeDifferentials f
  let d := Scheme.Hom.universalRelativeDerivation f
  obtain ⟨T, hxT, i, j, hT⟩ := X.presheaf.germ_eq x hxU hxV a b hab
  have hi := TopCat.Presheaf.germ_res_apply M.val.presheaf i x hxT (d.d a)
  have hj := TopCat.Presheaf.germ_res_apply M.val.presheaf j x hxT (d.d b)
  have hres : M.val.presheaf.map i.op (d.d a) = M.val.presheaf.map j.op (d.d b) := by
    change (M.val.map i.op).hom (d.d a) = (M.val.map j.op).hom (d.d b)
    exact (d.d_map i.op a).symm.trans
      ((congrArg (fun c => d.d c) hT).trans (d.d_map j.op b))
  exact hi.symm.trans ((congrArg (TopCat.Presheaf.germ M.val.presheaf T x hxT) hres).trans hj)

/-- **The module structure of `Stacks.SmoothAtJacobian.relativeDifferentialStalkModule`, at the
`M.val.presheaf` spelling of the underlying abelian presheaf.**

`Stacks.SmoothAtJacobian.relativeDifferentialStalk` is stated over
`Scheme.Modules.presheaf (Scheme.Hom.relativeDifferentials f)`, and
`AlgebraicGeometry.Scheme.Modules.presheaf M` is `M.val.presheaf` by definition but not
reducibly so.  Instance search unfolds neither, so the module structure has to be named at the
spelling the statement at hand uses;  this is that naming for the `M.val.presheaf` spelling. -/
private abbrev relativeDifferentialValStalkModule {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf x) :=
  SmoothAtJacobian.relativeDifferentialStalkModule f x

theorem HasNonzeroRelativeDifferential.ne_zero_of_germ_eq
    {X S : Scheme.{u}} {f : X ⟶ S} {x : X} {h : X.presheaf.stalk x}
    (hdh : HasNonzeroRelativeDifferential f x h)
    (U : X.Opens) (hxU : x ∈ U) (a : Γ(X, U))
    (ha : (X.presheaf.germ U x hxU).hom a = h) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials f).val.presheaf x) :=
      SmoothAtJacobian.relativeDifferentialStalkModule f x
    letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
      (X.residue x).hom.toAlgebra
    (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x]
      ((TopCat.Presheaf.germ (Scheme.Hom.relativeDifferentials f).val.presheaf
        U x hxU).hom ((Scheme.Hom.universalRelativeDerivation f).d a)) ≠ 0 := by
  obtain ⟨V, hxV, b, hb, hne⟩ := hdh
  let := relativeDifferentialValStalkModule f x
  let : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  rw [differential_germ_eq_of_germ_eq f x U V hxU hxV a b (ha.trans hb.symm)]
  exact hne

private theorem fiberImage_nonzero_of_hasNonzeroRelativeDifferential
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : X.presheaf.stalk x)
    (hdh : HasNonzeroRelativeDifferential f x h) :
    ∃ (W : X.Opens) (hxW : x ∈ W) (a : Γ(X, W)),
      ((TopCat.Presheaf.germ X.presheaf W x hxW).hom a = h) ∧
      letI : Module (X.presheaf.stalk x)
          (SmoothAtJacobian.relativeDifferentialStalk f x) :=
            SmoothAtJacobian.relativeDifferentialStalkModule f x
      letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
        (X.residue x).hom.toAlgebra
      let v := TensorProduct.tmul (X.presheaf.stalk x) (1 : X.residueField x)
        (show SmoothAtJacobian.relativeDifferentialStalk f x from
          ((TopCat.Presheaf.germ
            (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials
              (inverseImageStructureMap f)).val.presheaf W x hxW)).hom
            ((AlgebraicGeometry.SheafOfModules.universalDerivation
              (inverseImageStructureMap f)).d a))
      (ModuleCat.Hom.hom
        (FiberCotangentAssembly.fiberDifferentialsTensorIdentification f x).equiv.hom) v ≠ 0 ∧
      SmoothAtJacobian.IsFiberDifferentialsTensorEquiv f x
        (FiberCotangentAssembly.fiberDifferentialsTensorIdentification f x).equiv := by
  obtain ⟨W, hxW, a, ha, hne⟩ := hdh
  let : Module (X.presheaf.stalk x)
      (SmoothAtJacobian.relativeDifferentialStalk f x) :=
        SmoothAtJacobian.relativeDifferentialStalkModule f x
  let : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  let E := FiberCotangentAssembly.fiberDifferentialsTensorIdentification f x
  let v := TensorProduct.tmul (X.presheaf.stalk x) (1 : X.residueField x)
    (show SmoothAtJacobian.relativeDifferentialStalk f x from
      ((TopCat.Presheaf.germ
        (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials
          (inverseImageStructureMap f)).val.presheaf W x hxW)).hom
        ((AlgebraicGeometry.SheafOfModules.universalDerivation
          (inverseImageStructureMap f)).d a))
  refine ⟨W, hxW, a, ha, ?_, E.isCanonical⟩
  change E.equiv.hom.hom v ≠ 0
  intro hz
  change E.equiv.toLinearEquiv v = 0 at hz
  have hz' : E.equiv.toLinearEquiv v = E.equiv.toLinearEquiv 0 := by
    rw [hz, map_zero]
  exact hne (E.equiv.toLinearEquiv.injective hz')

theorem fiberImage_ne_zero_of_hasNonzeroRelativeDifferential
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : X.presheaf.stalk x)
    (hdh : HasNonzeroRelativeDifferential f x h) :
    ∃ (W : X.Opens) (hxW : x ∈ W) (a : Γ(X, W)),
      ((TopCat.Presheaf.germ X.presheaf W x hxW).hom a = h) ∧
      ∃ (hxIW : (f.fiberι (f x))
          (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x))) ∈ W),
        (((f.fiberι (f x)).stalkMap
          (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x)))).hom
          ((TopCat.Presheaf.germ X.presheaf W _ hxIW).hom a)) ≠ 0 ∧
        (letI : Module (ToType ((f.fiber (f x)).presheaf.stalk
            (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x)))))
            (SmoothAtJacobian.relativeDifferentialStalk
              (f.fiberToSpecResidueField (f x))
              (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x)))) :=
              SmoothAtJacobian.relativeDifferentialStalkModule _ _
         letI : Algebra (ToType ((f.fiber (f x)).presheaf.stalk
            (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x)))))
            (X.residueField x) :=
              (Scheme.stalkClosedPointTo (f.asFiberHom x)).hom.toAlgebra
         TensorProduct.tmul (ToType ((f.fiber (f x)).presheaf.stalk
            (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x)))))
            (1 : X.residueField x)
            (show SmoothAtJacobian.relativeDifferentialStalk
                (f.fiberToSpecResidueField (f x))
                (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x))) from
              ((TopCat.Presheaf.germ
                (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials
                  (inverseImageStructureMap
                    (f.fiberToSpecResidueField (f x)))).val.presheaf
                (f.fiberι (f x) ⁻¹ᵁ W)
                (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x)))
                (by
                  change ((f.fiberι (f x))
                    (f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x)))) ∈ W
                  exact hxIW)).hom
                ((AlgebraicGeometry.SheafOfModules.universalDerivation
                  (inverseImageStructureMap
                    (f.fiberToSpecResidueField (f x)))).d
                  (((f.fiberι (f x)).app W).hom a)))) ≠ 0) := by
  obtain ⟨W, hxW, a, ha, hv, hcan⟩ :=
    fiberImage_nonzero_of_hasNonzeroRelativeDifferential f x h hdh
  let i := f.fiberι (f x)
  let xf := f.asFiberHom x (IsLocalRing.closedPoint (X.residueField x))
  have hix : i xf = x := by
    change (f.asFiberHom x ≫ f.fiberι (f x))
      (IsLocalRing.closedPoint (X.residueField x)) = x
    rw [Scheme.Hom.asFiberHom_fiberι]
    exact Scheme.fromSpecResidueField_apply x _
  let Wf := i ⁻¹ᵁ W
  have hxfW : xf ∈ Wf := by
    change i xf ∈ W
    simpa only [hix] using hxW
  let fs := f.fiberToSpecResidueField (f x)
  let φ := inverseImageStructureMap fs
  let N := AlgebraicGeometry.SheafOfModules.moduleOfDifferentials φ
  let d := AlgebraicGeometry.SheafOfModules.universalDerivation φ
  let af := (i.app W).hom a
  let : Module (X.presheaf.stalk x) (SmoothAtJacobian.relativeDifferentialStalk f x) :=
    SmoothAtJacobian.relativeDifferentialStalkModule f x
  let : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  let : Module (ToType ((f.fiber (f x)).presheaf.stalk xf))
      (SmoothAtJacobian.relativeDifferentialStalk fs xf) :=
    SmoothAtJacobian.relativeDifferentialStalkModule fs xf
  let : Algebra (ToType ((f.fiber (f x)).presheaf.stalk xf)) (X.residueField x) :=
    (Scheme.stalkClosedPointTo (f.asFiberHom x)).hom.toAlgebra
  have htarget :
      (TensorProduct.tmul (ToType ((f.fiber (f x)).presheaf.stalk xf))
        (1 : X.residueField x)
        (show SmoothAtJacobian.relativeDifferentialStalk fs xf from
          ((TopCat.Presheaf.germ N.val.presheaf Wf xf hxfW).hom
            (d.d af))) :
        X.residueField x ⊗[ToType ((f.fiber (f x)).presheaf.stalk xf)]
          SmoothAtJacobian.relativeDifferentialStalk fs xf) ≠ 0 := by
    intro hz
    have hc := hcan W hxW a
    dsimp [i, xf, Wf, fs, φ, N, d, af] at hc
    exact hv (hc.trans hz)
  have hixW : i xf ∈ W := by simpa only [hix] using hxW
  refine ⟨W, hxW, a, ha, hixW, ?_, htarget⟩
  have hi := Scheme.Hom.germ_stalkMap_apply i W xf hixW a
  change (i.stalkMap xf).hom
    ((TopCat.Presheaf.germ X.presheaf W (i xf) hixW).hom a) ≠ 0
  rw [hi]
  intro hzImg
  obtain ⟨T, hxT, j₁, j₂, hT⟩ :=
    (f.fiber (f x)).presheaf.germ_eq xf hxfW hxfW af 0 (by simpa [Wf, af] using hzImg)
  have hrestrict : (N.val.map j₁.op).hom (d.d af) = 0 := by
    have hT' : (f.fiber (f x)).presheaf.map j₁.op af = 0 := by simpa using hT
    have hdmap := d.d_map j₁.op af
    change d.d ((f.fiber (f x)).presheaf.map j₁.op af) =
      (N.val.map j₁.op).hom (d.d af) at hdmap
    rw [← hdmap, hT']
    exact map_zero _
  have hderivzero :
      (TopCat.Presheaf.germ N.val.presheaf Wf xf hxfW).hom (d.d af) = 0 := by
    have hg := TopCat.Presheaf.germ_res_apply N.val.presheaf j₁ xf hxT (d.d af)
    rw [show N.val.presheaf.map j₁.op (d.d af) = 0 from hrestrict] at hg
    exact hg.symm.trans (map_zero _)
  apply htarget
  rw [hderivzero]
  exact TensorProduct.tmul_zero _ _

private theorem quotient_regularLocal_of_isUnit_derivation
    {k A : Type*} [Field k] [CommRing A] [IsRegularLocalRing A] [Algebra k A]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (D : Derivation k A A) (hD : IsUnit (D a)) :
    IsRegularLocalRing (A ⧸ Ideal.span {a}) ∧ IsSMulRegular A a := by
  let f : Fin 1 → A := fun _ => a
  let D' : Fin 1 → Derivation ℤ A A := fun _ => D.restrictScalars ℤ
  let M : Matrix (Fin 1) (Fin 1) A := fun i j => D' i (f j)
  have hdet : IsUnit M.det := by
    have heq : M.det = D a := by
      rw [Matrix.det_fin_one]
      simp [M, f, D']
    rwa [heq]
  obtain ⟨hquot, hreg⟩ :=
    isRegularLocalRing_quotient_span_range_and_isRegular_of_isUnit_det_derivation
      f (fun _ => ha) D' hdet
  have hquot' : IsRegularLocalRing (A ⧸ Ideal.span {a}) := by
    have hRange : Set.range f = {a} := by
      ext b
      simp [f]
    rwa [hRange] at hquot
  have hreg' : RingTheory.Sequence.IsRegular A [a] := by
    simpa [f] using hreg
  refine ⟨hquot', ?_⟩
  let p : Submodule A A := Ideal.ofList ([] : List A) • (⊤ : Submodule A A)
  have hp : p = ⊥ := by simp [p]
  have hreg0 : IsSMulRegular (A ⧸ p) a := by
    change IsSMulRegular
      (A ⧸ (Ideal.ofList ([] : List A) • (⊤ : Submodule A A))) a
    exact hreg'.regular_mod_prev 0 (by simp : 0 < [a].length)
  exact (Submodule.quotEquivOfEqBot p hp).isSMulRegular_congr a |>.mp hreg0

private theorem exists_unit_derivation_of_fiber_differential_ne_zero
    {k A κ : Type*} [CommRing k] [CommRing A] [IsLocalRing A] [Field κ]
    [Algebra k A] [Algebra A κ] [Algebra k κ] [IsScalarTower k A κ]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    (hsurj : Function.Surjective (algebraMap A κ)) {a : A}
    (ha : (1 : κ) ⊗ₜ[A] KaehlerDifferential.D k A a ≠ 0) :
    ∃ D : Derivation k A A, IsUnit (D a) := by
  classical
  by_contra h
  push Not at h
  have hnonunit : ∀ φ : Ω[A⁄k] →ₗ[A] A,
      ¬ IsUnit (φ (KaehlerDifferential.D k A a)) :=
    fun φ hu => h (φ.compDer (KaehlerDifferential.D k A)) hu
  have hker : RingHom.ker (algebraMap A κ) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  let b := Module.Free.chooseBasis A Ω[A⁄k]
  have hzero : (1 : κ) ⊗ₜ[A] KaehlerDifferential.D k A a = 0 := by
    rw [← b.sum_repr (KaehlerDifferential.D k A a), TensorProduct.tmul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hcoord : algebraMap A κ (b.repr (KaehlerDifferential.D k A a) i) = 0 := by
      apply RingHom.mem_ker.mp
      rw [hker]
      apply (IsLocalRing.mem_maximalIdeal _).mpr
      have hu : ¬ IsUnit ((Finsupp.lapply i).comp b.repr.toLinearMap
          (KaehlerDifferential.D k A a)) :=
        hnonunit ((Finsupp.lapply i).comp b.repr.toLinearMap)
      simpa using hu
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      mul_one, hcoord, TensorProduct.zero_tmul]
  exact ha hzero

private theorem regular_quotient_of_free_kaehler_and_nonzero_fiber_differential
    {k A κ : Type*} [Field k] [CommRing A] [IsRegularLocalRing A]
    [Field κ] [Algebra k A] [Algebra A κ] [Algebra k κ] [IsScalarTower k A κ]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    (hsurj : Function.Surjective (algebraMap A κ)) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A)
    (hda : (1 : κ) ⊗ₜ[A] KaehlerDifferential.D k A a ≠ 0) :
    IsRegularLocalRing (A ⧸ Ideal.span {a}) ∧ IsSMulRegular A a := by
  obtain ⟨D, hD⟩ := exists_unit_derivation_of_fiber_differential_ne_zero hsurj hda
  exact quotient_regularLocal_of_isUnit_derivation a ha D hD

private theorem quotient_flat_of_fiber_isSMulRegular
    {R A : Type*} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    (hfp : (algebraMap R A).EssentiallyOfFinitePresentation) (a : A)
    (ha : IsSMulRegular
      (A ⧸ (Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule A A))) a) :
    IsSMulRegular A a ∧ Module.Flat R (A ⧸ (Ideal.span {a} • (⊤ : Submodule A A))) :=
  Module.Flat.isSMulRegular_and_flat_quotient_smul_of_isSMulRegular_maximalIdeal hfp ha

private theorem formallySmooth_quotient_of_unit_derivation
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A] (a : A)
    (D : Derivation R A (A ⧸ Ideal.span {a}))
    (hDa : D a = 1) :
    Algebra.FormallySmooth R (A ⧸ Ideal.span {a}) := by
  let I : Ideal A := Ideal.span {a}
  let C := A ⧸ I
  let P : Algebra.Extension R C := Algebra.Extension.ofSurjective
    (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
  have hker : P.ker = I := Ideal.mk_ker (R := A) (I := I)
  let m : P.Cotangent := Algebra.Extension.Cotangent.mk
    ⟨a, hker.symm ▸ Ideal.mem_span_singleton_self a⟩
  let θ : C ⊗[A] Ω[A⁄R] →ₗ[C] C := D.liftKaehlerDifferential.liftBaseChange C
  let l : P.CotangentSpace →ₗ[C] P.Cotangent :=
    (LinearMap.toSpanSingleton C P.Cotangent m).comp θ
  have hl : l (P.cotangentComplex m) = m := by
    change θ (1 ⊗ₜ[A] KaehlerDifferential.D R A a) • m = m
    rw [LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D, hDa, one_smul]
  have hgen : ∀ z : P.Cotangent, ∃ c : C, z = c • m := by
    intro z
    obtain ⟨⟨b, hb⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
    rw [hker] at hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    refine ⟨algebraMap A C c, ?_⟩
    exact (Algebra.Extension.Cotangent.mk.map_smul c
        ⟨a, hker.symm ▸ Ideal.mem_span_singleton_self a⟩).trans
      (IsScalarTower.algebraMap_smul (R := A) (A := C) c m).symm
  have : Algebra.FormallySmooth R P.Ring :=
    inferInstanceAs (Algebra.FormallySmooth R A)
  apply (Algebra.Extension.formallySmooth_iff_split_injection P).2
  refine ⟨l, LinearMap.ext fun z => ?_⟩
  obtain ⟨c, rfl⟩ := hgen z
  change l (P.cotangentComplex (c • m)) = c • m
  rw [map_smul, map_smul, hl]

private theorem formallySmooth_quotient_of_nonzero_fiber_differential
    {R A κ : Type*} [CommRing R] [CommRing A] [IsLocalRing A] [Field κ]
    [Algebra R A] [Algebra A κ] [Algebra R κ] [IsScalarTower R A κ]
    [Algebra.FormallySmooth R A] [Module.Free A Ω[A⁄R]] [Module.Finite A Ω[A⁄R]]
    (hsurj : Function.Surjective (algebraMap A κ)) (a : A)
    (hda : (1 : κ) ⊗ₜ[A] KaehlerDifferential.D R A a ≠ 0) :
    Algebra.FormallySmooth R (A ⧸ Ideal.span {a}) := by
  obtain ⟨D, hD⟩ := exists_unit_derivation_of_fiber_differential_ne_zero hsurj hda
  obtain ⟨u, hu⟩ := hD
  let D' : Derivation R A A := (↑u⁻¹ : A) • D
  have hD' : D' a = 1 := by
    change (↑u⁻¹ : A) * D a = 1
    rw [← hu]
    exact Units.inv_mul u
  let q : A →ₗ[A] A ⧸ Ideal.span {a} := (Ideal.Quotient.mkₐ A (Ideal.span {a})).toLinearMap
  apply formallySmooth_quotient_of_unit_derivation a (q.compDer D')
  change q (D' a) = 1
  rw [hD']
  exact map_one (Ideal.Quotient.mkₐ A (Ideal.span {a}))

private theorem affineDifferential_ne_zero
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.affineOpens) (V : S.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (x : X) (hxU : x ∈ U.1) (a : Γ(X, U.1))
    {h : X.presheaf.stalk x} (hdh : HasNonzeroRelativeDifferential f x h)
    (ha : (X.presheaf.germ U.1 x hxU).hom a = h) :
    letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V U hUV).hom.toAlgebra
    letI : Algebra Γ(X, U.1) (X.residueField x) :=
      ((X.residue x).hom.comp (X.presheaf.germ U.1 x hxU).hom).toAlgebra
    (1 : X.residueField x) ⊗ₜ[Γ(X, U.1)]
      KaehlerDifferential.D Γ(S, V.1) Γ(X, U.1) a ≠ 0 := by
  have hne := hdh.ne_zero_of_germ_eq U.1 hxU a ha
  let B := Γ(X, U.1)
  let A := X.presheaf.stalk x
  let κ := X.residueField x
  let M := Scheme.Hom.relativeDifferentials f
  let : Algebra Γ(S, V.1) B := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra B κ :=
    ((X.residue x).hom.comp (X.presheaf.germ U.1 x hxU).hom).toAlgebra
  let : Algebra A κ := (X.residue x).hom.toAlgebra
  let := relativeDifferentialValStalkModule f x
  -- `A` and `M` are local names, which instance search does not unfold, so the module
  -- structure on the stalk is named again at the spelling that mentions them.
  let : Module A (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x) :=
    relativeDifferentialValStalkModule f x
  let N := κ ⊗[A] SmoothAtJacobian.relativeDifferentialStalk f x
  -- The sections of `M` over `U` and the Kähler differentials of `f.appLE V U hUV` are
  -- `ModuleCat`s over `Γ(X, U)` written through `X.ringCatSheaf`, not through `X.presheaf`;
  -- instance search reaches neither spelling from the other, so both objects and the
  -- isomorphism between them are named here over `B`, and everything below is `B`-linear on
  -- the nose.
  let MU : ModuleCat.{u} B := M.val.obj (.op U.1)
  let KD : ModuleCat.{u} B := CommRingCat.KaehlerDifferential (f.appLE V U hUV)
  let γ : MU →ₗ[B] N :=
    { toFun := fun m => 1 ⊗ₜ[A] (TopCat.Presheaf.germ M.val.presheaf U.1 x hxU).hom m
      map_add' := fun m₁ m₂ => by
        refine Eq.trans ?_ (TensorProduct.tmul_add (1 : κ) _ _)
        exact congrArg _ (map_add (TopCat.Presheaf.germ M.val.presheaf U.1 x hxU).hom m₁ m₂)
      map_smul' := by
        intro r m
        change 1 ⊗ₜ[A] (TopCat.Presheaf.germ M.val.presheaf U.1 x hxU (r • m)) = _
        have hsm : (TopCat.Presheaf.germ M.val.presheaf U.1 x hxU).hom (r • m) =
            (X.presheaf.germ U.1 x hxU).hom r •
              (TopCat.Presheaf.germ M.val.presheaf U.1 x hxU).hom m :=
          PresheafOfModules.germ_smul M.val x U.1 hxU r m
        rw [hsm]
        rw [TensorProduct.tmul_smul (R := A) (R' := A)]
        rfl }
  obtain ⟨e, he, -⟩ :=
    AffineDifferentialsIso.existsUnique_affineDifferentialsIso f U.2 hUV V.2
  let e' : MU ≅ KD := e
  let F : Ω[B⁄Γ(S, V.1)] →ₗ[B] N := γ.comp e'.inv.hom
  let Fκ : κ ⊗[B] Ω[B⁄Γ(S, V.1)] →ₗ[κ] N := F.liftBaseChange κ
  intro hz
  apply hne
  have hzero := congrArg Fκ hz
  rw [LinearMap.liftBaseChange_tmul, one_smul, map_zero] at hzero
  have he' : e.hom.hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
      KaehlerDifferential.D Γ(S, V.1) B a := he a
  rw [← he'] at hzero
  exact (congrArg (fun t => (1 : κ) ⊗ₜ[A]
      (TopCat.Presheaf.germ M.val.presheaf U.1 x hxU).hom t)
    (ConcreteCategory.congr_hom e.hom_inv_id
      ((Scheme.Hom.universalRelativeDerivation f).d a))).symm.trans hzero

/-- A representative of a germ restricts to one on an affine open inside any neighbourhood. -/
private theorem exists_affine_representative_le
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (h : X.presheaf.stalk x)
    (hdh : HasNonzeroRelativeDifferential f x h) (O : X.Opens) (hxO : x ∈ O) :
    ∃ (U : X.affineOpens) (hxU : x ∈ U.1), U.1 ≤ O ∧
      ∃ a : Γ(X, U.1), (X.presheaf.germ U.1 x hxU).hom a = h := by
  obtain ⟨W, hxW, b, hb, -⟩ := id hdh
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ W ⊓ O from ⟨hxW, hxO⟩) (W ⊓ O).isOpen
  have hUW : U ≤ W := fun y hy => (hsub hy).1
  exact ⟨⟨U, hU⟩, hxU, fun y hy => (hsub hy).2, (X.presheaf.map (homOfLE hUW).op).hom b,
    (X.presheaf.germ_res_apply (homOfLE hUW) x hxU b).trans hb⟩

private theorem exists_affine_representative_with_nonzero_differential
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (h : X.presheaf.stalk x)
    (hdh : HasNonzeroRelativeDifferential f x h) :
    ∃ (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1)
      (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (a : Γ(X, U.1)),
      (X.presheaf.germ U.1 x hxU).hom a = h ∧
      (letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V U hUV).hom.toAlgebra
       letI : Algebra Γ(X, U.1) (X.residueField x) :=
         ((X.residue x).hom.comp (X.presheaf.germ U.1 x hxU).hom).toAlgebra
       (1 : X.residueField x) ⊗ₜ[Γ(X, U.1)]
         KaehlerDifferential.D Γ(S, V.1) Γ(X, U.1) a ≠ 0) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨U, hxU, hUV, a, ha⟩ := exists_affine_representative_le f x h hdh (f ⁻¹ᵁ V) hsV
  exact ⟨U, ⟨V, hV⟩, hxU, hUV, a, ha, affineDifferential_ne_zero f U ⟨V, hV⟩ hUV x hxU a hdh ha⟩

private theorem exists_affine_representative_with_smooth_app
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (h : X.presheaf.stalk x)
    (hf : InfinitesimalLifting.SmoothAt f x)
    (hdh : HasNonzeroRelativeDifferential f x h) :
    ∃ (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1)
      (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (a : Γ(X, U.1)),
      (X.presheaf.germ U.1 x hxU).hom a = h ∧
      (f.appLE V U hUV).hom.Smooth ∧
      (letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V U hUV).hom.toAlgebra
       letI : Algebra Γ(X, U.1) (X.residueField x) :=
         ((X.residue x).hom.comp (X.presheaf.germ U.1 x hxU).hom).toAlgebra
       (1 : X.residueField x) ⊗ₜ[Γ(X, U.1)]
         KaehlerDifferential.D Γ(S, V.1) Γ(X, U.1) a ≠ 0) := by
  obtain ⟨U₀, V, hU₀, hV, hxU₀, hU₀V, hs⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine f x).mp hf
  have : IsAffine U₀.toScheme := hU₀
  have : IsAffine V.toScheme := hV
  have : Smooth (f.resLE V U₀ hU₀V) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2
      ((RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f V U₀ hU₀V)).mpr hs)
  obtain ⟨⟨U, hU⟩, hxU, hUU₀, a, ha⟩ := exists_affine_representative_le f x h hdh U₀ hxU₀
  have hUV : U ≤ f ⁻¹ᵁ V := hUU₀.trans hU₀V
  have : IsAffine U.toScheme := hU
  have : Smooth (f.resLE V U hUV) := by
    rw [← f.map_resLE hU₀V hUU₀]
    infer_instance
  have hsU : (f.appLE V U hUV).hom.Smooth :=
    (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V U hUV)).mp
        ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp inferInstance)
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV, a, ha, hsU,
    affineDifferential_ne_zero f ⟨U, hU⟩ ⟨V, hV⟩ hUV x hxU a hdh ha⟩

private theorem fiber_differential_ne_zero_of_formallyEtale
    {R B A κ : Type*} [CommRing R] [CommRing B] [CommRing A] [CommRing κ]
    [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    [Algebra B κ] [Algebra A κ] [IsScalarTower B A κ]
    [Algebra.FormallyEtale B A] (a : B)
    (hda : (1 : κ) ⊗ₜ[B] KaehlerDifferential.D R B a ≠ 0) :
    (1 : κ) ⊗ₜ[A] KaehlerDifferential.D R A (algebraMap B A a) ≠ 0 := by
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B A
  let F : κ ⊗[A] Ω[A⁄R] →ₗ[A] κ ⊗[B] Ω[B⁄R] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B A A κ Ω[B⁄R]).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : κ →ₗ[A] κ) e.symm.toLinearMap)
  intro hz
  apply hda
  have hzero := congrArg F hz
  simpa only [F, e, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul, map_zero] using hzero

private theorem formallySmooth_quotient_of_localization_differential
    {R B A κ : Type*} [CommRing R] [CommRing B] [CommRing A] [IsLocalRing A]
    [Field κ] [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    [Algebra B κ] [Algebra A κ] [IsScalarTower B A κ]
    [Algebra.EssFiniteType R B] (p : Ideal B) [p.IsPrime]
    [IsLocalization.AtPrime A p] [Algebra.IsSmoothAt R p]
    (hsurj : Function.Surjective (algebraMap A κ)) (a : B)
    (hda : (1 : κ) ⊗ₜ[B] KaehlerDifferential.D R B a ≠ 0) :
    Algebra.FormallySmooth R (A ⧸ Ideal.span {algebraMap B A a}) := by
  let : Algebra R κ := ((algebraMap A κ).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A κ := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FormallyEtale B A := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have : Algebra.FormallySmooth R A := Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).restrictScalars R)
  have : Algebra.EssFiniteType B A := Algebra.EssFiniteType.of_isLocalization A p.primeCompl
  have : Algebra.EssFiniteType R A := Algebra.EssFiniteType.comp R B A
  have : Module.Finite A Ω[A⁄R] := KaehlerDifferential.finite R A
  have : Module.Free A Ω[A⁄R] := Module.free_of_flat_of_isLocalRing
  exact formallySmooth_quotient_of_nonzero_fiber_differential hsurj
    (algebraMap B A a) (fiber_differential_ne_zero_of_formallyEtale a hda)

/-- A quotient of `A` by a principal kernel is formally smooth if `A ⧸ (a)` is. -/
private theorem formallySmooth_of_surjective_of_ker_eq_span
    {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    (f : A →ₐ[R] C) (hf : Function.Surjective f) (a : A)
    (hker : RingHom.ker f = Ideal.span {a})
    [Algebra.FormallySmooth R (A ⧸ Ideal.span {a})] : Algebra.FormallySmooth R C :=
  Algebra.FormallySmooth.of_equiv
    ((Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hf))

private theorem formallySmooth_of_surjective_of_principal_ker
    {R A C κ : Type*} [CommRing R] [CommRing A] [IsLocalRing A]
    [CommRing C] [Field κ] [Algebra R A] [Algebra R C]
    [Algebra A κ] [Algebra R κ] [IsScalarTower R A κ]
    [Algebra.FormallySmooth R A] [Algebra.EssFiniteType R A]
    (f : A →ₐ[R] C) (hf : Function.Surjective f) (a : A)
    (hker : RingHom.ker f = Ideal.span {a})
    (hκ : Function.Surjective (algebraMap A κ))
    (hda : (1 : κ) ⊗ₜ[A] KaehlerDifferential.D R A a ≠ 0) :
    Algebra.FormallySmooth R C := by
  have : Module.Finite A Ω[A⁄R] := KaehlerDifferential.finite R A
  have : Module.Free A Ω[A⁄R] := Module.free_of_flat_of_isLocalRing
  have : Algebra.FormallySmooth R (A ⧸ Ideal.span {a}) :=
    formallySmooth_quotient_of_nonzero_fiber_differential hκ a hda
  exact formallySmooth_of_surjective_of_ker_eq_span f hf a hker

private theorem isSmoothAt_of_surjective_of_principal_ker
    {R B C A κ : Type*} [CommRing R] [CommRing B] [CommRing C]
    [CommRing A] [IsLocalRing A] [Field κ]
    [Algebra R B] [Algebra R C] [Algebra.EssFiniteType R B]
    (f : B →ₐ[R] C) (hf : Function.Surjective f) (a : B)
    (hker : RingHom.ker f = Ideal.span {a}) (q : Ideal C) [q.IsPrime]
    [Algebra.IsSmoothAt R (q.comap f)]
    [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [IsLocalization.AtPrime A (q.comap f)]
    [Algebra B κ] [Algebra A κ] [IsScalarTower B A κ]
    (hκ : Function.Surjective (algebraMap A κ))
    (hda : (1 : κ) ⊗ₜ[B] KaehlerDifferential.D R B a ≠ 0) :
    Algebra.IsSmoothAt R q := by
  let p : Ideal B := q.comap f
  let E := Localization.AtPrime q
  have hle : p.primeCompl ≤ q.primeCompl.comap f.toRingHom := fun _ hb => hb
  let F : A →ₐ[R] E :=
    { toRingHom := IsLocalization.map E f.toRingHom (M := p.primeCompl)
        (T := q.primeCompl) hle
      commutes' := by
        intro r
        change (IsLocalization.map E f.toRingHom hle) (algebraMap R A r) = _
        rw [IsScalarTower.algebraMap_apply R B A, IsLocalization.map_eq]
        change algebraMap C E (f (algebraMap R B r)) = _
        rw [f.commutes]
        exact (IsScalarTower.algebraMap_apply R C E r).symm }
  have hT : p.primeCompl.map f.toRingHom = q.primeCompl := by
    ext c
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro hc
      obtain ⟨b, rfl⟩ := hf c
      exact ⟨b, hc, rfl⟩
  have hF : Function.Surjective F := by
    have : IsLocalization (p.primeCompl.map f.toRingHom) E := hT.symm ▸ inferInstance
    exact IsLocalization.map_surjective_of_surjective p.primeCompl A E hf
  have hKF : RingHom.ker F = Ideal.span {algebraMap B A a} := by
    change RingHom.ker (IsLocalization.map E f.toRingHom
      (M := p.primeCompl) (T := q.primeCompl) hle) = _
    rw [IsLocalization.ker_map E f.toRingHom hT]
    change RingHom.ker f.toRingHom = Ideal.span {a} at hker
    rw [hker, Ideal.map_span, Set.image_singleton]
  have : Algebra.FormallySmooth R (A ⧸ Ideal.span {algebraMap B A a}) :=
    formallySmooth_quotient_of_localization_differential p hκ a hda
  exact formallySmooth_of_surjective_of_ker_eq_span F hF _ hKF

theorem formallySmooth_stalkMap_of_principal_ker
    {Z X S : Scheme.{u}} (i : Z ⟶ X)
    (f : X ⟶ S) [Smooth f] (z : Z)
    (U : X.affineOpens) (V : S.affineOpens) (hz : i z ∈ U.1)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (hW : IsAffineOpen (i ⁻¹ᵁ U.1))
    (hi : Function.Surjective (i.app U.1)) (a : Γ(X, U.1))
    (hker : RingHom.ker (i.app U.1).hom = Ideal.span {a})
    (hda : HasNonzeroRelativeDifferential f (i z)
      ((X.presheaf.germ U.1 (i z) hz).hom a)) :
    ((i ≫ f).stalkMap z).hom.FormallySmooth := by
  let W := i ⁻¹ᵁ U.1
  have hzW : z ∈ W := hz
  have hWV : W ≤ (i ≫ f) ⁻¹ᵁ V.1 := fun y hy => hUV hy
  have hcomp : f.appLE V.1 U.1 hUV ≫ i.app U.1 =
      (i ≫ f).appLE V.1 W hWV := by
    rw [i.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  let R := Γ(S, V.1)
  let B := Γ(X, U.1)
  let C := Γ(Z, W)
  let A := X.presheaf.stalk (i z)
  let κ := X.residueField (i z)
  let : Algebra R B := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let : Algebra R C := ((i ≫ f).appLE V.1 W hWV).hom.toAlgebra
  let : Algebra B A := X.presheaf.algebra_section_stalk ⟨i z, hz⟩
  let : Algebra R A := ((algebraMap B A).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A κ := (X.residue (i z)).hom.toAlgebra
  let : Algebra B κ := ((X.residue (i z)).hom.comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A κ := IsScalarTower.of_algebraMap_eq' rfl
  let φ : B →ₐ[R] C :=
    { toRingHom := (i.app U.1).hom
      commutes' := fun r => ConcreteCategory.congr_hom hcomp r }
  let p := (U.2.primeIdealOf ⟨i z, hz⟩).asIdeal
  let q := (hW.primeIdealOf ⟨z, hzW⟩).asIdeal
  have hpq : q.comap φ = p := by
    have hc := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 W hW le_rfl hzW)
    change Ideal.comap (i.app U.1).hom q = p
    change Ideal.comap (i.appLE U.1 W le_rfl).hom q = p at hc
    rwa [show i.appLE U.1 W le_rfl = i.app U.1 from i.appLE_eq_app] at hc
  have : Algebra.FinitePresentation R B := f.finitePresentation_appLE V.2 U.2 hUV
  have : Algebra.IsSmoothAt R p := by
    have : Algebra.Smooth R B := f.smooth_appLE V.2 U.2 hUV
    infer_instance
  have : IsLocalization.AtPrime A p := U.2.isLocalization_stalk ⟨i z, hz⟩
  have : Algebra.IsSmoothAt R (q.comap φ) := by
    simpa only [hpq] using (inferInstance : Algebra.IsSmoothAt R p)
  have : IsLocalization.AtPrime A (q.comap φ) := by
    simpa only [hpq] using (inferInstance : IsLocalization.AtPrime A p)
  have hnonzero := affineDifferential_ne_zero f U V hUV (i z) hz a hda rfl
  have hsm : Algebra.IsSmoothAt R q :=
    isSmoothAt_of_surjective_of_principal_ker (A := A) (κ := κ)
      φ hi a hker q
      (X.residue_surjective (i z)) hnonzero
  exact (AlgebraicGeometry.formallySmooth_stalkMap_iff V.1 V.2 W hW hWV hzW).mpr hsm

end Stacks.AlgebraicGeometry

end
