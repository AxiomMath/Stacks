module

public import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SmoothSlice
public import StacksFrontier.RingTheory.Kaehler.Separable

/-!
# Criteria for a smooth hypersurface slice through a point

Let `f : X ⟶ S` be smooth at `x : X`, with image `s = f x`.  Tag 057C produces a smooth
effective Cartier divisor through `x` from a germ in the maximal ideal of `𝒪_{X,x}` whose
differential is nonzero in the residue-field fibre of the relative differentials.  This file
supplies that germ from hypotheses stated on the scheme-theoretic fibre `X_s` instead:  that the
map `Ω_{X_s/s,x} ⊗_{𝒪_{X_s,x}} κ(x) ⟶ Ω_{κ(x)/κ(s)}` has a nonzero kernel (Stacks tag 057D), and
that the residue field extension `κ(x)/κ(s)` is separable while `x` is not a generic point of
`X_s` (Stacks tag 057F).

## Main results

* `Stacks.AlgebraicGeometry.exists_smooth_divisor_of_nonzero_differential_kernel`:
  Stacks tag 057D.
* `Stacks.AlgebraicGeometry.exists_smooth_divisor_of_separable_residueField`:
  Stacks tag 057F.

## Implementation notes

The source's map `Ω_{X_s/s,x} ⊗_{𝒪_{X_s,x}} κ(x) ⟶ Ω_{κ(x)/κ(s)}` is Mathlib's
`KaehlerDifferential.mapBaseChange`, whose domain has the two tensor factors in the opposite
order;  the two orders are canonically isomorphic, and the left factor is the one carrying the
`κ(x)`-vector space structure.  A linear map has nonzero kernel exactly when it is not
injective, which is how the hypothesis is spelled.

`κ(s)` is `Stacks.FiberCotangentIdentification.targetResidue f x`, which is
`AlgebraicGeometry.Scheme.residueField (f x)` by `rfl` but in the spelling for which the
quotient algebra instances are found by instance search, and `Ω_{X_s/s,x}` is read as the Kähler
differentials `Ω[𝒪_{X_s,x}⁄κ(s)]` of the local ring of the fibre:  these are identified by
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, which is the
localization statement of Stacks tag 00RT that the source's proof opens with.

The `κ(s)`-algebra structure on `κ(x)` is the one induced by
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`, i.e. the canonical residue field extension of
the source.  That it agrees with the composite `κ(s) → 𝒪_{X_s,x} → κ(x)` through the local ring
of the fibre, which is the factorization the proof needs, is
`Stacks.AlgebraicGeometry.algebraMap_fiberStalk_comp_eq_residueFieldMap`;  this is the only new
compatibility statement here, and it is proved by reducing along the surjection
`𝒪_{S,s} ↠ κ(s)` to `AlgebraicGeometry.Scheme.residue_residueFieldMap`.

The passage from the fibre back to `X` uses only the first two of the three steps of the
comparison of Stacks tag 01V9 built in `StacksDraft.AlgebraicGeometry.FiberCotangentAssembly`,
namely `Stacks.FiberCotangentAssembly.sourceCongr` and
`Stacks.FiberCotangentAssembly.middleCongr`;  their composite lands in
`κ(x) ⊗ Ω[𝒪_{X_s,x}⁄κ(s)]`, which is where the exact sequence of Stacks tag 00RU lives, so the
third step to the differentials of the fibre as a sheaf is not needed.

Two rings are each spelled two ways and instance search unfolds neither:  the stalk of the
structure sheaf is `X.presheaf.stalk x` in `Stacks.AlgebraicGeometry.SmoothSlice` and
`X.sheaf.presheaf.stalk x` in `Stacks.FiberCotangentAssembly`, and the local ring of the fibre
likewise.  Both pairs are equal by `rfl` and not reducibly, so every scalar structure below is
named at the `sheaf.presheaf` spelling, each crossing to the other spelling is done in term mode
by `exact`, and the one scalar tower whose middle ring is spelled the other way is supplied with
its type written out.

Tag 057F is deduced from tag 057D rather than from tag 057C directly, which is where the source
deduces it:  the source's own proof of 057F establishes, from separability and from `𝔪/𝔪² ≠ 0`,
exactly that some `d\overline{h}` is nonzero, and that is the statement that the kernel in the
hypothesis of 057D is nonzero, so routing through 057D reuses the passage from the fibre back to
`X` instead of repeating it.  The two inputs that the source leaves implicit are supplied here:
the local ring of the fibre is Noetherian, because on a neighbourhood of `x` the morphism is
smooth and hence locally of finite type, so that fibre is a locally Noetherian scheme and maps
to `X_s` by an open immersion through the canonical point;  and `κ(x)` is essentially of finite
type over `κ(s)`, by the same restriction.

## References

* [Stacks Project, Tag 057D](https://stacks.math.columbia.edu/tag/057D)
* [Stacks Project, Tag 057F](https://stacks.math.columbia.edu/tag/057F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.FiberCotangentIdentification Stacks.FiberCotangentAssembly
open Stacks.RelativeDifferentialStalkMap Stacks.SmoothAtJacobian
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- **A nonzero kernel of `κ ⊗[R] Ω[R⁄k] → Ω[κ⁄k]` is witnessed by an element of the kernel of
`R → κ`.**  This is the exact sequence of Stacks tag 00RU read backwards:  the kernel of the base
change map is the image of `d : I/I² → κ ⊗[R] Ω[R⁄k]`, so a nonzero kernel produces an element
of `I = ker(R → κ)` whose universal differential is nonzero in the fibre. -/
private theorem exists_mem_ker_tmul_D_ne_zero
    {k R κ : Type*} [CommRing k] [CommRing R] [CommRing κ]
    [Algebra k R] [Algebra R κ] [Algebra k κ] [IsScalarTower k R κ]
    (hsurj : Function.Surjective (algebraMap R κ))
    (hni : ¬ Function.Injective (KaehlerDifferential.mapBaseChange k R κ)) :
    ∃ h : R, algebraMap R κ h = 0 ∧
      (1 : κ) ⊗ₜ[R] KaehlerDifferential.D k R h ≠ (0 : κ ⊗[R] Ω[R⁄k]) := by
  obtain ⟨v, hvker, hvne⟩ :
      ∃ v, KaehlerDifferential.mapBaseChange k R κ v = 0 ∧ v ≠ 0 := by
    by_contra hc
    refine hni fun p q hpq => sub_eq_zero.mp ?_
    by_contra hne
    exact hc ⟨p - q, by simp [hpq], hne⟩
  obtain ⟨w, hw⟩ :=
    (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R κ hsurj v).mp hvker
  obtain ⟨i, hi⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap R κ)) w
  refine ⟨i.1, RingHom.mem_ker.mp i.2, fun hzero => hvne ?_⟩
  rwa [← hw, ← hi, KaehlerDifferential.kerCotangentToTensor_toCotangent]

/-- **The map `𝒪_{X,x} → 𝒪_{X_s,x}` induced by the inclusion of the fibre is surjective.**  It
is an isomorphism of stalks followed by the stalk map of the fibre inclusion, which is a
preimmersion. -/
private theorem surjective_stalkToFiberStalk :
    Function.Surjective (stalkToFiberStalk f x) := by
  intro y
  obtain ⟨b, hb⟩ := (f.fiberι (f x)).stalkMap_surjective (fiberPoint f x) y
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso
    (X.presheaf.stalkCongr (Inseparable.of_eq (fiberι_fiberPoint f x).symm)).hom).2 b
  exact ⟨c, (congrArg ((f.fiberι (f x)).stalkMap (fiberPoint f x)).hom hc).trans hb⟩

/-- `Stacks.AlgebraicGeometry.surjective_stalkToFiberStalk` as surjectivity of the structural
algebra map. -/
private theorem surjective_algebraMap_stalkFiber :
    letI := algebraStalkFiber f x
    Function.Surjective (algebraMap (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))) :=
  surjective_stalkToFiberStalk f x

/-- **The map `𝒪_{X_s,x} → κ(x)` is surjective.**  Composed with `𝒪_{X,x} → 𝒪_{X_s,x}` it is the
residue map of `x`, which is surjective. -/
private theorem surjective_algebraMap_fiberResidueField :
    letI := algebraFiberResidue f x
    Function.Surjective (algebraMap
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x))) := by
  let := algebraFiberResidue f x
  intro y
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal
    (ToType (X.presheaf.stalk x))) y
  exact ⟨_, (ConcreteCategory.congr_hom (stalkClosedPointTo_asFiberHom_comp f x) b).trans hb⟩

/-- `κ(x)` as a `κ(s)`-algebra, through the residue field map of `f` at `x`.  This is the
canonical residue field extension of the source. -/
public abbrev algebraTargetResidueResidueField :
    Algebra (targetResidue f x) (ToType (X.residueField x)) :=
  (f.residueFieldMap x).hom.toAlgebra

/-- **The composite `κ(s) → 𝒪_{X_s,x} → κ(x)` is the residue field map of `f` at `x`.**  The
first map is the structural map of the fibre, the second the one induced by the canonical
residue-field point of the fibre. -/
public theorem algebraMap_fiberStalk_comp_eq_residueFieldMap :
    letI := algebraResidueFiber f x
    letI := algebraFiberResidue f x
    (algebraMap (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
          (ToType (X.residueField x))).comp
        (algebraMap (targetResidue f x)
          (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))) =
      (f.residueFieldMap x).hom := by
  let := algebraStalkMap f x
  let := algebraStalkFiber f x
  let := algebraTargetFiber f x
  let := algebraResidueFiber f x
  let := algebraFiberResidue f x
  let := algebraResidue x
  let := isScalarTowerStalkFiber f x
  let := isScalarTowerTargetResidueFiber f x
  let _ : IsScalarTower (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) := isScalarTower_residueField f x
  refine RingHom.ext fun c => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  have h1 : algebraMap (targetResidue f x)
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
        (algebraMap (ToType (S.presheaf.stalk (f x))) (targetResidue f x) a) =
      algebraMap (ToType (X.sheaf.presheaf.stalk x))
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
        (algebraMap (ToType (S.presheaf.stalk (f x)))
          (ToType (X.sheaf.presheaf.stalk x)) a) :=
    (IsScalarTower.algebraMap_apply (ToType (S.presheaf.stalk (f x))) (targetResidue f x)
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) a).symm.trans
      (IsScalarTower.algebraMap_apply (ToType (S.presheaf.stalk (f x)))
        (ToType (X.sheaf.presheaf.stalk x))
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) a)
  have h2 : algebraMap (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
        (ToType (X.residueField x))
        (algebraMap (ToType (X.sheaf.presheaf.stalk x))
          (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
          ((f.stalkMap x).hom a)) =
      (X.residue x).hom ((f.stalkMap x).hom a) :=
    (IsScalarTower.algebraMap_apply (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) ((f.stalkMap x).hom a)).symm
  show RingHom.comp _ _ _ = _
  rw [RingHom.comp_apply]
  exact (congrArg (algebraMap _ (ToType (X.residueField x))) h1).trans
    (h2.trans (ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap f x) a).symm)

/-- **The scalar tower `κ(s) → 𝒪_{X_s,x} → κ(x)`**, with `κ(x)` a `κ(s)`-algebra through the
residue field map of `f`.  This is
`Stacks.AlgebraicGeometry.algebraMap_fiberStalk_comp_eq_residueFieldMap` in the form the base
change map of Kähler differentials consumes. -/
public theorem isScalarTower_targetResidue_fiberStalk_residueField :
    letI := algebraResidueFiber f x
    letI := algebraFiberResidue f x
    letI := algebraTargetResidueResidueField f x
    IsScalarTower (targetResidue f x)
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) := by
  let := algebraResidueFiber f x
  let := algebraFiberResidue f x
  let := algebraTargetResidueResidueField f x
  exact IsScalarTower.of_algebraMap_eq'
    (algebraMap_fiberStalk_comp_eq_residueFieldMap f x).symm

/-- **The first two steps of the comparison of Stacks tag 01V9 carry the germ of a universal
relative differential to a universal differential of the local ring of the fibre.**  This is
`Stacks.FiberCotangentAssembly.fiberCotangentLinearEquiv_tmul_germ_d` stopped one step early, at
the Kähler differentials of `𝒪_{X_s,x}` over `κ(s)` rather than at the stalk of the sheaf of
relative differentials of the fibre. -/
private theorem middleCongr_sourceCongr_tmul_germ_d
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    (U : X.Opens) (hxU : x ∈ U) (a : ToType (X.presheaf.obj (op U))) :
    letI := algebraStalkMap f x
    letI := algebraResidue x
    letI := algebraStalkFiber f x
    letI := algebraResidueFiber f x
    letI := algebraFiberResidue f x
    middleCongr f x (sourceCongr f x
        ((1 : ToType (X.residueField x)) ⊗ₜ[ToType (X.sheaf.presheaf.stalk x)]
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (Scheme.Hom.relativeDifferentials f).val.presheaf U x hxU).hom
            ((Scheme.Hom.universalRelativeDerivation f).d a)))) =
      (1 : ToType (X.residueField x))
        ⊗ₜ[ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))]
        KaehlerDifferential.D (targetResidue f x)
          (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
          (algebraMap (ToType (X.sheaf.presheaf.stalk x))
            (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
            ((X.presheaf.germ U x hxU).hom a)) := by
  let := algebraStalkMap f x
  let := algebraResidue x
  let := algebraStalkFiber f x
  let := algebraTargetFiber f x
  let := algebraResidueFiber f x
  let := algebraFiberResidue f x
  have hA : (relativeDifferentialsStalkKaehlerEquiv f x)
      ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf U x hxU).hom
        ((Scheme.Hom.universalRelativeDerivation f).d a)) =
      KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
        (ToType (X.sheaf.presheaf.stalk x)) ((X.presheaf.germ U x hxU).hom a) :=
    relativeDifferentialsStalkKaehlerEquiv_germ_d f x
      (OrderDual.toDual (⟨U, hxU⟩ : OpenNhds x)) a
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, hA]
  exact middleCongr_tmul_D f x ((X.presheaf.germ U x hxU).hom a)

/-- **Stacks Project, Tag 057D.**  Let `f : X ⟶ S` be smooth at `x`, with image `s = f x`.  If
the map `Ω_{X_s/s,x} ⊗_{𝒪_{X_s,x}} κ(x) ⟶ Ω_{κ(x)/κ(s)}` has a nonzero kernel, then there is an
affine open neighbourhood `U` of `x` and an effective Cartier divisor `D ⊆ U` containing `x`
with `D ⟶ S` smooth. -/
@[stacks 057D]
public theorem exists_smooth_divisor_of_nonzero_differential_kernel
    (hf : InfinitesimalLifting.SmoothAt f x)
    (hker :
      letI := algebraResidueFiber f x
      letI := algebraFiberResidue f x
      letI := algebraTargetResidueResidueField f x
      letI := isScalarTower_targetResidue_fiberStalk_residueField f x
      ¬ Function.Injective (KaehlerDifferential.mapBaseChange (targetResidue f x)
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
        (ToType (X.residueField x)))) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U) (hxU : x ∈ U)
      (I : U.toScheme.IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor I ∧
      (⟨x, hxU⟩ : U.toScheme) ∈ I.support ∧
      Smooth (I.subschemeι ≫ U.ι ≫ f) := by
  classical
  let := algebraStalkMap f x
  let := algebraResidue x
  let := algebraStalkFiber f x
  let := algebraTargetFiber f x
  let := algebraResidueFiber f x
  let := algebraFiberResidue f x
  let := algebraTargetResidueResidueField f x
  let := isScalarTower_targetResidue_fiberStalk_residueField f x
  let _ : IsScalarTower (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) := isScalarTower_residueField f x
  obtain ⟨h, hh0, hdh⟩ :=
    exists_mem_ker_tmul_D_ne_zero (surjective_algebraMap_fiberResidueField f x) hker
  obtain ⟨b, hb⟩ := surjective_algebraMap_stalkFiber f x h
  have hres : algebraMap (ToType (X.sheaf.presheaf.stalk x))
      (ToType (X.residueField x)) b = 0 := by
    rw [IsScalarTower.algebraMap_apply (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) b, hb, hh0]
  have hbmax : b ∈ IsLocalRing.maximalIdeal (ToType (X.presheaf.stalk x)) := fun hu =>
    not_isUnit_zero (hres ▸ hu.map (algebraMap (ToType (X.sheaf.presheaf.stalk x))
      (ToType (X.residueField x))))
  obtain ⟨W, hxW, a, ha⟩ := X.presheaf.exists_germ_eq b
  have he : algebraMap (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      ((X.presheaf.germ W x hxW).hom a) = h :=
    (congrArg (algebraMap (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))) ha).trans hb
  have hne : ((1 : ToType (X.residueField x)) ⊗ₜ[ToType (X.sheaf.presheaf.stalk x)]
      ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf W x hxW).hom
        ((Scheme.Hom.universalRelativeDerivation f).d a))) ≠ 0 := fun hz => hdh <| by
    simpa only [middleCongr_sourceCongr_tmul_germ_d f x W hxW a, map_zero, he] using
      congrArg (fun z => middleCongr f x (sourceCongr f x z)) hz
  obtain ⟨U, hU, hxU, c, I, hc, hIc, hcart, hxI, hsm⟩ :=
    exists_smooth_effectiveCartierDivisor_of_nonzero_differential f x b hbmax hf
      ⟨W, hxW, a, ha, hne⟩
  exact ⟨U, hU, hxU, I, hcart, hxI, hsm⟩

/-! ### The separable residue field criterion -/

/-- **A separable residue field extension and a positive-dimensional local ring give a nonzero
kernel.**  By Stacks tag 00TU the differential `d : 𝔪/𝔪² → κ ⊗[R] Ω[R⁄k]` is injective, and its
image lies in the kernel of the base change map;  so an injective base change map forces
`𝔪/𝔪² = 0`, which for a Noetherian local ring means `R` is a field and hence has dimension
zero. -/
private theorem mapBaseChange_not_injective_of_pos_ringKrullDim
    (k R κ : Type*) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field κ] [Algebra k R] [Algebra R κ] [Algebra k κ] [IsScalarTower k R κ]
    [Algebra.EssFiniteType k κ] [Algebra.IsSeparableExtension k κ]
    (hsurj : Function.Surjective (algebraMap R κ)) (hdim : 0 < ringKrullDim R) :
    ¬ Function.Injective (KaehlerDifferential.mapBaseChange k R κ) := by
  intro hinj
  have hcot := KaehlerDifferential.kerCotangentToTensor_injective_of_isSeparableExtension
    k R κ hsurj
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R κ hsurj
  have hzero (a : (RingHom.ker (algebraMap R κ)).Cotangent) : a = 0 := by
    apply hcot
    apply hinj
    simpa using hex.apply_apply_eq_zero a
  have hsub : Subsingleton (RingHom.ker (algebraMap R κ)).Cotangent :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  rw [IsLocalRing.ker_eq_maximalIdeal _ hsurj] at hsub
  have hfield := IsLocalRing.subsingleton_cotangentSpace_iff.mp hsub
  exact hdim.ne' (ringKrullDim_eq_zero_of_isField hfield)

/-- **A point that is not a generic point of its fibre has a positive-dimensional local ring on
that fibre.**  Not being a generic point of an irreducible component of the fibre means not being
maximal for the specialization order, which is positivity of the coheight, and the coheight of a
point is the dimension of its local ring. -/
private theorem pos_ringKrullDim_fiberStalk_of_notMem_genericPoints
    (hngen : f.asFiber x ∉ genericPoints (f.fiber (f x))) :
    0 < ringKrullDim ((f.fiber (f x)).presheaf.stalk (fiberPoint f x)) := by
  have hngen' : fiberPoint f x ∉ genericPoints (f.fiber (f x)) := by
    rwa [fiberPoint_eq f x]
  have hnotmax : ¬ IsMax (fiberPoint f x) := by
    intro hmax
    let Z : irreducibleComponents (f.fiber (f x)) :=
      ⟨irreducibleComponent (fiberPoint f x),
        irreducibleComponent_mem_irreducibleComponents _⟩
    let η := genericPoints.ofComponent Z
    have hηx : fiberPoint f x ≤ η.1 := Scheme.le_iff_specializes.mpr
      ((genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent)
    have heq : fiberPoint f x = η.1 := (inseparable_iff_specializes_and.mpr
      ⟨Scheme.le_iff_specializes.mp (hmax hηx), Scheme.le_iff_specializes.mp hηx⟩).eq
    exact hngen' (heq ▸ η.2)
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_pos.mpr hnotmax

/-- **A morphism smooth at `x` is smooth on some open neighbourhood `W` of `x`**, in the form
`W.ι ≫ f`. -/
private theorem exists_smooth_ι_comp_of_smoothAt (hf : InfinitesimalLifting.SmoothAt f x) :
    ∃ W : X.Opens, x ∈ W ∧ Smooth (W.ι ≫ f) := by
  obtain ⟨W, hxW, _⟩ := hf
  refine ⟨W, hxW, ?_⟩
  rw [← f.resLE_comp_ι (U := ⊤) (V := W) le_top]
  infer_instance

/-- **The local ring of the fibre at a smooth point is Noetherian.**  On a neighbourhood `W` of
`x` the morphism is smooth, hence locally of finite type, so the fibre of `W ⟶ S` over `κ(s)` is
a locally Noetherian scheme;  that fibre maps to `X_s` by an open immersion hitting the canonical
point of `X_s`, so the two local rings are isomorphic. -/
private theorem isNoetherianRing_fiberStalk_of_smoothAt
    (hf : InfinitesimalLifting.SmoothAt f x) :
    IsNoetherianRing (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))) := by
  obtain ⟨W, hxW, hgsm⟩ := exists_smooth_ι_comp_of_smoothAt f x hf
  have hrange : Set.range (X.fromSpecResidueField x).base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨t, rfl⟩
    simpa [Scheme.fromSpecResidueField_apply] using hxW
  let a : Spec (X.residueField x) ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι (X.fromSpecResidueField x) hrange
  have haj : a ≫ W.ι = X.fromSpecResidueField x := IsOpenImmersion.lift_fac _ _ _
  have hab : a ≫ (W.ι ≫ f) =
      Spec.map (f.residueFieldMap x) ≫ S.fromSpecResidueField (f x) := by
    rw [← Category.assoc, haj]
    exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x).symm
  have e1 : (W.ι ≫ f) ≫ (𝟙 S) = W.ι ≫ f := by simp
  have e2 : S.fromSpecResidueField (f x) ≫ (𝟙 S) =
      (𝟙 (Spec (S.residueField (f x)))) ≫ S.fromSpecResidueField (f x) := by simp
  let jf : pullback (W.ι ≫ f) (S.fromSpecResidueField (f x)) ⟶ f.fiber (f x) :=
    pullback.map (W.ι ≫ f) (S.fromSpecResidueField (f x)) f
      (S.fromSpecResidueField (f x)) W.ι (𝟙 _) (𝟙 _) e1 e2
  have hoi : IsOpenImmersion jf :=
    Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  have hjfst : jf ≫ f.fiberι (f x) =
      pullback.fst (W.ι ≫ f) (S.fromSpecResidueField (f x)) ≫ W.ι := by
    simp only [jf, Scheme.Hom.fiberι, pullback.map]
    exact pullback.lift_fst _ _ _
  let z : Spec (X.residueField x) ⟶ pullback (W.ι ≫ f) (S.fromSpecResidueField (f x)) :=
    pullback.lift a (Spec.map (f.residueFieldMap x)) hab
  let yW := z (IsLocalRing.closedPoint (X.residueField x))
  have hzf : z ≫ pullback.fst (W.ι ≫ f) (S.fromSpecResidueField (f x)) = a :=
    pullback.lift_fst _ _ _
  have hz1 : z ≫ (jf ≫ f.fiberι (f x)) = X.fromSpecResidueField x := by
    rw [hjfst, ← Category.assoc, hzf, haj]
  have hyW : (f.fiberι (f x)) (jf yW) = x := by
    have h := congrArg (fun q : Spec (X.residueField x) ⟶ X =>
      q (IsLocalRing.closedPoint (X.residueField x))) hz1
    change (f.fiberι (f x)) (jf yW) =
      (X.fromSpecResidueField x) (IsLocalRing.closedPoint (X.residueField x)) at h
    exact h.trans (Scheme.fromSpecResidueField_apply x _)
  have hjpoint : jf yW = fiberPoint f x :=
    (AlgebraicGeometry.IsPreimmersion.isEmbedding (f.fiberι (f x))).injective
      (hyW.trans (fiberι_fiberPoint f x).symm)
  have hln : IsLocallyNoetherian
      (pullback (W.ι ≫ f) (S.fromSpecResidueField (f x))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (W.ι ≫ f) (S.fromSpecResidueField (f x)))
  let eX := (f.fiber (f x)).presheaf.stalkCongr (Inseparable.of_eq hjpoint)
  let e := (asIso (eX.inv ≫ jf.stalkMap yW)).commRingCatIsoToRingEquiv
  exact isNoetherianRing_of_ringEquiv
    ((pullback (W.ι ≫ f) (S.fromSpecResidueField (f x))).presheaf.stalk yW) e.symm

/-- **The residue field extension at a smooth point is essentially of finite type.**  On a
neighbourhood `W` of `x` the morphism is smooth, hence locally of finite type, so its stalk map
and therefore its residue field map are essentially of finite type;  the residue field map of the
inclusion of `W` is an isomorphism and is stripped off. -/
private theorem essFiniteType_residueFieldMap_of_smoothAt
    (hf : InfinitesimalLifting.SmoothAt f x) :
    (f.residueFieldMap x).hom.EssFiniteType := by
  obtain ⟨W, hxW, hgsm⟩ := exists_smooth_ι_comp_of_smoothAt f x hf
  let xW : W.toScheme := ⟨x, hxW⟩
  have hgft : ((W.ι ≫ f).residueFieldMap xW).hom.EssFiniteType :=
    (LocallyOfFiniteType.stalkMap (W.ι ≫ f) xW).residueFieldMap
  rw [Scheme.residueFieldMap_comp] at hgft
  have hinv : (CategoryTheory.inv (W.ι.residueFieldMap xW)).hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (CategoryTheory.inv (W.ι.residueFieldMap xW))).2).essFiniteType
  have h : ((f.residueFieldMap x ≫ W.ι.residueFieldMap xW ≫
      CategoryTheory.inv (W.ι.residueFieldMap xW))).hom.EssFiniteType := hgft.comp hinv
  have he : f.residueFieldMap x ≫ W.ι.residueFieldMap xW ≫
      CategoryTheory.inv (W.ι.residueFieldMap xW) = f.residueFieldMap x :=
    (congrArg (fun z => f.residueFieldMap x ≫ z)
      (IsIso.hom_inv_id (W.ι.residueFieldMap xW))).trans (Category.comp_id _)
  rwa [he] at h

/-- **Stacks Project, Tag 057F.**  Let `f : X ⟶ S` be smooth at `x`, with image `s = f x`.  If
the residue field extension `κ(x)/κ(s)` is separable and `x` is not a generic point of the fibre
`X_s`, then there is an affine open neighbourhood `U` of `x` and an effective Cartier divisor
`D ⊆ U` containing `x` with `D ⟶ S` smooth. -/
@[stacks 057F]
public theorem exists_smooth_divisor_of_separable_residueField
    (hf : InfinitesimalLifting.SmoothAt f x)
    (hsep : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension (ToType (S.residueField (f x)))
        (ToType (X.residueField x)))
    (hngen : f.asFiber x ∉ genericPoints (f.fiber (f x))) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U) (hxU : x ∈ U)
      (I : U.toScheme.IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor I ∧
      (⟨x, hxU⟩ : U.toScheme) ∈ I.support ∧
      Smooth (I.subschemeι ≫ U.ι ≫ f) := by
  let := algebraResidueFiber f x
  let := algebraFiberResidue f x
  let := algebraTargetResidueResidueField f x
  let := isScalarTower_targetResidue_fiberStalk_residueField f x
  let _ : Field (targetResidue f x) :=
    inferInstanceAs (Field (ToType (S.residueField (f x))))
  let _ : IsLocalRing (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
    inferInstanceAs (IsLocalRing (ToType ((f.fiber (f x)).presheaf.stalk (fiberPoint f x))))
  let _ : IsNoetherianRing
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
    isNoetherianRing_fiberStalk_of_smoothAt f x hf
  let _ : Algebra.EssFiniteType (targetResidue f x) (ToType (X.residueField x)) :=
    essFiniteType_residueFieldMap_of_smoothAt f x hf
  let _ : Algebra.IsSeparableExtension (targetResidue f x) (ToType (X.residueField x)) :=
    hsep
  exact exists_smooth_divisor_of_nonzero_differential_kernel f x hf
    (mapBaseChange_not_injective_of_pos_ringKrullDim (targetResidue f x)
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) (surjective_algebraMap_fiberResidueField f x)
      (pos_ringKrullDim_fiberStalk_of_notMem_genericPoints f x hngen))

end Stacks.AlgebraicGeometry

end
