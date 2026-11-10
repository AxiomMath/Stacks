module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness at a point of a regular fibre

Let `g : Y ⟶ S` be flat and locally of finite presentation, let `s` be a point of `S` and let `y`
be a point of the scheme-theoretic fibre of `g` over `s`. If the local ring of that fibre at `y`
is a regular local ring and the residue field extension `κ(y)/κ(s)` is separable, then `g` is
smooth at `y`.

Two steps make this up. Over a field, smoothness at a point with separable residue field is
regularity of the local ring there; and the smooth locus of a base change is the inverse image of
the smooth locus, which transfers smoothness of the fibre over `κ(s)` to smoothness of `g`.

## Main results

* `AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk`: for a scheme locally of finite type
  over a field, smoothness at a point whose residue field is separable over the field is
  regularity of the local ring at that point.
* `AlgebraicGeometry.smoothAt_fiberι_of_isRegularLocalRing_stalk`: a flat morphism locally of
  finite presentation is smooth at a point of a fibre whose local ring is regular and whose
  residue field is separable over that of the image point.
* `AlgebraicGeometry.smoothAt_fiberι_of_isField_stalk` and
  `AlgebraicGeometry.smoothAt_of_map_maximalIdeal_eq`: the same conclusion when the local ring of
  the fibre is a field, respectively when the maximal ideal of `𝒪_{S,s}` generates the maximal
  ideal of `𝒪_{Y,y}`.

## Implementation notes

Separability of a field extension is `Algebra.IsSeparableExtension`, which does not presuppose
algebraicity, and the `κ(s)`-algebra structure of `κ(y)` is the one induced by the structure
morphism of the fibre: a global function on `Spec κ(s)` is pulled back and evaluated at `y`. That
structure is supplied inside the statements, since it is not an instance.

The ring-theoretic input is read on an affine chart, over which the base is `Γ(Spec κ(s), ⊤)`
rather than `κ(s)` itself. Separability travels across that isomorphism as formal smoothness,
which is invariant under isomorphism of arrows, and
`Algebra.FormallySmooth.iff_isSeparableExtension` converts in both directions.

The two inputs are `Algebra.isSmoothAt_iff_isRegularLocalRing` and
`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`, read at a point of a
fibre.

## References

* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
* [Stacks Project, Tag 030O](https://stacks.math.columbia.edu/tag/030O)
-/

public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Evaluating a pulled-back global function at a point is the same as evaluating it there after
restriction to an open neighbourhood. -/
private theorem appLE_top_evaluation {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens) (x : X)
    (hxV : x ∈ V) (hVU : V ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ V hVU ≫ X.evaluation V x hxV = f.appTop ≫ X.Γevaluation x := by
  simp only [Scheme.Hom.appLE, Scheme.evaluation, Scheme.Γevaluation, Scheme.Hom.appTop,
    Category.assoc]
  rw [← Category.assoc (X.presheaf.map (homOfLE hVU).op), X.presheaf.germ_res]
  simp

/-- **Over a field, smoothness at a point with separable residue field is regularity of the local
ring.** Let `X` be a scheme locally of finite type over a field `k` and let `x` be a point of `X`
whose residue field is separable over `k`. Then `X` is smooth over `k` at `x` if and only if the
local ring `𝒪_{X,x}` is a regular local ring. -/
@[ega "IV 17.15.1",
  ega "IV 17.15.9" "a)",
  sga "1 II 5.10" "more general",
  sga "1 II 5.3" "more general"]
theorem smoothAt_iff_isRegularLocalRing_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hsep : letI : Algebra k (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparableExtension k (X.residueField x)) :
    InfinitesimalLifting.SmoothAt f x ↔ IsRegularLocalRing (X.presheaf.stalk x) := by
  let _ : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : (Spec (.of k)).Opens) := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let _ : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.isField (Field.toIsField k)).toField
  let _ : Algebra Γ(Spec (.of k), ⊤) Γ(X, V) := (f.appLE ⊤ V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, V) := f.finiteType_appLE hU hV hVU
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let eL : (X.presheaf.stalk x) ≃ₐ[Γ(X, V)] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl _ _
  let e : (↥(X.residueField x)) ≃+* q.ResidueField :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have he (r : Γ(X, V)) : e (X.evaluation V x hxV r) = algebraMap Γ(X, V) q.ResidueField r := by
    change IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
        (IsLocalRing.residue _ ((X.presheaf.germ V x hxV).hom r)) = _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue,
      IsScalarTower.algebraMap_apply Γ(X, V) (Localization.AtPrime q) q.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
    congr 1
    exact eL.commutes r
  have key : (algebraMap Γ(Spec (.of k), ⊤) q.ResidueField)
      = (e : ↥(X.residueField x) →+* q.ResidueField).comp
          ((f.appTop ≫ X.Γevaluation x).hom) := by
    ext a
    have h1 := congrArg (fun φ : Γ(Spec (.of k), ⊤) ⟶ X.residueField x => φ.hom a)
      (appLE_top_evaluation f V x hxV hVU)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1 ⊢
    rw [IsScalarTower.algebraMap_apply Γ(Spec (.of k), ⊤) Γ(X, V) q.ResidueField, ← h1]
    exact (he ((f.appLE ⊤ V hVU).hom a)).symm
  have hfs : Algebra.FormallySmooth Γ(Spec (.of k), ⊤) q.ResidueField := by
    rw [← RingHom.formallySmooth_algebraMap, key]
    refine (RingHom.FormallySmooth.respectsIso.cancel_right_isIso
      (f.appTop ≫ X.Γevaluation x) e.toCommRingCatIso.hom).mpr ?_
    refine (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of k)).inv (f.appTop ≫ X.Γevaluation x)).mp ?_
    exact RingHom.formallySmooth_algebraMap.mpr
      ((Algebra.FormallySmooth.iff_isSeparableExtension k _).mpr hsep)
  have := (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mp hfs
  rw [← Algebra.isSmoothAt_iff_isRegularLocalRing (k := Γ(Spec (.of k), ⊤)) q
    (X.presheaf.stalk x), show Algebra.IsSmoothAt Γ(Spec (.of k), ⊤) q ↔ _ from
      (formallySmooth_stalkMap_iff (⊤ : (Spec (.of k)).Opens) hU V hV hVU hxV).symm]
  exact ⟨InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x,
    InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f x⟩

/-- **A flat morphism locally of finite presentation is smooth at a point of a regular fibre.**
Let `g : Y ⟶ S` be flat and locally of finite presentation and let `y` be a point of the fibre of
`g` over `s` whose local ring is a regular local ring and whose residue field is separable over
`κ(s)`. Then `g` is smooth at the image of `y` in `Y`. -/
@[ega "IV 17.5.1" "b')⇒a), b)⇒a)", sga "1 II 5.3" "more general"]
theorem smoothAt_fiberι_of_isRegularLocalRing_stalk {Y S : Scheme.{u}} (g : Y ⟶ S)
    [Flat g] [LocallyOfFinitePresentation g] (s : S) (y : g.fiber s)
    (hreg : IsRegularLocalRing ((g.fiber s).presheaf.stalk y))
    (hsep : letI : Algebra (S.residueField s) ((g.fiber s).residueField y) :=
        ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
          (g.fiberToSpecResidueField s).appTop ≫ (g.fiber s).Γevaluation y).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField s) ((g.fiber s).residueField y)) :
    InfinitesimalLifting.SmoothAt g (g.fiberι s y) := by
  have hsq : IsPullback (g.fiberι s) (g.fiberToSpecResidueField s) g
      (S.fromSpecResidueField s) := IsPullback.of_hasPullback _ _
  have : LocallyOfFinitePresentation (g.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFinitePresentation
      (Limits.pullback.snd g (S.fromSpecResidueField s)))
  have hsm : InfinitesimalLifting.SmoothAt (g.fiberToSpecResidueField s) y :=
    (smoothAt_iff_isRegularLocalRing_stalk (k := ↥(S.residueField s))
      (g.fiberToSpecResidueField s) y hsep).mpr hreg
  have hmem : y ∈ (g.fiberToSpecResidueField s).smoothLocus :=
    Scheme.Hom.mem_smoothLocus.mpr (hsm.formallySmooth_stalkMap _ _)
  rw [Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hsq (Or.inl inferInstance)] at hmem
  obtain ⟨U, hU, W, hW, hWU, hyW, hsmooth⟩ :=
    exists_smooth_of_formallySmooth_stalk g (g.fiberι s y)
      (Scheme.Hom.mem_smoothLocus.mp hmem)
  exact (InfinitesimalLifting.smoothAt_iff_exists_affine g _).2
    ⟨W, U, hW, hU, hyW, hWU, hsmooth⟩

/-- **A flat morphism locally of finite presentation is smooth at a point of a fibre whose local
ring there is a field**, provided the residue field at that point is separable over the residue
field of its image. A field is a regular local ring. -/
@[ega "IV 17.5.1" "b')⇒a), b)⇒a)", sga "1 II 5.3" "special case"]
theorem smoothAt_fiberι_of_isField_stalk {Y S : Scheme.{u}} (g : Y ⟶ S)
    [Flat g] [LocallyOfFinitePresentation g] (s : S) (y : g.fiber s)
    (hfld : IsField ((g.fiber s).presheaf.stalk y))
    (hsep : letI : Algebra (S.residueField s) ((g.fiber s).residueField y) :=
        ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
          (g.fiberToSpecResidueField s).appTop ≫ (g.fiber s).Γevaluation y).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField s) ((g.fiber s).residueField y)) :
    InfinitesimalLifting.SmoothAt g (g.fiberι s y) := by
  refine smoothAt_fiberι_of_isRegularLocalRing_stalk g s y ?_ hsep
  let _ : Field ((g.fiber s).presheaf.stalk y) := hfld.toField
  infer_instance

/-- **A flat morphism locally of finite presentation is smooth at a point where the maximal ideal
of the base local ring generates the maximal ideal.** If the maximal ideal of `𝒪_{S,g x}`
generates the maximal ideal of `𝒪_{Y,x}`, the local ring of the fibre at `x` is the residue field
`κ(x)`, so it is a field; separability of the residue field of the fibre over `κ(g x)` then gives
smoothness at `x`. -/
@[sga "1 II 5.3" "special case"]
theorem smoothAt_of_map_maximalIdeal_eq {Y S : Scheme.{u}} (g : Y ⟶ S)
    [Flat g] [LocallyOfFinitePresentation g] (x : Y)
    (hm : Ideal.map (g.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (g x)))
      = IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
    (hsep : letI : Algebra (S.residueField (g x))
              ((g.fiber (g x)).residueField (g.asFiber x)) :=
            ((Scheme.ΓSpecIso (S.residueField (g x))).inv ≫
                (g.fiberToSpecResidueField (g x)).appTop ≫
                  (g.fiber (g x)).Γevaluation (g.asFiber x)).hom.toAlgebra
            Algebra.IsSeparableExtension (S.residueField (g x))
              ((g.fiber (g x)).residueField (g.asFiber x))) :
    InfinitesimalLifting.SmoothAt g x := by
  have hfld : IsField ((g.fiber (g x)).presheaf.stalk (g.asFiber x)) :=
    ((Ideal.quotEquivOfEq hm.symm).trans
      (quotientStalkEquivFiberStalk g x)).symm.isField
        (Field.toIsField (IsLocalRing.ResidueField (Y.presheaf.stalk x)))
  have h := smoothAt_fiberι_of_isField_stalk g (g x) (g.asFiber x) hfld hsep
  rwa [g.fiberι_asFiber x] at h

end AlgebraicGeometry
