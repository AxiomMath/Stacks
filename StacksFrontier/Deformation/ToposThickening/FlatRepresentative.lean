module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Deformation.ToposThickening.CurvatureClass

/-!
# Bounded above flat representatives, and the vanishing of the curvature class on a complex

Let `O` be a sheaf of commutative rings on a site. Every cochain complex of `O`-modules which
vanishes in degrees above `b` receives a termwise surjective quasi-isomorphism from a complex of
flat `O`-modules which again vanishes in degrees above `b`; so every object of `D(O)` with no
cohomology above `b` is represented by such a complex, and every bounded above object by a
bounded above one.

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings whose kernel is an ideal sheaf
`I` of square zero, and let `K₀` be a bounded above complex of `O₀`-modules. When a flat lift of
`K₀` has a lifted differential that already squares to zero — that is, when `K₀` is the
reduction of an honest bounded above complex of flat `O`-modules — its curvature vanishes
identically, so the canonical class `ω(K₀)` of Tag 0DIU is zero. This is the implication
`(2) ⇒ (1)` of Tag 0DIW.

## Main results

* `Deformation.ComplexLift.exists_isFlat_quasiIso_isStrictlyLE`: the flat resolution of a
  complex vanishing in degrees above `b`, again vanishing in degrees above `b`.
* `Deformation.ComplexLift.exists_isFlat_representative_of_isLE`: the bounded above flat
  representative of an object of `D(O)` with no cohomology above `b`.
* `Deformation.ComplexLift.exists_isFlat_representative`: the same for a bounded above object,
  with the bound produced rather than given.
* `Deformation.ComplexLift.curvature_eq_zero`,
  `Deformation.ComplexLift.curvatureMap_eq_zero`,
  `Deformation.ComplexLift.derivedCurvature_eq_zero`: a lifted differential squaring to zero has
  vanishing curvature, at the three levels at which the curvature is recorded.
* `Deformation.ComplexLift.obstructionMap_eq_zero_of_dd_eq_zero`: **Tag 0DIW, `(2) ⇒ (1)`** at a
  flat lift whose lifted differential squares to zero; the full equivalence is
  `Deformation.ComplexLift.omega_eq_zero_iff_nonempty_derivedLift`.

## Implementation notes

Flat resolutions come from the resolution of a complex by a class of objects every object is a
quotient of, `CochainComplex.exists_quasiIso_prop`, applied to the class of flat sheaves of
modules; that flat modules cover is Tag 03EW, and the class contains a zero object because a
zero module is a retract of a flat one. The bound on the resolution is the bound on the complex,
with no loss, which is what makes the resolution usable in the deformation argument: the square
of a lifted differential has to be read off a presentation that is bounded above.

Clause (2) of Tag 0DIW is an object `K` of `D⁻(O)` with `K ⊗^𝐋_O O₀ ≅ K₀`. The canonical class
of Tag 0DIU is attached to a `Deformation.ComplexLift.FlatLift`, that is to a bounded above flat
graded lift of a *complex* `K₀` together with the identification of its reduction with `K₀`; so
clause (2) is used here in the form the class is defined against, namely such a lift whose
differential squares to zero, which is what representing `K` by a bounded above complex of flat
`O`-modules produces. Vanishing is then the uniqueness clause
`Deformation.ComplexLift.eq_curvature_of_unit_comp` applied to the zero map.

## References

* [Stacks Project, Tag 0DIW](https://stacks.math.columbia.edu/tag/0DIW)
* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w d

namespace Deformation.ComplexLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

section FlatRepresentative

variable [HasSheafify J AddCommGrpCat.{w}] (O : Sheaf J CommRingCat.{w})

/-- Flatness of a sheaf of `O`-modules, as a property of objects of `Mod(O)`. -/
def flatModules : ObjectProperty (SheafMod O) :=
  fun F => AlgebraicGeometry.SheafOfModules.IsFlat (O := O) F

/-- A zero sheaf of `O`-modules is flat. -/
theorem flatModules_of_isZero (F : SheafMod O) (hF : IsZero F) : flatModules O F := by
  obtain ⟨N, p, hN, -⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat O F
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_retract O (hF.to_ N) p
    (hF.eq_of_src _ _) hN

/-- The class of flat sheaves of `O`-modules contains a zero object. -/
instance : (flatModules O).ContainsZero :=
  ⟨⟨kernel (𝟙 (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))),
    isZero_kernel_of_mono _, flatModules_of_isZero O _ (isZero_kernel_of_mono _)⟩⟩

/-- Every sheaf of `O`-modules is a quotient of a flat sheaf of `O`-modules. -/
theorem exists_epi_flatModules (F : SheafMod O) :
    ∃ (G : SheafMod O) (_ : flatModules O G) (p : G ⟶ F), Epi p := by
  obtain ⟨N, p, hN, hp⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat O F
  exact ⟨N, hN, p, hp⟩

/-- A complex of `O`-modules vanishing in degrees above `b` receives a termwise surjective
quasi-isomorphism from a complex of flat `O`-modules vanishing in degrees above `b`. -/
theorem exists_isFlat_quasiIso_isStrictlyLE (b : ℤ)
    (M : CochainComplex (SheafMod O) ℤ) [M.IsStrictlyLE b] :
    ∃ (P : CochainComplex (SheafMod O) ℤ) (p : P ⟶ M)
      (_ : ∀ n, Epi (p.f n)) (_ : QuasiIso p)
      (_ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n)),
      P.IsStrictlyLE b :=
  (CochainComplex.exists_quasiIso_prop (flatModules O) (exists_epi_flatModules O) b).1 M

/-- A complex of `O`-modules with no cohomology above `b` receives a quasi-isomorphism from a
complex of flat `O`-modules vanishing in degrees above `b`. -/
theorem exists_isFlat_quasiIso_isStrictlyLE_of_isLE (b : ℤ)
    (M : CochainComplex (SheafMod O) ℤ) [M.IsLE b] :
    ∃ (P : CochainComplex (SheafMod O) ℤ) (p : P ⟶ M) (_ : QuasiIso p)
      (_ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n)),
      P.IsStrictlyLE b :=
  (CochainComplex.exists_quasiIso_prop (flatModules O) (exists_epi_flatModules O) b).2 M

variable [HasDerivedCategory.{d} (SheafMod O)]

/-- An object of `D(O)` with no cohomology above `b` is represented by a complex of flat
`O`-modules vanishing in degrees above `b`. -/
theorem exists_isFlat_representative_of_isLE (b : ℤ) (E : DerivedCategory (SheafMod O))
    [E.IsLE b] :
    ∃ (P : CochainComplex (SheafMod O) ℤ)
      (_ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n))
      (_ : P.IsStrictlyLE b), Nonempty (DerivedCategory.Q.obj P ≅ E) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := E.exists_iso_Q_obj_of_isLE b
  have : M.IsStrictlyLE b := hM
  obtain ⟨P, p, hq, hflat, hLE⟩ := exists_isFlat_quasiIso_isStrictlyLE_of_isLE O b M
  have : QuasiIso p := hq
  exact ⟨P, hflat, hLE, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e.symm⟩⟩

/-- A bounded above object of `D(O)` is represented by a bounded above complex of flat
`O`-modules. -/
theorem exists_isFlat_representative (E : DerivedCategory.Minus (SheafMod O)) :
    ∃ (b : ℤ) (P : CochainComplex (SheafMod O) ℤ)
      (_ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n))
      (_ : P.IsStrictlyLE b), Nonempty (DerivedCategory.Q.obj P ≅ E.obj) := by
  obtain ⟨b, hb⟩ := E.property
  have : E.obj.IsLE b := hb
  obtain ⟨P, hflat, hLE, he⟩ := exists_isFlat_representative_of_isLE O b E.obj
  exact ⟨b, P, hflat, hLE, he⟩

end FlatRepresentative

section Vanishing

variable [HasWeakSheafify J AddCommGrpCat.{w}]
  {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).Additive]
  {S : SquareZeroIdeal f I}
  {K₀ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀} (T : IdealKernel S L)
  (hdd : ∀ n : ℤ, L.F.d n ≫ L.F.d (n + 1) = 0)

include hdd

/-- A lifted differential that squares to zero has vanishing curvature in every degree: the
zero map satisfies the characterization of the curvature. -/
theorem curvature_eq_zero (n : ℤ) : curvature T n = 0 :=
  (eq_curvature_of_unit_comp T n 0 (by rw [Functor.map_zero, zero_comp, comp_zero, hdd n])).symm

/-- A lifted differential that squares to zero has vanishing curvature class. -/
theorem curvatureMap_eq_zero : curvatureMap T = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [curvatureMap_f, curvature_eq_zero T hdd n, zero_comp, HomologicalComplex.zero_f]

variable [HasDerivedCategory.{d} (SheafMod O₀)]

/-- A lifted differential that squares to zero has vanishing curvature class in the derived
category of the reduction. -/
theorem derivedCurvature_eq_zero (D : DerivedIdealTensor I) : derivedCurvature D T = 0 := by
  simp [derivedCurvature, curvatureMap_eq_zero T hdd]

/-- **Stacks 0DIW, the implication `(2) ⇒ (1)`, at a flat lift whose differential squares to
zero.** If the lifted differential of a flat lift of `K₀` already squares to zero — that is, if
`K₀` is the reduction of a bounded above complex of flat `O`-modules — then the class computed by
that lift vanishes.

The curvature of such a lift is the zero map, because zero satisfies the characterization of the
curvature; and `ω(K₀)` is the curvature transported along isomorphisms. The implication for an
arbitrary `K ∈ D⁻(O)` with `K ⊗^L_O O₀ ≅ K₀` is
`Deformation.ComplexLift.omega_eq_zero_of_nonempty_derivedLift`, and the full equivalence of
Tag 0DIW is `Deformation.ComplexLift.omega_eq_zero_iff_nonempty_derivedLift`. -/
@[stacks 0DIW "(2) implies (1), at a flat lift whose lifted differential squares to zero"]
theorem obstructionMap_eq_zero_of_dd_eq_zero (D : DerivedIdealTensor I) :
    obstructionMap D T = 0 := by
  simp [obstructionMap, derivedCurvature_eq_zero T hdd D]

end Vanishing

end Deformation.ComplexLift

end
