module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.ReesPullback
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 0630: the conormal algebra of an immersion

Let `i : Z ⟶ X` be an immersion of schemes. By [Stacks, Tag 01R2] it factors as a closed
immersion `i.liftCoborder : Z ⟶ i.coborderRange` followed by the open immersion
`i.coborderRange.ι`. Writing `ℐ` for the ideal sheaf of `i.liftCoborder`, the **conormal
algebra** of `i` is the pullback along `i.liftCoborder` of the Rees algebra `⨁ₙ ℐⁿ`: a sheaf of
nonnegatively graded quasi-coherent algebras on `Z` whose degree `n` is `Iⁿ/Iⁿ⁺¹` on every
affine chart of `X` over which `i` restricts to a closed immersion, `I` being the kernel of the
map on functions.

This file assembles that description. The graded algebra is
`Stacks.Conormal.gradedPullback` of `Stacks.Blowup.reesGradedAlgebra`; its local presentations
come from `Stacks.Conormal.reesPullbackMap`, transported from an affine open of
`i.coborderRange` to the affine open of `X` it comes from.

## Main definitions

* `Stacks.Conormal.chartIdeal`: the kernel ideal of the immersion on an affine chart.
* `Stacks.Conormal.coborderIdeal`: the ideal sheaf of `i.liftCoborder` on `i.coborderRange`.
* `Stacks.Conormal.conormalGradedAlgebra`: the conormal algebra of `i`.
* `Stacks.Conormal.coborderAffineChart`: an affine open `U` of `X` over which `i` restricts to a
  closed immersion, read as an affine open of `i.coborderRange`, with
  `Stacks.Conormal.coborderSectionEquiv` the resulting isomorphism of rings of functions and
  `Stacks.Conormal.coborderPowerEquiv` the resulting bijection of the powers of the two kernel
  ideals.
* `Stacks.Conormal.coborderChartMap`: the local associated-graded presentation on such a chart.
* `Stacks.Conormal.ConormalAlgebraData`: a graded algebra together with those presentations.
* `Stacks.Conormal.conormalAlgebra`: the conormal algebra with its presentations.

## Main results

* `Stacks.Conormal.le_coborderRange_of_isClosedImmersion_resLE`: an affine open over which `i`
  restricts to a closed immersion is contained in `i.coborderRange`, so the chart is a chart of
  the closed-immersion factorization.
* `Stacks.Conormal.coborderAffineChart_preimage`: the two preimages of the chart agree,
  `i.liftCoborder ⁻¹ᵁ U = i ⁻¹ᵁ U`.
* `Stacks.Conormal.coborderChartMap_eq_zero_iff`, `coborderChartMap_surjective`,
  `coborderChartMap_smul`, `coborderChartMap_naturality`, `coborderChartMap_mul` and
  `coborderChartMap_one`: the six properties of the local presentation — its kernel is exactly
  `I(U)ⁿ⁺¹`, it is surjective, and it respects scalars, restriction, multiplication and the
  unit.
* `Stacks.Conormal.exists_conormalAlgebra`: the existence statement, `conormalAlgebra` read as
  the nonemptiness of `ConormalAlgebraData i`.

## Implementation notes

The chart is produced by `AlgebraicGeometry.affineOpensRestrict`, the bijection between the
affine opens of an open subscheme and the affine opens of the ambient scheme contained in it;
the containment is `Stacks.Conormal.le_coborderRange_of_isClosedImmersion_morphismRestrict`,
restated for the `Scheme.Hom.resLE` spelling through
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`. The map on functions of
`i.coborderRange.ι` over an open contained in `i.coborderRange` is an isomorphism, so the ring
of functions on the chart is the ring of functions on `U`, and the two kernel ideals correspond
under it because `i.liftCoborder ≫ i.coborderRange.ι = i`.

The one propositional identification that cannot be avoided is
`i.liftCoborder ⁻¹ᵁ (chart) = i ⁻¹ᵁ U`, which is where the sections of the conormal algebra are
read. It is carried by `AddEquiv.cast` on the family `W ↦ (piece n).val.obj (op W)`, and the
four lemmas `Stacks.Conormal.sectionSmul_cast`, `Stacks.Conormal.gradedMul_cast`,
`Stacks.Conormal.gradedOne_cast` and `Stacks.Conormal.moduleSectionMap_cast`
move it past the scalar action, the graded multiplication, the unit and the restriction maps.
Each is `by cases h; rfl` at free opens, so none of them costs anything at the concrete ones.

`Stacks.Conormal.conormalGradedAlgebra` is an `abbrev` so that `.piece`, `.mul` and `.one`
reduce to those of `Stacks.Conormal.gradedPullback` at reducible transparency; declaring it a
`def` makes the rewrites against `reesPullbackMap` fail to find their patterns.

`Stacks.Conormal.conormalAlgebra` is a concrete construction, and
`Stacks.Conormal.exists_conormalAlgebra` is derived from it.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- The kernel ideal of an immersion on an affine chart of the target. -/
abbrev chartIdeal (U : X.affineOpens) : Ideal Γ(X, U) := RingHom.ker (i.app U).hom

/-- **Restriction to a smaller affine chart carries the kernel ideal into the kernel ideal.**
The map on sections of a morphism of schemes is natural, so a function on the larger chart whose
pullback to the source vanishes has a restriction with the same property. -/
theorem map_mem_chartIdeal {U V : X.affineOpens} (hVU : V.1 ≤ U.1) {a : Γ(X, U)}
    (ha : a ∈ chartIdeal i U) :
    X.presheaf.map (homOfLE hVU).op a ∈ chartIdeal i V := by
  have hnat : (i.app V.1).hom (X.presheaf.map (homOfLE hVU).op a) =
      (Z.presheaf.map ((Opens.map i.base).map (homOfLE hVU)).op).hom ((i.app U.1).hom a) :=
    congrArg (fun f : Γ(X, U.1) ⟶ Γ(Z, i ⁻¹ᵁ V.1) => f.hom a) (i.naturality (homOfLE hVU).op)
  rw [RingHom.mem_ker] at ha ⊢
  rw [hnat, ha, map_zero]

/-- **Restriction to a smaller affine chart carries the powers of the kernel ideal into the
powers of the kernel ideal.** -/
theorem map_mem_chartIdeal_pow {U V : X.affineOpens} (hVU : V.1 ≤ U.1) (n : ℕ) {a : Γ(X, U)}
    (ha : a ∈ chartIdeal i U ^ n) :
    X.presheaf.map (homOfLE hVU).op a ∈ chartIdeal i V ^ n := by
  have h1 : Ideal.map (X.presheaf.map (homOfLE hVU).op).hom (chartIdeal i U) ≤ chartIdeal i V :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_mem_chartIdeal i hVU hx
  refine Ideal.pow_right_mono h1 n ?_
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

variable [IsImmersion i]

/-- **An affine open over which an immersion restricts to a closed immersion lies in the
coborder of its range**, in the `Scheme.Hom.resLE` spelling. -/
theorem le_coborderRange_of_isClosedImmersion_resLE (U : X.Opens)
    (hU : IsClosedImmersion (i.resLE U (i ⁻¹ᵁ U) le_rfl)) : U ≤ i.coborderRange := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hU
  exact le_coborderRange_of_isClosedImmersion_morphismRestrict i U

/-- The ideal sheaf of the closed immersion through which an immersion factors. -/
noncomputable def coborderIdeal : (i.coborderRange.toScheme).IdealSheafData :=
  i.liftCoborder.ker

/-- On an affine open of the coborder, the ideal sheaf of `i.liftCoborder` is the kernel of the
map on functions. -/
theorem coborderIdeal_ideal (U : (i.coborderRange.toScheme).affineOpens) :
    (coborderIdeal i).ideal U = RingHom.ker (i.liftCoborder.app U.1).hom :=
  i.liftCoborder.ker_apply U

/-- **The conormal algebra of an immersion**: the pullback along the closed immersion
`i.liftCoborder` of the Rees algebra of its ideal sheaf. -/
noncomputable abbrev conormalGradedAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf :=
  gradedPullback i.liftCoborder (Stacks.Blowup.reesGradedAlgebra (coborderIdeal i))

/-- Every homogeneous piece of the conormal algebra is quasi-coherent. -/
lemma conormalGradedAlgebra_isQuasicoherent (n : ℤ) :
    ((conormalGradedAlgebra i).piece n).IsQuasicoherent :=
  gradedPullback_isQuasicoherent i.liftCoborder (Stacks.Blowup.reesGradedAlgebra (coborderIdeal i))
    (Stacks.Blowup.reesPiece_isQuasicoherent (coborderIdeal i)) n

/-- The conormal algebra vanishes in negative degrees. -/
lemma conormalGradedAlgebra_negative_isZero (n : ℤ) (hn : n < 0) :
    Limits.IsZero ((conormalGradedAlgebra i).piece n) :=
  gradedPullback_negative_isZero i.liftCoborder
    (Stacks.Blowup.reesGradedAlgebra (coborderIdeal i))
    (Stacks.Blowup.reesPiece_negative_isZero (coborderIdeal i)) n hn

/-! ### Transport along the equality of the two preimages of a chart -/

private theorem sectionMap_comp_cast {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (j : A ⟶ C)
    (hj : f ≫ g = j) (W : C.Opens) (r : Γ(C, W)) :
    (AddEquiv.cast (M := fun V : A.Opens => Γ(A, V))
        (show f ⁻¹ᵁ (g ⁻¹ᵁ W) = j ⁻¹ᵁ W by rw [← hj, Scheme.Hom.comp_preimage]))
        ((f.app (g ⁻¹ᵁ W)).hom ((g.app W).hom r)) = (j.app W).hom r := by
  subst j
  simp only [Scheme.Hom.comp_app, AddEquiv.cast_apply]
  exact eq_of_heq (cast_heq _ _)

/-- **The transport of sections of the structure sheaf along an equality of opens is the
restriction map along that equality.** The transport is only an additive equivalence, while the
restriction map is a ring map; this is what lets a compatibility stated with `AddEquiv.cast` — the
hypothesis of `Stacks.Conormal.ChartAssociatedGradedEquiv.ofQuotientPresentation` — be checked on
generators of a ring. -/
theorem sectionsCast_eq_map {Z : Scheme.{u}} {W W' : Z.Opens} (h : W = W') (x : Γ(Z, W)) :
    (AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) h) x =
      (Z.presheaf.map (homOfLE h.ge).op).hom x := by
  cases h
  rw [show (homOfLE (le_refl W)) = 𝟙 W from Subsingleton.elim _ _, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  rfl

/-- The transport of sections along an equality of opens carries the scalar action of the
sections of the structure sheaf to the scalar action of their transport. -/
theorem sectionSmul_cast (M : Z.Modules) {W W' : Z.Opens} (h : W = W')
    (r : Γ(Z, W)) (x : M.val.obj (op W)) :
    (AddEquiv.cast (M := fun T : Z.Opens => M.val.obj (op T)) h)
        ((show Z.ringCatSheaf.obj.obj (op W) from r) • x) =
      (show Z.ringCatSheaf.obj.obj (op W') from
          (AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) h) r) •
        (AddEquiv.cast (M := fun T : Z.Opens => M.val.obj (op T)) h) x := by
  cases h
  rfl

/-- The transport of sections along an equality of opens is multiplicative for the
multiplication of a sheaf of graded algebras. -/
theorem gradedMul_cast (A : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf)
    (n m : ℤ) {W W' : Z.Opens} (h : W = W') (a : (A.piece n).val.obj (op W))
    (b : (A.piece m).val.obj (op W)) :
    (AddEquiv.cast (M := fun T : Z.Opens => (A.piece (n + m)).val.obj (op T)) h)
        ((A.mul n m).app (op W) a b) =
      (A.mul n m).app (op W')
        ((AddEquiv.cast (M := fun T : Z.Opens => (A.piece n).val.obj (op T)) h) a)
        ((AddEquiv.cast (M := fun T : Z.Opens => (A.piece m).val.obj (op T)) h) b) := by
  cases h
  rfl

/-- The transport of sections along an equality of opens carries the unit of a sheaf of graded
algebras to the unit. -/
theorem gradedOne_cast (A : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf)
    {W W' : Z.Opens} (h : W = W') :
    (AddEquiv.cast (M := fun T : Z.Opens => (A.piece 0).val.obj (op T)) h)
        (A.one.eval (op W)) = A.one.eval (op W') := by
  cases h
  rfl

/-- The transport of sections along an equality of opens commutes with the restriction maps:
restricting and then transporting is transporting and then restricting. -/
theorem moduleSectionMap_cast (M : Z.Modules) {W W' T T' : Z.Opens}
    (hW : W = W') (hT : T = T') (h : T ≤ W) (h' : T' ≤ W') (x : M.val.obj (op W)) :
    (AddEquiv.cast (M := fun S : Z.Opens => M.val.obj (op S)) hT)
        (M.val.map (homOfLE h).op x) =
      M.val.map (homOfLE h').op
        ((AddEquiv.cast (M := fun S : Z.Opens => M.val.obj (op S)) hW) x) := by
  cases hW
  cases hT
  rfl

section Charts

variable (U : X.affineOpens) (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))

include hU

/-- An affine open of `X` over which the immersion restricts to a closed immersion, read as an
affine open of the coborder of its range. -/
noncomputable def coborderAffineChart : (i.coborderRange.toScheme).affineOpens :=
  (affineOpensRestrict i.coborderRange).symm
    ⟨U, le_coborderRange_of_isClosedImmersion_resLE i U.1 hU⟩

/-- The chart is the preimage of `U` under the open immersion `i.coborderRange.ι`. -/
theorem coborderAffineChart_coe :
    (coborderAffineChart i U hU).1 = i.coborderRange.ι ⁻¹ᵁ U.1 := by
  rw [coborderAffineChart, affineOpensRestrict_symm_apply_coe]

/-- The image of the chart under the open immersion `i.coborderRange.ι` is `U`. -/
theorem coborderAffineChart_image :
    (i.coborderRange.ι ''ᵁ (coborderAffineChart i U hU).1) = U.1 := by
  have h := affineOpensRestrict_apply_coe_coe i.coborderRange (coborderAffineChart i U hU)
  simpa [coborderAffineChart] using h.symm

/-- The preimage of the chart under `i.liftCoborder` is the preimage of `U` under `i`. -/
theorem coborderAffineChart_preimage :
    i.liftCoborder ⁻¹ᵁ (coborderAffineChart i U hU).1 = i ⁻¹ᵁ U.1 := by
  rw [coborderAffineChart_coe, ← Scheme.Hom.comp_preimage, i.liftCoborder_ι]

/-- The functions on the chart of the coborder are the functions on the affine open of `X`. -/
noncomputable def coborderSectionEquiv :
    Γ(X, U) ≃+* Γ(i.coborderRange.toScheme, (coborderAffineChart i U hU).1) := by
  haveI : IsIso (i.coborderRange.ι.app U.1) := by
    rw [← coborderAffineChart_image i U hU]
    infer_instance
  change Γ(X, U) ≃+* Γ(i.coborderRange.toScheme, i.coborderRange.ι ⁻¹ᵁ U.1)
  exact (asIso (i.coborderRange.ι.app U.1)).commRingCatIsoToRingEquiv

/-- The isomorphism of rings of functions is the map on functions of `i.coborderRange.ι`. -/
theorem coborderSectionEquiv_apply (a : Γ(X, U)) :
    coborderSectionEquiv i U hU a = (i.coborderRange.ι.app U.1).hom a := rfl

/-- The kernel ideal of `i` over `U` corresponds to the kernel ideal of `i.liftCoborder` over
the chart. -/
theorem coborderSectionEquiv_mem_ideal (a : Γ(X, U)) :
    a ∈ chartIdeal i U ↔
      coborderSectionEquiv i U hU a ∈ (coborderIdeal i).ideal (coborderAffineChart i U hU) := by
  rw [chartIdeal, coborderIdeal_ideal]
  have hker : RingHom.ker (i.app U.1).hom =
      RingHom.ker ((i.liftCoborder ≫ i.coborderRange.ι).app U.1).hom :=
    congrArg (fun f : Z ⟶ X => RingHom.ker (f.app U.1).hom) i.liftCoborder_ι.symm
  rw [hker, Scheme.Hom.comp_app, coborderSectionEquiv_apply]
  rfl

/-- The isomorphism of rings of functions maps the kernel ideal of `i` over `U` onto the kernel
ideal of `i.liftCoborder` over the chart. -/
theorem coborderSectionEquiv_map_ideal :
    Ideal.map (coborderSectionEquiv i U hU) (chartIdeal i U) =
      (coborderIdeal i).ideal (coborderAffineChart i U hU) := by
  ext b
  rw [← Ideal.symm_apply_mem_of_equiv_iff, coborderSectionEquiv_mem_ideal i U hU,
    RingEquiv.apply_symm_apply]

/-- A function on `U` lies in the `n`-th power of the kernel ideal of `i` if and only if its image
lies in the `n`-th power of the kernel ideal of `i.liftCoborder` over the chart. -/
theorem coborderSectionEquiv_mem_power (n : ℕ) (a : Γ(X, U)) :
    a ∈ chartIdeal i U ^ n ↔
      coborderSectionEquiv i U hU a ∈
        (coborderIdeal i).ideal (coborderAffineChart i U hU) ^ n := by
  rw [← coborderSectionEquiv_map_ideal, ← Ideal.map_pow]
  exact Ideal.apply_mem_of_equiv_iff.symm

/-- The powers of the two kernel ideals correspond. -/
noncomputable def coborderPowerEquiv (n : ℕ) :
    ↥(chartIdeal i U ^ n) ≃+
      ↥((coborderIdeal i).ideal (coborderAffineChart i U hU) ^ n) where
  toFun a := ⟨coborderSectionEquiv i U hU a,
    (coborderSectionEquiv_mem_power i U hU n a).mp a.property⟩
  invFun b := ⟨(coborderSectionEquiv i U hU).symm b,
    (coborderSectionEquiv_mem_power i U hU n _).mpr
      (by rw [(coborderSectionEquiv i U hU).apply_symm_apply]; exact b.property)⟩
  left_inv a := Subtype.ext ((coborderSectionEquiv i U hU).symm_apply_apply a)
  right_inv b := Subtype.ext ((coborderSectionEquiv i U hU).apply_symm_apply b)
  map_add' a b := Subtype.ext ((coborderSectionEquiv i U hU).map_add a b)

/-- The bijection of powers of kernel ideals is the isomorphism of rings of functions on
underlying elements. -/
@[simp] theorem coborderPowerEquiv_coe (n : ℕ) (a : ↥(chartIdeal i U ^ n)) :
    ((coborderPowerEquiv i U hU n a : ↥((coborderIdeal i).ideal (coborderAffineChart i U hU) ^ n)) :
        Γ(i.coborderRange.toScheme, (coborderAffineChart i U hU).1)) =
      coborderSectionEquiv i U hU a := rfl

/-! ### The local associated-graded presentation on a chart -/

/-- **The local associated-graded presentation of the conormal algebra on a chart.** An element
of `I(U)ⁿ`, where `I(U)` is the kernel of `Γ(X, U) ⟶ Γ(Z, i⁻¹U)`, as a degree-`n` section of the
conormal algebra over `i⁻¹U`. -/
noncomputable def coborderChartMap (n : ℕ) :
    ↥(chartIdeal i U ^ n) →+
      ((conormalGradedAlgebra i).piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)) :=
  (AddEquiv.cast (M := fun W : Z.Opens =>
      ((conormalGradedAlgebra i).piece (n : ℤ)).val.obj (op W))
    (coborderAffineChart_preimage i U hU)).toAddMonoidHom.comp
      ((reesPullbackMap (coborderIdeal i) i.liftCoborder n
        (coborderAffineChart i U hU)).comp (coborderPowerEquiv i U hU n).toAddMonoidHom)

/-- The local presentation is the Rees-pullback map of the corresponding element of the power of
the ideal over the chart, transported along `coborderAffineChart_preimage`. -/
lemma coborderChartMap_apply (n : ℕ) (a : ↥(chartIdeal i U ^ n)) :
    coborderChartMap i U hU n a =
      AddEquiv.cast (M := fun W : Z.Opens =>
          ((conormalGradedAlgebra i).piece (n : ℤ)).val.obj (op W))
        (coborderAffineChart_preimage i U hU)
        (reesPullbackMap (coborderIdeal i) i.liftCoborder n (coborderAffineChart i U hU)
          (coborderPowerEquiv i U hU n a)) := rfl

/-- **Exactly `I(U)ⁿ⁺¹` dies in degree `n`.** -/
theorem coborderChartMap_eq_zero_iff (n : ℕ) (a : ↥(chartIdeal i U ^ n)) :
    coborderChartMap i U hU n a = 0 ↔ (a : Γ(X, U)) ∈ chartIdeal i U ^ (n + 1) := by
  rw [coborderChartMap_apply, AddEquiv.map_eq_zero_iff,
    reesPullbackMap_eq_zero_iff (coborderIdeal i) i.liftCoborder n (coborderAffineChart i U hU)
      ((coborderAffineChart i U hU).2.preimage i.liftCoborder)
      (coborderIdeal_ideal i (coborderAffineChart i U hU)).symm
      (i.liftCoborder.app_surjective (coborderAffineChart i U hU).1
        (coborderAffineChart i U hU).2)]
  exact (coborderSectionEquiv_mem_power i U hU (n + 1) a).symm

/-- **Every degree-`n` section over the chart comes from `I(U)ⁿ`.** -/
theorem coborderChartMap_surjective (n : ℕ) :
    Function.Surjective (coborderChartMap i U hU n) :=
  ((AddEquiv.cast (M := fun W : Z.Opens =>
        ((conormalGradedAlgebra i).piece (n : ℤ)).val.obj (op W))
      (coborderAffineChart_preimage i U hU)).surjective.comp
    ((reesPullbackMap_surjective (coborderIdeal i) i.liftCoborder n
        (coborderAffineChart i U hU)
        ((coborderAffineChart i U hU).2.preimage i.liftCoborder)
        (i.liftCoborder.app_surjective (coborderAffineChart i U hU).1
          (coborderAffineChart i U hU).2)).comp
      (coborderPowerEquiv i U hU n).surjective))

/-- The scalar carried across the identification of the two preimages of the chart is the image
of the scalar under the map on functions of `i`. -/
private theorem coborderChart_scalar_eq (r : Γ(X, U)) :
    (AddEquiv.cast (M := fun W : Z.Opens => Γ(Z, W)) (coborderAffineChart_preimage i U hU))
        ((i.liftCoborder.app (coborderAffineChart i U hU).1).hom
          (coborderSectionEquiv i U hU r)) = (i.app U.1).hom r := by
  rw [coborderSectionEquiv_apply]
  exact sectionMap_comp_cast i.liftCoborder i.coborderRange.ι i i.liftCoborder_ι U.1 r

/-- **The local presentation is linear over the map on functions.** -/
theorem coborderChartMap_smul (n : ℕ) (r : Γ(X, U)) (a b : ↥(chartIdeal i U ^ n))
    (hb : (b : Γ(X, U)) = r * (a : Γ(X, U))) :
    coborderChartMap i U hU n b =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom r) •
        coborderChartMap i U hU n a := by
  have hba : b = r • a := by
    apply Subtype.ext
    rw [SetLike.val_smul, smul_eq_mul, hb]
  subst hba
  have hp : coborderPowerEquiv i U hU n (r • a) =
      (show (i.coborderRange.toScheme).presheaf.obj
          (op (coborderAffineChart i U hU).1) from coborderSectionEquiv i U hU r) •
        coborderPowerEquiv i U hU n a := by
    refine Subtype.ext ?_
    change coborderSectionEquiv i U hU ((r • a : ↥(chartIdeal i U ^ n)) : Γ(X, U)) =
      coborderSectionEquiv i U hU r * coborderSectionEquiv i U hU (a : Γ(X, U))
    rw [SetLike.val_smul, smul_eq_mul, map_mul]
  rw [coborderChartMap_apply, coborderChartMap_apply, hp,
    reesPullbackMap_smul (coborderIdeal i) i.liftCoborder n (coborderAffineChart i U hU)
      (coborderSectionEquiv i U hU r) (coborderPowerEquiv i U hU n a),
    sectionSmul_cast ((conormalGradedAlgebra i).piece (n : ℤ))
      (coborderAffineChart_preimage i U hU)
      ((i.liftCoborder.app (coborderAffineChart i U hU).1).hom (coborderSectionEquiv i U hU r)),
    coborderChart_scalar_eq]

/-- **The local presentation is multiplicative.** -/
theorem coborderChartMap_mul (n m : ℕ) (a : ↥(chartIdeal i U ^ n)) (b : ↥(chartIdeal i U ^ m))
    (c : ↥(chartIdeal i U ^ (n + m))) (hc : (c : Γ(X, U)) = a * b) :
    coborderChartMap i U hU (n + m) c =
      ((conormalGradedAlgebra i).mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ U.1))
        (coborderChartMap i U hU n a) (coborderChartMap i U hU m b) := by
  rw [coborderChartMap_apply, coborderChartMap_apply, coborderChartMap_apply,
    reesPullbackMap_mul (coborderIdeal i) i.liftCoborder n m (coborderAffineChart i U hU)
      (coborderPowerEquiv i U hU n a) (coborderPowerEquiv i U hU m b)
      (coborderPowerEquiv i U hU (n + m) c)
      (by rw [coborderPowerEquiv_coe, coborderPowerEquiv_coe, coborderPowerEquiv_coe, hc,
        map_mul])]
  exact gradedMul_cast (conormalGradedAlgebra i) (n : ℤ) (m : ℤ)
    (coborderAffineChart_preimage i U hU) _ _

/-- **The class of `1` is the graded unit.** -/
theorem coborderChartMap_one (a : ↥(chartIdeal i U ^ 0)) (ha : (a : Γ(X, U)) = 1) :
    coborderChartMap i U hU 0 a = (conormalGradedAlgebra i).one.eval (op (i ⁻¹ᵁ U.1)) := by
  rw [coborderChartMap_apply,
    reesPullbackMap_one (coborderIdeal i) i.liftCoborder (coborderAffineChart i U hU)
      (coborderPowerEquiv i U hU 0 a)
      (by rw [coborderPowerEquiv_coe, ha, map_one])]
  exact gradedOne_cast (conormalGradedAlgebra i) (coborderAffineChart_preimage i U hU)

/-! ### Compatibility of the local presentations between two charts -/

section TwoCharts

variable (V : X.affineOpens) (hVU : V.1 ≤ U.1)
  (hV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl))

include hVU hV

/-- The chart of a smaller affine open is contained in the chart of the larger one. -/
theorem coborderAffineChart_mono :
    (coborderAffineChart i V hV).1 ≤ (coborderAffineChart i U hU).1 := by
  rw [coborderAffineChart_coe, coborderAffineChart_coe]
  exact fun x hx => hVU hx

/-- The isomorphisms of rings of functions on two charts commute with the restriction maps. -/
theorem coborderSectionEquiv_naturality (a : Γ(X, U)) :
    coborderSectionEquiv i V hV (X.presheaf.map (homOfLE hVU).op a) =
      i.coborderRange.toScheme.presheaf.map
          (homOfLE (coborderAffineChart_mono i U hU V hVU hV)).op
        (coborderSectionEquiv i U hU a) :=
  congrArg (fun f : Γ(X, U) ⟶ Γ(i.coborderRange.toScheme, (coborderAffineChart i V hV).1) =>
      f.hom a)
    (Scheme.Hom.naturality i.coborderRange.ι (homOfLE hVU).op)

/-- **The local presentations commute with restriction between charts.** -/
theorem coborderChartMap_naturality (hZU : i ⁻¹ᵁ V.1 ≤ i ⁻¹ᵁ U.1) (n : ℕ)
    (a : ↥(chartIdeal i U ^ n)) (b : ↥(chartIdeal i V ^ n))
    (hb : (b : Γ(X, V)) = X.presheaf.map (homOfLE hVU).op (a : Γ(X, U))) :
    ((conormalGradedAlgebra i).piece (n : ℤ)).val.map (homOfLE hZU).op
        (coborderChartMap i U hU n a) = coborderChartMap i V hV n b := by
  have hZW : i.liftCoborder ⁻¹ᵁ (coborderAffineChart i V hV).1 ≤
      i.liftCoborder ⁻¹ᵁ (coborderAffineChart i U hU).1 :=
    fun x hx => coborderAffineChart_mono i U hU V hVU hV hx
  rw [coborderChartMap_apply, coborderChartMap_apply,
    ← moduleSectionMap_cast ((conormalGradedAlgebra i).piece (n : ℤ))
      (coborderAffineChart_preimage i U hU) (coborderAffineChart_preimage i V hV) hZW hZU,
    reesPullbackMap_naturality (coborderIdeal i) i.liftCoborder n
      (coborderAffineChart i V hV) (coborderAffineChart i U hU)
      (coborderAffineChart_mono i U hU V hVU hV) hZW
      (coborderPowerEquiv i U hU n a) (coborderPowerEquiv i V hV n b)
      (by rw [coborderPowerEquiv_coe, coborderPowerEquiv_coe, hb,
        coborderSectionEquiv_naturality])]

end TwoCharts

end Charts

end Stacks.Conormal

namespace Stacks.Conormal

/-! ### Tag 0630: the conormal algebra of an immersion -/

/-- A graded sheaf of algebras with the canonical local presentations by
consecutive powers of the ideal of an immersion. -/
structure ConormalAlgebraData {Z X : Scheme.{u}} (i : Z ⟶ X) where
  /-- The graded algebra on the source scheme. -/
  algebra : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf
  /-- Its homogeneous sheaves are quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (algebra.piece n).IsQuasicoherent
  /-- It is concentrated in nonnegative degrees. -/
  negative_isZero (n : ℤ) (hn : n < 0) : Limits.IsZero (algebra.piece n)
  /-- On an affine closed-immersion chart, elements of `I^n` give degree-`n`
  sections of the conormal algebra. -/
  localMap (U : X.affineOpens)
      (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
      (n : ℕ) : ↥(chartIdeal i U ^ n) →+
        (algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1))
  /-- Exactly `I^(n+1)` maps to zero. -/
  localMap_eq_zero_iff (U : X.affineOpens)
      (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (n : ℕ)
      (a : ↥(chartIdeal i U ^ n)) :
    localMap U hU n a = 0 ↔ (a : Γ(X, U)) ∈ chartIdeal i U ^ (n + 1)
  /-- Every local homogeneous section on such a chart has a representative. -/
  localMap_surjective (U : X.affineOpens)
      (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (n : ℕ) :
    Function.Surjective (localMap U hU n)
  /-- The quotient presentation is linear for the canonical map from the
  functions on the ambient affine chart to those on the source chart. -/
  localMap_smul (U : X.affineOpens)
      (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
      (n : ℕ) (r : Γ(X, U)) (a b : ↥(chartIdeal i U ^ n))
      (hb : (b : Γ(X, U)) = r * (a : Γ(X, U))) :
    localMap U hU n b =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom r) •
        localMap U hU n a
  /-- The quotient presentations commute with restriction between affine
  closed-immersion charts. -/
  localMap_naturality (U V : X.affineOpens) (hVU : V.1 ≤ U.1)
      (hZU : (i ⁻¹ᵁ V.1) ≤ (i ⁻¹ᵁ U.1))
      (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
      (hV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl))
      (n : ℕ) (a : ↥(chartIdeal i U ^ n)) (b : ↥(chartIdeal i V ^ n))
      (hb : (b : Γ(X, V)) = X.presheaf.map (homOfLE hVU).op (a : Γ(X, U))) :
    (algebra.piece (n : ℤ)).val.map (homOfLE hZU).op (localMap U hU n a) =
      localMap V hV n b
  /-- The presentation is multiplicative. -/
  localMap_mul (U : X.affineOpens)
      (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (n m : ℕ)
      (a : ↥(chartIdeal i U ^ n)) (b : ↥(chartIdeal i U ^ m))
      (c : ↥(chartIdeal i U ^ (n + m))) (hc : (c : Γ(X, U)) = a * b) :
    localMap U hU (n + m) c =
      (algebra.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ U.1))
        (localMap U hU n a) (localMap U hU m b)
  /-- The class of `1` is the graded unit. -/
  localMap_one (U : X.affineOpens)
      (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
      (a : ↥(chartIdeal i U ^ 0)) (ha : (a : Γ(X, U)) = 1) :
    localMap U hU 0 a = algebra.one.eval (op (i ⁻¹ᵁ U.1))

/-- The conormal algebra of an immersion, together with its local associated-graded quotient
presentations. -/
@[stacks 0630 "the conormal algebra",
  stacks 0631 "its degree-n piece: i_* C_{Z/X, n} = I^n/I^{n+1}",
  ega "IV 16.1.2" "Gr_•(f), immersions"]
noncomputable def conormalAlgebra {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    ConormalAlgebraData i where
  algebra := conormalGradedAlgebra i
  isQuasicoherent := conormalGradedAlgebra_isQuasicoherent i
  negative_isZero := conormalGradedAlgebra_negative_isZero i
  localMap U hU n := coborderChartMap i U hU n
  localMap_eq_zero_iff U hU n a := coborderChartMap_eq_zero_iff i U hU n a
  localMap_surjective U hU n := coborderChartMap_surjective i U hU n
  localMap_smul U hU n r a b hb := coborderChartMap_smul i U hU n r a b hb
  localMap_naturality U V hVU hZU hU hV n a b hb :=
    coborderChartMap_naturality i U hU V hVU hV hZU n a b hb
  localMap_mul U hU n m a b c hc := coborderChartMap_mul i U hU n m a b c hc
  localMap_one U hU a ha := coborderChartMap_one i U hU a ha

/-- **The locally specified associated graded quotient of an immersion exists** as a
quasi-coherent graded algebra. -/
@[ega "IV 16.1.2" "Gr_•(f) existence"]
theorem exists_conormalAlgebra {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    Nonempty (ConormalAlgebraData i) :=
  ⟨conormalAlgebra i⟩

end Stacks.Conormal

end
