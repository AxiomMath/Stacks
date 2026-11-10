module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Reduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.AffineChart
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Nilpotent.Descent

/-!
# Local finite presentation under an infinitesimal deformation

In a cartesian finite-order deformation diagram in which the enlarged source is flat over the
enlarged base, the morphism of closed subschemes is locally of finite presentation exactly when
the morphism of ambient schemes is.

The reverse implication is base change. The forward one reduces, by
`Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.lift_of_isFirstOrderThickening`, to
the case of a first-order thickening of the base. There the question is affine-local: on charts
the deformation is a flat `R'`-algebra `B'` over an `A'`-algebra, with `I ⊆ R'` square-zero,
whose reduction `B' / I B' ` is of finite presentation over `A' / I A'`. One lifts a
presentation of the reduction to a presentation of `B'` over `A'`: Stacks Tag 0G8U makes `B'`
of finite type, and flatness of `B'` over `R'` gives `I P ∩ K ⊆ I P · K` for the kernel `K` of
the chosen polynomial surjection, which forces the lifted relations to generate `K`.

## Main results

* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.locallyOfFinitePresentation_iff`

## Implementation notes

Both sides use Mathlib's `AlgebraicGeometry.LocallyOfFinitePresentation`. The affine-local step
is stated for rings rather than for schemes, as
`Stacks.Thickenings.algebraMap_finitePresentation_of_flat_squareZero`, and the chart data is
assembled by `Stacks.Thickenings.FirstOrderThickeningChart`.

## References

* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- An ideal squeezed between `L` and `L ⊔ I * K`, for a square-zero ideal `I`, equals `L`. -/
theorem Ideal.eq_of_le_of_le_sup_mul_of_sq_eq_bot {R : Type*} [CommRing R] {I K L : Ideal R}
    (hI : I ^ 2 = ⊥) (hLK : L ≤ K) (hK : K ≤ L ⊔ I * K) : K = L := by
  have hIK : I * K ≤ L :=
    calc
      I * K ≤ I * (L ⊔ I * K) := Ideal.mul_mono le_rfl hK
      _ = I * L ⊔ I * (I * K) := by rw [Ideal.mul_sup]
      _ ≤ L := by
        apply sup_le Ideal.mul_le_right
        rw [← Ideal.mul_assoc, ← pow_two, hI, Ideal.bot_mul]
        exact bot_le
  exact le_antisymm (hK.trans (sup_le le_rfl hIK)) hLK

/-- If `L ≤ K` have the same image under a surjection `q`, then `K ≤ L ⊔ (ker q ⊓ K)`. -/
theorem Ideal.le_sup_ker_inf_of_map_le {P Q : Type*} [CommRing P] [CommRing Q] {q : P →+* Q}
    (hq : Function.Surjective q) {K L : Ideal P} (hLK : L ≤ K) (h : K.map q ≤ L.map q) :
    K ≤ L ⊔ (RingHom.ker q ⊓ K) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ :=
    (Ideal.mem_map_iff_of_surjective q hq).mp (h (Ideal.mem_map_of_mem q hx))
  refine Submodule.mem_sup.mpr
    ⟨y, hy, x - y, Submodule.mem_inf.mpr ⟨?_, K.sub_mem hx (hLK hy)⟩, by ring⟩
  rw [RingHom.mem_ker, map_sub, hxy, sub_self]

/-- In a commutative square of ring maps with surjective sides, if the kernel of the lower map
is the image of the kernel of the left map, then the kernel of the right map is the image of the
kernel of the upper map. -/
theorem Ideal.map_ker_eq_ker_of_comp_eq {P P₀ B B₀ : Type*} [CommRing P] [CommRing P₀]
    [CommRing B] [CommRing B₀] {p : P →+* B} {qP : P →+* P₀} {qB : B →+* B₀} {p₀ : P₀ →+* B₀}
    (hcomm : qB.comp p = p₀.comp qP) (hp : Function.Surjective p)
    (hqP : Function.Surjective qP) (hker : RingHom.ker qB = (RingHom.ker qP).map p) :
    (RingHom.ker p).map qP = RingHom.ker p₀ := by
  have h (x : P) : qB (p x) = p₀ (qP x) := RingHom.congr_fun hcomm x
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← h, RingHom.mem_ker.mp hx, map_zero]
  · intro x hx
    obtain ⟨y, rfl⟩ := hqP x
    have hy : p y ∈ (RingHom.ker qP).map p := by
      rw [← hker, RingHom.mem_ker, h, RingHom.mem_ker.mp hx]
    obtain ⟨z, hz, hpz⟩ := (Ideal.mem_map_iff_of_surjective p hp).mp hy
    refine (Ideal.mem_map_iff_of_surjective qP hqP).mpr ⟨y - z, ?_, ?_⟩
    · rw [RingHom.mem_ker, map_sub, hpz, sub_self]
    · rw [map_sub, RingHom.mem_ker.mp hz, sub_zero]

/-- Let `I ⊆ R` be square-zero and `K` an ideal of an `R`-algebra `P` with `P / K` flat over
`R`. If the image of `K` under a surjection with kernel `I P` is finitely generated, so is `K`. -/
theorem Ideal.fg_of_fg_map_of_flat_of_sq_eq_bot {R P Q : Type*} [CommRing R] [CommRing P]
    [CommRing Q] [Algebra R P] {I : Ideal R} (hI : I ^ 2 = ⊥) {q : P →+* Q}
    (hq : Function.Surjective q) (hker : RingHom.ker q = I.map (algebraMap R P)) {K : Ideal P}
    [Module.Flat R (P ⧸ K)] (hK : (K.map q).FG) : K.FG := by
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  choose z hzK hzq using fun i : Fin n => (Ideal.mem_map_iff_of_surjective q hq).mp
    (by rw [← hg]; exact Submodule.subset_span (Set.mem_range_self i))
  have hLK : Ideal.span (Set.range z) ≤ K := Ideal.span_le.mpr (Set.range_subset_iff.mpr hzK)
  have hmap : K.map q ≤ (Ideal.span (Set.range z)).map q := by
    rw [← hg, Ideal.map_span, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← hzq i]
    exact Ideal.subset_span ⟨z i, Set.mem_range_self i, rfl⟩
  have hsq : I.map (algebraMap R P) ^ 2 = ⊥ := by rw [← Ideal.map_pow, hI, Ideal.map_bot]
  have hinter : RingHom.ker q ⊓ K ≤ I.map (algebraMap R P) * K := by
    rw [hker]
    exact Ideal.map_inf_le_map_mul_of_flat I K
  exact (Ideal.eq_of_le_of_le_sup_mul_of_sq_eq_bot hsq hLK
    ((Ideal.le_sup_ker_inf_of_map_le hq hLK hmap).trans (sup_le_sup_left hinter _))) ▸
    Submodule.fg_span (Set.finite_range z)

/-- A surjection with kernel `J` induces an isomorphism from the quotient by `J`, compatible with
the quotient map. -/
private theorem exists_ringEquiv_quotient_apply_mk {P Q : Type*} [CommRing P] [CommRing Q]
    {J : Ideal P} {q : P →+* Q} (hq : Function.Surjective q) (hJ : RingHom.ker q = J) :
    ∃ e : (P ⧸ J) ≃+* Q, ∀ a, e (Ideal.Quotient.mk J a) = q a :=
  ⟨(Ideal.quotEquivOfEq hJ.symm).trans (RingHom.quotientKerEquivOfSurjective hq), fun a => by
    simp [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]⟩

/-- A ring map which, modulo ideals `J` and `K`, is identified with a map of finite
presentation induces a map of finite presentation `A' / J → B' / K`. -/
theorem RingHom.FinitePresentation.quotientMap_of_comp_eq {A' B' A B : Type*} [CommRing A']
    [CommRing B'] [CommRing A] [CommRing B] {J : Ideal A'} {K : Ideal B'} {φ' : A' →+* B'}
    {hJK : J ≤ K.comap φ'} (φ : A →+* B) (qA : A' →+* A) (qB : B' →+* B)
    (hqA : Function.Surjective qA) (hqB : Function.Surjective qB) (hJ : RingHom.ker qA = J)
    (hK : RingHom.ker qB = K) (hsq : φ.comp qA = qB.comp φ') (hφ : φ.FinitePresentation) :
    (Ideal.quotientMap K φ' hJK).FinitePresentation := by
  obtain ⟨eA, heA⟩ := exists_ringEquiv_quotient_apply_mk hqA hJ
  obtain ⟨eB, heB⟩ := exists_ringEquiv_quotient_apply_mk hqB hK
  have hconj : Ideal.quotientMap K φ' hJK = eB.symm.toRingHom.comp (φ.comp eA.toRingHom) := by
    ext a
    apply eB.injective
    change eB (Ideal.quotientMap K φ' hJK (Ideal.Quotient.mk J a)) =
      eB (eB.symm (φ (eA (Ideal.Quotient.mk J a))))
    rw [Ideal.quotientMap_mk, heB, heA, RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hsq a).symm
  rw [hconj]
  exact .comp (.of_bijective eB.symm.bijective) (.comp hφ (.of_bijective eA.bijective))

namespace Stacks.Thickenings

universe u

open MvPolynomial

/-- Let `I ⊆ R` be square-zero, `A` an `R`-algebra and `B` a flat `R`-algebra which is an
`A`-algebra compatibly, with `B / I B` of finite presentation over `A / I A`. Then every
surjection onto `B` from a polynomial ring over `A` in finitely many variables has finitely
generated kernel. -/
theorem ker_fg_of_flat_squareZero {R A B ι : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Module.Flat R B] [Finite ι]
    (I : Ideal R) (hI : I ^ 2 = ⊥) (p : MvPolynomial ι A →ₐ[A] B) (hp : Function.Surjective p)
    (hfp : (algebraMap (A ⧸ I.map (algebraMap R A))
      (B ⧸ (I.map (algebraMap R A)).map (algebraMap A B))).FinitePresentation) :
    (RingHom.ker p.toRingHom).FG := by
  let J : Ideal A := I.map (algebraMap R A)
  let K : Ideal B := J.map (algebraMap A B)
  let _ : Algebra (A ⧸ J) (B ⧸ K) := Ideal.Quotient.algebraQuotientMapQuotient
  let qP : MvPolynomial ι A →+* MvPolynomial ι (A ⧸ J) := MvPolynomial.map (Ideal.Quotient.mk J)
  have hqP : Function.Surjective qP :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  let p₀ : MvPolynomial ι (A ⧸ J) →ₐ[A ⧸ J] B ⧸ K :=
    MvPolynomial.aeval fun i => Ideal.Quotient.mk K (p (X i))
  have hcomm : (Ideal.Quotient.mk K).comp p.toRingHom = p₀.toRingHom.comp qP := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Ideal.Quotient.mk K (p (C a)) = p₀ (qP (C a))
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, p.commutes]
      exact (Ideal.Quotient.algebraMap_quotient_map_quotient a).symm
    · intro i
      change Ideal.Quotient.mk K (p (X i)) = p₀ (qP (X i))
      rw [MvPolynomial.map_X, MvPolynomial.aeval_X]
  have hp₀ : Function.Surjective p₀ := by
    intro b
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨x, rfl⟩ := hp b'
    exact ⟨qP x, (RingHom.congr_fun hcomm x).symm⟩
  have hqPker : RingHom.ker qP = I.map (algebraMap R (MvPolynomial ι A)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_map,
      IsScalarTower.algebraMap_eq R A (MvPolynomial ι A), MvPolynomial.algebraMap_eq]
  have hpcomp : p.toRingHom.comp (algebraMap A (MvPolynomial ι A)) = algebraMap A B :=
    RingHom.ext p.commutes
  have hker : RingHom.ker (Ideal.Quotient.mk K) = (RingHom.ker qP).map p.toRingHom := by
    rw [Ideal.mk_ker, hqPker, Ideal.map_map, IsScalarTower.algebraMap_eq R A (MvPolynomial ι A),
      ← RingHom.comp_assoc, hpcomp]
    exact Ideal.map_map _ _
  have _ : Algebra.FinitePresentation (A ⧸ J) (B ⧸ K) :=
    RingHom.finitePresentation_algebraMap.mp hfp
  have _ : Module.Flat R (MvPolynomial ι A ⧸ RingHom.ker p.toRingHom) :=
    Module.Flat.of_linearEquiv
      ((Ideal.quotientKerAlgEquivOfSurjective hp).toLinearEquiv.restrictScalars R)
  refine Ideal.fg_of_fg_map_of_flat_of_sq_eq_bot hI hqP hqPker ?_
  rw [Ideal.map_ker_eq_ker_of_comp_eq hcomm hp hqP hker]
  exact Algebra.FinitePresentation.ker_fG_of_surjective p₀ hp₀

/-- Let `I ⊆ R` be a square-zero ideal, `A` an `R`-algebra and `B` a flat `R`-algebra which is
an `A`-algebra compatibly. If `B / I B` is of finite presentation over `A / I A`, then `B` is
of finite presentation over `A`. -/
theorem algebraMap_finitePresentation_of_flat_squareZero
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.Flat R B]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hfp : (Ideal.quotientMap
      ((I.map (algebraMap R A)).map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map).FinitePresentation) :
    (algebraMap A B).FinitePresentation := by
  let J : Ideal A := I.map (algebraMap R A)
  let K : Ideal B := J.map (algebraMap A B)
  have hJ : J ^ 2 = ⊥ := by
    dsimp [J]
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  let _ : Algebra (A ⧸ J) (B ⧸ K) := Ideal.Quotient.algebraQuotientMapQuotient
  have hf₀ : Ideal.quotientMap K (algebraMap A B) Ideal.le_comap_map =
      algebraMap (A ⧸ J) (B ⧸ K) := by
    ext a
    change Ideal.Quotient.mk K (algebraMap A B a) =
      algebraMap (A ⧸ J) (B ⧸ K) (Ideal.Quotient.mk J a)
    exact (Ideal.Quotient.algebraMap_quotient_map_quotient a).symm
  have hfp₀ : (algebraMap (A ⧸ J) (B ⧸ K)).FinitePresentation := by rwa [← hf₀]
  have hft : Algebra.FiniteType A B :=
    finiteType_of_isNilpotent_quotient_finiteType A J B ⟨2, hJ⟩ (by
      simpa only [K] using
        (RingHom.finiteType_algebraMap.mp
          (RingHom.FiniteType.of_finitePresentation hfp₀)))
  obtain ⟨ι, _, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp hft
  exact RingHom.finitePresentation_algebraMap.mpr
    (Algebra.FinitePresentation.of_surjective (f := p) hp
      (ker_fg_of_flat_squareZero I hI p hp hfp₀))

/-- A commutative square of morphisms of schemes induces a commutative square of maps of
sections over an open, an open of the source mapping into it, and their preimages. -/
theorem app_comp_appLE_eq_of_comp_eq {X X' Y Y' : Scheme.{u}} {iX : X ⟶ X'} {iY : Y ⟶ Y'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (hcomm : f ≫ iY = iX ≫ f') (U' : Y'.Opens) (V' : X'.Opens)
    (hV'U : V' ≤ f' ⁻¹ᵁ U') (hVU : iX ⁻¹ᵁ V' ≤ f ⁻¹ᵁ (iY ⁻¹ᵁ U')) :
    iY.app U' ≫ f.appLE (iY ⁻¹ᵁ U') (iX ⁻¹ᵁ V') hVU = f'.appLE U' V' hV'U ≫ iX.app V' := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_hom_eq (f ≫ iY) (iX ≫ f') hcomm U' _ _ _

/-- On compatible affine charts, the ring map of the morphism of ambient schemes is of finite
presentation, in the situation of `locallyOfFinitePresentation_of_firstOrder`. -/
private theorem appLE_finitePresentation_of_firstOrder
    {X X' Y Y' S S' : Scheme.{u}}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (iS : S ⟶ S')
    (pX : X ⟶ S) (pX' : X' ⟶ S') (pY : Y ⟶ S) (pY' : Y' ⟶ S')
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hiS : IsFirstOrderThickening iS)
    (hcartX : IsPullback iX pX pX' iS)
    (hcartY : IsPullback iY pY pY' iS)
    (hfpX' : f' ≫ pY' = pX')
    (hcomm : f ≫ iY = iX ≫ f')
    (hflat : Flat pX') (hf : LocallyOfFinitePresentation f)
    {W' : S'.Opens} {U' : Y'.Opens} {V' : X'.Opens}
    (hW' : IsAffineOpen W') (hU' : IsAffineOpen U') (hV' : IsAffineOpen V')
    (hUW : U' ≤ pY' ⁻¹ᵁ W') (hVW : V' ≤ pX' ⁻¹ᵁ W') (hV'U : V' ≤ f' ⁻¹ᵁ U') :
    (f'.appLE U' V' hV'U).hom.FinitePresentation := by
  have hIX : IsFirstOrderThickening iX :=
    isFirstOrderThickening_isStableUnderBaseChange.of_isPullback hcartX.flip hiS
  have hIY : IsFirstOrderThickening iY :=
    isFirstOrderThickening_isStableUnderBaseChange.of_isPullback hcartY.flip hiS
  have _ : IsClosedImmersion iX := hIX.1
  have _ : IsClosedImmersion iY := hIY.1
  have hVU : iX ⁻¹ᵁ V' ≤ f ⁻¹ᵁ (iY ⁻¹ᵁ U') := by
    intro x hx
    change iY (f x) ∈ U'
    have hpoint : f' (iX x) = iY (f x) := by
      simpa [Scheme.Hom.comp_apply] using (congrArg (fun g : X ⟶ Y' => g x) hcomm).symm
    rw [← hpoint]
    exact hV'U hx
  let CY : FirstOrderThickeningChart :=
    { X := Y, X' := Y', S := S, S' := S', i := iY, j := iS, f := pY, f' := pY'
      i_firstOrder := hIY, j_firstOrder := hiS, cartesian := hcartY
      U' := W', V' := U', U'_affine := hW', V'_affine := hU', mapsTo := hUW }
  let CX : FirstOrderThickeningChart :=
    { X := X, X' := X', S := S, S' := S', i := iX, j := iS, f := pX, f' := pX'
      i_firstOrder := hIX, j_firstOrder := hiS, cartesian := hcartX
      U' := W', V' := V', U'_affine := hW', V'_affine := hV', mapsTo := hVW }
  let α := (pY'.appLE W' U' hUW).hom
  let φ' := (f'.appLE U' V' hV'U).hom
  let _ : Algebra Γ(S', W') Γ(Y', U') := α.toAlgebra
  let _ : Algebra Γ(S', W') Γ(X', V') := (pX'.appLE W' V' hVW).hom.toAlgebra
  let _ : Algebra Γ(Y', U') Γ(X', V') := φ'.toAlgebra
  have hcompSub : V' ≤ (f' ≫ pY') ⁻¹ᵁ W' := hfpX' ▸ hVW
  have hcompMap : (pX'.appLE W' V' hVW).hom = φ'.comp α :=
    congrArg CommRingCat.Hom.hom
      ((Scheme.Hom.appLE_comp_appLE f' pY' W' U' V' hUW hV'U).trans
        (appLE_eq_of_hom_eq (f' ≫ pY') pX' hfpX' W' V' hcompSub hVW)).symm
  have _ : IsScalarTower Γ(S', W') Γ(Y', U') Γ(X', V') := IsScalarTower.of_algebraMap_eq' hcompMap
  have _ : Module.Flat Γ(S', W') Γ(X', V') :=
    RingHom.flat_algebraMap_iff.mp (hflat.flat_appLE hW' hV' hVW)
  let I : Ideal Γ(S', W') := CY.baseIdeal
  let J : Ideal Γ(Y', U') := I.map (algebraMap Γ(S', W') Γ(Y', U'))
  let K : Ideal Γ(X', V') := J.map (algebraMap Γ(Y', U') Γ(X', V'))
  have hK : K = CX.sourceIdeal := by
    dsimp [J, K]
    rw [Ideal.map_map]
    change Ideal.map (φ'.comp α) I = CX.sourceIdeal
    rw [← hcompMap]
  have hquot : (Ideal.quotientMap K φ' Ideal.le_comap_map).FinitePresentation :=
    .quotientMap_of_comp_eq (f.appLE _ _ hVU).hom (iY.app U').hom (iX.app V').hom
      CY.source_app_surjective CX.source_app_surjective CY.sourceIdeal_eq_ker.symm
      (hK.trans CX.sourceIdeal_eq_ker).symm
      (congrArg CommRingCat.Hom.hom (app_comp_appLE_eq_of_comp_eq hcomm U' V' hV'U hVU))
      (hf.finitePresentation_appLE (hU'.preimage iY) (hV'.preimage iX) hVU)
  exact algebraMap_finitePresentation_of_flat_squareZero I CY.baseIdeal_sq_eq_bot hquot

/-- Local finite presentation ascends across a cartesian square of thickenings over a
first-order thickening of the base, when the enlarged source is flat over the enlarged base. -/
private theorem locallyOfFinitePresentation_of_firstOrder
    {X X' Y Y' S S' : Scheme.{u}}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (iS : S ⟶ S')
    (pX : X ⟶ S) (pX' : X' ⟶ S') (pY : Y ⟶ S) (pY' : Y' ⟶ S')
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hiS : IsFirstOrderThickening iS)
    (hcartX : IsPullback iX pX pX' iS)
    (hcartY : IsPullback iY pY pY' iS)
    (hfpX' : f' ≫ pY' = pX')
    (hcomm : f ≫ iY = iX ≫ f')
    (hflat : Flat pX') (hf : LocallyOfFinitePresentation f) :
    LocallyOfFinitePresentation f' := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left]
  intro x'
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW, _⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pX' x')) isOpen_univ
  have hbase (x : X') : pY' (f' x) = pX' x := by
    simpa [Scheme.Hom.comp_apply] using congrArg (fun g : X' ⟶ S' => g x) hfpX'
  have hxU : f' x' ∈ pY' ⁻¹ᵁ (W' : S'.Opens) := by
    change pY' (f' x') ∈ W'
    rwa [hbase x']
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hUW⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open hxU
      (pY' ⁻¹ᵁ (W' : S'.Opens)).isOpen
  let O : X'.Opens := pX' ⁻¹ᵁ (W' : S'.Opens) ⊓ f' ⁻¹ᵁ (U' : Y'.Opens)
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVO⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (show x' ∈ O from ⟨hxW, hxU'⟩) O.2
  have hV'U : (V' : X'.Opens) ≤ f' ⁻¹ᵁ (U' : Y'.Opens) := hVO.trans inf_le_right
  exact ⟨⟨U', hU'⟩, ⟨V', hV'⟩, hxV', hV'U,
    appLE_finitePresentation_of_firstOrder iX iY iS pX pX' pY pY' f f' hiS hcartX hcartY hfpX'
      hcomm hflat hf hW' hU' hV' hUW (hVO.trans inf_le_left) hV'U⟩

namespace CartesianFiniteOrderDeformationDiagram

/-- Local finite presentation is invariant under a cartesian finite-order deformation when the
enlarged source is flat over the enlarged base. -/
@[stacks 06AG "locally_finite_presentation"]
theorem locallyOfFinitePresentation_iff
    (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    LocallyOfFinitePresentation D.f ↔ LocallyOfFinitePresentation D.f' :=
  ⟨lift_of_isFirstOrderThickening (P := @LocallyOfFinitePresentation)
    (fun E hfirst hfE => locallyOfFinitePresentation_of_firstOrder
      E.iX E.iY E.iS E.pX E.pX' E.pY E.pY' E.f E.f'
      hfirst E.X_cartesian E.Y_cartesian E.f'_over_S' E.f_thickening_comm E.X'_flat hfE) D,
    property_of_baseChange (@LocallyOfFinitePresentation) D⟩

end CartesianFiniteOrderDeformationDiagram

end Stacks.Thickenings

end
