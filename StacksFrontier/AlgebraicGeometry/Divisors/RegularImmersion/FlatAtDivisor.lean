module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularFlatRingMap
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.RelativeFlatness
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier

/-!
# Flatness at a point of a relative effective Cartier divisor

Let `f : X ⟶ S` be a morphism of schemes and `D ⊆ X` a relative effective Cartier divisor over
`S`.  At a point `x` of `D` whose local ring `𝒪_{X,x}` is Noetherian, `f` is flat.

## The argument

Tag 01WS presents `D` near `x` as the vanishing locus of a nonzerodivisor `t` on an affine open
`U ∋ x`.  Its germ `h = t_x` is then a nonzerodivisor of the Noetherian local ring
`B = 𝒪_{X,x}`, because the germ map is flat, and it lies in the maximal ideal because `x` lies
in the support of `D`.  The stalk of `D` at `x` is the kernel of `𝒪_{X,x} ⟶ 𝒪_{D,x}`, so
`B ⧸ (h) ≅ 𝒪_{D,x}`, which is flat over `A = 𝒪_{S,f x}` since `D ⟶ S` is flat.  Flatness then
lifts along the nonzerodivisor `h`, which is
`AlgebraicGeometry.flat_of_regular_quotient_flat`.

## Main results

* `AlgebraicGeometry.stalkMap_ker_localized`: the kernel of the stalk map of a closed immersion
  read on an affine chart, after localization.
* `AlgebraicGeometry.stalk_ker_eq_of_affine_target`: the stalk of the ideal sheaf of a closed
  immersion is the kernel of its stalk map.
* `AlgebraicGeometry.isRegular_map_of_flat` of
  `StacksFrontier.AlgebraicGeometry.Divisors.RegularFlatRingMap`, imported here: a nonzerodivisor
  stays one along a flat ring map.
* `AlgebraicGeometry.isFlatAt_of_relativeEffectiveCartierDivisor`: **Stacks Tag 062U.**

## Implementation notes

The divisor is given by its ideal sheaf data and membership in it is membership in
`Scheme.IdealSheafData.supportSet`; flatness at the point is `AlgebraicGeometry.IsFlatAt`, the
flatness of the induced map of local rings.

The identification of the stalk of the ideal sheaf with the kernel of the stalk map goes
through `IsAffineOpen.arrowStalkMapIso`, which presents both stalks as localizations of the
rings of sections on an affine chart, and `IsLocalization.ker_map`, which computes the kernel of
the localized map of a surjection.

## References

* [Stacks Project, Tag 062U](https://stacks.math.columbia.edu/tag/062U)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Divisors
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The kernel of the stalk map of a closed immersion, after localization.**  On affine charts
`U ⊆ Y` and `V ⊆ f⁻¹U` the stalk map of `f` at `x ∈ V` is the localization of
`Γ(Y, U) ⟶ Γ(X, V)` at the prime of `x`, so its kernel is the extension of the kernel of the
map on sections. -/
theorem stalkMap_ker_localized
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V)
    (hgsurj : Function.Surjective (f.appLE U V hVU).hom) :
    let p := hU.primeIdealOf ⟨f x, (show f x ∈ U from hVU hx)⟩
    let g := (f.appLE U V hVU).hom
    let e := (asIso (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx).hom.left)
      |>.commRingCatIsoToRingEquiv
    Ideal.map e.toRingHom (RingHom.ker (f.stalkMap x).hom) =
      Ideal.map (algebraMap Γ(Y, U) (Localization.AtPrime p.asIdeal))
        (RingHom.ker g) := by
  classical
  dsimp only
  have hfx : f x ∈ U := hVU hx
  let p := hU.primeIdealOf ⟨f x, hfx⟩
  let q := hV.primeIdealOf ⟨x, hx⟩
  let g := (f.appLE U V hVU).hom
  have hcomap : p.asIdeal = Ideal.comap g q.asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm
  let loc := Localization.localRingHom p.asIdeal q.asIdeal g hcomap
  let hArrow := IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx
  let e₁ := (asIso hArrow.hom.left).commRingCatIsoToRingEquiv
  let e₂ := (asIso hArrow.hom.right).commRingCatIsoToRingEquiv
  have hcomm (a : Y.presheaf.stalk (f x)) :
      loc (e₁ a) = e₂ ((f.stalkMap x).hom a) := by
    have hcat := hArrow.hom.w
    change (asIso hArrow.hom.left).hom ≫ CommRingCat.ofHom loc =
      CommRingCat.ofHom (f.stalkMap x).hom ≫ (asIso hArrow.hom.right).hom at hcat
    have hfun := CommRingCat.hom_ext_iff.mp hcat
    have h := congrArg (fun φ : Y.presheaf.stalk (f x) →+* _ => φ a) hfun
    convert h using 1 <;> rfl
  have htransport :
      Ideal.map e₁.toRingHom (RingHom.ker (f.stalkMap x).hom) = RingHom.ker loc := by
    ext z
    rw [Ideal.mem_map_iff_of_surjective e₁.toRingHom e₁.surjective]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [RingHom.mem_ker] at ha ⊢
      change loc (e₁ a) = 0
      rw [hcomm a, ha, map_zero]
    · intro hz
      obtain ⟨a, rfl⟩ := e₁.surjective z
      refine ⟨a, ?_, rfl⟩
      apply e₂.injective
      rw [RingHom.mem_ker] at hz
      simpa [hz] using (hcomm a).symm
  have hT : Submonoid.map g p.asIdeal.primeCompl = q.asIdeal.primeCompl := by
    simpa only [hcomap] using Ideal.map_primeCompl_comap_of_surjective g hgsurj q.asIdeal
  have hkerLoc : RingHom.ker loc =
      Ideal.map (algebraMap Γ(Y, U) (Localization.AtPrime p.asIdeal))
        (RingHom.ker g) := by
    simpa [loc, Localization.localRingHom] using
      (IsLocalization.ker_map (Localization.AtPrime q.asIdeal) g hT)
  rw [htransport, hkerLoc]

/-- **The stalk of the ideal sheaf of a closed immersion is the kernel of its stalk map.** -/
theorem stalk_ker_eq_of_affine_target
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    IdealSheafData.stalk f.ker (f x) =
      RingHom.ker (f.stalkMap x).hom := by
  classical
  let V : X.Opens := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  have hxV : x ∈ V := by simpa [V] using hx
  let hVU : V ≤ f ⁻¹ᵁ U := le_rfl
  let g := (f.appLE U V hVU).hom
  have hgsurj : Function.Surjective g := by
    simpa [g, V, hVU, Scheme.Hom.appLE] using f.app_surjective U hU
  have hcomap : (hU.primeIdealOf ⟨f x, hx⟩).asIdeal =
      Ideal.comap g (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm
  let p := hU.primeIdealOf ⟨f x, hx⟩
  let _ : Algebra Γ(Y, U) (Y.presheaf.stalk (f x)) :=
    Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  have _ : IsLocalization p.asIdeal.primeCompl (Y.presheaf.stalk (f x)) :=
    hU.isLocalization_stalk ⟨f x, hx⟩
  let hArrow := IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hxV
  let e₁ := (asIso hArrow.hom.left).commRingCatIsoToRingEquiv
  have hring : e₁.toRingHom.comp (Y.presheaf.germ U (f x) hx).hom =
      algebraMap Γ(Y, U) (Localization.AtPrime p.asIdeal) := by
    ext s
    change (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Y.presheaf.stalk (f x)) (Localization.AtPrime p.asIdeal)).toRingEquiv
        ((Y.presheaf.germ U (f x) hx).hom s) = _
    change (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Y.presheaf.stalk (f x)) (Localization.AtPrime p.asIdeal)).toRingEquiv
        (algebraMap Γ(Y, U) (Y.presheaf.stalk (f x)) s) = _
    exact (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Y.presheaf.stalk (f x)) (Localization.AtPrime p.asIdeal)).commutes s
  have happ : g = (f.app U).hom := by
    simp [g, V, Scheme.Hom.appLE]
  have hmapIdeal :
      Ideal.map e₁.toRingHom (IdealSheafData.stalk f.ker (f x)) =
        Ideal.map (algebraMap Γ(Y, U)
          (Localization.AtPrime (hU.primeIdealOf ⟨f x, hx⟩).asIdeal))
          (RingHom.ker g) := by
    rw [IdealSheafData.stalk_eq_map_germ f.ker (f x) ⟨U, hU⟩ hx, Scheme.Hom.ker_apply, ← happ,
      Ideal.map_map]
    exact congrArg (fun φ : Γ(Y, U) →+* _ =>
      Ideal.map φ (RingHom.ker g)) hring
  have hmapKer' :
      Ideal.map e₁.toRingHom (RingHom.ker (f.stalkMap x).hom) =
        Ideal.map (algebraMap Γ(Y, U)
          (Localization.AtPrime (hU.primeIdealOf ⟨f x, hx⟩).asIdeal))
          (RingHom.ker g) := by
    simpa [g, hcomap] using stalkMap_ker_localized f x U hU V hV hVU hxV hgsurj
  simpa only [Ideal.comap_map_of_bijective e₁.toRingHom e₁.bijective] using
    congrArg (Ideal.comap e₁.toRingHom) (hmapIdeal.trans hmapKer'.symm)


/-- **Stacks Project, Tag 062U.**  The ambient morphism is flat at a point of a relative
effective Cartier divisor whose ambient local ring is Noetherian. -/
@[stacks 062U]
theorem isFlatAt_of_relativeEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
    (hI : IsRelativeEffectiveCartierDivisor f I)
    (x : X) (hx : x ∈ I.supportSet)
    (hNoetherian : IsNoetherianRing (X.presheaf.stalk x)) :
    IsFlatAt f.toLRSHom.toShHom x := by
  classical
  have hxSupport : x ∈ I.support :=
    Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hx
  obtain ⟨U, hU, hxU, t, ht, e, he⟩ :=
    (isEffectiveCartierDivisor_iff_affineLocal I).mp hI.1 x hx
  let Ua : X.affineOpens := ⟨U, hU⟩
  have hIdeal : I.ideal Ua = Ideal.span {t} :=
    ideal_eq_quotient_of_chart I U hU (Ideal.span {t}) e he
  let i := I.subschemeι
  have hxRange : x ∈ Set.range i := by
    change x ∈ Set.range I.subschemeι
    rw [I.range_subschemeι]
    exact hxSupport
  obtain ⟨y, hy⟩ := hxRange
  have hyU : i y ∈ U := by simpa [hy] using hxU
  let B := X.presheaf.stalk (i y)
  let A := S.presheaf.stalk (f (i y))
  let C := I.subscheme.presheaf.stalk y
  let germ := (X.presheaf.germ Ua.1 (i y) hyU).hom
  let h := germ t
  let ψ : B →+* C := (i.stalkMap y).hom
  let φ : A →+* B := (f.stalkMap (i y)).hom
  let α : A →+* C := ((i ≫ f).stalkMap y).hom
  have hStalkIdeal : IdealSheafData.stalk I (i y) = Ideal.span {h} := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I (i y) Ua hyU, hIdeal, Ideal.map_span]
    simp [h, germ]
  have hiSupport : i y ∈ I.support := by simpa [hy] using hxSupport
  have hStalkLe : IdealSheafData.stalk I (i y) ≤ IsLocalRing.maximalIdeal B :=
    (stalk_le_maximalIdeal_iff_mem_support I (i y)).2 hiSupport
  have hhmax : h ∈ IsLocalRing.maximalIdeal B := by
    have hmem : h ∈ IdealSheafData.stalk I (i y) := by
      rw [hStalkIdeal]
      exact Ideal.subset_span (by simp)
    exact hStalkLe hmem
  let p := hU.primeIdealOf ⟨i y, hyU⟩
  let _ : Algebra Γ(X, U) B := X.presheaf.algebra_section_stalk ⟨i y, hyU⟩
  have _ : IsLocalization p.asIdeal.primeCompl B := hU.isLocalization_stalk ⟨i y, hyU⟩
  have hflatGerm : RingHom.Flat germ := by
    exact IsLocalization.flat B p.asIdeal.primeCompl
  have hRegular : IsRegular h :=
    isRegular_map_of_flat (φ := germ) hflatGerm ht
  have hsurj : Function.Surjective ψ := i.stalkMap_surjective y
  have hker : RingHom.ker ψ = Ideal.span {h} := by
    calc
      RingHom.ker ψ = IdealSheafData.stalk i.ker (i y) :=
        (stalk_ker_eq_of_affine_target i y U hU hyU).symm
      _ = IdealSheafData.stalk I (i y) := by rw [I.ker_subschemeι]
      _ = Ideal.span {h} := hStalkIdeal
  have hα : α = ψ.comp φ := by
    dsimp [α, ψ, φ]
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  algebraize [φ, ψ, α]
  have _ : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (f.stalkMap (i y)).hom
    infer_instance
  have _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact congrArg (fun g : A →+* C => g a) hα)
  have hflatC : Module.Flat A C := (Flat.iff_flat_stalkMap (i ≫ f)).mp hI.2 y
  let e : B ⧸ RingHom.ker ψ ≃+* C := RingHom.quotientKerEquivOfSurjective hsurj
  have heComm (a : A) : e (algebraMap A (B ⧸ RingHom.ker ψ) a) = algebraMap A C a := by
    change e (Ideal.Quotient.mk (RingHom.ker ψ) (φ a)) = α a
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk, hα]
    rfl
  let eL : (B ⧸ RingHom.ker ψ) ≃ₗ[A] C :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a b
        change e (algebraMap A (B ⧸ RingHom.ker ψ) a * b) =
          algebraMap A C a * e b
        rw [map_mul, heComm] }
  have hflatQuotient : Module.Flat A (B ⧸ Ideal.span {h}) := by
    rw [← hker]
    exact (Module.Flat.equiv_iff eL).mpr hflatC
  have _ : IsNoetherianRing B := by
    cases hy
    exact hNoetherian
  have hflatB : Module.Flat A B :=
    flat_of_regular_quotient_flat h
      (isRegular_iff_mem_nonZeroDivisors.mp hRegular) hhmax hflatQuotient
  have hflatAt : RingHom.Flat (f.stalkMap (i y)).hom := by
    change Module.Flat A B
    exact hflatB
  change RingHom.Flat (f.stalkMap x).hom
  cases hy
  exact hflatAt


end AlgebraicGeometry

end
