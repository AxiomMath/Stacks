module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.AffineVanishingAboveDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DegreeTwoOpenRestrictionSurjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimePowerVanishingStatement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.VanishingAboveDegreeTwo

/-!
# Constant coefficients of order prime to the characteristic on a smooth curve: the Kummer side

Let `X` be a smooth curve over an algebraically closed field `k`, let `ℓ` be invertible in `k`
and let `F` be the constant sheaf `𝐙/ℓ𝐙` on the small étale site of `X`. This file contains the
part of Case I of Stacks 0A5B that is read off the Kummer sequence
`0 → μ_ℓ → 𝐆_m → 𝐆_m → 0` (Tag 03PL), the vanishing `H^q(X, 𝐆_m) = 0` for `q ≥ 2` (Tag 03RM) and
`μ_ℓ ≅ 𝐙/ℓ𝐙`:

* statement (1) of Situation 0A52, `H^q(X, F) = 0` for `q > 2`;
* the reduction of statement (8), the surjectivity of `H²(X, F) → H²(U, F)` for an open
  `U ⊆ X`, to the surjectivity of `H¹(X, 𝐆_m) → H¹(U, 𝐆_m)`.

## Main results

* `subsingleton_sheafH_rootsOfUnitySheaf_of_smoothCurve`: `H^q(X, μ_ℓ) = 0` for `q > 2`.
* `isVanishingAboveDegreeTwo_constantSheaf_of_smoothCurve`: statement (1) for a constant sheaf
  cyclic of order `ℓ`.
* `surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_surjective_X₃`: restriction is
  surjective in degree `q + 1` on the subsheaf of a short exact sequence if it is surjective in
  degree `q` on the quotient and the middle term restricted has no degree-`q + 1` cohomology.
* `isDegreeTwoOpenRestrictionSurjective_constantSheaf_of_multiplicative`: statement (8) for a
  constant sheaf cyclic of order `ℓ`, from the surjectivity of restriction on `H¹(-, 𝐆_m)` along
  every nonempty open.

## References

* [Stacks Project, Tag 0A5B](https://stacks.math.columbia.edu/tag/0A5B)
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-! ### Restriction maps along isomorphisms and short exact sequences -/

section Restriction

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Surjectivity of restriction is invariant under isomorphism of the sheaf.** -/
theorem surjective_etaleCohomologyRestrictionMap_of_iso
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (e : F ≅ G) (q : ℕ)
    (h : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i F q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i G q) := by
  intro y
  obtain ⟨x, hx⟩ := h (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map e.inv))
    (add_zero q))
  refine ⟨x.comp (Ext.mk₀ e.hom) (add_zero q), ?_⟩
  rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i e.hom q x, hx,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id, Ext.comp_mk₀_id]

/-- **Surjectivity of restriction on the subsheaf of a short exact sequence, one degree up.** Let
`0 → F₁ → F₂ → F₃ → 0` be short exact on `X_étale`. If restriction along `i` is surjective in
degree `q` for `F₃`, and the degree-`r = q + 1` cohomology of `i⁻¹F₂` vanishes, then restriction
is surjective in degree `r` for `F₁`: every class downstairs is a boundary, and boundaries are
compatible with restriction. -/
theorem surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_surjective_X₃
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (q r : ℕ) (hqr : q + 1 = r)
    (hvanishing : Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj S.X₂) r))
    (h₃ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ r) := by
  intro y
  obtain ⟨y₃, hy₃⟩ := Ext.covariant_sequence_exact₁ _
    (hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)) y (hvanishing.elim _ _) hqr
  obtain ⟨x₃, hx₃⟩ := h₃ y₃
  refine ⟨x₃.comp hS.extClass hqr, ?_⟩
  rwa [etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} i hS q r hqr x₃, hx₃]

end Restriction

/-! ### Sheaves torsion for two coprime integers -/

/-- **A sheaf of abelian groups that is `p`-power torsion and locally killed by an integer `ℓ`
prime to `p` is zero.** Locally a section is killed by `p ^ r` and by `ℓ`, hence by
`gcd(p ^ r, ℓ) = 1`, and a section of a sheaf vanishing locally vanishes. -/
theorem eq_zero_of_isPrimePowerTorsion_of_coprime {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F : Sheaf J AddCommGrpCat.{w}} {p ℓ : ℕ}
    (hcop : Nat.Coprime p ℓ) (hp : Stacks.Torsion.IsPrimePowerTorsion J p F)
    (hℓ : ∀ (U : C) (y : F.obj.obj (op U)), ∃ R : Sieve U, R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f → ℓ • F.obj.map f.op y = 0)
    (U : C) (y : F.obj.obj (op U)) : y = 0 := by
  obtain ⟨R, hR, hannℓ⟩ := hℓ U y
  refine F.isSeparated U R hR y 0 fun V f hf => ?_
  rw [map_zero]
  have hzℓ : ℓ • F.obj.map f.op y = 0 := hannℓ V f hf
  set z := F.obj.map f.op y
  obtain ⟨R', hR', hannp⟩ := hp V z
  refine F.isSeparated V R' hR' z 0 fun V' g hg => ?_
  rw [map_zero]
  obtain ⟨r, -, hr⟩ := hannp V' g hg
  have hbez := Nat.gcd_eq_gcd_ab (p ^ r) ℓ
  rw [(hcop.pow_left r).gcd_eq_one, Nat.cast_one] at hbez
  set z' := F.obj.map g.op z
  have hℓ' : ℓ • z' = 0 := by rw [← map_nsmul, hzℓ, map_zero]
  calc z' = ((1 : ℤ)) • z' := (one_zsmul z').symm
    _ = Nat.gcdA (p ^ r) ℓ • ((p ^ r : ℕ) • z') + Nat.gcdB (p ^ r) ℓ • (ℓ • z') := by
        rw [hbez, add_smul, mul_comm, mul_comm (ℓ : ℤ), mul_smul, mul_smul, natCast_zsmul,
          natCast_zsmul]
    _ = 0 := by rw [hr, hℓ', smul_zero, smul_zero, add_zero]

/-- **The étale cohomology of a zero sheaf vanishes in every degree.** -/
theorem subsingleton_etaleSheafH_of_isZero {X : Scheme.{u}}
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hF : IsZero F) (q : ℕ) :
    Subsingleton (Sheaf.H.{w} F q) :=
  subsingleton_of_forall_eq 0 fun z => by
    rw [← Ext.comp_mk₀_id z, hF.eq_of_src (𝟙 F) 0, Ext.mk₀_zero, Ext.comp_zero]

/-- **A constant sheaf whose value is killed by `ℓ` is locally killed by `ℓ`**: its sections are
locally constant. -/
theorem exists_sieve_nsmul_eq_zero_constantSheaf {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] (ℓ : ℕ) (E : AddCommGrpCat.{w})
    (hE : ∀ x : E, ℓ • x = 0) (U : C)
    (y : ((constantSheaf J AddCommGrpCat.{w}).obj E).obj.obj (op U)) :
    ∃ R : Sieve U, R ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), R f →
      ℓ • ((constantSheaf J AddCommGrpCat.{w}).obj E).obj.map f.op y = 0 := by
  let η := CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj E)
  refine ⟨Presheaf.imageSieve η y, Presheaf.imageSieve_mem J η y, fun V f hf => ?_⟩
  obtain ⟨t, ht⟩ := hf
  change ℓ • (sheafify J ((Functor.const Cᵒᵖ).obj E)).map f.op y = 0
  rw [← ht, ← map_nsmul, hE t, map_zero]

/-! ### Sheaves on an empty scheme -/

/-- **An abelian sheaf on the small étale site of an empty scheme is zero.** -/
theorem isZero_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) : IsZero F :=
  isZero_of_forall_isZero_sections F fun V =>
    isZero_sections_of_isEmpty F V ⟨fun x => IsEmpty.false (show X from V.hom.base x)⟩

/-- **The étale cohomology of an empty scheme vanishes in every degree.** -/
theorem subsingleton_sheafH_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Subsingleton (Sheaf.H.{w} F q) :=
  subsingleton_etaleSheafH_of_isZero (isZero_of_isEmpty F) q

/-! ### Degree zero -/

/-- **`H⁰` of a constant sheaf with finite value on a connected scheme is finite**: it is the group
of locally constant functions on `X` with values in the finite group (Stacks 03P5), and on a
preconnected space such a function is determined by its value at one point. -/
theorem finite_sheafH_zero_constantSheaf (X : Scheme.{u}) [PreconnectedSpace X]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (E : AddCommGrpCat.{max (u + 1) v}) [Finite E] :
    Finite (Sheaf.H.{w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) 0) := by
  let T := Scheme.Etale.mk (𝟙 X)
  let e₁ := Sheaf.H.equiv₀
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E)
    (isTerminalEtaleMkId X)
  let e₂ := (smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb.{u, v} X (ToType E) T)
  have hfin : Finite (LocallyConstant X (ToType E)) := by
    by_cases hX : Nonempty X
    · obtain ⟨x₀⟩ := hX
      refine Finite.of_injective (fun f : LocallyConstant X (ToType E) => f x₀) fun f g h => ?_
      ext x
      rwa [f.apply_eq_of_preconnectedSpace x x₀, g.apply_eq_of_preconnectedSpace x x₀]
    · have : Subsingleton (LocallyConstant X (ToType E)) :=
        ⟨fun f g => LocallyConstant.ext fun x => (hX ⟨x⟩).elim⟩
      exact Finite.of_subsingleton
  have : Finite (ToType (((constantSheaf X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ToType E))).obj.obj (op T))) :=
    Finite.of_equiv (LocallyConstant X (ToType E)) e₂.addCommGroupIsoToAddEquiv.toEquiv.symm
  exact Finite.of_equiv _ e₁.toEquiv.symm

/-! ### `𝐆_m` restricted along an étale morphism -/

/-- **`𝐆_m` restricted along an étale morphism `j : U ⟶ X` is `𝐆_m` of `U`**: both have the
invertible global functions of an étale `U`-scheme as sections. -/
def etaleRestrictionMultiplicativeSheafIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleRestriction.{u, v} j).obj (Stacks.Kummer.multiplicativeSheaf.{u, v} X) ≅
      Stacks.Kummer.multiplicativeSheaf.{u, v} U :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- **`𝐆_m` pulled back along an étale morphism `j : U ⟶ X` is `𝐆_m` of `U`.** -/
def etaleAbelianInverseImageMultiplicativeSheafIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleAbelianInverseImage.{u, v} j).obj (Stacks.Kummer.multiplicativeSheaf.{u, v} X) ≅
      Stacks.Kummer.multiplicativeSheaf.{u, v} U :=
  (etaleAbelianInverseImageRestrictionIso.{u, v} j).app _ ≪≫
    etaleRestrictionMultiplicativeSheafIso.{u, v} j

/-! ### The Kummer computation on a smooth curve -/

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))

omit [IsAlgClosed k] in
include g in
/-- A natural number invertible in the base field is invertible in the global functions. -/
theorem isUnit_natCast_globalSections_of_isUnit {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) :
    IsUnit ((ℓ : ℕ) : Γ(X, ⊤)) := by
  have h := hℓk.map ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom
  rwa [map_natCast] at h

omit [IsAlgClosed k] in
/-- A natural number invertible in a field is nonzero. -/
theorem ne_zero_of_isUnit_natCast {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) : ℓ ≠ 0 := by
  rintro rfl
  simp at hℓk

/-- A constant sheaf with value cyclic of order `ℓ` is isomorphic to `μ_ℓ`. -/
private theorem nonempty_constantSheaf_iso_rootsOfUnitySheaf_of_isUnit (g : X ⟶ Spec (.of k))
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ)) :
    Nonempty (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, v} X ℓ) :=
  Stacks.Kummer.nonempty_constantSheaf_iso_rootsOfUnitySheaf.{u, v} k g ℓ
    (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast hℓk)) hℓk E hE

variable [IsCurve k g] [Smooth g]

include g

/-- **`H^q(X, μ_ℓ) = 0` for `q > 2`** on a smooth curve over an algebraically closed field, `ℓ`
invertible in `k`: the Kummer sequence places `H^q(X, μ_ℓ)` between `H^{q-1}(X, 𝐆_m)` and
`H^q(X, 𝐆_m)`, both zero by Tag 03RM. -/
theorem subsingleton_sheafH_rootsOfUnitySheaf_of_smoothCurve
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{w} (Stacks.Kummer.rootsOfUnitySheaf.{u, v} X ℓ) q) := by
  have hSE := Stacks.Kummer.kummerSequence_shortExact.{u, v} X
    (ne_zero_of_isUnit_natCast hℓk) (isUnit_natCast_globalSections_of_isUnit g hℓk)
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  exact Stacks.Cohomology.subsingleton_sheafH_X₁_of_shortExact hSE p (p + 1) rfl
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ g (p + 1) (by omega))
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ g p (by omega))

/-- **Statement (1) of Situation 0A52 for `𝐙/ℓ𝐙` on a smooth curve**, `ℓ` invertible in `k`: for
a constant sheaf `F` on `X_étale` whose value is cyclic of order `ℓ`, `H^q(X, F) = 0` for
`q > 2`. -/
theorem isVanishingAboveDegreeTwo_constantSheaf_of_smoothCurve
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ)) :
    IsVanishingAboveDegreeTwo.{u, v, w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) := by
  intro q hq
  obtain ⟨e⟩ := nonempty_constantSheaf_iso_rootsOfUnitySheaf_of_isUnit.{u, v} g hℓk E hE
  exact (Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_congr e q).2
    (subsingleton_sheafH_rootsOfUnitySheaf_of_smoothCurve g hℓk q hq)

/-- **Statement (8) of Situation 0A52 for `𝐙/ℓ𝐙` on a smooth curve, from the surjectivity of
`H¹(X, 𝐆_m) → H¹(U, 𝐆_m)`.** Let `F` be a constant sheaf on `X_étale` cyclic of order `ℓ`, `ℓ`
invertible in `k`. If restriction `H¹(X, 𝐆_m) → H¹(U, 𝐆_m)` is surjective for every nonempty
open `U ⊆ X`, then `H²(X, F) → H²(U, F)` is surjective for every open `U ⊆ X`.

The Kummer sequence restricted to `U` has `H²(U, 𝐆_m) = 0` (Tag 03RM, `U` being again a smooth
curve), so its connecting map `H¹(U, 𝐆_m) → H²(U, μ_ℓ)` is onto, and connecting maps commute
with restriction. The empty open has no cohomology. -/
theorem isDegreeTwoOpenRestrictionSurjective_constantSheaf_of_multiplicative
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    (hpic : ∀ (U : X.Opens) [Nonempty U]
      [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})],
      Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} U.ι
        (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1)) :
    IsDegreeTwoOpenRestrictionSurjective.{u, v, w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) := by
  intro U _
  obtain ⟨e⟩ := nonempty_constantSheaf_iso_rootsOfUnitySheaf_of_isUnit.{u, v} g hℓk E hE
  refine surjective_etaleCohomologyRestrictionMap_of_iso U.ι e.symm 2 ?_
  rcases isEmpty_or_nonempty U with hU | hU
  · exact fun _ => ⟨0, (subsingleton_sheafH_of_isEmpty _ 2).elim _ _⟩
  · have hSE := Stacks.Kummer.kummerSequence_shortExact.{u, v} X
      (ne_zero_of_isUnit_natCast hℓk) (isUnit_natCast_globalSections_of_isUnit g hℓk)
    exact surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_surjective_X₃ U.ι hSE 1 2
      rfl ((Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_congr
        (etaleAbelianInverseImageMultiplicativeSheafIso.{u, v} U.ι) 2).2
        (subsingleton_sheafH_multiplicativeSheaf_opens_of_smoothCurve g U 2 le_rfl)) (hpic U)

omit g [IsAlgClosed k] [IsCurve k g] [Smooth g] in
/-- **Statement (3) of Situation 0A52 for `𝐙/ℓ𝐙`, `ℓ` invertible in `k`.** For a constant sheaf
`F` on the small étale site of a `k`-scheme whose value is cyclic of order `ℓ` with `ℓ`
invertible in `k`, if `F` is `p`-power torsion for `p = char(k) > 0` then `F = 0`, `p` and `ℓ`
being coprime; so its cohomology vanishes. -/
theorem isPrimePowerTorsionVanishing_constantSheaf_of_isUnit
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ)) (p : ℕ) [CharP k p] :
    IsPrimePowerTorsionVanishing.{u, v, w} k p
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) := by
  intro hp hF q _
  obtain ⟨e⟩ := hE
  have hcop : Nat.Coprime p ℓ := by
    refine (Nat.coprime_or_dvd_of_prime (CharP.char_prime_of_ne_zero k hp.ne') ℓ).resolve_right
      fun hdvd => ?_
    rw [(CharP.cast_eq_zero_iff k p ℓ).2 hdvd] at hℓk
    exact not_isUnit_zero hℓk
  have hEℓ : ∀ x : E, ℓ • x = 0 := fun x => by
    apply e.injective
    rw [map_nsmul, map_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine subsingleton_etaleSheafH_of_isZero (isZero_of_forall_isZero_sections _ fun V => ?_) q
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact subsingleton_of_forall_eq 0 (eq_zero_of_isPrimePowerTorsion_of_coprime hcop hF
    (exists_sieve_nsmul_eq_zero_constantSheaf _ ℓ E hEℓ) V)

/-- **The Kummer computation of `H²(X, μ_ℓ)`: it vanishes as soon as `H¹(X, 𝐆_m)` is
`ℓ`-divisible.** The Kummer sequence gives `H¹(X, 𝐆_m) →ℓ H¹(X, 𝐆_m) → H²(X, μ_ℓ) → H²(X, 𝐆_m)`,
and `H²(X, 𝐆_m) = 0` (Tag 03RM). -/
theorem subsingleton_sheafH_two_rootsOfUnitySheaf_of_divisible
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k))
    (hdiv : ∀ c : Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1,
      ∃ d, ℓ • d = c) :
    Subsingleton (Sheaf.H.{w} (Stacks.Kummer.rootsOfUnitySheaf.{u, v} X ℓ) 2) := by
  have hSE := Stacks.Kummer.kummerSequence_shortExact.{u, v} X
    (ne_zero_of_isUnit_natCast hℓk) (isUnit_natCast_globalSections_of_isUnit g hℓk)
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ _ hSE y
    ((subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ.{u, v, w} g 2 le_rfl).elim _ _)
    (show 1 + 1 = 2 from rfl)
  obtain ⟨d, rfl⟩ := hdiv x
  let S := Stacks.Kummer.kummerSequence.{u, v} X ℓ
  let d' : Ext ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift ℤ))) S.X₂ 1 := d
  have hn : ∀ n : ℕ, d'.comp (Ext.mk₀ (n • 𝟙 S.X₂)) (add_zero 1) = n • d' := by
    intro n
    induction n with
    | zero => rw [zero_smul, zero_smul, Ext.mk₀_zero, Ext.comp_zero]
    | succ n ih => rw [succ_nsmul, Ext.mk₀_add, Ext.comp_add, ih, Ext.comp_mk₀_id, succ_nsmul]
  have key : d'.comp (Ext.mk₀ S.g) (add_zero 1) = ℓ • d' := hn ℓ
  change (ℓ • d').comp hSE.extClass (show 1 + 1 = 2 from rfl) = y at hx
  rw [← hx, ← key]
  exact (Ext.comp_assoc_of_second_deg_zero d' (Ext.mk₀ S.g) hSE.extClass
    (show 1 + 1 = 2 from rfl)).trans (by rw [hSE.comp_extClass, Ext.comp_zero]; rfl)

/-- **Statement (2) of Situation 0A52 for `𝐙/ℓ𝐙` on a smooth curve, from the `ℓ`-divisibility of
`H¹(X, 𝐆_m)` for `X` affine.** In degrees `q ≥ 3` the vanishing is statement (1); in degree two
it is `subsingleton_sheafH_two_rootsOfUnitySheaf_of_divisible`. -/
theorem isAffineVanishingAboveDegreeOne_constantSheaf_of_divisible
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    (hdiv : IsAffine X → ∀ c : Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1,
      ∃ d, ℓ • d = c) :
    Stacks.EtaleCohomology.IsAffineVanishingAboveDegreeOne.{u, v, w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) := by
  intro hX q hq
  rcases Nat.lt_or_ge 2 q with h | h
  · exact isVanishingAboveDegreeTwo_constantSheaf_of_smoothCurve g hℓk E hE q h
  · obtain rfl : q = 2 := by omega
    obtain ⟨e⟩ := nonempty_constantSheaf_iso_rootsOfUnitySheaf_of_isUnit.{u, v} g hℓk E hE
    exact (Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_congr e 2).2
      (subsingleton_sheafH_two_rootsOfUnitySheaf_of_divisible g hℓk (hdiv hX))

end Curve

end Stacks.EtaleCohomology

end
