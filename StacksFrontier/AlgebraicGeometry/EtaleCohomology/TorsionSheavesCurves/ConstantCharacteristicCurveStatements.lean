module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionFirstCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AlgClosedCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantPrimeToCharacteristicCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionSmoothCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.SmoothReduction
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.CurveCover
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.AffineOrProjective

/-!
# Case II of Stacks 0A5B: the constant sheaf `𝐙/p𝐙` on a curve in characteristic `p`

Let `k` be an algebraically closed field of characteristic `p > 0`, let `X` be a curve over `k`
and let `F` be a constant sheaf on `X_étale` whose value is cyclic of order `p`. This file proves
the statements of Situation 0A52 for `F`, bundled as `Stacks.EtaleCohomology.CurveStatements`,
following the source's Case II of Lemma 0A5B:

* `H^q(X, F) = 0` for `q ≥ 2`: a curve is affine or projective (Tag 0A27); on an affine scheme
  this is Tag 0A3K (1), on a proper one of dimension one it is the vanishing of the proper case
  of Tag 0A3N. This gives statements (1), (2), (3) and, applied to every open, statement (8).
* `F` is never torsion prime to `p` unless it is zero, so statements (4) and (6) are trivial.
* Statement (5) is Tag 0A3P (1).
* Statement (7) is bijectivity of restriction to `X_{k'}` for proper `X`: in degree `0` it is
  Tag 0A3I in degree zero, in degrees `≥ 2` both sides vanish, `X_{k'}` being again a curve, and
  in degree one it is Tag 0A3P (2) in degree one for a proper scheme covered by two affine opens
  (`Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_constantZMod_one_of_cover`),
  a proper curve being so covered.

## Main results

* `Stacks.EtaleCohomology.subsingleton_etaleH_constantZMod_of_isCurve`: `H^q(X, 𝐙/p𝐙) = 0` for
  `q ≥ 2` on every curve over `k`.
* `Stacks.EtaleCohomology.curveStatements_constantSheaf_of_charP`: the bundle
  `Stacks.EtaleCohomology.CurveStatements` for `F` on every curve over `k`.
* `Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_charP`: the base case
  `Stacks.EtaleCohomology.CurveStatementsConstantOnSmoothCurves k E` of Lemma 03SG for `E` cyclic
  of order `p = char(k)`.

## Implementation notes

No `@[stacks 0A5B]` attribute: Lemma 0A5B also covers primes `ℓ` invertible in `k` (Case I), and
the source states it for smooth curves; this file proves Case II, for every curve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

/-! ### Sheaves torsion prime to `p` and killed by `p` -/

/-- **A sheaf of abelian groups that is torsion prime to `p` and locally killed by `p` is zero.**
Locally a section is killed by some `n` prime to `p` and by `p`, hence by `gcd(n, p) = 1`, and a
section of a sheaf vanishing locally vanishes. -/
theorem eq_zero_of_isPrimeToCharacteristicTorsion_of_nsmul {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F : Sheaf J AddCommGrpCat.{w}} {p : ℕ}
    (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion J p F)
    (hp : ∀ (U : C) (y : F.obj.obj (op U)), ∃ R : Sieve U, R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f → p • F.obj.map f.op y = 0)
    (U : C) (y : F.obj.obj (op U)) : y = 0 := by
  obtain ⟨R, hR, hannp⟩ := hp U y
  refine F.isSeparated U R hR y 0 fun V f hf => ?_
  rw [map_zero]
  have hzp : p • F.obj.map f.op y = 0 := hannp V f hf
  set z := F.obj.map f.op y
  obtain ⟨R', hR', hannn⟩ := hF V z
  refine F.isSeparated V R' hR' z 0 fun V' g hg => ?_
  rw [map_zero]
  obtain ⟨n, -, hcop, hn⟩ := hannn V' g hg
  have hbez := Nat.gcd_eq_gcd_ab n p
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set z' := F.obj.map g.op z
  have hp' : p • z' = 0 := by rw [← map_nsmul, hzp, map_zero]
  calc z' = (1 : ℤ) • z' := (one_zsmul z').symm
    _ = Nat.gcdA n p • (n • z') + Nat.gcdB n p • (p • z') := by
        rw [hbez, add_smul, mul_comm, mul_comm (p : ℤ), mul_smul, mul_smul, natCast_zsmul,
          natCast_zsmul]
    _ = 0 := by rw [hn, hp', smul_zero, smul_zero, add_zero]

/-! ### The constant sheaf with value cyclic of order `p` -/

section Constant

variable {p : ℕ} (X : Scheme.{u}) (E : AddCommGrpCat.{u + 1})

/-- A constant sheaf on `X_étale` whose value is cyclic of order `p` is the constant sheaf
`Stacks.ArtinSchreier.etaleConstantZMod X p`. -/
def constantSheafIsoEtaleConstantZMod (e : E ≃+ ZMod p) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E ≅
      Stacks.ArtinSchreier.etaleConstantZMod X p :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
    (e.trans AddEquiv.ulift.symm).toAddCommGrpIso

/-- A constant sheaf on `X_étale` whose value is cyclic of order a prime `p`, torsion prime to
`p`, is zero. -/
theorem isZero_constantSheaf_of_isPrimeToCharacteristicTorsion (e : E ≃+ ZMod p)
    (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) :
    IsZero ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) := by
  have hEp : ∀ x : E, p • x = 0 := fun x => by
    apply e.injective
    rw [map_nsmul, map_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine isZero_of_forall_isZero_sections.{u, 0} _ fun V => ?_
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  have h0 := eq_zero_of_isPrimeToCharacteristicTorsion_of_nsmul hF
    (exists_sieve_nsmul_eq_zero_constantSheaf _ p E hEp) V
  exact ⟨fun a b => (h0 a).trans (h0 b).symm⟩

end Constant

/-! ### Vanishing in degrees at least two on a curve -/

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : p.Prime)

include hp in
/-- **`H^q(X, 𝐙/p𝐙) = 0` for `q ≥ 2` on a curve `X` over an algebraically closed field of
characteristic `p`.** By Tag 0A27 `X` is affine or projective. If affine, this is Tag 0A3K (1);
if projective, `X` is proper of dimension one and this is the proper case of Tag 0A3N. -/
theorem subsingleton_etaleH_constantZMod_of_isCurve {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (Stacks.ArtinSchreier.etaleConstantZMod X p) q) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases isAffine_or_isProjectiveMorphism k g with h | h
  · exact Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isAffine_constantSequence p X
      (Stacks.ArtinSchreier.natCast_eq_zero_of_charP k p g) q hq
  · have : IsProper g := isProper_of_isProjectiveMorphism g h
    refine Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isProper_of_isAlgClosed hp k
      g 1 ?_ q hq
    rw [IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)]
    rfl

include hp in
/-- **`H^q(X, F) = 0` for `q ≥ 2`** for a constant sheaf `F` with value cyclic of order `p` on a
curve over an algebraically closed field of characteristic `p`. -/
theorem subsingleton_sheafH_constantSheaf_of_isCurve {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (E : AddCommGrpCat.{u + 1}) (hE : Nonempty (E ≃+ ZMod p)) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) q) := by
  obtain ⟨e⟩ := hE
  exact (Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_congr
    (constantSheafIsoEtaleConstantZMod X E e) q).2
    (subsingleton_etaleH_constantZMod_of_isCurve hp g q hq)

/-- If `H^q(Y, F)` vanishes for the constant sheaf `F` on `Y`, so does `H^q` of the inverse image
along `f : Y ⟶ X` of the constant sheaf on `X` with value `E`. -/
private theorem subsingleton_sheafH_inverseImage_constantSheaf {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : AddCommGrpCat.{u + 1})
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w}
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) q)) :
    Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} f).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) q) :=
  (Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_congr
    ((etaleAbelianInverseImageConstantIso.{u, 0} f).app E) q).2 h

include hp in
/-- **`H^q(U, F) = 0` for `q ≥ 2` on every open `U` of a curve**, for the restriction of a
constant sheaf `F` with value cyclic of order `p`: a nonempty open of a curve is a curve, and the
empty scheme has no cohomology. -/
theorem subsingleton_sheafH_inverseImage_constantSheaf_opens {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] (E : AddCommGrpCat.{u + 1})
    (hE : Nonempty (E ≃+ ZMod p)) (U : X.Opens)
    [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} U.ι).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) q) := by
  by_cases hU : Nonempty U
  · have : IsCurve k (U.ι ≫ g) := isCurve_opensι_comp k g U
    exact subsingleton_sheafH_inverseImage_constantSheaf U.ι E q
      (subsingleton_sheafH_constantSheaf_of_isCurve hp (U.ι ≫ g) E hE q hq)
  · have : IsEmpty U := not_nonempty_iff.mp hU
    exact subsingleton_sheafH_of_isEmpty.{u, 0} _ q

end Curve

/-! ### The bundle -/

section Bundle

variable {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : p.Prime)

include hp in
/-- **Bijectivity of restriction to `X_{k'}` in degrees other than one**, for a constant sheaf
with value cyclic of order `p` on a curve over an algebraically closed field of characteristic
`p`: in degree `0` this is Tag 0A3I in degree zero, and in degrees `≥ 2` both sides vanish,
`X_{k'}` being a curve over the algebraically closed field `k'` of characteristic `p`. -/
theorem bijective_etaleCohomologyRestrictionMap_constantSheaf_of_ne_one {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] (E : AddCommGrpCat.{u + 1})
    (hE : Nonempty (E ≃+ ZMod p)) (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' g).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : q ≠ 1) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' g)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · exact bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_zero k k' g _
  · have hq2 : 2 ≤ q := by omega
    have : CharP k' p := charP_of_injective_algebraMap' k p
    have : IsCurve k' (scalarExtensionSnd k k' g) := isCurve_scalarExtension k k' g
    have h₁ := subsingleton_sheafH_constantSheaf_of_isCurve hp g E hE q hq2
    have h₂ := subsingleton_sheafH_inverseImage_constantSheaf (scalarExtensionFst k k' g) E q
      (subsingleton_sheafH_constantSheaf_of_isCurve hp (scalarExtensionSnd k k' g) E hE q hq2)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

include hp in
/-- **The bundle of Situation 0A52 for `𝐙/p𝐙` on a curve in characteristic `p`, from
bijectivity of restriction to `X_{k'}` in degree one for proper `X`.** Let `k` be algebraically
closed of characteristic `p`, `X` a curve over `k` and `F` a constant sheaf with value cyclic of
order `p`. Statements (1), (2), (3), (8) follow from `H^q = 0` for `q ≥ 2` on every curve,
statements (4), (6) are vacuous (`F` is not torsion prime to `p` unless zero), statement (5) is
Tag 0A3P (1), and statement (7) holds outside degree one. -/
theorem curveStatements_constantSheaf_of_charP_of {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (E : AddCommGrpCat.{u + 1}) (hE : Nonempty (E ≃+ ZMod p))
    (h7 : IsProper g → ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
        [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
        [HasExt.{u + 1} (Sheaf (scalarExtension k k' g).smallEtaleTopology
          AddCommGrpCat.{u + 1})],
        Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' g)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) 1)) :
    CurveStatements.{u, 0, u + 1} g
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) := by
  have : Fact p.Prime := ⟨hp⟩
  have hzero : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) →
      IsZero ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) := by
    intro h
    obtain ⟨e⟩ := hE
    rw [ringExpChar.eq k p] at h
    exact isZero_constantSheaf_of_isPrimeToCharacteristicTorsion X E e h
  have hvan : ∀ q : ℕ, 2 ≤ q → Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) q) :=
    subsingleton_sheafH_constantSheaf_of_isCurve hp g E hE
  exact
  { vanishing := fun q hq => hvan q (by omega)
    affineVanishing := fun _ q hq => hvan q (by omega)
    primePowerVanishing := fun _ _ _ _ q hq => hvan q (by omega)
    finite_of_isPrimeToCharacteristicTorsion := fun _ _ _ _ _ h q => by
      have := subsingleton_etaleSheafH_of_isZero.{u, 0} (hzero h) q
      exact Finite.of_subsingleton
    finite_of_isProper := fun _ _ _ _ _ _ q => by
      obtain ⟨e⟩ := hE
      have := Stacks.ArtinSchreier.finite_etaleH_constantZMod_of_isProper_of_isAlgClosed hp k g q
      exact Finite.of_equiv _ (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr
        (constantSheafIsoEtaleConstantZMod X E e) q).toEquiv.symm
    bijective_of_isPrimeToCharacteristicTorsion := fun h _ _ _ _ _ _ q =>
      bijective_etaleCohomologyRestrictionMap_of_isZero _ (hzero h) q
    bijective_of_isProper := fun hprop k' _ _ _ _ _ q => by
      by_cases hq : q = 1
      · subst hq
        exact h7 hprop k'
      · exact bijective_etaleCohomologyRestrictionMap_constantSheaf_of_ne_one hp g E hE k' q hq
    surjective := isDegreeTwoOpenRestrictionSurjective_of_subsingleton _ fun U _ =>
      subsingleton_sheafH_inverseImage_constantSheaf_opens hp g E hE U 2 le_rfl }

include hp in
/-- **Restriction to `X_{k'}` is bijective in degree one for a proper curve**, for a constant
sheaf with value cyclic of order `p`. A separated Noetherian scheme of dimension one is covered
by two affine opens (`Stacks.TwoAffineCech.exists_isAffineOpen_sup_eq_top`), whose intersection
is affine by separatedness, and Tag 0A3P (2) in degree one holds for such a scheme
(`Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_constantZMod_one_of_cover`). -/
theorem bijective_etaleCohomologyRestrictionMap_constantSheaf_one_of_isProper {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [IsProper g] (E : AddCommGrpCat.{u + 1})
    (hE : Nonempty (E ≃+ ZMod p)) (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' g).smallEtaleTopology AddCommGrpCat.{u + 1})] :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' g)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) 1) := by
  obtain ⟨e⟩ := hE
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian X := ⟨⟩
  have : X.IsSeparated := by
    refine ⟨?_⟩
    have : IsSeparated (g ≫ Limits.terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  obtain ⟨U, V, hU, hV, hUV⟩ := Stacks.TwoAffineCech.exists_isAffineOpen_sup_eq_top X
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le
  have h := Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_constantZMod_one_of_cover
    hp k k' g U V hUV hU hV (hU.inf hV)
  exact etaleCohomologyRestrictionMap_bijective_of_retract.{u, 0, u + 1} _
    (constantSheafIsoEtaleConstantZMod X E e).hom (constantSheafIsoEtaleConstantZMod X E e).inv
    (Iso.hom_inv_id _) h

include hp in
/-- **Case II of Lemma 0A5B: the statements of Situation 0A52 for `𝐙/p𝐙` on a curve in
characteristic `p`.** Let `k` be an algebraically closed field of characteristic `p > 0`, `X` a
curve over `k` and `F` a constant sheaf on `X_étale` with value cyclic of order `p`. Then
statements (1) -- (8) of Situation 0A52 hold for `F`. -/
theorem curveStatements_constantSheaf_of_charP {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (E : AddCommGrpCat.{u + 1}) (hE : Nonempty (E ≃+ ZMod p)) :
    CurveStatements.{u, 0, u + 1} g
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) :=
  curveStatements_constantSheaf_of_charP_of hp g E hE fun _ k' _ _ _ _ _ =>
    bijective_etaleCohomologyRestrictionMap_constantSheaf_one_of_isProper hp g E hE k'

include hp in
/-- **The base case of the dévissage of Theorem 03SC in characteristic `p`, for `ℓ = p`**: the
hypothesis `Stacks.EtaleCohomology.CurveStatementsConstantOnSmoothCurves k E` of Lemma 03SG holds
for every `E` cyclic of order `p = char(k)`. -/
theorem curveStatementsConstantOnSmoothCurves_of_charP (E : AddCommGrpCat.{u + 1})
    (hE : Nonempty (E ≃+ ZMod p)) : CurveStatementsConstantOnSmoothCurves k E :=
  fun _ g _ _ => curveStatements_constantSheaf_of_charP hp g E hE

end Bundle

end Stacks.EtaleCohomology

end
