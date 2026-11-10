module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAllDegreesGmVanishing
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowTorsionCard
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 03RQ with the torsion of `Pic⁰(X)` derived from the Jacobian

The eight-clause assemblies of [Stacks, Tag 03RQ] in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityAllDegreesGmVanishing.lean`
carry `hgenus`, the identification `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`. That is clause (7) of
[Stacks, Tag 03RP] applied to the Jacobian, and this file derives it from that clause as proved
in `Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isFiniteLocallyFreeOfRank`.

## Main results

* `nonempty_curvePicardDegreeZeroTorsion_addEquiv_of_jacobian`:
  `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}` from an abelian variety whose rational points are `Pic⁰(X)`, of
  dimension `g`, on which multiplication by each prime `p ∣ n` has degree `p ^ {2g}`.
* `etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_rank`:
  all eight clauses of [Stacks, Tag 03RQ] with `hgenus` derived as well.

## Implementation notes

What replaces `hgenus` is what the Jacobian construction supplies:

* `φ` is now a *bijection* from the rational points of `Pic⁰_{X/k}` onto `Pic⁰(X)`, not just a
  surjection, since the torsion is transported along it;
* `hdim`, that `Pic⁰_{X/k}` has dimension `g`, the dimension count of [Stacks, Tag 0BA0];
* `hrank`, that multiplication by each prime `p ∣ n` on it is finite locally free of degree
  `p ^ {2g}`, which is [Stacks, Tag 0BFG] at those primes.

Multiplication by `n` being étale and flat for `n` invertible in `k`
(`Stacks.Groupoids.etale_natCast_zpow_id_left_of_isUnit`) is not carried anywhere.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe t u

namespace AlgebraicGeometry

section ProjectiveCurve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [IsProjectiveVariety k f] (n : ℕ)

omit [IsAlgClosed k] in
/-- The torsion `Pic⁰(X)[n]` is the image of the `n`-torsion under an additive isomorphism onto
`Pic⁰(X)`. -/
private lemma map_torsionBy_eq_curvePicardDegreeZeroTorsion {M : Type*} [AddCommGroup M]
    (e : M ≃+ ↥(curvePicardDegreeZero k X f)) :
    (AddSubgroup.torsionBy M (n : ℤ)).map e.toAddMonoidHom =
      curvePicardDegreeZeroTorsion k X f n := by
  ext x
  refine ⟨?_, fun hx => ⟨e.symm x, ?_, by simp⟩⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : (n : ℤ) • y = 0 := hy
    change n • e y = 0
    rw [← map_nsmul, ← natCast_zsmul, hy', map_zero]
  · have hx' : n • x = 0 := hx
    change (n : ℤ) • e.symm x = 0
    rw [natCast_zsmul, ← map_nsmul, hx', map_zero]

include f in
/-- **`Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}` from the Jacobian.** Let `X` be a smooth projective curve of
genus `g` over an algebraically closed field `k` and let `n` be invertible in `k`. Suppose that
`H` is a proper, smooth, connected open subgroup scheme of a group scheme over `k`, of dimension
`g`, whose rational points are identified with `Pic⁰(X)` by `φ`, and that multiplication by each
prime `p ∣ n` on `H` is finite locally free of degree `p ^ {2 dim H}`. Then
`Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`.

`H` is an abelian variety by `AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier`, its
`n`-torsion is `(𝐙/n𝐙)^{2g}` by clause (7) of [Stacks, Tag 03RP]
(`Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isFiniteLocallyFreeOfRank`), and `φ` carries the
`n`-torsion onto `Pic⁰(X)[n]`.

This is a partial form of [Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP). -/
theorem nonempty_curvePicardDegreeZeroTorsion_addEquiv_of_jacobian (hn : IsUnit (n : k))
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (hdim : Stacks.Groupoids.abelianVarietyDimension H.carrier.X = genus f)
    (hrank : ∀ p : ℕ, p.Prime → p ∣ n →
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((𝟙 H.carrier.X : H.carrier.X ⟶ H.carrier.X) ^ (p : ℤ)).left
        (p ^ (2 * Stacks.Groupoids.abelianVarietyDimension H.carrier.X)))
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → ↥(curvePicardDegreeZero k X f))
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hbij : Function.Bijective φ) :
    Nonempty (↥(curvePicardDegreeZeroTorsion k X f n) ≃+ (Fin (2 * genus f) → ZMod n)) := by
  have : IsAbelianVariety k H.carrier.X := H.isAbelianVariety_carrier hproper hsmooth hconn
  let : IsCommMonObj H.carrier.X :=
    isCommMonObj_of_isProper_of_geometricallyIntegral H.carrier.X
  obtain ⟨e₀⟩ := Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isFiniteLocallyFreeOfRank
    H.carrier.X n (2 * genus f) hn (fun p hp hpn => hdim ▸ hrank p hp hpn)
  let P := Additive (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X)
  let φ' : P →+ ↥(curvePicardDegreeZero k X f) :=
    AddMonoidHom.mk' (fun a : P => φ a.toMul) fun a b : P => hmul a.toMul b.toMul
  let e : P ≃+ ↥(curvePicardDegreeZero k X f) := AddEquiv.ofBijective φ' hbij
  exact ⟨((AddSubgroup.equivMapOfInjective _ e.toAddMonoidHom e.injective).trans
    (AddEquiv.addSubgroupCongr
      (map_torsionBy_eq_curvePicardDegreeZeroTorsion k X f n e))).symm.trans e₀⟩

variable (B : BigEtaleSite.{u}) (hX : B.Contains X)
  [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

include f in
/-- **All eight clauses of [Stacks, Tag 03RQ], with `hgenus` derived from the Jacobian.** This is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_gm`
with its `hgenus` supplied by
`AlgebraicGeometry.nonempty_curvePicardDegreeZeroTorsion_addEquiv_of_jacobian`.

Beyond `hn`, a hypothesis of the source lemma itself, only the Jacobian input is carried: `G`,
`H`, `hproper`, `hsmooth`, `hconn` and `hdim` (the abelian variety `Pic⁰_{X/k}` of dimension
`g`, [Stacks, Tag 0BA0]), `φ`, `hmul` and `hbij` (its rational points are `Pic⁰(X)`), and
`hrank` (the degree of `[p]` on it for the primes `p ∣ n`, [Stacks, Tag 0BFG]).

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
@[sga "4 IX 4.6" "partial, special case"]
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_rank
    [Smooth f] (hn : IsUnit (n : k))
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (hdim : Stacks.Groupoids.abelianVarietyDimension H.carrier.X = genus f)
    (hrank : ∀ p : ℕ, p.Prime → p ∣ n →
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((𝟙 H.carrier.X : H.carrier.X ⟶ H.carrier.X) ^ (p : ℤ)).left
        (p ^ (2 * Stacks.Groupoids.abelianVarietyDimension H.carrier.X)))
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → ↥(curvePicardDegreeZero k X f))
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hbij : Function.Bijective φ) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Function.Bijective
        (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn) ∧
      (∃ e : Sheaf.H (kummerSmallEtale B X hX n).X₁ 2 ≃+ ZMod n,
        ∀ x, e (etaleH2RootsOfUnityFromPicard k X f B hX n hn x) =
          picardDegreeZMod k X f n x) ∧
      (∀ q, 3 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 1 ≃+
        (Fin (2 * genus f) → ZMod n)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) q) :=
  etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_gm k X f B hX n hn
    (nonempty_curvePicardDegreeZeroTorsion_addEquiv_of_jacobian k X f n hn H hproper hsmooth hconn
      hdim hrank φ hmul hbij)
    H hproper hsmooth hconn φ hmul hbij.2

end ProjectiveCurve

end AlgebraicGeometry

end
