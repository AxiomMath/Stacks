module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionDegreeZero

/-!
# Case I of Stacks 0A5B: which of the eight statements are proved

Let `X` be a smooth curve over an algebraically closed field `k`, `ℓ` invertible in `k` and `F`
a constant sheaf on `X_étale` whose value is cyclic of order `ℓ`. Of the eight statements of
Situation 0A52 for `F`, bundled as `Stacks.EtaleCohomology.CurveStatements`, three are proved
outright here and in the files imported:

* statement (1), `H^q(X, F) = 0` for `q > 2`;
* statement (3), which is vacuous for `F` (a `p`-power torsion sheaf killed by `ℓ` prime to `p`
  is zero);
* statement (8), `H²(X, F) → H²(U, F)` surjective for every open `U`.

Statement (2) is reduced to the `ℓ`-divisibility of `H¹(X, 𝐆_m)` for affine `X`
(`Stacks.EtaleCohomology.isAffineVanishingAboveDegreeOne_constantSheaf_of_divisible`).

Statements (4), (5) are proved in degree `0` (locally constant functions on a connected scheme)
and in degrees `q ≥ 3` (vanishing); statements (6), (7) in degree `0` (Tag 0A3I in degree zero,
`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_zero`).

`Stacks.EtaleCohomology.curveStatements_constantSheaf_of_smoothCurve_of` assembles the bundle from
the remaining inputs: that divisibility, finiteness in degrees one and two, and bijectivity of
restriction to `X_{k'}` in positive degrees. It is a reduction, recorded so that the inputs still
to be proved are explicit; nothing is registered.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-- **The bundle of Situation 0A52 for `𝐙/ℓ𝐙` on a smooth curve, `ℓ ∈ k^*`, from its four
remaining inputs.** Statements (1), (3) and (8) are proved; statement (2) is supplied by the
`ℓ`-divisibility of `H¹(X, 𝐆_m)` on affine `X`; statements (4), (5) by finiteness in degrees one
and two; statements (6), (7) by bijectivity in positive degrees. -/
theorem curveStatements_constantSheaf_of_smoothCurve_of {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    (hdiv : IsAffine X → ∀ c : Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1,
      ∃ d, ℓ • d = c)
    (h4 : ∀ q : ℕ, 1 ≤ q → q ≤ 2 → Finite (Sheaf.H.{w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) q))
    (h6 : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
        [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
        [HasExt.{w} (Sheaf (scalarExtension k k' g).smallEtaleTopology
          AddCommGrpCat.{max (u + 1) v})] (q : ℕ), 1 ≤ q →
        Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} (scalarExtensionFst k k' g)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) q)) :
    CurveStatements.{u, v, w} g
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) := by
  have hfin : ∀ q : ℕ, Finite (Sheaf.H.{w}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) q) := by
    intro q
    obtain ⟨e⟩ := hE
    rcases Nat.lt_or_ge 2 q with h | h
    · have := isVanishingAboveDegreeTwo_constantSheaf_of_smoothCurve g hℓk E ⟨e⟩ q h
      exact Finite.of_subsingleton
    · rcases Nat.eq_zero_or_pos q with rfl | hq
      · have : NeZero ℓ := ⟨ne_zero_of_isUnit_natCast hℓk⟩
        have : Finite E := Finite.of_equiv _ e.toEquiv.symm
        have : IrreducibleSpace X := inferInstance
        have : PreconnectedSpace X := PreirreducibleSpace.preconnectedSpace X
        exact finite_sheafH_zero_constantSheaf X E
      · exact h4 q hq h
  have hbij : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
      [HasExt.{w} (Sheaf (scalarExtension k k' g).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} (scalarExtensionFst k k' g)
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) q) := by
    intro k' _ _ _ _ _ q
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_zero k k' g _
    · exact h6 k' q hq
  exact
  { vanishing := isVanishingAboveDegreeTwo_constantSheaf_of_smoothCurve g hℓk E hE
    affineVanishing := isAffineVanishingAboveDegreeOne_constantSheaf_of_divisible g hℓk E hE hdiv
    primePowerVanishing := fun p _ =>
      isPrimePowerTorsionVanishing_constantSheaf_of_isUnit hℓk E hE p
    finite_of_isPrimeToCharacteristicTorsion := fun _ _ _ _ _ _ => hfin
    finite_of_isProper := fun _ _ _ _ _ _ => hfin
    bijective_of_isPrimeToCharacteristicTorsion := fun _ => hbij
    bijective_of_isProper := fun _ => hbij
    surjective := isDegreeTwoOpenRestrictionSurjective_constantSheaf_of_smoothCurve g hℓk E hE }

end Stacks.EtaleCohomology

end
