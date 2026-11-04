module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClosedSupportVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DegreeZeroRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictToDenseOpen

/-!
# Stacks Tag 0GJA, the direction towards the middle term

Let `i : Z ⟶ X` be a closed immersion over an algebraically closed field `k` with `Z` finite over
`k`, and `j : U ⟶ X` the open immersion of its complement. For an abelian sheaf `F` on `X_étale`,
the localization sequence `0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0` of Tag 095L reduces the eight
assertions of Tag 03SC for `F` to those for `j_! j⁻¹ F`: the quotient is supported on `Z`, so its
cohomology vanishes in positive degrees, also after any scalar extension and on every open, and in
degree zero restriction to a scalar extension is bijective by Tag 0A3I.

The one input not supplied here is the finiteness of `H⁰(X, i_* i⁻¹ F)` when it is constructible,
`hfin`.

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_cohomology_concentrated_of_constructible`:
  the variant of `of_cohomology_concentrated` asking finiteness only for constructible sheaves.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_extensionByZero`: the reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The variant of `of_cohomology_concentrated` in which `H⁰` is only required to be finite when
the sheaf is constructible, which is all assertions (4) and (5) use. -/
theorem of_cohomology_concentrated_of_constructible
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hvanish : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} G q))
    (hfinite : IsConstructibleSmallEtaleSheaf G → Finite (Sheaf.H.{u + 1} G 0))
    (hrestr : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
      (q : ℕ), Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' f) G q))
    (hopen : ∀ (U : X.Opens)
      [HasExt.{u + 1} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1})],
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, u + 1} U.ι).obj G) 2)) :
    TorsionCurveAssertions f G :=
  have hfin (hc : IsConstructibleSmallEtaleSheaf G) (q : ℕ) : Finite (Sheaf.H.{u + 1} G q) :=
    q.casesOn (hfinite hc) fun n => have := hvanish (n + 1) n.succ_pos; .of_subsingleton
  { vanishing q hq := hvanish q (by omega)
    vanishing_of_isAffine _ q hq := hvanish q (by omega)
    vanishing_of_isPrimePowerTorsion _ _ _ _ q hq := hvanish q (by omega)
    finite_of_isPrimeToCharacteristicTorsion hc _ q := hfin hc q
    finite_of_isProper _ hc q := hfin hc q
    bijective_of_isPrimeToCharacteristicTorsion _ k' _ _ _ _ q := hrestr k' q
    bijective_of_isProper _ k' _ _ _ _ q := hrestr k' q
    surjective_restriction U _ := fun _ => ⟨0, Subsingleton.elim _ _⟩ }

variable [IsAlgClosed k] {Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
  [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.base)ᶜ) [IsFinite (i ≫ f)]

include hij in
/-- **The eight assertions for a sheaf supported on a finite closed part**, with the degree-zero
comparison discharged by Tag 0A3I. -/
theorem of_isZero_etaleRestriction_of_constructible
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hQ : IsZero ((etaleRestriction.{u, u + 1} j).obj Q))
    (hfin : IsConstructibleSmallEtaleSheaf Q → Finite (Sheaf.H.{u + 1} Q 0)) :
    TorsionCurveAssertions f Q := by
  obtain ⟨hA, hcl, hsep⟩ := isAffine_isClosed_isSepClosed_of_isFinite (i ≫ f)
  let : HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives.{u + 1} _
  have hv : ∀ q, 0 < q → Subsingleton (Sheaf.H.{u + 1} Q q) := fun q hq =>
    subsingleton_sheafH_of_isZero_etaleRestriction_of_affine_closedPoints i j hij hcl hsep Q hQ q hq
  refine of_cohomology_concentrated_of_constructible f hv hfin (fun k' _ _ _ _ q => ?_)
    (fun V _ => ?_)
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact bijective_etaleCohomologyRestrictionMap_zero_of_isSepClosed k k' f Q
    · have := hv q hq
      have := isFinite_pullback_scalarExtension f i k'
      have := subsingleton_sheafH_inverseImage_of_isZero_etaleRestriction i j hij
        (scalarExtensionFst k k' f) (K := k') (pullback.snd i (scalarExtensionFst k k' f) ≫
          pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) Q hQ q hq
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · have := isFinite_pullback_opens f i V
    exact subsingleton_sheafH_inverseImage_of_isZero_etaleRestriction i j hij V.ι (K := k)
      (pullback.fst i V.ι ≫ i ≫ f) Q hQ 2 two_pos

include hij in
/-- **Stacks Tag 0GJA, towards the middle term.** On a Noetherian scheme over an algebraically
closed field, with `Z` finite over `k` and `U` its open complement, the eight assertions for
`j_! j⁻¹ F` give them for `F`, provided `H⁰(X, i_* i⁻¹ F)` is finite when constructible. -/
theorem of_extensionByZero [AlgebraicGeometry.IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfin : IsConstructibleSmallEtaleSheaf ((etaleAbelianDirectImage.{u, u + 1} i).obj
        ((etaleAbelianInverseImage.{u, u + 1} i).obj F)) →
      Finite (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} i).obj
        ((etaleAbelianInverseImage.{u, u + 1} i).obj F)) 0))
    (h : TorsionCurveAssertions f ((extensionByZero.{u, u + 1} j).obj
      ((etaleRestriction.{u, u + 1} j).obj F))) :
    TorsionCurveAssertions f F :=
  of_shortExact f (openClosedShortComplex_shortExact.{u, u + 1} i j hij F) h
    (of_isZero_etaleRestriction_of_constructible f i j hij _
      (isZero_etaleRestriction_etaleAbelianDirectImage.{u, u + 1} i j hij _) hfin)

omit [IsAlgClosed k] [IsClosedImmersion i] [IsOpenImmersion j] [IsFinite (i ≫ f)] in
/-- **The eight assertions pass from the middle term of a short exact sequence to the sub-sheaf**,
when the quotient has cohomology concentrated in degree zero, also on every open and with
bijective restriction to every scalar extension. This is the direction of Tag 0GJA from `F` to
`j_! j⁻¹ F`; the torsion and constructibility conditions on the sub-sheaf have to be passed up to
the middle term, which is what `hp`, `ht` and `hc` say. -/
theorem of_shortExact_X₁
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₂ : TorsionCurveAssertions f S.X₂)
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} S.X₃ q))
    (hc : IsConstructibleSmallEtaleSheaf S.X₁ →
      IsConstructibleSmallEtaleSheaf S.X₂ ∧ Finite (Sheaf.H.{u + 1} S.X₃ 0))
    (hp : ∀ p : ℕ, Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p S.X₁ →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p S.X₂)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k)
        S.X₁ →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) S.X₂)
    (hres : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
      (q : ℕ), Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' f) S.X₃ q))
    (hopen : ∀ (V : X.Opens)
      [HasExt.{u + 1} (Sheaf (V : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1})],
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, u + 1} V.ι).obj S.X₃) 1)) :
    TorsionCurveAssertions f S.X₁ where
  vanishing q hq := subsingleton_sheafCohomology_X₁_of_shortExact_of_two_le hS hpos q (by omega)
    (h₂.vanishing q hq)
  vanishing_of_isAffine hX q hq := subsingleton_sheafCohomology_X₁_of_shortExact_of_two_le hS hpos q
    (by omega) (h₂.vanishing_of_isAffine hX q hq)
  vanishing_of_isPrimePowerTorsion p hp' hp0 hF q hq :=
    subsingleton_sheafCohomology_X₁_of_shortExact_of_two_le hS hpos q (by omega)
      (h₂.vanishing_of_isPrimePowerTorsion p hp' hp0 (hp p hF) q hq)
  finite_of_isPrimeToCharacteristicTorsion hcF htF q :=
    finite_sheafCohomology_X₁_of_shortExact_of_acyclic hS (hc hcF).2 hpos q
      (h₂.finite_of_isPrimeToCharacteristicTorsion (hc hcF).1 (ht htF) q)
  finite_of_isProper hf hcF q :=
    finite_sheafCohomology_X₁_of_shortExact_of_acyclic hS (hc hcF).2 hpos q
      (h₂.finite_of_isProper hf (hc hcF).1 q)
  bijective_of_isPrimeToCharacteristicTorsion htF k' _ _ _ _ q :=
    bijective_etaleCohomologyRestrictionMap_X₁_of_shortExact.{u, u + 1, u + 1} _ hS
      (fun n => h₂.bijective_of_isPrimeToCharacteristicTorsion (ht htF) k' n) (hres k') q
  bijective_of_isProper hf k' _ _ _ _ q :=
    bijective_etaleCohomologyRestrictionMap_X₁_of_shortExact.{u, u + 1, u + 1} _ hS
      (fun n => h₂.bijective_of_isProper hf k' n) (hres k') q
  surjective_restriction V _ := by
    have h2 := hpos 2 two_pos
    have h1 := hopen V
    refine surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_injective.{u, u + 1, u + 1}
      _ hS 2 (h₂.surjective_restriction V) (fun _ _ _ => Subsingleton.elim _ _) ?_
    intro q hq
    obtain rfl : q = 1 := by omega
    exact fun _ => ⟨0, Subsingleton.elim _ _⟩

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
