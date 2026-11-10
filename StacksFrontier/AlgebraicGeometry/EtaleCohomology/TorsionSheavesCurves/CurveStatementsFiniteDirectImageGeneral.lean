module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.InverseImageLocallyAnnihilated
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsShortExactConstructible
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksCore.Tactic.StacksAttribute

/-!
# Lemma 0A5D: the statements of Situation 0A52 pass to a finite direct image

Lemma 0A5D: for a finite morphism `f : X ⟶ Y` of separated finite type schemes of dimension at
most one over an algebraically closed field and a torsion abelian sheaf `F` on `X`, if statements
(1) -- (8) of Situation 0A52 hold for `F`, they hold for `f_* F`.

The cohomology comparison `H^q(X, F) = H^q(Y, f_* F)` (Tags 03QP and 0733) and its compatibility
with restriction along the scalar extensions and open subschemes (Tag 0959) are those of
`Stacks.EtaleCohomology.CurveStatements.directImage_of_nsmul_eq_zero`, which treats a
constructible `F` killed by a prime. For a general `F` the statements for `f_* F` carry side
conditions on `f_* F` — being `p`-power torsion in (3), being constructible and of torsion prime
to the characteristic in (4), (5), (6) — and these have to be moved back to `F` before the
statements for `F` can be used. They move because `F` is a quotient of `f⁻¹ f_* F` (Tag 04C9),
inverse image preserves the two torsion conditions and constructibility (Tag 095G), and quotients
preserve them too (Proposition 09BH for constructibility on the Noetherian scheme `X`).

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_of_directImage`: constructibility of
  `f_* F` implies that of `F` for `f` integral and `X` Noetherian.
* `Stacks.EtaleCohomology.CurveStatements.directImage_of_isFinite`: **Lemma 0A5D**.

## Implementation notes

The coefficients are `AddCommGrpCat.{u + 1}` and the `Ext`-universe is `u + 1`, as for
`Stacks.EtaleCohomology.CurveStatements.directImage_of_nsmul_eq_zero`: the base change
comparison of Tag 0959 is available at these coefficients, and statements (6) and (7) for `f_* F`
compare with those for `F` only if the `Ext`-groups over the scalar extension of `X` exist.

Of the source's hypotheses only the finiteness of `f` and the Noetherianity of `X` are used; the
latter follows from `X` being of finite type over a field. The base field need not be
algebraically closed, the schemes need not be separated nor of dimension at most one, and `F`
need not be torsion.

## References

* [Stacks Project, Tag 0A5D](https://stacks.math.columbia.edu/tag/0A5D)
* [Stacks Project, Tag 04C9](https://stacks.math.columbia.edu/tag/04C9)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

section DirectImage

variable (B : BigEtaleSite.{u})
  [∀ (T T' : B.Scheme) (f : T' ⟶ T),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
      (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
    HasWeakSheafify ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
      AddCommGrpCat.{u + 1}]

/-- **Constructibility descends along an integral direct image.** Let `f : X ⟶ Y` be an integral
morphism of schemes contained in a big étale site `B`, with `X` Noetherian. An abelian sheaf `F`
on `X_étale` is constructible if `f_* F` is: `F` is a quotient of `f⁻¹ f_* F` (Tag 04C9), which is
constructible (Tag 095G), and quotients of constructible sheaves on a Noetherian scheme are
constructible (Proposition 09BH). -/
theorem isConstructibleEtaleAbelianSheaf_of_directImage {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) (hf : IsIntegralHom f) (hX : B.Contains X) (hY : B.Contains Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : IsConstructibleEtaleAbelianSheaf.{u, 0} B Y hY
      ((etaleAbelianDirectImage.{u, 0} f).obj F)) :
    IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX F :=
  have := epi_etaleAbelianInverseImageDirectImageAdj_counit_app f hf F
  isConstructibleEtaleAbelianSheaf_of_epi B hX
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).counit.app F)
    (isConstructibleFiniteSheaf_etaleAbelianInverseImage B
      (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY) _ h)

end DirectImage

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsFinite f]

/-- **Stacks Project, Lemma 0A5D.** Let `f : X ⟶ Y` be a finite morphism of schemes over a field
`k`, with `X` Noetherian, and let `F` be an abelian sheaf on `X_étale`. If statements (1) -- (8)
of Situation 0A52 hold for `F`, they hold for `f_* F`. -/
@[stacks 0A5D "all eight statements of 0A52 at once, at the coefficients AddCommGrpCat.{u+1}; \
only f finite and X Noetherian are used"]
theorem CurveStatements.directImage_of_isFinite [IsNoetherian X]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (h : CurveStatements.{u, 0, u + 1} (f ≫ π) F) :
    CurveStatements.{u, 0, u + 1} π ((etaleAbelianDirectImage.{u, 0} f).obj F) := by
  have hf : IsIntegralHom f := inferInstance
  have hcoh : ∀ q, Function.Bijective (etaleCohomologyDirectImageMap.{u, 0, u + 1} f F q) :=
    etaleCohomologyDirectImageMap_bijective.{u, 0, u + 1} f F
  have hsub : ∀ q, Subsingleton (Sheaf.H.{u + 1} F q) →
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} f).obj F) q) :=
    fun q hq ↦ (hcoh q).1.subsingleton
  have hfin : ∀ q, Finite (Sheaf.H.{u + 1} F q) →
      Finite (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} f).obj F) q) :=
    fun q hq ↦ Finite.of_injective _ (hcoh q).1
  -- Restriction along the base change of `f` to a cartesian square, on the cohomology of `f_* F`
  -- and of `F`.
  have hres : ∀ {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'},
      IsPullback g' f' f g → ∀ q,
      (Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g
        ((etaleAbelianDirectImage.{u, 0} f).obj F) q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g' F q)) ∧
      (Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g
        ((etaleAbelianDirectImage.{u, 0} f).obj F) q) ↔
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g' F q)) := by
    intro X' Y' g g' f' sq q
    have : IsFinite f' := MorphismProperty.of_isPullback sq ‹IsFinite f›
    have := isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback f g g' f' sq
    exact ⟨bijective_etaleCohomologyRestrictionMap_directImage_iff.{u, 0, u + 1} f g g' f' sq.w F q,
      surjective_etaleCohomologyRestrictionMap_directImage_iff.{u, 0, u + 1} f g g' f' sq.w F q⟩
  have hXB : ∀ (B : BigEtaleSite.{u}), B.Contains Y → B.Contains X := fun B hY ↦
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hY
  refine
    { vanishing := fun q hq ↦ hsub q (h.vanishing q hq)
      affineVanishing := fun hY q hq ↦ by
        have : IsAffine Y := hY
        exact hsub q (h.affineVanishing (isAffine_of_isAffineHom f) q hq)
      primePowerVanishing := fun p _ hp htor q hq ↦
        hsub q (h.primePowerVanishing p hp (isPrimePowerTorsion_of_directImage f hf htor) q hq)
      finite_of_isPrimeToCharacteristicTorsion := fun B hY _ _ hc htor q ↦
        have hX := hXB B hY
        hfin q (h.finite_of_isPrimeToCharacteristicTorsion B hX
          (isConstructibleEtaleAbelianSheaf_of_directImage B f hf hX hY F hc)
          (isPrimeToCharacteristicTorsion_of_directImage f hf htor) q)
      finite_of_isProper := fun B hY _ _ hπ hc q ↦ by
        have : IsProper π := hπ
        have hX := hXB B hY
        exact hfin q (h.finite_of_isProper B hX inferInstance
          (isConstructibleEtaleAbelianSheaf_of_directImage B f hf hX hY F hc) q)
      bijective_of_isPrimeToCharacteristicTorsion := fun htor k' _ _ _ _ _ q ↦
        (hres (isPullback_scalarExtension k' f π) q).1.mpr
          (h.bijective_of_isPrimeToCharacteristicTorsion
            (isPrimeToCharacteristicTorsion_of_directImage f hf htor) k' q)
      bijective_of_isProper := fun hπ k' _ _ _ _ _ q ↦ by
        have : IsProper π := hπ
        exact (hres (isPullback_scalarExtension k' f π) q).1.mpr
          (h.bijective_of_isProper inferInstance k' q)
      surjective := fun U _ ↦
        (hres (isPullback_morphismRestrict f U).flip 2).2.mpr (h.surjective (f ⁻¹ᵁ U)) }

end Stacks.EtaleCohomology

end
