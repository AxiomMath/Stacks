module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClassGroupPicardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.KummerClassGroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroDivisibility
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Injectivity
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections

/-!
# The class group inputs of Case I of Tag 0A5B, from the Jacobian

Let `Y` be a smooth proper curve over an algebraically closed field `k` and `ℓ ∈ k^*`. Case I of
Tag 0A5B is reduced (`Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_classGroup`)
to properties of the divisor class group `Stacks.EtaleCohomology.curveClassGroup q`. Through
`Cl(Y) ≅ Pic(Y)` (`Stacks.EtaleCohomology.curveClassGroupAddEquivSchemePicard`, which sends `[y]`
to `𝒪_Y(y)`, of degree one) they are the properties of `Pic⁰(Y)` proved through the Jacobian in
`StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroDivisibility`:

* (A) the difference `[x] - [y]` of two point classes is divisible by `ℓ`;
* (B) the `ℓ`-torsion of `Cl(Y)` is finite;
* under scalar extension to `k'/k`: `Cl(Y)` maps injectively to `Cl(Y_{k'})` (Tag 0CC5 through
  Tag 0CDT, `H⁰(Y, 𝒪_Y) = k`), and the `ℓ`-torsion maps bijectively, for any homomorphism
  `Cl(Y) → Cl(Y_{k'})` sending the class of each closed point to the class of the closed point
  above it — the homomorphism is then pullback of line bundles.

## Main results

* `Stacks.EtaleCohomology.exists_nsmul_eq_sub_curveClassGroup_single`: (A).
* `Stacks.EtaleCohomology.finite_nsmul_torsion_curveClassGroup`: (B).
* `Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_scalarExtension`: the base case
  of Theorem 03SC for `𝐙/ℓ`, `ℓ ∈ k^*`, with (A) and (B) discharged.
* `Stacks.EtaleCohomology.curveClassGroupAddEquivSchemePicard_scalarExtensionClosedPoint`: the
  class of the closed point over `x` is the pullback of the class of `x`.
* `Stacks.EtaleCohomology.injective_of_map_single_eq` and
  `Stacks.EtaleCohomology.bijective_torsion_of_map_single_eq`: the scalar extension inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-! ### (A) and (B) -/

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))
  [IsCurve k q] [Smooth q] [IsProper q]

/-- **(A) of Case I of Tag 0A5B**: on a smooth proper curve over an algebraically closed field,
the difference of the classes of two closed points is divisible by every `ℓ ∈ k^*` in the class
group. It is a degree-zero class, and `Pic⁰` is `ℓ`-divisible (Tag 03RP (4) through the
Jacobian). -/
theorem exists_nsmul_eq_sub_curveClassGroup_single {ℓ : ℕ} (hℓ : IsUnit (ℓ : k))
    (x y : closedPoints Y) :
    ∃ b : curveClassGroup q,
      (QuotientAddGroup.mk (Finsupp.single x (1 : ℤ)) : curveClassGroup q) -
        QuotientAddGroup.mk (Finsupp.single y (1 : ℤ)) = ℓ • b := by
  have hdim : topologicalKrullDim Y ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := q)).le
  set e := curveClassGroupAddEquivSchemePicard q
  set c : curveClassGroup q :=
    (QuotientAddGroup.mk (Finsupp.single x (1 : ℤ)) : curveClassGroup q) -
      QuotientAddGroup.mk (Finsupp.single y (1 : ℤ))
  have hc : e c ∈ picardDegreeZero k q hdim := by
    simp only [c, e, mem_picardDegreeZero_iff, map_sub,
      picardDegree_curveClassGroupAddEquivSchemePicard_single q hdim, sub_self]
  obtain ⟨w, hw⟩ := exists_nsmul_eq_of_mem_picardDegreeZero q hdim hℓ ⟨e c, hc⟩
  refine ⟨e.symm w.1, e.injective ?_⟩
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  exact (congrArg Subtype.val hw).symm

/-- **(B) of Case I of Tag 0A5B**: on a smooth proper curve over an algebraically closed field,
the `ℓ`-torsion of the class group is finite for `ℓ ∈ k^*` (Tag 03RP through the Jacobian). -/
theorem finite_nsmul_torsion_curveClassGroup {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) :
    Finite {c : curveClassGroup q // ℓ • c = 0} :=
  finite_nsmul_torsion_of_addEquiv (curveClassGroupAddEquivSchemePicard q)
    (finite_schemePicard_torsion q hℓ)

end Curve

/-! ### The base case with (A) and (B) discharged -/

section BaseCase

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **The base case of the dévissage of Theorem 03SC for `E ≅ 𝐙/ℓ𝐙`, `ℓ ∈ k^*`, given only the
scalar extension input for statements (6), (7)**: the class group inputs (A) and (B) of
`Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_classGroup` hold by
`Stacks.EtaleCohomology.exists_nsmul_eq_sub_curveClassGroup_single` and
`Stacks.EtaleCohomology.finite_nsmul_torsion_curveClassGroup`. It is a reduction; nothing is
registered. -/
theorem curveStatementsConstantOnSmoothCurves_of_scalarExtension
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{u + 1})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    (h6 : ∀ (C : Scheme.{u}) (g : C ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
        (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
        [HasExt.{u + 1} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})]
        [HasExt.{u + 1} (Sheaf (scalarExtension k k' g).smallEtaleTopology
          AddCommGrpCat.{u + 1})] (q : ℕ), 1 ≤ q →
        Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' g)
          ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) q)) :
    CurveStatementsConstantOnSmoothCurves k E :=
  curveStatementsConstantOnSmoothCurves_of_classGroup k hℓk E hE
    (fun _ q _ _ _ x y => exists_nsmul_eq_sub_curveClassGroup_single q hℓk x y)
    (fun _ q _ _ _ => finite_nsmul_torsion_curveClassGroup q hℓk) h6

end BaseCase

/-! ### Scalar extension -/

section ScalarExtension

attribute [local instance] isCurve_scalarExtension smooth_scalarExtension

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k']

/-- **The class of the closed point over `x` is the pullback of the class of `x`**: under
`Cl ≅ Pic` on `X` and on `X_{k'}`, pullback of line bundles along `X_{k'} ⟶ X` sends the class of
a closed point `x` to the class of the closed point `x'` above it. -/
theorem curveClassGroupAddEquivSchemePicard_scalarExtensionClosedPoint (x : closedPoints X) :
    curveClassGroupAddEquivSchemePicard (scalarExtensionSnd k k' g)
        (QuotientAddGroup.mk (Finsupp.single (scalarExtensionClosedPoint g k' x) (1 : ℤ)) :
          curveClassGroup (scalarExtensionSnd k k' g)) =
      schemePicardPullbackHom (scalarExtensionFst k k' g)
        (curveClassGroupAddEquivSchemePicard g
          (QuotientAddGroup.mk (Finsupp.single x 1) : curveClassGroup g)) := by
  have := isEffectiveCartierDivisor_closedPoint g x
  rw [curveClassGroupAddEquivSchemePicard_single, curveClassGroupAddEquivSchemePicard_single,
    ← picardModelAddEquiv_schemePullbackClass_closedPoint g k' x,
    ← schemePicardPullbackHom_picardModelAddEquiv, AddEquiv.apply_symm_apply]

/-- **A class group map sending point classes to point classes is pullback of line bundles**:
if `φ : Cl(X) → Cl(X_{k'})` sends the class of every closed point `x` to the class of the closed
point over `x`, then under `Cl ≅ Pic` it is pullback along `X_{k'} ⟶ X`. -/
theorem curveClassGroupAddEquivSchemePicard_map_of_map_single_eq
    (φ : curveClassGroup g →+ curveClassGroup (scalarExtensionSnd k k' g))
    (hφ : ∀ x : closedPoints X, φ (QuotientAddGroup.mk (Finsupp.single x (1 : ℤ))) =
      QuotientAddGroup.mk (Finsupp.single (scalarExtensionClosedPoint g k' x) (1 : ℤ)))
    (c : curveClassGroup g) :
    curveClassGroupAddEquivSchemePicard (scalarExtensionSnd k k' g) (φ c) =
      schemePicardPullbackHom (scalarExtensionFst k k' g)
        (curveClassGroupAddEquivSchemePicard g c) := by
  have := isLocallyNoetherian_of_isCurve g
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  have h : ((curveClassGroupAddEquivSchemePicard (scalarExtensionSnd k k' g)).toAddMonoidHom.comp
      φ) = (schemePicardPullbackHom (scalarExtensionFst k k' g)).comp
        (curveClassGroupAddEquivSchemePicard g).toAddMonoidHom := by
    refine AddMonoidHom.eq_of_eqOn_dense (closure_range_closedPointClassGroup_single X) ?_
    rintro _ ⟨x, rfl⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [hφ x]
    exact curveClassGroupAddEquivSchemePicard_scalarExtensionClosedPoint g k' x
  exact DFunLike.congr_fun h c

omit [Smooth g] in
/-- On a smooth proper curve over an algebraically closed field the global functions are the
constants: the curve is geometrically integral (Tag 0BUG (8)). -/
theorem isIso_globalSections_of_isCurve_of_isProper [IsProper g] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) := by
  have : GeometricallyIrreducible g :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X g
  have : GeometricallyReduced g := geometricallyReduced_of_isReduced g
  have : GeometricallyIntegral g :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible g
  exact isIso_globalSections_of_geometricallyIntegral k g

/-- **Pullback of line bundles to `X_{k'}` is injective** on a smooth proper curve over an
algebraically closed field (Tag 0CDT from Tag 0CC5, `H⁰(X, 𝒪_X) = k`). -/
theorem injective_schemePicardPullbackHom_scalarExtensionFst [IsProper g] :
    Function.Injective (schemePicardPullbackHom (scalarExtensionFst k k' g)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
  have hinj := Stacks.Picard.injective_schemePullbackClass_of_globalSectionsIso
    (algebraMap k k') g (isIso_globalSections_of_isCurve_of_isProper g)
  intro a b hab
  have h := congrArg (Stacks.GluePicard.picardModelAddEquiv
    (scalarExtension k k' g).toRingedSpace).symm hab
  simp only [schemePicardPullbackHom, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply] at h
  exact (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm.injective (hinj h)

/-- **The scalar extension map on class groups is injective** (input (I) of Case I of Tag 0A5B),
for any homomorphism `Cl(X) → Cl(X_{k'})` sending point classes to point classes. -/
theorem injective_of_map_single_eq [IsProper g]
    (φ : curveClassGroup g →+ curveClassGroup (scalarExtensionSnd k k' g))
    (hφ : ∀ x : closedPoints X, φ (QuotientAddGroup.mk (Finsupp.single x (1 : ℤ))) =
      QuotientAddGroup.mk (Finsupp.single (scalarExtensionClosedPoint g k' x) (1 : ℤ))) :
    Function.Injective φ := by
  intro a b hab
  have h := congrArg (curveClassGroupAddEquivSchemePicard (scalarExtensionSnd k k' g)) hab
  simp only [curveClassGroupAddEquivSchemePicard_map_of_map_single_eq g k' φ hφ] at h
  exact (curveClassGroupAddEquivSchemePicard g).injective
    (injective_schemePicardPullbackHom_scalarExtensionFst g k' h)

/-- **The scalar extension map on the `ℓ`-torsion of class groups is bijective** for `ℓ ∈ k^*`
(input (S) of Case I of Tag 0A5B, and its injective half), for any homomorphism
`Cl(X) → Cl(X_{k'})` sending point classes to point classes: it is pullback of line bundles, which
is bijective on `ℓ`-torsion through the Jacobian. -/
theorem bijective_torsion_of_map_single_eq [IsProper g] {ℓ : ℕ} (hℓ : IsUnit (ℓ : k))
    (φ : curveClassGroup g →+ curveClassGroup (scalarExtensionSnd k k' g))
    (hφ : ∀ x : closedPoints X, φ (QuotientAddGroup.mk (Finsupp.single x (1 : ℤ))) =
      QuotientAddGroup.mk (Finsupp.single (scalarExtensionClosedPoint g k' x) (1 : ℤ))) :
    Function.Bijective (fun c : {c : curveClassGroup g // ℓ • c = 0} =>
      (⟨φ c.1, by rw [← map_nsmul, c.2, map_zero]⟩ :
        {c' : curveClassGroup (scalarExtensionSnd k k' g) // ℓ • c' = 0})) := by
  set e := curveClassGroupAddEquivSchemePicard g
  set e' := curveClassGroupAddEquivSchemePicard (scalarExtensionSnd k k' g)
  have hb := bijective_schemePicardPullbackHom_torsion g k' hℓ
  refine ⟨fun a b hab => ?_, fun c' => ?_⟩
  · exact Subtype.ext (injective_of_map_single_eq g k' φ hφ (congrArg Subtype.val hab))
  · obtain ⟨⟨z, hz⟩, hzc⟩ := hb.2 ⟨e' c'.1, by rw [← map_nsmul, c'.2, map_zero]⟩
    have hzc' : schemePicardPullbackHom (scalarExtensionFst k k' g) z = e' c'.1 :=
      congrArg Subtype.val hzc
    refine ⟨⟨e.symm z, by rw [← map_nsmul, hz, map_zero]⟩, Subtype.ext (e'.injective ?_)⟩
    change e' (φ (e.symm z)) = e' c'.1
    rw [curveClassGroupAddEquivSchemePicard_map_of_map_single_eq g k' φ hφ,
      AddEquiv.apply_symm_apply, hzc']

end ScalarExtension

end Stacks.EtaleCohomology

end
