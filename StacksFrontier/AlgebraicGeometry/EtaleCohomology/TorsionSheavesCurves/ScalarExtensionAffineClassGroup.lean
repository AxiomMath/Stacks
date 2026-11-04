module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionRootsOfUnity

/-!
# The class group of an open subcurve under extension of the algebraically closed base field

Let `j : X ⟶ Y` be an open immersion of smooth curves over an algebraically closed field `k`, `Y`
proper, and `k'/k` an algebraically closed extension. Then `j_{k'} : X_{k'} ⟶ Y_{k'}` is an open
immersion whose image is the preimage of the image of `j`, and the closed points of `Y_{k'}`
outside `X_{k'}` are exactly the closed points over the closed points of `Y` outside `X`. Hence
`Cl(X_{k'}) = Cl(Y_{k'})/⟨σ(Y ∖ X)⟩` is the quotient of `Cl(Y_{k'})` by the image of the kernel of
`Cl(Y) → Cl(X)`, and `Cl(X) → Cl(X_{k'})` is injective and surjective on `ℓ`-torsion for `ℓ ∈ k^*`,
as `Cl(Y) → Cl(Y_{k'})` is.

## Main results

* `Stacks.EtaleCohomology.scalarExtensionMap`: `j_{k'}`, with
  `Stacks.EtaleCohomology.range_scalarExtensionMap`.
* `Stacks.EtaleCohomology.exists_scalarExtensionClosedPoint_eq_of_notMem_range`: the points at
  infinity of `Y_{k'}` lie over points at infinity of `Y`.
* `Stacks.EtaleCohomology.closedPointClassGroupRestriction_curveClassGroupScalarExtensionMap`:
  restriction to the open subcurve commutes with the class group maps.
* `Stacks.EtaleCohomology.injective_curveClassGroupScalarExtensionMap_of_isOpenImmersion`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.EtaleCohomology

/-- A smooth curve over `k`, extended to `k'`, has a Noetherian underlying space. -/
instance noetherianSpace_scalarExtension {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k']
    [IsAlgClosed k'] : NoetherianSpace (scalarExtension k k' g) :=
  (isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve
    (scalarExtensionSnd k k' g)).2.2.1

section Map

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) (j : X ⟶ Y)
  (k' : Type u) [Field k'] [Algebra k k']

/-- **The scalar extension of a morphism over `k`**: `j_{k'} : X_{k'} ⟶ Y_{k'}`. -/
def scalarExtensionMap : scalarExtension k k' (j ≫ q) ⟶ scalarExtension k k' q :=
  pullback.map (j ≫ q) _ q _ j (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- `j_{k'}` lies over `j`. -/
@[reassoc (attr := simp)]
theorem scalarExtensionMap_fst :
    scalarExtensionMap q j k' ≫ scalarExtensionFst k k' q = scalarExtensionFst k k' (j ≫ q) ≫ j :=
  pullback.lift_fst _ _ _

/-- `j_{k'}` is a morphism over `k'`. -/
@[reassoc (attr := simp)]
theorem scalarExtensionMap_snd :
    scalarExtensionMap q j k' ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k k'))) =
      pullback.snd (j ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The scalar extension of an open immersion is an open immersion. -/
instance isOpenImmersion_scalarExtensionMap [IsOpenImmersion j] :
    IsOpenImmersion (scalarExtensionMap q j k') := by
  unfold scalarExtensionMap
  infer_instance

/-- **The image of `j_{k'}` is the preimage of the image of `j`.** -/
theorem range_scalarExtensionMap :
    Set.range (scalarExtensionMap q j k').base =
      (scalarExtensionFst k k' q).base ⁻¹' Set.range j.base := by
  unfold scalarExtensionMap
  rw [Scheme.Pullback.range_map]
  exact Set.ext fun z => ⟨fun h => h.1, fun h => ⟨h, _, rfl⟩⟩

end Map

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))
  (j : X ⟶ Y) [IsOpenImmersion j] [IsCurve k q] [Smooth q] [IsCurve k (j ≫ q)] [Smooth (j ≫ q)]
  (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']

omit [Smooth (j ≫ q)] [IsAlgClosed k'] in
/-- **`j_{k'}` sends the closed point over `x` to the closed point over `j x`.** -/
theorem scalarExtensionMap_scalarExtensionClosedPoint (x : closedPoints X) :
    (scalarExtensionMap q j k').base (scalarExtensionClosedPoint (j ≫ q) k' x).1 =
      (scalarExtensionClosedPoint q k' (closedPointsMapOfOpenImmersion (j ≫ q) q j x)).1 := by
  refine eq_scalarExtensionClosedPoint q k' _ ?_
  rw [← Scheme.Hom.comp_apply, scalarExtensionMap_fst, Scheme.Hom.comp_apply,
    scalarExtensionFst_scalarExtensionClosedPoint]
  rfl

omit [Smooth (j ≫ q)] [IsAlgClosed k'] in
/-- `j_{k'}` on closed points sends the closed point over `x` to the closed point over `j x`. -/
theorem closedPointsMapOfOpenImmersion_scalarExtensionClosedPoint (x : closedPoints X) :
    closedPointsMapOfOpenImmersion (scalarExtensionSnd k k' (j ≫ q)) (scalarExtensionSnd k k' q)
        (scalarExtensionMap q j k') (scalarExtensionClosedPoint (j ≫ q) k' x) =
      scalarExtensionClosedPoint q k' (closedPointsMapOfOpenImmersion (j ≫ q) q j x) :=
  Subtype.ext (scalarExtensionMap_scalarExtensionClosedPoint q j k' x)

omit [IsOpenImmersion j] [IsCurve k q] [IsCurve k (j ≫ q)] [Smooth (j ≫ q)] [IsAlgClosed k'] in
/-- The closed point over `y` lies in `X_{k'}` exactly when `y` lies in `X`. -/
theorem scalarExtensionClosedPoint_mem_range_iff (y : closedPoints Y) :
    (scalarExtensionClosedPoint q k' y).1 ∈ Set.range (scalarExtensionMap q j k').base ↔
      y.1 ∈ Set.range j.base := by
  rw [range_scalarExtensionMap, Set.mem_preimage, scalarExtensionFst_scalarExtensionClosedPoint]

omit [Smooth (j ≫ q)] [IsAlgClosed k'] in
/-- **The points at infinity of `Y_{k'}` lie over points at infinity of `Y`**: a closed point of
`Y_{k'}` outside `X_{k'}` lies over a point of `Y` outside `X`, which is not the generic point
(it lies in `X`), hence closed; so it is the closed point over it. -/
theorem exists_scalarExtensionClosedPoint_eq_of_notMem_range
    (y' : closedPoints (scalarExtension k k' q))
    (hy' : y'.1 ∉ Set.range (scalarExtensionMap q j k').base) :
    ∃ y : closedPoints Y, y.1 ∉ Set.range j.base ∧ scalarExtensionClosedPoint q k' y = y' := by
  rw [range_scalarExtensionMap, Set.mem_preimage] at hy'
  have hη : j.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral j).out 1 2).mp
      (isDominant_of_isOpenImmersion_of_isCurve (j ≫ q) q j)
  have hne : (scalarExtensionFst k k' q).base y'.1 ≠ genericPoint Y := fun h =>
    hy' ⟨genericPoint X, hη.trans h.symm⟩
  let y : closedPoints Y :=
    ⟨_, Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint Y
      (IsCurve.topologicalKrullDim_eq_one q) hne⟩
  exact ⟨y, hy', Subtype.ext (eq_scalarExtensionClosedPoint q k' y rfl).symm⟩

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [NoetherianSpace X] [NoetherianSpace Y]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [NoetherianSpace X] [NoetherianSpace Y]
  [Smooth (j ≫ q)] [IsAlgClosed k'] in
/-- **Restriction of divisors to the open subcurve commutes with scalar extension.** -/
theorem closedPointDivisorRestriction_mapDomain_scalarExtensionClosedPoint
    (d : closedPoints Y →₀ ℤ) :
    closedPointDivisorRestriction (scalarExtensionSnd k k' (j ≫ q)) (scalarExtensionSnd k k' q)
        (scalarExtensionMap q j k') (Finsupp.mapDomain (scalarExtensionClosedPoint q k') d) =
      Finsupp.mapDomain (scalarExtensionClosedPoint (j ≫ q) k')
        (closedPointDivisorRestriction (j ≫ q) q j d) := by
  refine Finsupp.ext fun x' => ?_
  rw [closedPointDivisorRestriction_apply]
  by_cases hx' : x' ∈ Set.range (scalarExtensionClosedPoint (j ≫ q) k')
  · obtain ⟨x, rfl⟩ := hx'
    rw [closedPointsMapOfOpenImmersion_scalarExtensionClosedPoint,
      Finsupp.mapDomain_apply (injective_scalarExtensionClosedPoint q k'),
      Finsupp.mapDomain_apply (injective_scalarExtensionClosedPoint (j ≫ q) k'),
      closedPointDivisorRestriction_apply]
  · rw [Finsupp.mapDomain_notin_range _ _ hx', Finsupp.mapDomain_notin_range]
    rintro ⟨y, hy⟩
    have hmem : (scalarExtensionClosedPoint q k' y).1 ∈
        Set.range (scalarExtensionMap q j k').base := by
      rw [hy]
      exact ⟨x'.1, rfl⟩
    rw [scalarExtensionClosedPoint_mem_range_iff] at hmem
    obtain ⟨x, hx⟩ := exists_closedPointsMapOfOpenImmersion_eq (j ≫ q) q j y hmem
    refine hx' ⟨x, injective_closedPointsMapOfOpenImmersion
      (scalarExtensionSnd k k' (j ≫ q)) (scalarExtensionSnd k k' q) (scalarExtensionMap q j k') ?_⟩
    rw [closedPointsMapOfOpenImmersion_scalarExtensionClosedPoint, hx, hy]

/-- **The class group map on divisor classes** is `σ_*` on divisors. -/
theorem curveClassGroupScalarExtensionMap_mk {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    [IsCurve k g] [Smooth g] (d : closedPoints Z →₀ ℤ) :
    curveClassGroupScalarExtensionMap g k' (QuotientAddGroup.mk d : curveClassGroup g) =
      (QuotientAddGroup.mk (Finsupp.mapDomain (scalarExtensionClosedPoint g k') d) :
        curveClassGroup (scalarExtensionSnd k k' g)) := by
  induction d using Finsupp.induction_linear with
  | zero =>
    rw [Finsupp.mapDomain_zero, QuotientAddGroup.mk_zero, QuotientAddGroup.mk_zero, map_zero]
  | add d e hd he =>
    rw [Finsupp.mapDomain_add, QuotientAddGroup.mk_add, QuotientAddGroup.mk_add, map_add, hd, he]
  | single x n =>
    rw [Finsupp.mapDomain_single, ← Finsupp.smul_single_one x n,
      ← Finsupp.smul_single_one (scalarExtensionClosedPoint g k' x) n,
      QuotientAddGroup.mk_zsmul, QuotientAddGroup.mk_zsmul, map_zsmul,
      curveClassGroupScalarExtensionMap_single]

/-- **Restriction to the open subcurve commutes with the class group maps**:
`Cl(Y) → Cl(Y_{k'}) → Cl(X_{k'})` is `Cl(Y) → Cl(X) → Cl(X_{k'})`. -/
theorem closedPointClassGroupRestriction_curveClassGroupScalarExtensionMap
    (c : curveClassGroup q) :
    closedPointClassGroupRestriction (scalarExtensionSnd k k' (j ≫ q)) (scalarExtensionSnd k k' q)
        (scalarExtensionMap q j k') (curveClassGroupScalarExtensionMap q k' c) =
      curveClassGroupScalarExtensionMap (j ≫ q) k'
        (closedPointClassGroupRestriction (j ≫ q) q j c) := by
  induction c using QuotientAddGroup.induction_on with
  | H d =>
    rw [curveClassGroupScalarExtensionMap_mk, closedPointClassGroupRestriction_mk,
      closedPointClassGroupRestriction_mk, curveClassGroupScalarExtensionMap_mk,
      closedPointDivisorRestriction_mapDomain_scalarExtensionClosedPoint]

/-- **The kernel of `Cl(Y_{k'}) → Cl(X_{k'})` is the image of the kernel of `Cl(Y) → Cl(X)`.** -/
theorem ker_closedPointClassGroupRestriction_scalarExtension :
    (closedPointClassGroupRestriction (scalarExtensionSnd k k' (j ≫ q)) (scalarExtensionSnd k k' q)
        (scalarExtensionMap q j k')).ker =
      (closedPointClassGroupRestriction (j ≫ q) q j).ker.map
        (curveClassGroupScalarExtensionMap q k') := by
  rw [ker_closedPointClassGroupRestriction, ker_closedPointClassGroupRestriction,
    AddMonoidHom.map_closure, Set.image_image]
  congr 1
  ext c
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨y, hy, rfl⟩ := exists_scalarExtensionClosedPoint_eq_of_notMem_range q j k' y' hy'
    exact ⟨y, hy, curveClassGroupScalarExtensionMap_single q k' y⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨scalarExtensionClosedPoint q k' y, ?_,
      (curveClassGroupScalarExtensionMap_single q k' y).symm⟩
    show (scalarExtensionClosedPoint q k' y).1 ∉ _
    rwa [scalarExtensionClosedPoint_mem_range_iff]

/-- **`Cl(X) → Cl(X_{k'})` is injective and surjective on `ℓ`-torsion** for an open subcurve `X` of
a smooth proper curve `Y` and `ℓ ∈ k^*`: `Cl(X)` and `Cl(X_{k'})` are the quotients of `Cl(Y)` and
`Cl(Y_{k'})` by the classes of the points at infinity, and `Cl(Y) → Cl(Y_{k'})` is injective,
injective modulo `ℓ` and surjective on `ℓ`-torsion. -/
theorem injective_curveClassGroupScalarExtensionMap_of_isOpenImmersion [IsProper q] {ℓ : ℕ}
    (hℓ : IsUnit (ℓ : k)) :
    Function.Injective (curveClassGroupScalarExtensionMap (j ≫ q) k') ∧
      ∀ c', ℓ • c' = 0 → ∃ c, ℓ • c = 0 ∧ curveClassGroupScalarExtensionMap (j ≫ q) k' c = c' := by
  have hℓ' : IsUnit (ℓ : k') := by simpa using hℓ.map (algebraMap k k')
  obtain ⟨y₀⟩ := nonempty_closedPoints_of_isCurve q
  set φ := curveClassGroupScalarExtensionMap q k'
  have hφ := curveClassGroupScalarExtensionMap_single q k'
  have hQ := AddMonoidHom.nsmul_comparison_of_degree φ (curveClassGroupDegree q)
    (curveClassGroupDegree (scalarExtensionSnd k k' q)) ℓ
    (curveClassGroupDegree_curveClassGroupScalarExtensionMap q k')
    (QuotientAddGroup.mk (Finsupp.single y₀ (1 : ℤ)))
    (exists_sub_degree_nsmul_curveClassGroup q hℓ y₀)
    (fun c' => by
      rw [hφ y₀]
      exact exists_sub_degree_nsmul_curveClassGroup (scalarExtensionSnd k k' q) hℓ'
        (scalarExtensionClosedPoint q k' y₀) c')
  refine AddMonoidHom.nsmul_torsion_comparison_of_quotient φ
    (closedPointClassGroupRestriction (j ≫ q) q j)
    (closedPointClassGroupRestriction (scalarExtensionSnd k k' (j ≫ q))
      (scalarExtensionSnd k k' q) (scalarExtensionMap q j k'))
    (curveClassGroupScalarExtensionMap (j ≫ q) k') ℓ _
    (injective_of_map_single_eq q k' φ hφ) hQ.1 (fun c' hc' => ?_)
    (surjective_closedPointClassGroupRestriction _ _ _)
    (surjective_closedPointClassGroupRestriction _ _ _) rfl
    (ker_closedPointClassGroupRestriction_scalarExtension q j k')
    (fun c => (closedPointClassGroupRestriction_curveClassGroupScalarExtensionMap q j k' c).symm)
  obtain ⟨⟨c, hc⟩, hcc⟩ := (bijective_torsion_of_map_single_eq q k' hℓ φ hφ).2 ⟨c', hc'⟩
  exact ⟨c, hc, congrArg Subtype.val hcc⟩

end Curve

end Stacks.EtaleCohomology

end
