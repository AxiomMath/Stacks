module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Degree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionAffineClassGroup
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs

/-!
# Units of an open subcurve modulo `ℓ`-th powers under extension of the base field

Let `j : X ⟶ Y` be an open immersion of smooth curves over an algebraically closed field `k`, `Y`
proper, and `k'/k` an algebraically closed extension. An invertible function `f` on `X` is a
rational function on `Y`; its divisor `u(f)` on `Y` is supported on the points at infinity. Then:

* `u(f) = 0` only for constants, so only for `ℓ`-th powers (`k` is algebraically closed);
* a divisor of `Y` supported at infinity whose class vanishes is some `u(f)`;
* `u(f_{k'}) = σ_* u(f)` for the closed points `σ(y)` of `Y_{k'}` over the closed points `y` of
  `Y`, and every `u(f')` on `X_{k'}` is some `σ_* d`.

With the injectivity of `Cl(Y) → Cl(Y_{k'})` the diagram chase
`AddMonoidHom.nsmul_comparison_of_divisor` then shows that `Γ(X, 𝒪_X)^* → Γ(X_{k'}, 𝒪)^*` is
bijective modulo `ℓ`-th powers (`Stacks.EtaleCohomology.unitsScalarExtension_nsmul_comparison`).

## Main results

* `AddMonoidHom.nsmul_comparison_of_divisor`: the diagram chase.
* `Stacks.EtaleCohomology.unitsDivisor`: the divisor on `Y` of an invertible function on `X`.
* `Stacks.EtaleCohomology.unitsDivisor_scalarExtension`: compatibility with scalar extension.
* `Stacks.EtaleCohomology.unitsScalarExtension_nsmul_comparison`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order IsLocalRing

universe u

/-- **The diagram chase for units modulo `ℓ`-th powers.** Let `u : A → D` and `u' : A' → D'`
(divisors of units) be compatible with `r : A → A'` and an injective `s : D → D'`, with every
`u' a'` in the image of `s`, let `cl, cl'` (classes) be compatible with an injective `φ`, with
`cl' ∘ u' = 0`, and `R, R'` (restriction) compatible with an injective `t`, with `R' ∘ u' = 0`.
If `d` with `cl d = 0`, `R d = 0` is some `u a`, and the kernels of `u`, `u'` consist of `ℓ`-th
multiples, then `r` is injective and surjective modulo `ℓ`. -/
theorem AddMonoidHom.nsmul_comparison_of_divisor {A A' D D' C C' E E' : Type*} [AddCommGroup A]
    [AddCommGroup A'] [AddCommGroup D] [AddCommGroup D'] [AddCommGroup C] [AddCommGroup C']
    [AddCommGroup E] [AddCommGroup E'] (ℓ : ℕ) (r : A →+ A') (u : A →+ D) (u' : A' →+ D')
    (s : D →+ D') (cl : D →+ C) (cl' : D' →+ C') (φ : C →+ C') (R : D →+ E) (R' : D' →+ E')
    (t : E →+ E') (hu : ∀ a, u' (r a) = s (u a)) (hφ : ∀ d, φ (cl d) = cl' (s d))
    (hφinj : Function.Injective φ) (hcl' : ∀ a', cl' (u' a') = 0) (hR' : ∀ a', R' (u' a') = 0)
    (hexact : ∀ d, cl d = 0 → R d = 0 → ∃ a, u a = d) (hRs : ∀ d, R' (s d) = t (R d))
    (ht : Function.Injective t) (hs : Function.Injective s) (hrange : ∀ a', ∃ d, u' a' = s d)
    (hker : ∀ a, u a = 0 → ∃ z, ℓ • z = a) (hker' : ∀ a', u' a' = 0 → ∃ z', ℓ • z' = a') :
    (∀ a z', ℓ • z' = r a → ∃ z, ℓ • z = a) ∧ (∀ a', ∃ a z', a' = r a + ℓ • z') := by
  have key : ∀ a' d, u' a' = s d → ∃ h, u h = d := fun a' d hd => hexact d
    (hφinj (by rw [hφ, ← hd, hcl', map_zero]))
    (ht (by rw [← hRs, ← hd, hR', map_zero]))
  refine ⟨fun a z' hz => ?_, fun a' => ?_⟩
  · obtain ⟨e, he⟩ := hrange z'
    obtain ⟨h, rfl⟩ := key z' e he
    have hua : u a = ℓ • u h := hs (by rw [map_nsmul s, ← he, ← map_nsmul, hz, hu])
    obtain ⟨w, hw⟩ := hker (a - ℓ • h) (by rw [map_sub, map_nsmul, hua, sub_self])
    exact ⟨w + h, by rw [nsmul_add, hw, sub_add_cancel]⟩
  · obtain ⟨d, hd⟩ := hrange a'
    obtain ⟨h, rfl⟩ := key a' d hd
    obtain ⟨z', hz'⟩ := hker' (a' - r h) (by rw [map_sub, hd, hu, sub_self])
    exact ⟨h, z', by rw [hz', add_sub_cancel]⟩

namespace Stacks.EtaleCohomology

/-! ### The divisor of an invertible function on an open subscheme -/

section UnitsDivisor

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [IsIntegral X] [IsIntegral Y]
  [IsDominant j]

/-- **An invertible function on a dense open `X ⊆ Y`, as a rational function on `Y`.** -/
def unitsToFunctionField : (Γ(X, ⊤))ˣ →* (Y.functionField)ˣ :=
  Units.map ((Stacks.Chow.functionFieldEquiv_openImmersion j).symm.toRingHom.comp
    (X.germToFunctionField ⊤).hom).toMonoidHom

/-- Restricted to `X`, the rational function of `f` is the germ of `f`. -/
theorem dominantFunctionFieldMap_unitsToFunctionField (a : (Γ(X, ⊤))ˣ) :
    dominantFunctionFieldMap j (unitsToFunctionField j a : Y.functionField) =
      X.germToFunctionField ⊤ (a : Γ(X, ⊤)) :=
  (Stacks.Chow.functionFieldEquiv_openImmersion j).apply_symm_apply _

/-- Distinct invertible functions give distinct rational functions. -/
theorem injective_unitsToFunctionField : Function.Injective (unitsToFunctionField j) :=
  fun _ _ h => Units.ext (Scheme.germToFunctionField_injective X ⊤
    ((Stacks.Chow.functionFieldEquiv_openImmersion j).symm.injective (congrArg Units.val h)))

variable [IsLocallyNoetherian Y] [NoetherianSpace Y]

/-- **The divisor on `Y` of an invertible function on `X`**, supported on the closed points. -/
def unitsDivisor : Additive (Γ(X, ⊤))ˣ →+ (closedPoints Y →₀ ℤ) :=
  (closedPointDivisorOfUnit Y).comp (unitsToFunctionField j).toAdditive

/-- The coefficient of `u(f)` at `y` is the order of vanishing of `f` at `y`. -/
theorem unitsDivisor_apply (a : Additive (Γ(X, ⊤))ˣ) (y : closedPoints Y) :
    unitsDivisor j a y =
      Y.ord (unitsToFunctionField j (Additive.toMul a) : Y.functionField) y.1 :=
  closedPointDivisorOfUnit_apply Y _ y

/-- **An invertible function on `X` has no zero or pole on `X`.** -/
theorem unitsDivisor_eq_zero_of_mem_range [IsLocallyNoetherian X] (a : Additive (Γ(X, ⊤))ˣ)
    (y : closedPoints Y) (hy : y.1 ∈ Set.range j.base) : unitsDivisor j a y = 0 := by
  obtain ⟨x, hx⟩ := hy
  rw [unitsDivisor_apply, ← hx, ← Stacks.Chow.ord_functionFieldEquiv_openImmersion]
  show X.ord (dominantFunctionFieldMap j _) x = 0
  rw [dominantFunctionFieldMap_unitsToFunctionField]
  exact Scheme.ord_of_isUnit (Additive.toMul a).isUnit trivial

end UnitsDivisor

/-! ### Open subcurves -/

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))
  (j : X ⟶ Y) [IsOpenImmersion j] [IsCurve k q] [Smooth q] [IsCurve k (j ≫ q)] [Smooth (j ≫ q)]
  [IsDominant j] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [NoetherianSpace X]
  [NoetherianSpace Y] [IsNormal X] [IsNormal Y]

omit [IsAlgClosed k] [Smooth q] [IsLocallyNoetherian Y] [NoetherianSpace Y] [IsNormal Y] in
include q in
/-- A point of coheight one of a curve is not its generic point. -/
theorem ne_genericPoint_of_coheight_eq_one {y : Y} (hy : coheight y = 1) :
    y ≠ genericPoint Y := by
  rintro rfl
  have hmax : IsMax (genericPoint Y) := fun b _ => genericPoint_specializes b
  rw [Order.coheight_eq_zero.mpr hmax] at hy
  exact zero_ne_one hy

omit [IsAlgClosed k] [Smooth q] [Smooth (j ≫ q)] [NoetherianSpace X] [IsNormal Y] in
include q in
/-- **A divisor at infinity with trivial class is the divisor of an invertible function on `X`**:
it is `div F` for a rational function `F`, which has no zero or pole on `X`, so is an invertible
function on the normal curve `X`. -/
theorem exists_unitsDivisor_eq (d : closedPoints Y →₀ ℤ)
    (hd : (QuotientAddGroup.mk d : closedPointClassGroup Y) = 0)
    (hR : ∀ y : closedPoints Y, y.1 ∈ Set.range j.base → d y = 0) :
    ∃ a, unitsDivisor j a = d := by
  obtain ⟨F, hF⟩ := (QuotientAddGroup.eq_zero_iff d).1 hd
  let G : (X.functionField)ˣ :=
    Units.map (Stacks.Chow.functionFieldEquiv_openImmersion j).toMonoidHom (Additive.toMul F)
  have h0 : ∀ z : X, coheight z = 1 → X.ord (G : X.functionField) z = 0 := by
    intro z hz
    have hzc := isClosed_singleton_of_coheight_eq_one (j ≫ q) hz
    show X.ord (Stacks.Chow.functionFieldEquiv_openImmersion j
      ((Additive.toMul F : (Y.functionField)ˣ) : Y.functionField)) z = 0
    rw [Stacks.Chow.ord_functionFieldEquiv_openImmersion]
    have h :=
      closedPointDivisorOfUnit_apply Y F (closedPointsMapOfOpenImmersion (j ≫ q) q j ⟨z, hzc⟩)
    rw [hF, hR _ ⟨z, rfl⟩] at h
    exact h.symm
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalUnit_of_forall_ord_eq_zero G h0
  refine ⟨Additive.ofMul s, ?_⟩
  rw [← hF]
  refine congrArg (closedPointDivisorOfUnit Y) (congrArg Additive.ofMul (Units.ext ?_))
  show (Stacks.Chow.functionFieldEquiv_openImmersion j).symm
    (X.presheaf.germ ⊤ (genericPoint X) trivial (s : Γ(X, ⊤))) = _
  rw [hs]
  exact (Stacks.Chow.functionFieldEquiv_openImmersion j).symm_apply_apply _

omit [Smooth (j ≫ q)] [IsLocallyNoetherian X] [NoetherianSpace X] [IsNormal X] in
include q in
/-- **On a proper curve an invertible function on `X` without zeros and poles is an `ℓ`-th
power**: it extends to a global unit of `Y`, a constant, and `k` is algebraically closed. -/
theorem exists_nsmul_eq_of_unitsDivisor_eq_zero [IsProper q] {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (a : (Γ(X, ⊤))ˣ) (ha : unitsDivisor j (Additive.ofMul a) = 0) :
    ∃ z, ℓ • z = Additive.ofMul a := by
  have h0 : ∀ y : Y, coheight y = 1 →
      Y.ord (unitsToFunctionField j a : Y.functionField) y = 0 := by
    intro y hy
    have hyc := isClosed_singleton_of_coheight_eq_one q hy
    have h := DFunLike.congr_fun ha ⟨y, hyc⟩
    rwa [unitsDivisor_apply] at h
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalUnit_of_forall_ord_eq_zero _ h0
  have := isIso_globalSections_of_isCurve_of_isProper q
  let ψ : k ≃+* Γ(Y, ⊤) := RingEquiv.ofBijective ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom
    (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop))
  let c : kˣ := Units.map ψ.symm.toMonoidHom s
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (c : k) (Nat.pos_of_ne_zero hℓ)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← ht, zero_pow hℓ])
  let w : (Γ(X, ⊤))ˣ := Units.map (j.appTop.hom.comp ψ.toRingHom).toMonoidHom (Units.mk0 t ht0)
  refine ⟨Additive.ofMul w, ?_⟩
  rw [← ofMul_pow]
  refine congrArg Additive.ofMul (injective_unitsToFunctionField j (Units.ext ?_))
  refine (dominantFunctionFieldMap j).injective ?_
  rw [dominantFunctionFieldMap_unitsToFunctionField, dominantFunctionFieldMap_unitsToFunctionField]
  have hw : ((w ^ ℓ : (Γ(X, ⊤))ˣ) : Γ(X, ⊤)) = j.appTop (s : Γ(Y, ⊤)) := by
    show j.appTop (ψ t) ^ ℓ = _
    rw [← map_pow, ← map_pow, ht]
    exact congrArg j.appTop (ψ.apply_symm_apply _)
  rw [hw, ← Stacks.Chow.dominantFunctionFieldMap_germToFunctionField,
    ← dominantFunctionFieldMap_unitsToFunctionField j a]
  exact congrArg (dominantFunctionFieldMap j) hs

variable (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']

/-- `j_{k'}` is dominant. -/
instance isDominant_scalarExtensionMap : IsDominant (scalarExtensionMap q j k') :=
  isDominant_of_isOpenImmersion_of_isCurve (scalarExtensionSnd k k' (j ≫ q))
    (scalarExtensionSnd k k' q) (scalarExtensionMap q j k')

omit [IsDominant j] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [NoetherianSpace X]
  [NoetherianSpace Y] [IsNormal X] [IsNormal Y] [Smooth (j ≫ q)] in
/-- **The divisor of an invertible function on `X_{k'}` is carried by the points over the points at
infinity of `Y`.** -/
theorem exists_unitsDivisor_scalarExtension_eq_mapDomain
    (a' : Additive (Γ(scalarExtension k k' (j ≫ q), ⊤))ˣ) :
    ∃ d, unitsDivisor (scalarExtensionMap q j k') a' =
      Finsupp.mapDomain (scalarExtensionClosedPoint q k') d := by
  have hsupp : ↑(unitsDivisor (scalarExtensionMap q j k') a').support ⊆
      Set.range (scalarExtensionClosedPoint q k') := by
    intro y' hy'
    by_cases hm : y'.1 ∈ Set.range (scalarExtensionMap q j k').base
    · exact absurd (unitsDivisor_eq_zero_of_mem_range _ a' y' hm) (Finsupp.mem_support_iff.1 hy')
    · obtain ⟨y, -, hy⟩ := exists_scalarExtensionClosedPoint_eq_of_notMem_range q j k' y' hm
      exact ⟨y, hy⟩
  exact ⟨_, (Finsupp.mapDomain_comapDomain _ (injective_scalarExtensionClosedPoint q k') _
    hsupp).symm⟩

omit [Smooth (j ≫ q)] [IsLocallyNoetherian X] [NoetherianSpace X] [IsNormal X] [IsNormal Y] in
/-- **The divisor of the pullback of an invertible function to `X_{k'}` is `σ_*` of its
divisor**: at the closed point over a closed point `y` of `Y` the order of vanishing is
unchanged (`Stacks.Chow.ord_dominantFunctionFieldMap_of_flat`), and at a closed point of
`Y_{k'}` over the generic point of `Y` it vanishes. -/
theorem unitsDivisor_scalarExtension (a : Additive (Γ(X, ⊤))ˣ) :
    unitsDivisor (scalarExtensionMap q j k')
        (Additive.ofMul (Units.map (scalarExtensionFst k k' (j ≫ q)).appTop.hom.toMonoidHom
          (Additive.toMul a))) =
      Finsupp.mapDomain (scalarExtensionClosedPoint q k') (unitsDivisor j a) := by
  have := surjective_scalarExtensionFst q k'
  have := surjective_scalarExtensionFst (j ≫ q) k'
  set F := (unitsToFunctionField j (Additive.toMul a) : Y.functionField)
  have hcongr : ∀ {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B] (f g : A ⟶ B) (_ : f = g)
      [IsDominant f] [IsDominant g], dominantFunctionFieldMap f = dominantFunctionFieldMap g := by
    intro A B _ _ f g h _ _
    subst h
    rfl
  have key : (unitsToFunctionField (scalarExtensionMap q j k')
      (Units.map (scalarExtensionFst k k' (j ≫ q)).appTop.hom.toMonoidHom (Additive.toMul a)) :
        (scalarExtension k k' q).functionField) =
      dominantFunctionFieldMap (scalarExtensionFst k k' q) F := by
    refine (dominantFunctionFieldMap (scalarExtensionMap q j k')).injective ?_
    rw [dominantFunctionFieldMap_unitsToFunctionField, ← RingHom.comp_apply,
      ← Stacks.Chow.dominantFunctionFieldMap_comp,
      hcongr _ _ (scalarExtensionMap_fst q j k'), Stacks.Chow.dominantFunctionFieldMap_comp,
      RingHom.comp_apply, dominantFunctionFieldMap_unitsToFunctionField,
      Stacks.Chow.dominantFunctionFieldMap_germToFunctionField]
    rfl
  refine Finsupp.ext fun y' => ?_
  rw [unitsDivisor_apply, toMul_ofMul, key]
  by_cases hy : y' ∈ Set.range (scalarExtensionClosedPoint q k')
  · obtain ⟨y, rfl⟩ := hy
    rw [Finsupp.mapDomain_apply (injective_scalarExtensionClosedPoint q k'), unitsDivisor_apply]
    have hy1 : IsClosed ({(scalarExtensionFst k k' q).base (scalarExtensionClosedPoint q k' y).1} :
        Set Y) := by
      rw [scalarExtensionFst_scalarExtensionClosedPoint]
      exact y.2
    have hcoh : coheight ((scalarExtensionFst k k' q).base (scalarExtensionClosedPoint q k' y).1) =
        coheight (scalarExtensionClosedPoint q k' y).1 := by
      rw [coheight_eq_one_of_isCurve k q hy1,
        coheight_eq_one_of_isCurve k' (scalarExtensionSnd k k' q)
          (scalarExtensionClosedPoint q k' y).2]
    refine (Stacks.Chow.ord_dominantFunctionFieldMap_of_flat (scalarExtensionFst k k' q) _
      (map_maximalIdeal_stalk_scalarExtension q k' _ hy1) hcoh F).trans ?_
    rw [scalarExtensionFst_scalarExtensionClosedPoint]
  · rw [Finsupp.mapDomain_notin_range _ _ hy]
    have hη : (scalarExtensionFst k k' q).base y'.1 = genericPoint Y := by
      by_contra h
      exact hy ⟨⟨_,
        Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
          Y (IsCurve.topologicalKrullDim_eq_one q) h⟩,
        (Subtype.ext (eq_scalarExtensionClosedPoint q k' _ rfl)).symm⟩
    exact Stacks.Chow.ord_dominantFunctionFieldMap_eq_zero_of_maximalIdeal_eq_bot _ y'.1
      (by rw [hη]; exact IsLocalRing.maximalIdeal_eq_bot) F

omit [NoetherianSpace X] in
/-- **Invertible functions modulo `ℓ`-th powers under extension of the base field**: for an open
subcurve `X` of a smooth proper curve `Y`, pullback `Γ(X, 𝒪_X)^* → Γ(X_{k'}, 𝒪)^*` is injective and
surjective modulo `ℓ`-th powers, `ℓ ≠ 0`. -/
theorem unitsScalarExtension_nsmul_comparison [IsProper q] {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    (∀ (a : Additive (Γ(X, ⊤))ˣ) (z' : Additive (Γ(scalarExtension k k' (j ≫ q), ⊤))ˣ),
      ℓ • z' = (Units.map (scalarExtensionFst k k' (j ≫ q)).appTop.hom.toMonoidHom).toAdditive a →
        ∃ z, ℓ • z = a) ∧
    (∀ a' : Additive (Γ(scalarExtension k k' (j ≫ q), ⊤))ˣ, ∃ a z',
      a' = (Units.map (scalarExtensionFst k k' (j ≫ q)).appTop.hom.toMonoidHom).toAdditive a +
        ℓ • z') := by
  have : IsCurve k' (scalarExtensionMap q j k' ≫ scalarExtensionSnd k k' q) := by
    rw [scalarExtensionMap_snd]
    infer_instance
  have : Smooth (scalarExtensionMap q j k' ≫ scalarExtensionSnd k k' q) := by
    rw [scalarExtensionMap_snd]
    infer_instance
  exact AddMonoidHom.nsmul_comparison_of_divisor ℓ _ (unitsDivisor j)
    (unitsDivisor (scalarExtensionMap q j k'))
    (Finsupp.mapDomain.addMonoidHom (scalarExtensionClosedPoint q k'))
    (QuotientAddGroup.mk' (closedPointDivisorOfUnit Y).range)
    (QuotientAddGroup.mk' (closedPointDivisorOfUnit (scalarExtension k k' q)).range)
    (curveClassGroupScalarExtensionMap q k') (closedPointDivisorRestriction (j ≫ q) q j)
    (closedPointDivisorRestriction (scalarExtensionSnd k k' (j ≫ q)) (scalarExtensionSnd k k' q)
      (scalarExtensionMap q j k'))
    (Finsupp.mapDomain.addMonoidHom (scalarExtensionClosedPoint (j ≫ q) k'))
    (unitsDivisor_scalarExtension q j k') (curveClassGroupScalarExtensionMap_mk k' q)
    (injective_of_map_single_eq q k' _ (curveClassGroupScalarExtensionMap_single q k'))
    (fun a' => (QuotientAddGroup.eq_zero_iff _).2 ⟨_, rfl⟩)
    (fun a' => Finsupp.ext fun x' => by
      rw [closedPointDivisorRestriction_apply]
      exact unitsDivisor_eq_zero_of_mem_range _ a' _ ⟨x'.1, rfl⟩)
    (fun d hd hR => exists_unitsDivisor_eq q j d hd fun y hy => by
      obtain ⟨x, rfl⟩ := exists_closedPointsMapOfOpenImmersion_eq (j ≫ q) q j y hy
      exact DFunLike.congr_fun hR x)
    (closedPointDivisorRestriction_mapDomain_scalarExtensionClosedPoint q j k')
    (Finsupp.mapDomain_injective (injective_scalarExtensionClosedPoint (j ≫ q) k'))
    (Finsupp.mapDomain_injective (injective_scalarExtensionClosedPoint q k'))
    (exists_unitsDivisor_scalarExtension_eq_mapDomain q j k')
    (fun a ha => exists_nsmul_eq_of_unitsDivisor_eq_zero q j hℓ (Additive.toMul a) ha)
    (fun a' ha' => exists_nsmul_eq_of_unitsDivisor_eq_zero (scalarExtensionSnd k k' q)
      (scalarExtensionMap q j k') hℓ (Additive.toMul a') ha')

end Curve

end Stacks.EtaleCohomology

end
