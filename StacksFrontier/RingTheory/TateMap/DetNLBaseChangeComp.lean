module

public import StacksFrontier.RingTheory.TateMap.DetNLBaseChange
public import StacksFrontier.RingTheory.TateMap.DetTransport
public import StacksFrontier.Homology.TwoTermComplex.DeterminantEquivBaseChange

/-!
# Composition of base changes of the determinant of the naive cotangent complex

The identification `B' ⊗_B det(NL_{B/A}) ≅ det(NL_{B'/A'})` of
`Stacks.TateMap.detNLBaseChange` is compatible with composition of chart base changes and is
the canonical identification for the identity square.

## Main results

* `Stacks.TateMap.detNLBaseChangeOfIsIso_comp`: compatibility with composition, along squares
  whose comparisons of naive cotangent complexes are quasi-isomorphisms.
* `Stacks.TateMap.detNLBaseChange_comp`: compatibility with composition of chart base changes.
* `Stacks.TateMap.detNLBaseChange_refl`: the base change along the identity square is
  `B ⊗_B det(NL_{B/A}) ≅ det(NL_{B/A})`.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
* [Stacks Project, Lemma 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.TateMap

attribute [local instance] HasDerivedCategory.standard

open NaiveCotangent

section Comp

variable {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra A' A''] [Algebra B' B''] [Algebra A A''] [Algebra B B''] [Algebra A'' B'']
  [IsScalarTower A A' A''] [IsScalarTower B B' B'']
  [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [Algebra A' B''] [IsScalarTower A' B' B''] [IsScalarTower A' A'' B'']
  [Algebra A B''] [IsScalarTower A B B''] [IsScalarTower A A'' B'']

/-- The comparison `NL(P) ⊗_B B' → NL(P')` of a family of generators of `B` over `A` with one of
`B'` over `A'`. -/
def nlGensMap {ι ι' : Type} (P : Algebra.Generators A B ι) (P' : Algebra.Generators A' B' ι') :
    ChainMap (nlExtensionBaseChange P.toExtension B') (NL P') :=
  nlExtensionBaseChangeMap (P.defaultHom P').toExtensionHom

/-- Post-composing the comparison with the comparison of `P'` with the canonical presentation. -/
theorem nlCanonicalMap_comp_nlGensMap {ι ι' : Type} (P : Algebra.Generators A B ι)
    (P' : Algebra.Generators A' B' ι') :
    (nlCanonicalMap A' B' P').comp (nlGensMap P P') =
      nlExtensionBaseChangeMap ((P'.defaultHom (Algebra.Generators.self A' B')).toExtensionHom.comp
        (P.defaultHom P').toExtensionHom) := by
  let hc := (P'.defaultHom (Algebra.Generators.self A' B')).toExtensionHom
  let h' := (P.defaultHom P').toExtensionHom
  have k₁ : ∀ z : B' ⊗[B] P.toExtension.Cotangent,
      Algebra.Extension.Cotangent.map hc
          ((Algebra.Extension.Cotangent.map h').liftBaseChange B' z) =
        (Algebra.Extension.Cotangent.map (hc.comp h')).liftBaseChange B' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul b x => simp [Algebra.Extension.Cotangent.map_comp]
  have k₀ : ∀ z : B' ⊗[B] P.toExtension.CotangentSpace,
      Algebra.Extension.CotangentSpace.map hc
          ((Algebra.Extension.CotangentSpace.map h').liftBaseChange B' z) =
        (Algebra.Extension.CotangentSpace.map (hc.comp h')).liftBaseChange B' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul b x => simp [Algebra.Extension.CotangentSpace.map_comp]
  exact ChainMap.ext (LinearMap.ext k₁) (LinearMap.ext k₀)

omit [IsScalarTower A B B''] in
/-- Pre-composing the comparison for `B' → B''` with the base change of the comparison for
`B → B'` is the comparison for `B → B''`, up to the cancellation of the intermediate base
change. -/
theorem nlBaseChangeMap_comp_baseChange_nlGensMap {ι ι' : Type} (P : Algebra.Generators A B ι)
    (P' : Algebra.Generators A' B' ι') :
    (nlBaseChangeMap (A' := A'') (B' := B'') P').comp ((nlGensMap P P').baseChange B'') =
      (nlExtensionBaseChangeMap
        ((P'.defaultHom (Algebra.Generators.self A'' B'')).toExtensionHom.comp
          (P.defaultHom P').toExtensionHom)).comp
        (cancelBaseChangeChainMap (D := B') (C := B'') P.toExtension) := by
  let hc := (P'.defaultHom (Algebra.Generators.self A'' B'')).toExtensionHom
  let h' := (P.defaultHom P').toExtensionHom
  have k₁ : ∀ z : B'' ⊗[B'] (B' ⊗[B] P.toExtension.Cotangent),
      (Algebra.Extension.Cotangent.map hc).liftBaseChange B''
          (((Algebra.Extension.Cotangent.map h').liftBaseChange B').baseChange B'' z) =
        (Algebra.Extension.Cotangent.map (hc.comp h')).liftBaseChange B''
          (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B''
            P.toExtension.Cotangent z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul c w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, hx, hy]
      | tmul b x =>
        simp [Algebra.Extension.Cotangent.map_comp]
  have k₀ : ∀ z : B'' ⊗[B'] (B' ⊗[B] P.toExtension.CotangentSpace),
      (Algebra.Extension.CotangentSpace.map hc).liftBaseChange B''
          (((Algebra.Extension.CotangentSpace.map h').liftBaseChange B').baseChange B'' z) =
        (Algebra.Extension.CotangentSpace.map (hc.comp h')).liftBaseChange B''
          (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B''
            P.toExtension.CotangentSpace z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul c w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, hx, hy]
      | tmul b x =>
        simp [Algebra.Extension.CotangentSpace.map_comp]
  exact ChainMap.ext (LinearMap.ext k₁) (LinearMap.ext k₀)

end Comp

/-- The cochain-model identification undoes its inverse. -/
theorem coneLine_lineCongr {R : Type u} [CommRing R] (T : TwoTerm.{u, u, u} R)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₀] [Module.Projective R T.X₀] (y : TwoTermComplex.determinantLine T.d) :
    coneLine T (TwoTermComplex.lineCongr T.d ((cone T).d (-1) 0).hom
      (coneNegOneIso T).toLinearEquiv (coneZeroIso T).toLinearEquiv y) = y := by
  have hr₁ : (coneNegOneIso T).toLinearEquiv.trans (coneNegOneIso T).symm.toLinearEquiv =
      LinearEquiv.refl R _ := by
    ext z
    exact (coneNegOneIso T).hom_inv_id_apply z
  have hr₀ : (coneZeroIso T).toLinearEquiv.trans (coneZeroIso T).symm.toLinearEquiv =
      LinearEquiv.refl R _ := by
    ext z
    exact (coneZeroIso T).hom_inv_id_apply z
  have hl := TwoTermComplex.lineCongr_trans T.d ((cone T).d (-1) 0).hom T.d
    (coneNegOneIso T).toLinearEquiv (coneZeroIso T).toLinearEquiv
    (coneNegOneIso T).symm.toLinearEquiv (coneZeroIso T).symm.toLinearEquiv
  rw [hr₁, hr₀, TwoTermComplex.lineCongr_refl] at hl
  exact LinearEquiv.congr_fun hl y

/-- The determinant equivalence of a degreewise surjective quasi-isomorphism commutes with base
change, on elements `1 ⊗ y`. -/
theorem lineBaseChange_detEquiv {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {K₁ K₀ L₁ L₀ : Type u}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} (a : TwoTermComplex.Hom d d')
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (ha' : (a.baseChange S).IsDegreewiseSurjective) (hqa' : (a.baseChange S).IsQuasiIso)
    (y : TwoTermComplex.determinantLine d) :
    TwoTermComplex.lineBaseChange S d' (1 ⊗ₜ TwoTermComplex.detEquiv a ha hqa y) =
      TwoTermComplex.detEquiv (a.baseChange S) ha' hqa'
        (TwoTermComplex.lineBaseChange S d (1 ⊗ₜ y)) := by
  have h := TwoTermComplex.lineBaseChange_determinantEquivOfSurjectiveQuasiIso S a ha hqa ha' hqa'
    (1 ⊗ₜ y)
  rwa [LinearEquiv.baseChange_tmul] at h

/-- Cancelling an intermediate base change commutes with base change, inverse form. -/
theorem cancelBaseChange_symm_baseChange_comm {B B' B'' : Type u} [CommRing B] [CommRing B']
    [CommRing B''] [Algebra B B'] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B'']
    {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (f : M →ₗ[B] N)
    (z : B'' ⊗[B] M) :
    LinearMap.baseChange B'' (LinearMap.baseChange B' f)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' M).symm z) =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' N).symm
        (LinearMap.baseChange B'' f z) := by
  apply (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' N).injective
  rw [LinearEquiv.apply_symm_apply, ← cancelBaseChange_baseChange_comm,
    LinearEquiv.apply_symm_apply]

/-! ### The algebra of the composite -/

/-- The base change of the second leg of the span of `φ'` is homotopic to the base change of `φ'`
composed with the base change of the first leg. -/
private theorem homotopic_bcSpanQ {R B B' B'' : Type u} [CommRing R] [CommRing B] [CommRing B']
    [CommRing B''] [Algebra R B] [Algebra B B'] [Algebra B' B''] {Q : Algebra.Extension R B}
    {T' : TwoTerm.{u, u, u} B'} {φ' : ChainMap (nlExtensionBaseChange Q B') T'} :
    Homotopic ((spanQ φ').baseChange B'')
      ((φ'.baseChange B'').comp ((spanP _ T').baseChange B'')) := by
  rw [← ChainMap.baseChange_comp]
  exact (homotopic_spanQ φ').baseChange B''

section Algebra

variable {R B B' B'' : Type u} [CommRing R] [CommRing B] [CommRing B'] [CommRing B'']
  [Algebra R B] [Algebra B B'] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B'']
  (Q : Algebra.Extension R B)
  [Module.Finite B Q.Cotangent] [Module.Projective B Q.Cotangent]
  [Module.Finite B Q.CotangentSpace] [Module.Projective B Q.CotangentSpace]
  {T' : TwoTerm.{u, u, u} B'} [Module.Finite B' T'.X₁] [Module.Projective B' T'.X₁]
  [Module.Finite B' T'.X₀] [Module.Projective B' T'.X₀]

/-- The degree `1` term of `NL(Q) ⊗_B B'` is a finite `B'`-module. -/
instance : Module.Finite B' (nlExtensionBaseChange Q B').X₁ :=
  inferInstanceAs (Module.Finite B' (B' ⊗[B] Q.Cotangent))
/-- The degree `1` term of `NL(Q) ⊗_B B'` is a projective `B'`-module. -/
instance : Module.Projective B' (nlExtensionBaseChange Q B').X₁ :=
  inferInstanceAs (Module.Projective B' (B' ⊗[B] Q.Cotangent))
/-- The degree `0` term of `NL(Q) ⊗_B B'` is a finite `B'`-module. -/
instance : Module.Finite B' (nlExtensionBaseChange Q B').X₀ :=
  inferInstanceAs (Module.Finite B' (B' ⊗[B] Q.CotangentSpace))
/-- The degree `0` term of `NL(Q) ⊗_B B'` is a projective `B'`-module. -/
instance : Module.Projective B' (nlExtensionBaseChange Q B').X₀ :=
  inferInstanceAs (Module.Projective B' (B' ⊗[B] Q.CotangentSpace))

/-- The first leg `W ⊗ B'' → NL(Q) ⊗_B B''` of the base changed span, through the cancellation
of the intermediate base change. -/
def bcSpanP (T' : TwoTerm.{u, u, u} B') :
    ChainMap ((spanTwoTerm (nlExtensionBaseChange Q B') T').baseChange B'')
      (nlExtensionBaseChange Q B'') :=
  (cancelBaseChangeChainMap (D := B') (C := B'') Q).comp
    ((spanP (nlExtensionBaseChange Q B') T').baseChange B'')

omit [Module.Finite B Q.Cotangent] [Module.Projective B Q.Cotangent]
  [Module.Finite B Q.CotangentSpace] [Module.Projective B Q.CotangentSpace]
  [Module.Finite B' T'.X₁] [Module.Projective B' T'.X₁] [Module.Finite B' T'.X₀]
  [Module.Projective B' T'.X₀] in
/-- The first leg of the base changed span is degreewise surjective. -/
theorem bcSpanP_surjective : (toHom (bcSpanP (B'' := B'') Q T')).IsDegreewiseSurjective := by
  constructor
  · intro z
    obtain ⟨w, hw⟩ := surjective_baseChange (T := B'')
      (LinearMap.fst_surjective (R := B') (M := B' ⊗[B] Q.Cotangent) (M₂ := T'.X₁))
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' Q.Cotangent).symm z)
    refine ⟨w, ?_⟩
    show TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' Q.Cotangent
      (LinearMap.baseChange B'' (LinearMap.fst B' _ T'.X₁) w) = z
    rw [hw]
    exact LinearEquiv.apply_symm_apply _ z
  · intro z
    obtain ⟨w, hw⟩ := surjective_baseChange (T := B'')
      (LinearMap.fst_surjective (R := B') (M := B' ⊗[B] Q.CotangentSpace) (M₂ := T'.X₁))
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' Q.CotangentSpace).symm z)
    refine ⟨w, ?_⟩
    show TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' Q.CotangentSpace
      (LinearMap.baseChange B'' (LinearMap.fst B' _ T'.X₁) w) = z
    rw [hw]
    exact LinearEquiv.apply_symm_apply _ z

omit [Module.Finite B Q.Cotangent] [Module.Projective B Q.Cotangent]
  [Module.Finite B Q.CotangentSpace] [Module.Projective B Q.CotangentSpace]
  [Module.Finite B' T'.X₁] [Module.Projective B' T'.X₁] [Module.Finite B' T'.X₀]
  [Module.Projective B' T'.X₀] in
/-- The first leg of the base changed span is a quasi-isomorphism. -/
theorem bcSpanP_isQuasiIso : IsQuasiIso (bcSpanP (B'' := B'') Q T') :=
  TwoTermHomotopy.isQuasiIso_comp
    (isQuasiIso_of_isHomotopyEquiv ((isHomotopyEquiv_spanP _ T').baseChange B''))
    (isQuasiIso_cancelBaseChangeChainMap _)

variable {Q}

omit [Algebra B B''] [IsScalarTower B B' B''] [Module.Finite B Q.Cotangent]
  [Module.Projective B Q.Cotangent] [Module.Finite B Q.CotangentSpace]
  [Module.Projective B Q.CotangentSpace] [Module.Finite B' T'.X₁] [Module.Projective B' T'.X₁]
  [Module.Finite B' T'.X₀] [Module.Projective B' T'.X₀] in
/-- The base change to `B''` of the second leg of the span of `φ'` is degreewise surjective. -/
theorem bcSpanQ_surjective {φ' : ChainMap (nlExtensionBaseChange Q B') T'}
    (hφ' : IsQuasiIso φ') : (toHom ((spanQ φ').baseChange B'')).IsDegreewiseSurjective :=
  ⟨surjective_baseChange B'' (spanQ_surjective hφ').1,
    surjective_baseChange B'' (spanQ_surjective hφ').2⟩

omit [Algebra B B''] [IsScalarTower B B' B''] [Module.Finite B Q.Cotangent]
  [Module.Projective B Q.Cotangent] [Module.Finite B Q.CotangentSpace]
  [Module.Projective B Q.CotangentSpace] [Module.Finite B' T'.X₁] [Module.Projective B' T'.X₁]
  [Module.Finite B' T'.X₀] [Module.Projective B' T'.X₀] in
/-- If the base change of `φ'` to `B''` is a quasi-isomorphism, then so is the base change to
`B''` of the second leg of the span of `φ'`. -/
theorem bcSpanQ_isQuasiIso {φ' : ChainMap (nlExtensionBaseChange Q B') T'}
    (hφ'bc : IsQuasiIso (φ'.baseChange B'')) : IsQuasiIso ((spanQ φ').baseChange B'') :=
  TwoTermHomotopy.isQuasiIso (TwoTermHomotopy.symm homotopic_bcSpanQ)
    (TwoTermHomotopy.isQuasiIso_comp
      (isQuasiIso_of_isHomotopyEquiv ((isHomotopyEquiv_spanP _ T').baseChange B'')) hφ'bc)

/-- Transporting the base change of a determinant line along
the base changed span agrees with base changing its transport along the span. -/
theorem detEquiv_span_baseChange {φ' : ChainMap (nlExtensionBaseChange Q B') T'}
    (hφ' : IsQuasiIso φ') (hφ'bc : IsQuasiIso (φ'.baseChange B''))
    (φP : TwoTermComplex.determinantLine Q.cotangentComplex) :
    TwoTermComplex.detEquiv (toHom ((spanQ φ').baseChange B'')) (bcSpanQ_surjective hφ')
        (toHom_isQuasiIso (bcSpanQ_isQuasiIso hφ'bc))
        ((TwoTermComplex.detEquiv (toHom (bcSpanP (B'' := B'') Q T')) (bcSpanP_surjective Q)
          (toHom_isQuasiIso (bcSpanP_isQuasiIso Q))).symm
            (TwoTermComplex.lineBaseChange B'' Q.cotangentComplex (1 ⊗ₜ φP))) =
      TwoTermComplex.lineBaseChange B'' T'.d (1 ⊗ₜ TwoTermComplex.detEquiv (toHom (spanQ φ'))
        (spanQ_surjective hφ') (toHom_isQuasiIso (isQuasiIso_spanQ hφ'))
        ((TwoTermComplex.detEquiv (toHom (spanP _ T')) (spanP_surjective _ T')
          (toHom_isQuasiIso (isQuasiIso_spanP _ T'))).symm
            (TwoTermComplex.lineBaseChange B' Q.cotangentComplex (1 ⊗ₜ φP)))) := by
  let T₁ := nlExtensionBaseChange Q B'
  let Ep := TwoTermComplex.detEquiv (toHom (spanP T₁ T')) (spanP_surjective _ T')
    (toHom_isQuasiIso (isQuasiIso_spanP _ T'))
  let u := TwoTermComplex.lineBaseChange B' Q.cotangentComplex (1 ⊗ₜ φP)
  have hc2q := lineBaseChange_detEquiv (S := B'') (toHom (spanQ φ')) (spanQ_surjective hφ')
    (toHom_isQuasiIso (isQuasiIso_spanQ hφ')) (bcSpanQ_surjective hφ')
    (toHom_isQuasiIso (bcSpanQ_isQuasiIso hφ'bc)) (Ep.symm u)
  have hpbs : ((toHom (spanP T₁ T')).baseChange B'').IsDegreewiseSurjective :=
    ⟨surjective_baseChange B'' LinearMap.fst_surjective,
      surjective_baseChange B'' LinearMap.fst_surjective⟩
  have hspanPbc : IsQuasiIso ((spanP T₁ T').baseChange B'') :=
    isQuasiIso_of_isHomotopyEquiv ((isHomotopyEquiv_spanP T₁ T').baseChange B'')
  have hc2p := lineBaseChange_detEquiv (S := B'') (toHom (spanP T₁ T'))
    (spanP_surjective T₁ T') (toHom_isQuasiIso (isQuasiIso_spanP T₁ T')) hpbs
    (toHom_isQuasiIso hspanPbc) (Ep.symm u)
  have hc2p' : TwoTermComplex.lineBaseChange B'' T₁.d (1 ⊗ₜ u) =
      TwoTermComplex.detEquiv ((toHom (spanP T₁ T')).baseChange B'') hpbs
        (toHom_isQuasiIso hspanPbc)
        (TwoTermComplex.lineBaseChange B'' (spanTwoTerm T₁ T').d (1 ⊗ₜ Ep.symm u)) := by
    rwa [show TwoTermComplex.detEquiv (toHom (spanP T₁ T')) (spanP_surjective T₁ T')
      (toHom_isQuasiIso (isQuasiIso_spanP T₁ T')) (Ep.symm u) = u from
        LinearEquiv.apply_symm_apply Ep u] at hc2p
  let c := cancelBaseChangeChainMap (D := B') (C := B'') Q
  have hcs : (toHom c).IsDegreewiseSurjective :=
    ⟨LinearEquiv.surjective _, LinearEquiv.surjective _⟩
  have hcq : (toHom c).IsQuasiIso := toHom_isQuasiIso (isQuasiIso_cancelBaseChangeChainMap _)
  have hEp₃ : TwoTermComplex.detEquiv (toHom (bcSpanP (B'' := B'') Q T')) (bcSpanP_surjective Q)
      (toHom_isQuasiIso (bcSpanP_isQuasiIso Q)) =
      (TwoTermComplex.detEquiv ((toHom (spanP T₁ T')).baseChange B'') hpbs
        (toHom_isQuasiIso hspanPbc)).trans (TwoTermComplex.detEquiv (toHom c) hcs hcq) :=
    TwoTermComplex.detEquiv_comp (toHom c) ((toHom (spanP T₁ T')).baseChange B'') hpbs
      (toHom_isQuasiIso hspanPbc) hcs hcq (bcSpanP_surjective Q)
      (toHom_isQuasiIso (bcSpanP_isQuasiIso Q))
  have hEc := TwoTermComplex.detEquiv_eq_lineCongr (toHom c) hcs hcq
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' Q.Cotangent)
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' Q.CotangentSpace) rfl rfl
  have hT4 := TwoTermComplex.lineBaseChange_trans B' B'' Q.cotangentComplex φP
  have hw : TwoTermComplex.detEquiv (toHom (bcSpanP (B'' := B'') Q T')) (bcSpanP_surjective Q)
      (toHom_isQuasiIso (bcSpanP_isQuasiIso Q))
        (TwoTermComplex.lineBaseChange B'' (spanTwoTerm T₁ T').d (1 ⊗ₜ Ep.symm u)) =
      TwoTermComplex.lineBaseChange B'' Q.cotangentComplex (1 ⊗ₜ φP) := by
    refine (LinearEquiv.congr_fun hEp₃ _).trans ?_
    show TwoTermComplex.detEquiv (toHom c) hcs hcq (TwoTermComplex.detEquiv
      ((toHom (spanP T₁ T')).baseChange B'') hpbs (toHom_isQuasiIso hspanPbc)
        (TwoTermComplex.lineBaseChange B'' (spanTwoTerm T₁ T').d (1 ⊗ₜ Ep.symm u))) = _
    rw [← hc2p', hEc]
    exact hT4
  exact (congrArg _ ((LinearEquiv.symm_apply_eq _).2 hw.symm)).trans hc2q.symm

end Algebra

/-- If `g ∘ φ` is homotopic to `f`, then `φ` is compatible with the inverses of the cone maps of
`f` and `g` in the derived category. -/
private theorem inv_comp_coneMap_eq {R : Type u} [CommRing R] {X Y Z : TwoTerm.{u, u, u} R}
    (φ : ChainMap X Y) (g : ChainMap Y Z) (f : ChainMap X Z)
    [IsIso (DerivedCategory.Q.map (coneMap f))] [IsIso (DerivedCategory.Q.map (coneMap g))]
    (h : Homotopic (g.comp φ) f) :
    (asIso (DerivedCategory.Q.map (coneMap f))).symm.hom ≫ DerivedCategory.Q.map (coneMap φ) =
      (asIso (DerivedCategory.Q.map (coneMap g))).symm.hom := by
  have h' : DerivedCategory.Q.map (coneMap φ) ≫ DerivedCategory.Q.map (coneMap g) =
      DerivedCategory.Q.map (coneMap f) := by
    rw [← Functor.map_comp, ← coneMap_comp]
    exact Q_map_coneMap_eq_of_homotopic h
  simp only [Iso.symm_hom, asIso_inv]
  rw [IsIso.inv_comp_eq, ← h', Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Two `B'`-linear equivalences out of `B' ⊗[B] M` agreeing on the elements `1 ⊗ₜ x` are equal. -/
private theorem baseChange_linearEquiv_ext {B B' M N : Type u} [CommRing B] [CommRing B']
    [Algebra B B'] [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B' N]
    (f g : B' ⊗[B] M ≃ₗ[B'] N) (h : ∀ x : M, f (1 ⊗ₜ x) = g (1 ⊗ₜ x)) : f = g := by
  refine LinearEquiv.ext fun w => ?_
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  | tmul b x =>
    have hb : (b ⊗ₜ[B] x : B' ⊗[B] M) = b • ((1 : B') ⊗ₜ[B] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hb, map_smul, map_smul, h]

section CompMain

variable {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra A' A''] [Algebra B' B''] [Algebra A A''] [Algebra B B''] [Algebra A'' B'']
  [IsScalarTower A A' A''] [IsScalarTower B B' B'']
  [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [Algebra A' B''] [IsScalarTower A' B' B''] [IsScalarTower A' A'' B'']
  [Algebra A B''] [IsScalarTower A B B''] [IsScalarTower A A'' B'']
  [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A'' B'']

/-- The determinant line element `1 ⊗ x` of `NL(P) ⊗_B B'`, transported along the cone
presentation, is the base change of the determinant line element of `x`. -/
private theorem coneLine_detNLBaseChangeOfIsIso
    (hq : IsIso (DerivedCategory.Q.map (coneMap (nlBaseChangeMap (A' := A') (B' := B')
      (gens A B))))) (x : detNL A B) :
    coneLine (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))
        (TwoTermDeterminant.detPresentationIso (nlObject A' B') (nlBaseChangePresentation hq)
          (detNLBaseChangeOfIsIso hq (1 ⊗ₜ x))) =
      TwoTermComplex.lineBaseChange B' (gens A B).toExtension.cotangentComplex
        (1 ⊗ₜ detNLEquiv (gens A B) x) := by
  simp only [detNLBaseChangeOfIsIso, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  exact (congrArg _ (LinearEquiv.apply_symm_apply _ _)).trans (coneLine_lineCongr _ _)

/-- The base changes of `det(NL)` along squares whose comparisons of naive cotangent complexes are
quasi-isomorphisms are compatible with composition. -/
theorem detNLBaseChangeOfIsIso_comp
    (hg₁ : IsQuasiIso (nlBaseChangeMap (A' := A') (B' := B') (gens A B)))
    (hg₂ : IsQuasiIso (nlBaseChangeMap (A' := A'') (B' := B'') (gens A' B')))
    (hg₃ : IsQuasiIso (nlBaseChangeMap (A' := A'') (B' := B'') (gens A B)))
    (hq₁ : IsIso (DerivedCategory.Q.map (coneMap (nlBaseChangeMap (A' := A') (B' := B')
      (gens A B)))))
    (hq₂ : IsIso (DerivedCategory.Q.map (coneMap (nlBaseChangeMap (A' := A'') (B' := B'')
      (gens A' B')))))
    (hq₃ : IsIso (DerivedCategory.Q.map (coneMap (nlBaseChangeMap (A' := A'') (B' := B'')
      (gens A B))))) :
    detNLBaseChangeOfIsIso hq₃ =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' (detNL A B)).symm ≪≫ₗ
        (detNLBaseChangeOfIsIso hq₁).baseChange B' B'' _ _ ≪≫ₗ detNLBaseChangeOfIsIso hq₂ := by
  let P := gens A B
  let P' := gens A' B'
  let T₁ : TwoTerm.{u, u, u} B' := nlBaseChangeTwoTerm (A := A) (B := B) (B' := B')
  let T' : TwoTerm.{u, u, u} B' := NL P'
  let T₃ : TwoTerm.{u, u, u} B'' := nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'')
  let T₂ : TwoTerm.{u, u, u} B'' := nlBaseChangeTwoTerm (A := A') (B := B') (B' := B'')
  let φ' : ChainMap T₁ T' := nlGensMap P P'
  let g₁ := nlBaseChangeMap (A' := A') (B' := B') P
  let g₂ := nlBaseChangeMap (A' := A'') (B' := B'') P'
  let g₃ := nlBaseChangeMap (A' := A'') (B' := B'') P
  let nlc := nlCanonicalMap A' B' P'
  have hnlc : IsQuasiIso nlc :=
    (nlMap_isHomotopyEquiv_and_isQuasiIso (by simpa using Function.bijective_id)
      (by simpa using Function.bijective_id) P' _ _).2
  have hφ'g : Homotopic (nlc.comp φ') g₁ := by
    show Homotopic ((nlCanonicalMap A' B' P').comp (nlGensMap P P')) g₁
    rw [nlCanonicalMap_comp_nlGensMap]
    exact homotopic_nlExtensionBaseChangeMap _ _
  have hφ' : IsQuasiIso φ' :=
    TwoTermHomotopy.isQuasiIso_of_comp hnlc
      (TwoTermHomotopy.isQuasiIso (TwoTermHomotopy.symm hφ'g) hg₁)
  have hfB' : (asIso (DerivedCategory.Q.map (coneMap g₁))).symm.hom ≫
      DerivedCategory.Q.map (coneMap φ') = (nlConeIso A' B' P').symm.hom :=
    inv_comp_coneMap_eq φ' nlc g₁ hφ'g
  let W := spanTwoTerm T₁ T'
  let c : ChainMap (T₁.baseChange B'') T₃ :=
    cancelBaseChangeChainMap (D := B') (C := B'') P.toExtension
  let cinv : ChainMap T₃ (T₁.baseChange B'') :=
    { f₁ := (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B''
        P.toExtension.Cotangent).symm.toLinearMap
      f₀ := (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B''
        P.toExtension.CotangentSpace).symm.toLinearMap
      comm := LinearMap.ext fun z =>
        cancelBaseChange_symm_baseChange_comm P.toExtension.cotangentComplex z }
  have hc_cinv : c.comp cinv = ChainMap.id T₃ :=
    ChainMap.ext (LinearEquiv.comp_symm _) (LinearEquiv.comp_symm _)
  have hcinv_c : cinv.comp c = ChainMap.id (T₁.baseChange B'') :=
    ChainMap.ext (LinearEquiv.symm_comp _) (LinearEquiv.symm_comp _)
  let φ'' : ChainMap T₃ T₂ := (φ'.baseChange B'').comp cinv
  have hcomp₂ : g₂.comp (φ'.baseChange B'') =
      (nlExtensionBaseChangeMap
        ((P'.defaultHom (Algebra.Generators.self A'' B'')).toExtensionHom.comp
        (P.defaultHom P').toExtensionHom)).comp c :=
    nlBaseChangeMap_comp_baseChange_nlGensMap P P'
  have hg₂φ'' : Homotopic (g₂.comp φ'') g₃ := by
    have e : g₂.comp φ'' = nlExtensionBaseChangeMap
        ((P'.defaultHom (Algebra.Generators.self A'' B'')).toExtensionHom.comp
          (P.defaultHom P').toExtensionHom) := by
      have h1 := congrArg ChainMap.f₁ hcomp₂
      have h0 := congrArg ChainMap.f₀ hcomp₂
      have k1 := congrArg ChainMap.f₁ hc_cinv
      have k0 := congrArg ChainMap.f₀ hc_cinv
      refine ChainMap.ext ?_ ?_
      · exact (congrArg (fun m => m ∘ₗ cinv.f₁) h1).trans
          ((LinearMap.comp_assoc _ _ _).trans (congrArg (fun m => _ ∘ₗ m) k1))
      · exact (congrArg (fun m => m ∘ₗ cinv.f₀) h0).trans
          ((LinearMap.comp_assoc _ _ _).trans (congrArg (fun m => _ ∘ₗ m) k0))
    rw [e]
    exact homotopic_nlExtensionBaseChangeMap _ _
  have hφ'bc : IsQuasiIso (φ'.baseChange B'') := by
    refine TwoTermHomotopy.isQuasiIso_of_comp hg₂ ?_
    refine (congrArg IsQuasiIso hcomp₂).mpr ?_
    refine TwoTermHomotopy.isQuasiIso_comp (isQuasiIso_cancelBaseChangeChainMap _) ?_
    exact TwoTermHomotopy.isQuasiIso (homotopic_nlExtensionBaseChangeMap (T := B'') _ _) hg₃
  have hcinvq : IsQuasiIso cinv :=
    isQuasiIso_of_bijective _ (LinearEquiv.bijective _) (LinearEquiv.bijective _)
  have hφ'' : IsQuasiIso φ'' := TwoTermHomotopy.isQuasiIso_comp hcinvq hφ'bc
  have hfB'' : (asIso (DerivedCategory.Q.map (coneMap g₃))).symm.hom ≫
      DerivedCategory.Q.map (coneMap φ'') =
        (asIso (DerivedCategory.Q.map (coneMap g₂))).symm.hom :=
    inv_comp_coneMap_eq φ'' g₂ g₃ hg₂φ''
  let W'' := W.baseChange B''
  let p₃ : ChainMap W'' T₃ := c.comp ((spanP T₁ T').baseChange B'')
  let q₂ : ChainMap W'' T₂ := (spanQ φ').baseChange B''
  have hp₃s : (toHom p₃).IsDegreewiseSurjective := bcSpanP_surjective P.toExtension
  have hp₃q : IsQuasiIso p₃ := bcSpanP_isQuasiIso P.toExtension
  have hq₂s : (toHom q₂).IsDegreewiseSurjective := bcSpanQ_surjective hφ'
  have hq₂q : IsQuasiIso q₂ := bcSpanQ_isQuasiIso hφ'bc
  have hh'' : Homotopic q₂ (φ''.comp p₃) := by
    have : φ''.comp p₃ = (φ'.baseChange B'').comp ((spanP T₁ T').baseChange B'') := by
      refine ChainMap.ext (LinearMap.ext fun z => ?_) (LinearMap.ext fun z => ?_)
      · show (φ'.baseChange B'').f₁ (cinv.f₁ (c.f₁ (((spanP T₁ T').baseChange B'').f₁ z))) =
          (φ'.baseChange B'').f₁ (((spanP T₁ T').baseChange B'').f₁ z)
        exact congrArg _ (LinearEquiv.symm_apply_apply _ _)
      · show (φ'.baseChange B'').f₀ (cinv.f₀ (c.f₀ (((spanP T₁ T').baseChange B'').f₀ z))) =
          (φ'.baseChange B'').f₀ (((spanP T₁ T').baseChange B'').f₀ z)
        exact congrArg _ (LinearEquiv.symm_apply_apply _ _)
    rw [this]
    exact homotopic_bcSpanQ
  have key : ∀ x : detNL A B, detNLBaseChangeOfIsIso hq₃ (1 ⊗ₜ x) =
      detNLBaseChangeOfIsIso hq₂ (1 ⊗ₜ detNLBaseChangeOfIsIso hq₁ (1 ⊗ₜ x)) := by
    intro x
    let φP := detNLEquiv P x
    let u := TwoTermComplex.lineBaseChange B' P.toExtension.cotangentComplex (1 ⊗ₜ φP)
    let z := detNLBaseChangeOfIsIso hq₁ (1 ⊗ₜ x)
    have hz := coneLine_detNLBaseChangeOfIsIso hq₁ x
    let ζ := detNLBaseChangeOfIsIso hq₃ (1 ⊗ₜ x)
    have hζ := coneLine_detNLBaseChangeOfIsIso hq₃ x
    have hR := coneLine_detNLBaseChangeOfIsIso hq₂ z
    have hP' : detNLEquiv P' z = coneLine T' (TwoTermDeterminant.detPresentationIso
        (nlObject A' B') (nlPresentation A' B' P') z) := rfl
    have hB' := coneLine_detPresentationIso_span (nlObject A' B') T₁ T' W
      (asIso (DerivedCategory.Q.map (coneMap g₁))).symm (nlConeIso A' B' P').symm φ' hfB'
      (spanP T₁ T') (spanQ φ') (spanP_surjective T₁ T') (isQuasiIso_spanP T₁ T')
      (spanQ_surjective hφ') (isQuasiIso_spanQ hφ') (homotopic_spanQ φ') z
    have : Module.Finite B'' W''.X₁ := inferInstanceAs (Module.Finite B'' (B'' ⊗[B'] W.X₁))
    have : Module.Projective B'' W''.X₁ :=
      inferInstanceAs (Module.Projective B'' (B'' ⊗[B'] W.X₁))
    have : Module.Finite B'' W''.X₀ := inferInstanceAs (Module.Finite B'' (B'' ⊗[B'] W.X₀))
    have : Module.Projective B'' W''.X₀ :=
      inferInstanceAs (Module.Projective B'' (B'' ⊗[B'] W.X₀))
    have hB'' := coneLine_detPresentationIso_span (nlObject A'' B'') T₃ T₂ W''
      (asIso (DerivedCategory.Q.map (coneMap g₃))).symm
      (asIso (DerivedCategory.Q.map (coneMap g₂))).symm φ'' hfB''
      p₃ q₂ hp₃s hp₃q hq₂s hq₂q hh'' ζ
    let Ep := TwoTermComplex.detEquiv (toHom (spanP T₁ T')) (spanP_surjective T₁ T')
      (toHom_isQuasiIso (isQuasiIso_spanP T₁ T'))
    let Eq := TwoTermComplex.detEquiv (toHom (spanQ φ')) (spanQ_surjective hφ')
      (toHom_isQuasiIso (isQuasiIso_spanQ hφ'))
    let Ep₃ := TwoTermComplex.detEquiv (toHom p₃) hp₃s (toHom_isQuasiIso hp₃q)
    let Eq₂ := TwoTermComplex.detEquiv (toHom q₂) hq₂s (toHom_isQuasiIso hq₂q)
    have hB'₁ : coneLine T' (TwoTermDeterminant.detPresentationIso (nlObject A' B')
        (nlPresentation A' B' P') z) = Eq (Ep.symm (coneLine T₁
          (TwoTermDeterminant.detPresentationIso (nlObject A' B')
            (nlBaseChangePresentation hq₁) z))) := hB'
    have hB''₁ : coneLine T₂ (TwoTermDeterminant.detPresentationIso (nlObject A'' B'')
        (nlBaseChangePresentation hq₂) ζ) = Eq₂ (Ep₃.symm (coneLine T₃
          (TwoTermDeterminant.detPresentationIso (nlObject A'' B'')
            (nlBaseChangePresentation hq₃) ζ))) := hB''
    have hfin : Eq₂ (Ep₃.symm (TwoTermComplex.lineBaseChange B''
        P.toExtension.cotangentComplex (1 ⊗ₜ φP))) =
        TwoTermComplex.lineBaseChange B'' P'.toExtension.cotangentComplex
          (1 ⊗ₜ Eq (Ep.symm u)) :=
      detEquiv_span_baseChange (Q := P.toExtension) hφ' hφ'bc φP
    have h : coneLine T₂ (TwoTermDeterminant.detPresentationIso (nlObject A'' B'')
        (nlBaseChangePresentation hq₂) ζ) = coneLine T₂ (TwoTermDeterminant.detPresentationIso
          (nlObject A'' B'') (nlBaseChangePresentation hq₂)
            (detNLBaseChangeOfIsIso hq₂ (1 ⊗ₜ z))) :=
      hB''₁.trans ((congrArg (fun t => Eq₂ (Ep₃.symm t)) hζ).trans (hfin.trans
        ((congrArg (fun t => TwoTermComplex.lineBaseChange B'' P'.toExtension.cotangentComplex
          (1 ⊗ₜ t)) (hP'.trans (hB'₁.trans (congrArg (fun t => Eq (Ep.symm t)) hz)))).symm.trans
            hR.symm)))
    exact (TwoTermDeterminant.detPresentationIso (nlObject A'' B'')
      (nlBaseChangePresentation hq₂)).injective ((coneLine T₂).injective h)
  exact baseChange_linearEquiv_ext _ _ key

end CompMain

/-! ### Composition and identity for chart base changes -/

/-- For chart base changes `D₁ : (A → B) ⟶ (A' → B')`, `D₂ : (A' → B') ⟶ (A'' → B'')` and
`D₃ : (A → B) ⟶ (A'' → B'')` of syntomic algebras, compatible through `A → A' → A''` and
`B → B' → B''`, the base change of `det(NL_{B/A})` along `D₃` is the composite of those along `D₁`
and `D₂`. -/
theorem detNLBaseChange_comp {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A A']
    [Algebra A' B'] [Algebra B B'] [Algebra A' A''] [Algebra B' B''] [Algebra A A'']
    [Algebra B B''] [Algebra A'' B''] [IsScalarTower A A' A''] [IsScalarTower B B' B'']
    [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A'' B'']
    (D₁ : ChartBaseChange A B A' B') (D₂ : ChartBaseChange A' B' A'' B'')
    (D₃ : ChartBaseChange A B A'' B'') :
    detNLBaseChange D₃ =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B'' (detNL A B)).symm ≪≫ₗ
        (detNLBaseChange D₁).baseChange B' B'' _ _ ≪≫ₗ detNLBaseChange D₂ := by
  let : Algebra A B' := ((algebraMap B B').comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun a =>
    D₁.algebraMap_comm a
  let : Algebra A' B'' := ((algebraMap B' B'').comp (algebraMap A' B')).toAlgebra
  have : IsScalarTower A' B' B'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A' A'' B'' := IsScalarTower.of_algebraMap_eq fun a =>
    D₂.algebraMap_comm a
  let : Algebra A B'' := ((algebraMap B B'').comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B B'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A A'' B'' := IsScalarTower.of_algebraMap_eq fun a =>
    D₃.algebraMap_comm a
  have hg₁ := isQuasiIso_nlBaseChangeMap D₁ (gens A B)
  have hg₂ := isQuasiIso_nlBaseChangeMap D₂ (gens A' B')
  have hg₃ := isQuasiIso_nlBaseChangeMap D₃ (gens A B)
  exact detNLBaseChangeOfIsIso_comp hg₁ hg₂ hg₃
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_coneMap hg₁))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_coneMap hg₂))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_coneMap hg₃))

/-- For a chart base change from `A → B` to itself, the base change of `det(NL_{B/A})` is
`B ⊗_B det(NL_{B/A}) ≅ det(NL_{B/A})`. -/
theorem detNLBaseChange_refl {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] (D : ChartBaseChange A B A B) :
    detNLBaseChange D = TensorProduct.lid B (detNL A B) := by
  have h := detNLBaseChange_comp D D D
  have key : ∀ x : detNL A B, detNLBaseChange D (1 ⊗ₜ x) = x := by
    intro x
    have h1 := LinearEquiv.congr_fun h (1 ⊗ₜ x)
    simp only [LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul] at h1
    have h2 := (detNLBaseChange D).injective h1
    have h3 := congrArg (TensorProduct.lid B (detNL A B)) h2
    simpa using h3.symm
  refine baseChange_linearEquiv_ext _ _ fun x => ?_
  simpa using key x

end Stacks.TateMap
