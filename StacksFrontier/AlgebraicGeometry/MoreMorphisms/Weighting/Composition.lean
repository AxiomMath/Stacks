module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.PurelyInseparableDecomposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FiniteChart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.PurelyInseparablePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import StacksCore.Tactic.StacksAttribute

/-!
# Composing weightings

The pointwise product of a weighting of `f : X ⟶ Y` and the pullback along `f` of a weighting of
`g : Y ⟶ Z` is a weighting of the composite.

## Main results

* `AlgebraicGeometry.IsWeighting.mul_comp`: the product of a weighting of `f` and the pullback of
  a weighting of `g` is a weighting of `f ≫ g`.

## Implementation notes

The weighted fibre sum of a composite of two finite morphisms factors as an iterated sum, because
the separable degree of a residue-field extension is multiplicative in a tower and the
residue-field extensions of a locally quasi-finite morphism are finite, hence algebraic. For a
finite open chart of `f ≫ g` whose distinguished fibre is a single point with purely inseparable
residue-field extension, this factorization identifies the chart's weighted fibre sum, near the
distinguished point, with a constant times the weighted fibre sum of a chart of `g`; both
factors are locally constant by the two weighting hypotheses. A general finite open chart is
decomposed into such pieces together with a residual piece whose distinguished fibre is empty.

## References

* [Stacks Project, Tag 0GK9](https://stacks.math.columbia.edu/tag/0GK9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Ideal IsLocalRing Localization

universe u

namespace AlgebraicGeometry

open scoped Topology

/-- The residue-field extension at a point of a locally quasi-finite morphism is algebraic, for
any algebra structure equal to the one induced by the morphism. -/
private theorem residueFieldMap_isAlgebraic {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (x : X)
    [alg : Algebra (Y.residueField (f x)) (X.residueField x)]
    (halg : alg = (f.residueFieldMap x).hom.toAlgebra) :
    Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) := by
  have h₀ : @Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) _ _
      ((f.residueFieldMap x).hom.toAlgebra) := by
    let : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    have : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
      module_finite_residueFieldMap f x
    exact Algebra.IsAlgebraic.of_finite _ _
  exact halg.symm ▸ h₀

private theorem finSepDegree_tower_of_isAlgebraic
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic E K] :
    Field.finSepDegree F K = Field.finSepDegree F E * Field.finSepDegree E K :=
  (Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F E K).symm
private theorem finSepDegree_residueField_tower {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] (x : X)
    [algFK : Algebra (Z.residueField (g (f x))) (X.residueField x)]
    [algFE : Algebra (Z.residueField (g (f x))) (Y.residueField (f x))]
    [algEK : Algebra (Y.residueField (f x)) (X.residueField x)]
    (hFK : algFK = ((f ≫ g).residueFieldMap x).hom.toAlgebra)
    (hFE : algFE = (g.residueFieldMap (f x)).hom.toAlgebra)
    (hEK : algEK = (f.residueFieldMap x).hom.toAlgebra) :
    Field.finSepDegree (Z.residueField (g (f x))) (X.residueField x) =
      Field.finSepDegree (Z.residueField (g (f x))) (Y.residueField (f x)) *
        Field.finSepDegree (Y.residueField (f x)) (X.residueField x) := by
  let F := Z.residueField (g (f x))
  let E := Y.residueField (f x)
  let K := X.residueField x
  have hFK' : @Algebra.algebraMap F K _ _ algFK = ((f ≫ g).residueFieldMap x).hom := by
    rw [hFK]
    rfl
  have hFE' : @Algebra.algebraMap F E _ _ algFE = (g.residueFieldMap (f x)).hom := by
    rw [hFE]
    rfl
  have hEK' : @Algebra.algebraMap E K _ _ algEK = (f.residueFieldMap x).hom := by
    rw [hEK]
    rfl
  have hmap : algebraMap F K = (algebraMap E K).comp (algebraMap F E) := by
    apply RingHom.ext
    intro a
    change (@Algebra.algebraMap F K _ _ algFK) a =
      (@Algebra.algebraMap E K _ _ algEK) ((@Algebra.algebraMap F E _ _ algFE) a)
    rw [hFK', hEK', hFE']
    have h := congrArg CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.residueFieldMap_comp f g x)
    simp [RingHom.comp_apply]
  have : IsScalarTower F E K := IsScalarTower.of_algebraMap_eq' hmap
  have : Algebra.IsAlgebraic E K :=
    residueFieldMap_isAlgebraic f x (alg := algEK) hEK
  simpa [F, E, K] using finSepDegree_tower_of_isAlgebraic (F := F) (E := E) (K := K)
private theorem finsum_sigma_eq_iterated {α : Type*} (β : α → Type*)
    [Finite α] [∀ a, Finite (β a)] (F : Sigma β → ℤ) :
    (∑ᶠ p : Sigma β, F p) = ∑ᶠ a, ∑ᶠ b, F ⟨a, b⟩ := by
  let _ : Fintype α := Fintype.ofFinite α
  let _ : ∀ a, Fintype (β a) := fun a ↦ Fintype.ofFinite (β a)
  rw [finsum_eq_sum_of_fintype, Fintype.sum_sigma, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun a _ ↦ (finsum_eq_sum_of_fintype _).symm

private theorem weightedFiberSum_comp_finite
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [LocallyOfFiniteType a] [LocallyQuasiFinite a]
    [LocallyOfFiniteType b] [LocallyQuasiFinite b]
    (ha : ∀ y, (a ⁻¹' {y}).Finite) (hb : ∀ z, (b ⁻¹' {z}).Finite)
    (w₁ : X → ℤ) (w₂ : Y → ℤ) (z : Z) :
    separableDegreeWeightedFiberSum (a ≫ b) (fun x ↦ w₁ x * w₂ (a x)) z =
      ∑ᶠ y : {y : Y // y ∈ b ⁻¹' {z}},
        (letI := (b.residueFieldMap y.1).hom.toAlgebra
         w₂ y.1 * (Field.finSepDegree (Z.residueField (b y.1)) (Y.residueField y.1) : ℤ)) *
          (∑ᶠ x : {x : X // x ∈ a ⁻¹' {y.1}},
            let _i := (a.residueFieldMap x.1).hom.toAlgebra
            w₁ x.1 * (Field.finSepDegree (Y.residueField (a x.1)) (X.residueField x.1) : ℤ)) := by
  classical
  let B := {y : Y // y ∈ b ⁻¹' {z}}
  let A : B → Type u := fun y ↦ {x : X // x ∈ a ⁻¹' {y.1}}
  have : Finite B := (hb z).to_subtype
  have : Fintype B := Fintype.ofFinite B
  have (y : B) : Finite (A y) := (ha y.1).to_subtype
  have (y : B) : Fintype (A y) := Fintype.ofFinite (A y)
  let C := {x : X // (a ≫ b) x = z}
  let e : (Σ y : B, A y) ≃ C :=
    { toFun := fun p ↦ ⟨p.2.1, by
        have hxy : a p.2.1 = p.1.1 := by
          simpa only [Set.mem_preimage, Set.mem_singleton_iff] using p.2.2
        have hyz : b p.1.1 = z := by
          simpa only [Set.mem_preimage, Set.mem_singleton_iff] using p.1.2
        change (a ≫ b) p.2.1 = z
        rw [Scheme.Hom.comp_apply, hxy, hyz]⟩
      invFun := fun x ↦ ⟨⟨a x.1, by
          have hx := x.2
          have hx' : b (a x.1) = z := by simpa only [Scheme.Hom.comp_apply] using hx
          simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx'⟩, ⟨x.1, by simp⟩⟩
      left_inv := by
        rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
        dsimp
        have hxy : y = a x := by
          simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx.symm
        subst y
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }
  have : Fintype C := Fintype.ofEquiv (Σ y : B, A y) e
  let termC : C → ℤ := fun x ↦ by
    let _i := ((a ≫ b).residueFieldMap x.1).hom.toAlgebra
    exact w₁ x.1 * w₂ (a x.1) *
      (Field.finSepDegree (Z.residueField ((a ≫ b) x.1)) (X.residueField x.1) : ℤ)
  let termSigma : (Σ y : B, A y) → ℤ := fun p ↦ by
    let _i := (b.residueFieldMap p.1.1).hom.toAlgebra
    exact (w₂ p.1.1 *
      (Field.finSepDegree (Z.residueField (b p.1.1)) (Y.residueField p.1.1) : ℤ)) *
      (let _i := (a.residueFieldMap p.2.1).hom.toAlgebra
       w₁ p.2.1 *
        (Field.finSepDegree (Y.residueField (a p.2.1)) (X.residueField p.2.1) : ℤ))
  have hterms (p : Σ y : B, A y) : termSigma p = termC (e p) := by
    rcases p with ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
    have hyx : y = a x := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx.symm
    subst y
    have hdegree := finSepDegree_residueField_tower a b x
      (algFK := ((a ≫ b).residueFieldMap x).hom.toAlgebra)
      (algFE := (b.residueFieldMap (a x)).hom.toAlgebra)
      (algEK := (a.residueFieldMap x).hom.toAlgebra) rfl rfl rfl
    let _i := ((a ≫ b).residueFieldMap x).hom.toAlgebra
    let _i := (b.residueFieldMap (a x)).hom.toAlgebra
    let _i := (a.residueFieldMap x).hom.toAlgebra
    change (w₂ (a x) *
        (Field.finSepDegree (Z.residueField (b (a x)))
          (Y.residueField (a x)) : ℤ)) *
        (w₁ x * (Field.finSepDegree (Y.residueField (a x))
          (X.residueField x) : ℤ)) =
      w₁ x * w₂ (a x) *
        (Field.finSepDegree (Z.residueField ((a ≫ b) x))
          (X.residueField x) : ℤ)
    have hdegree' :
        Field.finSepDegree (Z.residueField ((a ≫ b) x)) (X.residueField x) =
          Field.finSepDegree (Z.residueField (b (a x))) (Y.residueField (a x)) *
            Field.finSepDegree (Y.residueField (a x)) (X.residueField x) := hdegree
    rw [hdegree']
    push_cast
    ring
  have hsum := Fintype.sum_equiv e termSigma termC hterms
  rw [separableDegreeWeightedFiberSum_eq_finsum_fiber, finsum_eq_sum_of_fintype termC, ← hsum,
    ← finsum_eq_sum_of_fintype termSigma, finsum_sigma_eq_iterated A termSigma]
  apply finsum_congr
  intro y
  let _i := (b.residueFieldMap y.1).hom.toAlgebra
  let c := w₂ y.1 * (Field.finSepDegree (Z.residueField (b y.1))
    (Y.residueField y.1) : ℤ)
  change (∑ᶠ x : A y, c * (let _i := (a.residueFieldMap x.1).hom.toAlgebra;
      w₁ x.1 * (Field.finSepDegree (Y.residueField (a x.1))
        (X.residueField x.1) : ℤ))) = _
  exact (mul_finsum _ c).symm
private theorem locallyConstant_weightedFiberSum_comp_branch
    {X Y Z E D B : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (e : E ⟶ Z)
    (d : D ⟶ B) (b : B ⟶ E) (h : D ⟶ X) (k : B ⟶ Y)
    (commD : h ≫ f = d ≫ k) (commB : k ≫ g = b ≫ e)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    [Etale k] [Etale e] [IsFinite d] [IsFinite b]
    [IsOpenImmersion (pullback.lift h d commD)]
    [IsOpenImmersion (pullback.lift k b commB)]
    {w_f : X → ℤ} {w_g : Y → ℤ}
    (hwf : IsWeighting f w_f)
    (hwg : IsWeighting g w_g)
    {t : E} {y : B}
    (hfiber : ∀ z, b z = t → z = y) :
    ∃ W : E.Opens, t ∈ W ∧
      IsLocallyConstant
        (separableDegreeWeightedFiberSum (d ≫ b)
          (fun x ↦ w_f (h x) * w_g (k (d x))) ∘ W.ι) := by
  classical
  let A : B → ℤ :=
    separableDegreeWeightedFiberSum d (w_f ∘ h)
  let G : E → ℤ :=
    separableDegreeWeightedFiberSum b (w_g ∘ k)
  let F : E → ℤ :=
    separableDegreeWeightedFiberSum (d ≫ b)
      (fun x ↦ w_f (h x) * w_g (k (d x)))
  have hA : IsLocallyConstant A :=
    hwf.isLocallyConstant h d k commD inferInstance inferInstance inferInstance
  have hG : IsLocallyConstant G :=
    hwg.isLocallyConstant k b e commB inferInstance inferInstance inferInstance
  obtain ⟨O, hO, hyO, hconst⟩ :=
    ((IsLocallyConstant.iff_exists_open A).mp hA) y
  let O' : B.Opens := ⟨O, hO⟩
  obtain ⟨W, htW, hpre⟩ := exists_isOpen_preimage_subset_of_isFinite
    b (𝟙 B) t O' (by
      intro z hzt
      have hzy := hfiber z hzt
      subst z
      simpa [O'] using hyO)
  have hfactor (v : E) (hv : v ∈ W) : F v = A y * G v := by
    change separableDegreeWeightedFiberSum (d ≫ b)
      (fun x ↦ (w_f ∘ h) x * (w_g ∘ k) (d x)) v =
        A y * separableDegreeWeightedFiberSum b (w_g ∘ k) v
    rw [weightedFiberSum_comp_finite d b
      (fun z ↦ d.finite_preimage_singleton z)
      (fun z ↦ b.finite_preimage_singleton z)
      (w_f ∘ h) (w_g ∘ k) v]
    rw [separableDegreeWeightedFiberSum_eq_finsum_preimage b (w_g ∘ k) v, mul_finsum]
    refine finsum_congr fun z ↦ ?_
    let _i := (b.residueFieldMap z.1).hom.toAlgebra
    have hzv : b z.1 = v := z.2
    have hzO : z.1 ∈ O := hpre z.1 (by simpa [hzv] using hv)
    have hAz : A z.1 = A y := hconst z.1 hzO
    have hinner :
        (∑ᶠ x : {x : D // x ∈ d ⁻¹' {z.1}},
          let _i := (d.residueFieldMap x.1).hom.toAlgebra
          (w_f ∘ h) x.1 *
            (Field.finSepDegree (B.residueField (d x.1))
              (D.residueField x.1) : ℤ)) = A z.1 := by
      simpa [A] using
        (separableDegreeWeightedFiberSum_eq_finsum_preimage d (w_f ∘ h) z.1).symm
    rw [hinner, hAz]
    ring
  have hprodW : IsLocallyConstant ((fun v : E ↦ A y * G v) ∘ W.ι) :=
    ((IsLocallyConstant.const (A y)).mul hG).comp_continuous W.ι.continuous
  refine ⟨W, htW, ?_⟩
  have hEq : F ∘ W.ι = (fun v : E ↦ A y * G v) ∘ W.ι := by
    funext v
    exact hfactor (W.ι v) v.property
  exact hEq ▸ hprodW

private theorem locallyConstant_composite_branch_chart
    {X Y Z U V E : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    (h : U ⟶ X) (π : U ⟶ V) (q : V ⟶ Z)
    (comm : h ≫ (f ≫ g) = π ≫ q)
    [Etale q] [IsFinite π]
    [IsOpenImmersion (pullback.lift h π comm)]
    (qE : E ⟶ V) [Etale qE]
    (D : (pullback π qE).Opens) (a : D) (v : E)
    [IsFinite (D.ι ≫ pullback.snd π qE)]
    (hv : (D.ι ≫ pullback.snd π qE) a = v)
    (hfiber : (D.ι ≫ pullback.snd π qE) ⁻¹' {v} = {a})
    (hpure : (((E.residueFieldCongr hv).inv ≫
      (D.ι ≫ pullback.snd π qE).residueFieldMap a).hom).IsPurelyInseparable)
    {wf : X → ℤ} {wg : Y → ℤ}
    (hwf : IsWeighting f wf)
    (hwg : IsWeighting g wg) :
    ∃ (N : EtaleNeighborhood E v)
      (W : N.scheme.Opens), N.point ∈ W ∧
      IsLocallyConstant
        ((separableDegreeWeightedFiberSum
          (D.ι ≫ pullback.snd π qE)
        (fun x ↦ wf (h (pullback.fst π qE (D.ι x))) *
            wg (f (h (pullback.fst π qE (D.ι x))))) ∘ N.toBase) ∘ W.ι) := by
  let F := f ≫ g
  let eOld := qE ≫ q
  let h0 : D.toScheme ⟶ X := D.ι ≫ pullback.fst π qE ≫ h
  let p0 : D.toScheme ⟶ E := D.ι ≫ pullback.snd π qE
  have comm0 : h0 ≫ F = p0 ≫ eOld := by
    dsimp [h0, p0, F, eOld]
    calc
      D.ι ≫ pullback.fst π qE ≫ h ≫ (f ≫ g) =
          D.ι ≫ pullback.fst π qE ≫ (h ≫ (f ≫ g)) := by simp
      _ = D.ι ≫ pullback.fst π qE ≫ (π ≫ q) := by rw [comm]
      _ = D.ι ≫ (pullback.fst π qE ≫ π) ≫ q := by simp [Category.assoc]
      _ = D.ι ≫ (pullback.snd π qE ≫ qE) ≫ q := by rw [pullback.condition]
      _ = D.ι ≫ pullback.snd π qE ≫ qE ≫ q := by simp [Category.assoc]
  let c0 : D.toScheme ⟶ pullback F eOld :=
    pullback.lift h0 p0 comm0
  let cU := baseChangedChartMap F q qE h π comm
  have hC0 : c0 = D.ι ≫ cU := by
    apply pullback.hom_ext
    · calc
        c0 ≫ pullback.fst F eOld = h0 := by dsimp [c0]; exact pullback.lift_fst _ _ _
        _ = D.ι ≫ pullback.fst π qE ≫ h := rfl
        _ = D.ι ≫ (cU ≫ pullback.fst F eOld) := by
          dsimp [cU]
          rw [baseChangedChartMap_fst]
        _ = (D.ι ≫ cU) ≫ pullback.fst F eOld := by simp [Category.assoc]
    · calc
        c0 ≫ pullback.snd F eOld = p0 := by dsimp [c0]; exact pullback.lift_snd _ _ _
        _ = D.ι ≫ pullback.snd π qE := rfl
        _ = D.ι ≫ (cU ≫ pullback.snd F eOld) := by
          dsimp [cU]
          rw [baseChangedChartMap_snd]
        _ = (D.ι ≫ cU) ≫ pullback.snd F eOld := by simp [Category.assoc]
  have : IsOpenImmersion c0 := by
    rw [hC0]
    have : IsOpenImmersion cU := baseChangedChartMap_isOpenImmersion F q qE h π comm
    infer_instance
  let Q := pullback g eOld
  let gE : Q ⟶ E := pullback.snd g eOld
  have : LocallyOfFiniteType gE := inferInstance
  have : LocallyQuasiFinite gE := inferInstance
  have commQ : h0 ≫ f ≫ g = p0 ≫ eOld := by
    simpa only [F, Category.assoc] using comm0
  let aD : D.toScheme := ⟨a.1, a.2⟩
  let m : D.toScheme ⟶ Q := pullback.lift (h0 ≫ f) p0 (by
    simpa only [Category.assoc] using commQ)
  have hyE : gE (m aD) = v := by
    have hma : gE (m aD) = p0 aD := by
      change (pullback.snd g eOld) (m aD) = p0 aD
      have hh := pullback.lift_snd (h0 ≫ f) p0 (by
        simpa only [Category.assoc] using commQ)
      exact congrArg (fun φ : D.toScheme ⟶ E => φ aD) hh
    exact hma.trans hv
  obtain ⟨N₀, mN, GN, aN, hdata, hcover⟩ :=
    exists_finite_opens_chart_at_point gE (m aD)
  let r0 := N₀.toBase
  let T0 := pullback p0 r0
  let pT0 := pullback.snd p0 r0
  have hmE : m ≫ gE = p0 := by
    dsimp [m, gE]
    exact pullback.lift_snd _ _ _
  have commT0 :
          (pullback.fst p0 r0 ≫ m) ≫ gE = pT0 ≫ r0 := by
    rw [Category.assoc, hmE]
    exact pullback.condition
  let qT0 : T0 ⟶ pullback gE r0 :=
    pullback.lift (pullback.fst p0 r0 ≫ m) pT0 commT0
  have hqT0fstHom : qT0 ≫ pullback.fst gE r0 = pullback.fst p0 r0 ≫ m := by
    dsimp [qT0]
    exact pullback.lift_fst _ _ _
  have hqT0sndHom : qT0 ≫ pullback.snd gE r0 = pT0 := by
    dsimp [qT0]
    exact pullback.lift_snd _ _ _
  have hNpoint : r0 N₀.point = v := N₀.map_point.trans hyE
  obtain ⟨aT, haT, htT⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := p0) (g := r0) aD N₀.point (hv.trans hNpoint.symm)
  have hTunique : ∀ z : T0, pT0 z = N₀.point → z = aT := by
    intro z hz
    exact Scheme.Pullback.eq_of_snd_eq_of_isPurelyInseparable
      p0 a v hv hfiber hpure r0 N₀.point hNpoint hz htT
  have hqT0fst : pullback.fst gE r0 (qT0 aT) = m aD := by
    change (qT0 ≫ pullback.fst gE r0) aT = m aD
    simp only [hqT0fstHom, Scheme.Hom.comp_apply, haT]
  have hqT0snd : pullback.snd gE r0 (qT0 aT) = N₀.point := by
    change (qT0 ≫ pullback.snd gE r0) aT = N₀.point
    simpa only [hqT0sndHom, Scheme.Hom.comp_apply, htT]
  obtain ⟨j, hj⟩ := hcover (qT0 aT) hqT0snd hqT0fst
  let G := GN j
  let aG := aN j
  let hG : G.toScheme ⟶ pullback gE r0 := G.ι
  let bG : G.toScheme ⟶ N₀.scheme := G.ι ≫ pullback.snd gE r0
  let kG : G.toScheme ⟶ Y :=
    G.ι ≫ pullback.fst gE r0 ≫ pullback.fst g eOld
  have commG0 :
      (G.ι ≫ pullback.fst gE r0) ≫ gE = bG ≫ r0 := by
    calc
      (G.ι ≫ pullback.fst gE r0) ≫ gE =
          G.ι ≫ (pullback.fst gE r0 ≫ gE) := by simp only [Category.assoc]
      _ = G.ι ≫ (pullback.snd gE r0 ≫ r0) := by rw [pullback.condition]
      _ = bG ≫ r0 := by simp [bG, Category.assoc]
  have commG :
      (G.ι ≫ pullback.fst gE r0 ≫ pullback.fst g eOld) ≫ g =
        bG ≫ r0 ≫ eOld := by
    calc
      (G.ι ≫ pullback.fst gE r0 ≫ pullback.fst g eOld) ≫ g =
          G.ι ≫ pullback.fst gE r0 ≫ (pullback.fst g eOld ≫ g) := by
            simp only [Category.assoc]
      _ = G.ι ≫ pullback.fst gE r0 ≫ (pullback.snd g eOld ≫ eOld) := by
            rw [pullback.condition]
      _ = G.ι ≫ (pullback.fst gE r0 ≫ gE) ≫ eOld := by
            change G.ι ≫ (pullback.fst gE r0 ≫ pullback.snd g eOld) ≫ eOld = _
            rfl
      _ = G.ι ≫ (pullback.snd gE r0 ≫ r0) ≫ eOld := by
            rw [pullback.condition]
      _ = bG ≫ r0 ≫ eOld := by simp [bG, Category.assoc]
  obtain ⟨hfiniteG, hfiberG, hxG, ⟨hpointG, hpureG⟩⟩ := hdata j
  have hliftG : pullback.lift (G.ι ≫ pullback.fst gE r0) bG commG0 = G.ι := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]
  have : IsOpenImmersion
      (pullback.lift (G.ι ≫ pullback.fst gE r0) bG commG0) := by
    rw [hliftG]
    infer_instance
  have hTintoG : ∀ z : T0, pT0 z = N₀.point → qT0 z ∈ G := by
    intro z hz
    have hza : z = aT := hTunique z hz
    subst z
    change qT0 aT ∈ G
    rw [← hj]
    exact aG.property
  obtain ⟨W0, hW0, hfactor⟩ :=
    exists_isOpen_preimage_subset_of_isFinite pT0 qT0 N₀.point G hTintoG
  let r1 : W0.toScheme ⟶ E := W0.ι ≫ r0
  let T1 := pullback p0 r1
  let pT1 : T1 ⟶ W0.toScheme := pullback.snd p0 r1
  let uT : T1 ⟶ T0 := pullback.lift (pullback.fst p0 r1)
    (pT1 ≫ W0.ι) (by
      calc
        pullback.fst p0 r1 ≫ p0 = pT1 ≫ r1 := pullback.condition
        _ = pT1 ≫ W0.ι ≫ r0 := by simp [r1])
  have huTbase : uT ≫ pT0 = pT1 ≫ W0.ι := by
    dsimp [uT, pT0, pT1]
    exact pullback.lift_snd _ _ _
  have huTG : ∀ z : T1, qT0 (uT z) ∈ G := by
    intro z
    have hzbase : pT0 (uT z) = W0.ι (pT1 z) :=
      congrArg (fun l : T1 ⟶ N₀.scheme => l z) huTbase
    apply hfactor (uT z)
    rw [hzbase]
    exact (pT1 z).property
  have hrangeG : Set.range (uT ≫ qT0) ⊆ Set.range G.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨qT0 (uT z), huTG z⟩, rfl⟩
  let aGmap : T1 ⟶ G.toScheme :=
    IsOpenImmersion.lift G.ι (uT ≫ qT0) hrangeG
  have haGmap : aGmap ≫ G.ι = uT ≫ qT0 :=
    IsOpenImmersion.lift_fac G.ι (uT ≫ qT0) hrangeG
  let Tchart := pullback bG W0.ι
  let B1 := Tchart
  let b1 : B1 ⟶ W0.toScheme := pullback.snd bG W0.ι
  let d1 : T1 ⟶ B1 := pullback.lift aGmap pT1 (by
    calc
      aGmap ≫ bG = (aGmap ≫ G.ι) ≫ pullback.snd gE r0 := by rfl
      _ = (uT ≫ qT0) ≫ pullback.snd gE r0 := by rw [haGmap]
      _ = uT ≫ pT0 := by
        calc
          (uT ≫ qT0) ≫ pullback.snd gE r0 =
              uT ≫ (qT0 ≫ pullback.snd gE r0) := Category.assoc _ _ _
          _ = uT ≫ pT0 := congrArg (fun l : T0 ⟶ N₀.scheme => uT ≫ l) hqT0sndHom
      _ = pT1 ≫ W0.ι := huTbase
    )
  have hd1b1 : d1 ≫ b1 = pT1 := by
    dsimp [d1, b1]
    exact pullback.lift_snd _ _ _
  let h1 : T1 ⟶ X := pullback.fst p0 r1 ≫ h0
  let k1 : B1 ⟶ Y := pullback.fst bG W0.ι ≫ kG
  let e1 : W0.toScheme ⟶ Z := r1 ≫ eOld
  have commB1 : k1 ≫ g = b1 ≫ e1 := by
    change (pullback.fst bG W0.ι ≫ kG) ≫ g =
      pullback.snd bG W0.ι ≫ (W0.ι ≫ r0 ≫ eOld)
    calc
      (pullback.fst bG W0.ι ≫ kG) ≫ g =
          pullback.fst bG W0.ι ≫ (kG ≫ g) := by simp only [Category.assoc]
      _ = pullback.fst bG W0.ι ≫ (bG ≫ r0 ≫ eOld) := by rw [commG]
      _ = (pullback.fst bG W0.ι ≫ bG) ≫ r0 ≫ eOld := by
            simp only [Category.assoc]
      _ = (pullback.snd bG W0.ι ≫ W0.ι) ≫ r0 ≫ eOld := by
            rw [pullback.condition]
      _ = pullback.snd bG W0.ι ≫ (W0.ι ≫ r0 ≫ eOld) := by
            simp only [Category.assoc]
  let iB1 := baseChangedChartMap gE r0 W0.ι
    (G.ι ≫ pullback.fst gE r0) bG commG0
  have : IsOpenImmersion iB1 :=
    baseChangedChartMap_isOpenImmersion gE r0 W0.ι
      (G.ι ≫ pullback.fst gE r0) bG commG0
  let Q1 := pullback g e1
  let isoQ := pullbackLeftPullbackSndIso g eOld r1
  let iB : B1 ⟶ Q1 := iB1 ≫ isoQ.hom
  have : IsOpenImmersion iB := by
    dsimp [iB]
    infer_instance
  have hchartB : pullback.lift k1 b1 commB1 = iB := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      have hiB1fst : iB1 ≫ pullback.fst gE (W0.ι ≫ r0) =
          pullback.fst bG W0.ι ≫ G.ι ≫ pullback.fst gE r0 := by
        dsimp [iB1]
        rw [baseChangedChartMap_fst]
      dsimp [iB, isoQ]
      rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
        ← Category.assoc, hiB1fst]
      rfl
    · rw [pullback.lift_snd]
      have hiB1snd : iB1 ≫ pullback.snd gE (W0.ι ≫ r0) =
          pullback.snd bG W0.ι := by
        dsimp [iB1]
        rw [baseChangedChartMap_snd]
      dsimp [iB, isoQ, b1]
      rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
        hiB1snd]
  let C1 := pullback F e1
  let qC : C1 ⟶ Q1 := pullback.lift
    (pullback.fst F e1 ≫ f) (pullback.snd F e1) (by
      calc
        (pullback.fst F e1 ≫ f) ≫ g = pullback.fst F e1 ≫ F := by
          simp [F, Category.assoc]
        _ = pullback.snd F e1 ≫ e1 := pullback.condition)
  let cT := baseChangedChartMap F eOld r1 h0 p0 comm0
  have : IsOpenImmersion cT := baseChangedChartMap_isOpenImmersion F eOld r1 h0 p0 comm0
  let comm1 : h1 ≫ F = pT1 ≫ e1 := by
    dsimp [h1, e1, F, r1]
    calc
      (pullback.fst p0 (W0.ι ≫ r0) ≫ h0) ≫ (f ≫ g) =
          pullback.fst p0 (W0.ι ≫ r0) ≫ (h0 ≫ (f ≫ g)) := by simp [Category.assoc]
      _ = pullback.fst p0 (W0.ι ≫ r0) ≫ (p0 ≫ eOld) := by rw [comm0]
      _ = (pullback.fst p0 (W0.ι ≫ r0) ≫ p0) ≫ eOld := by simp [Category.assoc]
      _ = (pT1 ≫ W0.ι ≫ r0) ≫ eOld := by rw [pullback.condition]
      _ = pT1 ≫ (W0.ι ≫ r0 ≫ eOld) := by simp [Category.assoc]
  have hcTf : cT ≫ pullback.fst F e1 = h1 := by
    dsimp [cT, h1]
    rw [baseChangedChartMap_fst]
  have hcTs : cT ≫ pullback.snd F e1 = pT1 := by
    dsimp [cT, pT1]
    rw [baseChangedChartMap_snd]
  have : IsFinite pT1 := by dsimp [pT1]; infer_instance
  have : IsFinite b1 := by
    dsimp [b1]
    infer_instance
  have : IsFinite (d1 ≫ b1) := by rw [hd1b1]; infer_instance
  have : IsFinite d1 := by
    have : IsSeparated b1 := inferInstance
    exact IsFinite.of_comp d1 b1
  have : Etale e1 := by
    dsimp [e1, r1]
    infer_instance
  have : Etale k1 := by
    dsimp [k1, kG]
    infer_instance
  have hbase : k1 = iB ≫ pullback.fst g e1 := by
    have := congrArg (fun l : B1 ⟶ pullback g e1 => l ≫ pullback.fst g e1) hchartB
    simpa only [pullback.lift_fst] using this
  let eSmall := pullback.congrHom (f₁ := f) (f₂ := f)
    (g₁ := k1) (g₂ := iB ≫ pullback.fst g e1) rfl hbase
  let cSmall0 : pullback f (iB ≫ pullback.fst g e1) ⟶
      pullback f (pullback.fst g e1) :=
    (pullbackLeftPullbackSndIso f (pullback.fst g e1) iB).inv ≫
      pullback.fst (pullback.snd f (pullback.fst g e1)) iB
  let cSmall := eSmall.hom ≫ cSmall0
  have : IsOpenImmersion cSmall := by
    dsimp [cSmall]
    infer_instance
  let isoBig := pullbackRightPullbackFstIso g e1 f
  let jChart : pullback f k1 ⟶ C1 := cSmall ≫ isoBig.hom
  have : IsOpenImmersion jChart := by
    dsimp [jChart]
    infer_instance
  have heSmallF : eSmall.hom ≫ pullback.fst f (iB ≫ pullback.fst g e1) =
      pullback.fst f k1 := by
    dsimp [eSmall]
    simp only [pullback.congrHom_hom, pullback.map, pullback.lift_fst,
      Category.comp_id]
  have heSmallS : eSmall.hom ≫ pullback.snd f (iB ≫ pullback.fst g e1) =
      pullback.snd f k1 := by
    dsimp [eSmall]
    simp only [pullback.congrHom_hom, pullback.map, pullback.lift_snd,
      Category.comp_id]
  have hsmallF : cSmall ≫ pullback.fst f (pullback.fst g e1) =
      pullback.fst f k1 := by
    dsimp [cSmall, cSmall0]
    calc
      eSmall.hom ≫ (pullbackLeftPullbackSndIso f (pullback.fst g e1) iB).inv ≫
          pullback.fst (pullback.snd f (pullback.fst g e1)) iB ≫
          pullback.fst f (pullback.fst g e1) =
        eSmall.hom ≫ ((pullbackLeftPullbackSndIso f (pullback.fst g e1) iB).inv ≫
          pullback.fst (pullback.snd f (pullback.fst g e1)) iB ≫
          pullback.fst f (pullback.fst g e1)) := rfl
      _ = eSmall.hom ≫ pullback.fst f (iB ≫ pullback.fst g e1) :=
        congrArg (fun m : pullback f (iB ≫ pullback.fst g e1) ⟶ X ↦ eSmall.hom ≫ m)
          (pullbackLeftPullbackSndIso_inv_fst f (pullback.fst g e1) iB)
      _ = pullback.fst f k1 := heSmallF
  have hsmallS : cSmall ≫ pullback.snd f (pullback.fst g e1) ≫
      pullback.snd g e1 = pullback.snd f k1 ≫ iB ≫ pullback.snd g e1 := by
    dsimp [cSmall, cSmall0]
    calc
      eSmall.hom ≫ (pullbackLeftPullbackSndIso f (pullback.fst g e1) iB).inv ≫
          pullback.fst (pullback.snd f (pullback.fst g e1)) iB ≫
          pullback.snd f (pullback.fst g e1) ≫ pullback.snd g e1 =
        eSmall.hom ≫ ((pullbackLeftPullbackSndIso f (pullback.fst g e1) iB).inv ≫
          pullback.fst (pullback.snd f (pullback.fst g e1)) iB ≫
          pullback.snd f (pullback.fst g e1) ≫ pullback.snd g e1) := rfl
      _ = eSmall.hom ≫ (pullback.snd f (iB ≫ pullback.fst g e1) ≫
            iB ≫ pullback.snd g e1) :=
            congrArg (fun m : pullback f (iB ≫ pullback.fst g e1) ⟶ W0.toScheme
              ↦ eSmall.hom ≫ m)
              (pullbackLeftPullbackSndIso_inv_fst_snd_assoc
                f (pullback.fst g e1) iB (pullback.snd g e1))
      _ = pullback.snd f k1 ≫ iB ≫ pullback.snd g e1 := by
            simpa only [Category.assoc] using
              congrArg (fun m : pullback f k1 ⟶ B1 ↦ m ≫ iB ≫ pullback.snd g e1)
                heSmallS
  have hjChartF : jChart ≫ pullback.fst F e1 = pullback.fst f k1 := by
    dsimp [jChart, isoBig]
    calc
      cSmall ≫ (pullbackRightPullbackFstIso g e1 f).hom ≫ pullback.fst F e1 =
          cSmall ≫ pullback.fst f (pullback.fst g e1) := by
            rw [pullbackRightPullbackFstIso_hom_fst]
      _ = pullback.fst f k1 := hsmallF
  have hiBsnd : iB ≫ pullback.snd g e1 = b1 := by
    have hh := congrArg (fun l : B1 ⟶ pullback g e1 => l ≫ pullback.snd g e1) hchartB
    simpa only [pullback.lift_snd] using hh.symm
  have hjChartS : jChart ≫ pullback.snd F e1 = pullback.snd f k1 ≫ b1 := by
    dsimp [jChart, isoBig]
    calc
          cSmall ≫ (pullbackRightPullbackFstIso g e1 f).hom ≫ pullback.snd F e1 =
          cSmall ≫ (pullback.snd f (pullback.fst g e1) ≫ pullback.snd g e1) :=
            congrArg (fun m : pullback f (pullback.fst g e1) ⟶ W0.toScheme ↦ cSmall ≫ m)
              (pullbackRightPullbackFstIso_hom_snd g e1 f)
      _ = pullback.snd f k1 ≫ iB ≫ pullback.snd g e1 := hsmallS
      _ = pullback.snd f k1 ≫ b1 := by rw [hiBsnd]
  have hqCfst : qC ≫ pullback.fst g e1 = pullback.fst F e1 ≫ f := by
    dsimp [qC]
    exact pullback.lift_fst _ _ _
  have hqCsnd : qC ≫ pullback.snd g e1 = pullback.snd F e1 := by
    dsimp [qC]
    exact pullback.lift_snd _ _ _
  have hd1k1 : d1 ≫ k1 = h1 ≫ f := by
    calc
      d1 ≫ k1 = (d1 ≫ pullback.fst bG W0.ι) ≫ kG := by
        simp only [k1, Category.assoc]
      _ = aGmap ≫ kG := by
        rw [pullback.lift_fst]
      _ = (aGmap ≫ G.ι) ≫ pullback.fst gE r0 ≫ pullback.fst g eOld := by
        rfl
      _ = uT ≫ qT0 ≫ pullback.fst gE r0 ≫ pullback.fst g eOld := by
        rw [haGmap]
        simp only [Category.assoc]
      _ = uT ≫ (pullback.fst p0 r0 ≫ m) ≫ pullback.fst g eOld := by
        calc
          (uT ≫ qT0) ≫ pullback.fst gE r0 ≫ pullback.fst g eOld =
              uT ≫ (qT0 ≫ pullback.fst gE r0) ≫ pullback.fst g eOld := by
                simp only [Category.assoc]
          _ = uT ≫ (pullback.fst p0 r0 ≫ m) ≫ pullback.fst g eOld := by
                rw [hqT0fstHom]
      _ = uT ≫ pullback.fst p0 r0 ≫ (m ≫ pullback.fst g eOld) := by
        simp only [Category.assoc]
      _ = pullback.fst p0 r1 ≫ h0 ≫ f := by
        have huTfst : uT ≫ pullback.fst p0 r0 = pullback.fst p0 r1 := by
          dsimp [uT]
          exact pullback.lift_fst _ _ _
        calc
          uT ≫ (pullback.fst p0 r0 ≫ m) ≫ pullback.fst g eOld =
              uT ≫ pullback.fst p0 r0 ≫ (m ≫ pullback.fst g eOld) := by
                simp only [Category.assoc]
          _ = uT ≫ pullback.fst p0 r0 ≫ (h0 ≫ f) := by
                rw [show m ≫ pullback.fst g eOld = h0 ≫ f by
                  dsimp [m]
                  exact pullback.lift_fst _ _ _]
          _ = pullback.fst p0 r1 ≫ h0 ≫ f :=
                congrArg (fun k : T1 ⟶ D.toScheme ↦ k ≫ h0 ≫ f) huTfst
      _ = h1 ≫ f := by rfl
  let commD : h1 ≫ f = d1 ≫ k1 := hd1k1.symm
  let chartLift : T1 ⟶ pullback f k1 := pullback.lift h1 d1 commD
  have hcompLift : chartLift ≫ jChart = cT := by
    apply pullback.hom_ext
    · calc
        (chartLift ≫ jChart) ≫ pullback.fst F e1 =
            chartLift ≫ (jChart ≫ pullback.fst F e1) := Category.assoc _ _ _
        _ = chartLift ≫ pullback.fst f k1 :=
          congrArg (fun m : pullback f k1 ⟶ X ↦ chartLift ≫ m) hjChartF
        _ = h1 := by dsimp [chartLift]; exact pullback.lift_fst _ _ _
        _ = cT ≫ pullback.fst F e1 := hcTf.symm
    · calc
        (chartLift ≫ jChart) ≫ pullback.snd F e1 =
            chartLift ≫ (jChart ≫ pullback.snd F e1) := Category.assoc _ _ _
        _ = chartLift ≫ (pullback.snd f k1 ≫ b1) :=
          congrArg (fun m : pullback f k1 ⟶ W0.toScheme ↦ chartLift ≫ m) hjChartS
        _ = d1 ≫ b1 :=
          congrArg (fun l : T1 ⟶ B1 ↦ l ≫ b1) (pullback.lift_snd h1 d1 commD)
        _ = pT1 := hd1b1
        _ = cT ≫ pullback.snd F e1 := hcTs.symm
  have : IsOpenImmersion (chartLift ≫ jChart) := by rw [hcompLift]; infer_instance
  have : IsOpenImmersion chartLift := IsOpenImmersion.of_comp _ jChart
  let wpoint : W0 := ⟨N₀.point, hW0⟩
  obtain ⟨aB1, haB1, hbpointB⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := bG) (g := W0.ι) aG wpoint (hpointG.trans (show W0.ι wpoint = N₀.point from rfl).symm)
  have hB1unique : ∀ z : B1, b1 z = wpoint → z = aB1 := by
    intro z hz
    exact Scheme.Pullback.eq_of_snd_eq_of_isPurelyInseparable
      bG aG N₀.point hpointG hfiberG hpureG W0.ι wpoint rfl hz hbpointB
  have : IsFinite bG := hfiniteG
  have : IsOpenImmersion (pullback.lift k1 b1 commB1) := by
    rw [hchartB]
    infer_instance
  obtain ⟨WM, hMW, hLCM⟩ := locallyConstant_weightedFiberSum_comp_branch
    f g e1 d1 b1 h1 k1 commD commB1 hwf hwg
    (t := wpoint) (y := aB1) hB1unique
  let w0 : D.toScheme → ℤ := fun x ↦ wf (h0 x) * wg (f (h0 x))
  let w1 : T1 → ℤ := fun x ↦ wf (h1 x) * wg (k1 (d1 x))
  let F0 : E → ℤ := separableDegreeWeightedFiberSum p0 w0
  let F1 : W0.toScheme → ℤ :=
    separableDegreeWeightedFiberSum (d1 ≫ b1) w1
  have hbaseChange := separableDegreeWeightedFiberSum_comp_of_isPullback
    p0 (pullback.fst p0 r1) pT1 r1 (IsPullback.of_hasPullback p0 r1)
    (fun z ↦ p0.finite_preimage_singleton z) w0
  have hweights : w0 ∘ pullback.fst p0 r1 = w1 := by
    funext x
    have hxk : k1 (d1 x) = f (h1 x) := by
      have hh := congrArg (fun m : T1 ⟶ Y ↦ m x) hd1k1
      simpa only [Scheme.Hom.comp_apply] using hh
    simp only [Function.comp_apply, w0, w1]
    rw [show h0 (pullback.fst p0 r1 x) = h1 x by rfl, ← hxk]
  have hsumChange :
      separableDegreeWeightedFiberSum pT1
          (w0 ∘ pullback.fst p0 r1) = F1 := by
    funext y
    rw [← hd1b1]
    change separableDegreeWeightedFiberSum (d1 ≫ b1)
        (w0 ∘ pullback.fst p0 r1) y =
      separableDegreeWeightedFiberSum (d1 ≫ b1) w1 y
    exact congrArg (fun ww : T1 → ℤ ↦
      separableDegreeWeightedFiberSum (d1 ≫ b1) ww y) hweights
  have hsumAt (y : W0.toScheme) : F0 (r1 y) = F1 y := by
    have hh := congrFun hbaseChange y
    change F0 (r1 y) =
      separableDegreeWeightedFiberSum pT1
        (w0 ∘ pullback.fst p0 r1) y at hh
    rw [hsumChange] at hh
    exact hh
  let N : EtaleNeighborhood E v :=
    { scheme := WM.toScheme
      point := ⟨wpoint, hMW⟩
      toBase := WM.ι ≫ W0.ι ≫ r0
      map_point := by
        change r0 (W0.ι wpoint) = v
        exact hNpoint }
  have hsumEq : F0 ∘ N.toBase = F1 ∘ WM.ι := by
    funext x
    change F0 (r1 (WM.ι x)) = F1 (WM.ι x)
    exact hsumAt (WM.ι x)
  have hLCN : IsLocallyConstant (F0 ∘ N.toBase) := by
    rw [hsumEq]
    exact hLCM
  refine ⟨N, (⊤ : N.scheme.Opens), Set.mem_univ _, ?_⟩
  simpa [F0, p0, w0, h0, Function.comp_assoc] using hLCN.comp_continuous
    ((⊤ : N.scheme.Opens).ι.continuous)
private theorem locallyConstant_composite_branch_eventually
    {X Y Z U V E : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    (h : U ⟶ X) (π : U ⟶ V) (q : V ⟶ Z)
    (comm : h ≫ (f ≫ g) = π ≫ q)
    [Etale q] [IsFinite π]
    [IsOpenImmersion (pullback.lift h π comm)]
    (qE : E ⟶ V) [Etale qE]
    (D : (pullback π qE).Opens) (a : D) (v : E)
    [IsFinite (D.ι ≫ pullback.snd π qE)]
    (hv : (D.ι ≫ pullback.snd π qE) a = v)
    (hfiber : (D.ι ≫ pullback.snd π qE) ⁻¹' {v} = {a})
    (hpure : (((E.residueFieldCongr hv).inv ≫
      (D.ι ≫ pullback.snd π qE).residueFieldMap a).hom).IsPurelyInseparable)
    {wf : X → ℤ} {wg : Y → ℤ}
    (hwf : IsWeighting f wf)
    (hwg : IsWeighting g wg) :
    ∀ᶠ t in 𝓝 v,
      separableDegreeWeightedFiberSum
        (D.ι ≫ pullback.snd π qE)
        (fun x ↦ wf (h (pullback.fst π qE (D.ι x))) *
          wg (f (h (pullback.fst π qE (D.ι x))))) t =
      separableDegreeWeightedFiberSum
        (D.ι ≫ pullback.snd π qE)
        (fun x ↦ wf (h (pullback.fst π qE (D.ι x))) *
          wg (f (h (pullback.fst π qE (D.ι x))))) v := by
  obtain ⟨N, W, hvW, hLC⟩ := locallyConstant_composite_branch_chart
    f g h π q comm qE D a v hv hfiber hpure hwf hwg
  let Npoint : W := ⟨N.point, hvW⟩
  let qW : W.toScheme ⟶ E := W.ι ≫ N.toBase
  let F : E → ℤ := separableDegreeWeightedFiberSum
    (D.ι ≫ pullback.snd π qE)
    (fun x ↦ wf (h (pullback.fst π qE (D.ι x))) *
      wg (f (h (pullback.fst π qE (D.ι x)))))
  have hqpoint : qW Npoint = v := by
    change N.toBase N.point = v
    exact N.map_point
  have : Etale N.toBase := inferInstance
  have : IsOpenImmersion W.ι := inferInstance
  have : IsOpenMap qW := by
    change IsOpenMap (N.toBase ∘ W.ι)
    exact N.toBase.isOpenMap.comp W.ι.isOpenMap
  obtain ⟨O, hOopen, hvO, hconst⟩ :=
    exists_open_neighborhood_eq_of_isLocallyConstant_comp_of_isOpenMap
      qW qW.isOpenMap F hLC Npoint
  filter_upwards [hOopen.mem_nhds (hqpoint ▸ hvO)] with t ht
  have hh := hconst t ht
  rw [hqpoint] at hh
  exact hh
/-- The pointwise product of a weighting of `f` and the pullback of a weighting
of `g` is a weighting of `f ≫ g`. -/
@[stacks 0GK9, sga "4 XVII 6.2.4" "composite"]
theorem IsWeighting.mul_comp {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    {w_f : X → ℤ} {w_g : Y → ℤ}
    (hw_f : IsWeighting f w_f)
    (hw_g : IsWeighting g w_g) :
    IsWeighting (f ≫ g) (fun x ↦ w_f x * w_g (f x)) :=
  by
    rw [isWeighting_iff]
    intro U V h π q comm hq hopen hfinite
    rw [IsLocallyConstant.iff_eventually_eq]
    intro v
    have : IsFinite π := hfinite
    have hfiniteπ : ∀ t, (π ⁻¹' {t}).Finite := fun t ↦ π.finite_preimage_singleton t
    obtain ⟨n, xs, hxs, hxsi⟩ := exists_fin_bijective_isolated_fiber π hfiniteπ v
    have : LocallyOfFiniteType π := inferInstance
    have : IsSeparated π := inferInstance
    obtain ⟨E, m, D, d, hdisj, hcover, hclopen, hspec, hnone⟩ :=
      exists_etaleNeighborhood_purelyInseparable_decomposition
        π n v xs hxs.1 hxsi
    let Ebase : E.scheme ⟶ V := E.toBase
    let P := pullback π Ebase
    let πP : P ⟶ E.scheme := pullback.snd π Ebase
    let wP : P → ℤ := fun z ↦
      w_f (h (pullback.fst π Ebase z)) *
        w_g (f (h (pullback.fst π Ebase z)))
    let F (z : Option (Σ i : Fin n, Fin (m i))) : E.scheme → ℤ :=
      separableDegreeWeightedFiberSum ((D z).ι ≫ πP)
        (wP ∘ (D z).ι)
    have hpieces : ∀ z, ∀ᶠ t in 𝓝 E.point, F z t = F z E.point := by
      intro z
      cases z with
      | none =>
        have hempty := fiber_eq_empty_of_forall_ne
          π v xs hxs.2 E (D none) hnone
        have hzero := separableDegreeWeightedFiberSum_eventually_eq_zero
          πP (D none) (hclopen none).1 E.point hempty (wP ∘ (D none).ι)
        have hzeroAt : F none E.point = 0 := hzero.self_of_nhds
        filter_upwards [hzero] with t ht
        rw [hzeroAt]
        exact ht
      | some z =>
        obtain ⟨i, j⟩ := z
        obtain ⟨hfin, hfiber, _, ⟨hvu, hpure⟩⟩ := hspec i j
        have : IsFinite ((D (some ⟨i, j⟩)).ι ≫ πP) := hfin
        have hevent := locallyConstant_composite_branch_eventually
          f g h π q comm Ebase (D (some ⟨i, j⟩)) (d i j)
          E.point hvu hfiber hpure hw_f hw_g
        filter_upwards [hevent] with t ht
        simpa [F, wP, πP, Function.comp_def] using ht
    have hdisj' : ∀ i j, i ≠ j →
        Disjoint (D i : Set P) (D j : Set P) := by
      intro i j hij
      exact hdisj (Set.mem_univ i) (Set.mem_univ j) hij
    have hcover' : ∀ p : P, ∃ i, p ∈ D i := by
      intro p
      have hp : p ∈ ⋃ i, (D i).1 := by rw [hcover]; trivial
      exact Set.mem_iUnion.mp hp
    have : IsFinite πP := by dsimp [πP]; infer_instance
    have hpartition := separableDegreeWeightedFiberSum_eq_sum_opens
      πP wP D hdisj' hcover' (fun t ↦ πP.finite_preimage_singleton t)
    have hlocalSum := eventuallyEq_sum (s := Finset.univ) (f := F)
      (g := fun z _ ↦ F z E.point) (fun z _ ↦ hpieces z)
    have hlocalP : ∀ᶠ t in 𝓝 E.point,
        separableDegreeWeightedFiberSum πP wP t =
          separableDegreeWeightedFiberSum πP wP E.point := by
      simpa [hpartition, F, Filter.EventuallyEq] using hlocalSum
    have hbase := separableDegreeWeightedFiberSum_comp_of_isPullback
      π (pullback.fst π Ebase) πP Ebase (IsPullback.of_hasPullback π Ebase)
      hfiniteπ (fun x ↦ w_f (h x) * w_g (f (h x)))
    have hlocalComp : ∀ᶠ t in 𝓝 E.point,
        separableDegreeWeightedFiberSum π
            (fun x ↦ w_f (h x) * w_g (f (h x))) (Ebase t) =
          separableDegreeWeightedFiberSum π
            (fun x ↦ w_f (h x) * w_g (f (h x))) (Ebase E.point) := by
      have hpoint (t : E.scheme) :
          separableDegreeWeightedFiberSum π
              (fun x ↦ w_f (h x) * w_g (f (h x))) (Ebase t) =
            separableDegreeWeightedFiberSum πP wP t := by
        simpa [wP, Function.comp_def] using congrFun hbase t
      filter_upwards [hlocalP] with t ht
      calc
        separableDegreeWeightedFiberSum π
            (fun x ↦ w_f (h x) * w_g (f (h x))) (Ebase t) =
            separableDegreeWeightedFiberSum πP wP t := hpoint t
        _ = separableDegreeWeightedFiberSum πP wP E.point := ht
        _ = separableDegreeWeightedFiberSum π
            (fun x ↦ w_f (h x) * w_g (f (h x))) (Ebase E.point) :=
              (hpoint E.point).symm
    have : Etale Ebase := inferInstance
    have hlocalV := eventually_eq_of_openMap_comp Ebase Ebase.isOpenMap
      (separableDegreeWeightedFiberSum π
        (fun x ↦ w_f (h x) * w_g (f (h x)))) E.point hlocalComp
    simpa [Ebase, E.map_point, Function.comp_def] using hlocalV

end AlgebraicGeometry
