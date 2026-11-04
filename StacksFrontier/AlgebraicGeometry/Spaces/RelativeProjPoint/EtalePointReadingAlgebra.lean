module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjF1Generated
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingInvertibleQuotients

/-!
# The readings of an étale scheme point form a morphism of graded algebras

Let `f : T ⟶ X` be an étale scheme point of the base of Situation 0849. A Zariski open `W` of `T`
is an étale chart `W ⟶ T ⟶ X` of `X`, and
`AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading` identifies the sections of the
restriction `f^*𝒜_n` over `W` with the sections of `𝒜_n` over that chart (Stacks 03LW). This file
proves that these readings are compatible with all the structure: they are additive, semilinear
along the identification of the functions on `W` with the functions on the chart, multiplicative
and unital, and natural in the open `W`.

## Main definitions

* `AlgebraicGeometry.Space.etalePointPieceReading`: the identification of Stacks 03LW on the
  sections of the pullback `f^*A` of a graded algebra over an étale chart of `T`.
* `AlgebraicGeometry.Space.etalePointChartRingHom`: the identification of the functions on `W`
  with the functions on the chart `W ⟶ T ⟶ X`; it is bijective
  (`AlgebraicGeometry.Space.bijective_etalePointChartRingHom`).

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading_add`,
  `etalePointReading_zero`, `etalePointReading_smul`: the readings are semilinear.
* `AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading_mul` and
  `etalePointReading_one`: the readings are multiplicative and unital.
* `AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading_restrict`: the readings are
  natural in the open.

## Implementation notes

Multiplicativity is `AlgebraicGeometry.Space.modulePullbackIso_hom_gradedPull_mul`, the
multiplicativity of Stacks 03LW on the pullback of graded algebras along an étale representable
morphism (a scheme point of an algebraic space is representable), followed by the multiplicativity
of the re-presentation of `𝒜` with sections in the universe of the site. The unit is then forced: a
multiplicative surjection carries a unit to a unit (`AlgebraicGeometry.Space.map_one_of_map_mul`).

All the facts are first proved for an arbitrary graded algebra `A` on `X`, where nothing has to
be unfolded, and only then instantiated. The reading of the situation is defined through the
situation rebuilt with `RelativeProjSituation.mk`, and the comparison of the two is made once, in
`etalePointReading_eq`; the remaining statements never compare the two presentations.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

/-- A multiplicative map between two families of graded pieces, onto in degree `0`, carries a
left unit of the source to a right unit of the target. -/
theorem map_one_of_map_mul {P Q : ℤ → Type*} (mulP : ∀ i j, P i → P j → P (i + j))
    (mulQ : ∀ i j, Q i → Q j → Q (i + j)) (oneP : P 0) (oneQ : Q 0) (φ : ∀ n, P n → Q n)
    (hP : ∀ a : P 0, HEq (mulP 0 0 oneP a) a) (hQ : ∀ b : Q 0, HEq (mulQ 0 0 b oneQ) b)
    (hφ : ∀ a b : P 0, φ (0 + 0) (mulP 0 0 a b) = mulQ 0 0 (φ 0 a) (φ 0 b))
    (hs : ∃ a : P 0, φ 0 a = oneQ) : φ 0 oneP = oneQ := by
  obtain ⟨a, ha⟩ := hs
  have hcongr : ∀ {i j : ℤ} (_ : i = j) {x : P i} {y : P j}, HEq x y → HEq (φ i x) (φ j y) := by
    intro i j hij x y hxy
    subst hij
    rw [eq_of_heq hxy]
  refine eq_of_heq (((hQ (φ 0 oneP)).symm.trans ?_).trans (heq_of_eq ha))
  rw [← ha, ← hφ]
  exact hcongr (add_zero 0) (hP a)

section Abstract

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X.1)
  (hf : IsEtale B S hS (pointHom (X := X) f).hom)

/-- The identification of Stacks 03LW for the étale scheme point `f`, on the sections of the
pulled-back graded algebra `f^*A` over an étale chart `V` of `T`: they are sections of `A` over
the composite chart `V ⟶ T ⟶ X`. -/
def etalePointPieceReading (n : ℤ) (V : SmallEtale B S hS (yoneda.obj T))
    (x : ((etalePointAlgebra A T f).piece n).val.obj (op V)) :
    (A.piece n).val.obj (op ((smallEtalePostcomp B S hS (pointHom f) hf).obj V)) :=
  ((modulePullbackIsoEtaleModulePullback B S hS (pointHom f) hf).hom.app (A.piece n)).val.app
    (op V) x

/-- The reading of the sections of `f^*A` over `V` is additive. -/
theorem etalePointPieceReading_add (n : ℤ) (V : SmallEtale B S hS (yoneda.obj T))
    (x y : ((etalePointAlgebra A T f).piece n).val.obj (op V)) :
    etalePointPieceReading A f hf n V (x + y) =
      etalePointPieceReading A f hf n V x + etalePointPieceReading A f hf n V y :=
  map_add (((modulePullbackIsoEtaleModulePullback B S hS (pointHom f) hf).hom.app
    (A.piece n)).val.app (op V)).hom x y

/-- The reading of the sections of `f^*A` over `V` is linear over the ring of the chart, which is
the ring of the composite chart. -/
theorem etalePointPieceReading_smul (n : ℤ) (V : SmallEtale B S hS (yoneda.obj T))
    (r : (structureRingSheaf B S hS (yonedaSpace B S hS T)).obj.obj (op V))
    (x : ((etalePointAlgebra A T f).piece n).val.obj (op V)) :
    etalePointPieceReading A f hf n V (r • x) =
      (show (structureRingSheaf B S hS X).obj.obj
          (op ((smallEtalePostcomp B S hS (pointHom f) hf).obj V)) from r) •
        etalePointPieceReading A f hf n V x :=
  (((modulePullbackIsoEtaleModulePullback B S hS (pointHom f) hf).hom.app
    (A.piece n)).val.app (op V)).hom.map_smul r x

/-- **The reading of the sections of `f^*A` over `V` is multiplicative**: Stacks 03LW carries the
multiplication of the pullback of graded algebras to that of `A` over the composite chart. -/
theorem etalePointPieceReading_mul (i j : ℤ) (V : SmallEtale B S hS (yoneda.obj T))
    (x : ((etalePointAlgebra A T f).piece i).val.obj (op V))
    (y : ((etalePointAlgebra A T f).piece j).val.obj (op V)) :
    etalePointPieceReading A f hf (i + j) V (((etalePointAlgebra A T f).mul i j).app (op V) x y) =
      (A.mul i j).app (op ((smallEtalePostcomp B S hS (pointHom f) hf).obj V))
        (etalePointPieceReading A f hf i V x) (etalePointPieceReading A f hf j V y) := by
  have h := modulePullbackIso_hom_gradedPull_mul A (pointHom f) hf
    ((Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X.1)).1
      X.2.diagonal_representable f) V i j x y
  refine Eq.trans ?_ (Eq.trans h ?_)
  · rfl
  · rfl

/-- The reading of the sections of `f^*A` over `V` is onto. -/
theorem etalePointPieceReading_surjective (n : ℤ) (V : SmallEtale B S hS (yoneda.obj T)) :
    Function.Surjective (etalePointPieceReading A f hf n V) := fun z =>
  ⟨((modulePullbackIsoEtaleModulePullback B S hS (pointHom f) hf).inv.app (A.piece n)).val.app
      (op V) z,
    congrArg (fun k => k.val.app (op V) z)
      ((modulePullbackIsoEtaleModulePullback B S hS (pointHom f) hf).app (A.piece n)).inv_hom_id⟩

/-- **The reading of the sections of `f^*A` over `V` is unital.** -/
theorem etalePointPieceReading_one (V : SmallEtale B S hS (yoneda.obj T)) :
    etalePointPieceReading A f hf 0 V ((etalePointAlgebra A T f).one.eval (op V)) =
      A.one.eval (op ((smallEtalePostcomp B S hS (pointHom f) hf).obj V)) :=
  map_one_of_map_mul (P := fun n => ((etalePointAlgebra A T f).piece n).val.obj (op V))
    (Q := fun n => (A.piece n).val.obj (op ((smallEtalePostcomp B S hS (pointHom f) hf).obj V)))
    (fun i j a b => ((etalePointAlgebra A T f).mul i j).app (op V) a b)
    (fun i j a b => (A.mul i j).app (op ((smallEtalePostcomp B S hS (pointHom f) hf).obj V)) a b)
    ((etalePointAlgebra A T f).one.eval (op V))
    (A.one.eval (op ((smallEtalePostcomp B S hS (pointHom f) hf).obj V)))
    (fun n x => etalePointPieceReading A f hf n V x)
    (fun a => (etalePointAlgebra A T f).one_mul 0 (op V) a)
    (fun b => A.mul_one 0 _ b)
    (fun a b => etalePointPieceReading_mul A f hf 0 0 V a b)
    (etalePointPieceReading_surjective A f hf 0 V _)

/-- The reading of the sections of `f^*A` is natural in the chart. -/
theorem etalePointPieceReading_naturality (n : ℤ) {V V' : SmallEtale B S hS (yoneda.obj T)}
    (g : V' ⟶ V) (x : ((etalePointAlgebra A T f).piece n).val.obj (op V)) :
    etalePointPieceReading A f hf n V' (((etalePointAlgebra A T f).piece n).val.map g.op x) =
      (A.piece n).val.map ((smallEtalePostcomp B S hS (pointHom f) hf).map g).op
        (etalePointPieceReading A f hf n V x) := by
  refine Eq.trans ?_ (Eq.trans (PresheafOfModules.naturality_apply
    ((modulePullbackIsoEtaleModulePullback B S hS (pointHom f) hf).hom.app (A.piece n)).val
    g.op x) ?_)
  · rfl
  · rfl

/-- **The identification of the structure rings of a Zariski open `W` of an étale scheme point
and of the chart `W ⟶ T ⟶ X`**: a function on `W`, read as a function on the étale chart `W` of
the represented space, which is a function on the composite chart. -/
def etalePointChartRingHom (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    Γ((BigFppfOver.toScheme B S hS).obj T, W) →+*
      (structureRingSheaf B S hS X).obj.obj
        (op ((smallEtalePostcomp B S hS (pointHom f) hf).obj
          ((selfOpensFunctor B S hS T).obj W))) :=
  ((selfOpensStructureMap B S hS T).hom.app (op W)).hom

/-- The identification of the structure rings is bijective. -/
theorem bijective_etalePointChartRingHom (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    Function.Bijective (etalePointChartRingHom f hf W) :=
  bijective_selfOpensStructureMap_hom_app T W

end Abstract

namespace RelativeProjSituation

section Mk

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜 : SheafOfModules.GradedAlgebra.{u, u, u, u + 1} (structureRingSheaf B S hS X)}
  (hc : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜.piece i).val.obj U)
    (b : (𝒜.piece j).val.obj U), HEq ((𝒜.mul i j).app U a b) ((𝒜.mul j i).app U b a))
  (hn : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜.piece n))
  (hq : ∀ n : ℤ, (𝒜.piece n).IsQuasicoherentOnSite)
  (hk : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜.piece n).val.obj U) B.cutoff)
  {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X.1)
  (hf : IsEtale B S hS (pointHom (X := X) f).hom)

local notation "𝔰" => RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hk

/-- The identification of the sections of `f^*𝒜_n` over `W` with those of `𝒜_n` over the chart,
for a situation presented by `RelativeProjSituation.mk`, through `etalePointPieceReading`. -/
private theorem etalePointSectionsEquiv_eq (n : ℤ) (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (a : Γ(((𝔰).relativeProjPoints.algebra T f).piece n, W)) :
    (𝔰).etalePointSectionsEquiv f hf n W a =
      SheafOfModules.GradedAlgebra.smallPieceEquiv 𝒜 n (op ((𝔰).etalePointChart f hf W))
        (etalePointPieceReading (𝔰).shrink.algebra f hf n ((selfOpensFunctor B S hS T).obj W) a) :=
  ((etalePointSectionsEquiv_apply hc hn hq hk f hf n W a).trans
    (rfl : _ = SheafOfModules.GradedAlgebra.smallPieceEquiv 𝒜 n (op ((𝔰).etalePointChart f hf W))
      (etalePointPieceReading (𝔰).smallAlgebra f hf n ((selfOpensFunctor B S hS T).obj W) a))).trans
    (congrArg (SheafOfModules.GradedAlgebra.smallPieceEquiv 𝒜 n (op ((𝔰).etalePointChart f hf W)))
      (rfl : etalePointPieceReading (𝔰).smallAlgebra f hf n ((selfOpensFunctor B S hS T).obj W) a =
        etalePointPieceReading (𝔰).shrink.algebra f hf n ((selfOpensFunctor B S hS T).obj W) a))

end Mk

section Situation

variable (s : RelativeProjSituation.{u, u}) {T : BigFppfOver s.site s.base s.containsBase}
  (f : yoneda.obj T ⟶ s.space.1)
  (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)

/-- **The reading on the chart, unfolded**: the identification of Stacks 03LW followed by the
comparison of the re-presentation of `𝒜` with `𝒜`. -/
theorem etalePointReading_eq (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointReading f hf n W a =
      SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n (op (s.etalePointChart f hf W))
        (etalePointPieceReading s.shrink.algebra f hf n
          ((selfOpensFunctor s.site s.base s.containsBase T).obj W) a) := by
  have e := etalePointSectionsEquiv_eq s.mul_comm s.negative_isZero s.isQuasicoherent
    s.sections_hasCardinalLT f hf n W a
  refine Eq.trans ?_ (Eq.trans e ?_)
  · rfl
  · rfl

/-- **The reading on the chart is additive.** -/
theorem etalePointReading_add (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a b : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointReading f hf n W (a + b) =
      s.etalePointReading f hf n W a + s.etalePointReading f hf n W b := by
  simp only [etalePointReading_eq]
  erw [etalePointPieceReading_add, map_add]

/-- The reading on the chart carries `0` to `0`. -/
theorem etalePointReading_zero (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
    s.etalePointReading f hf n W 0 = 0 := by
  have h := s.etalePointReading_add f hf n W 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- **The reading on the chart is semilinear** along the identification
`AlgebraicGeometry.Space.etalePointChartRingHom` of the functions on `W` with the functions on
the chart `W ⟶ T ⟶ X`, which is bijective (`bijective_etalePointChartRingHom`). -/
theorem etalePointReading_smul (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (c : Γ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T, W))
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointReading f hf n W (c • a) =
      etalePointChartRingHom f hf W c • s.etalePointReading f hf n W a := by
  simp only [etalePointReading_eq]
  erw [etalePointPieceReading_smul, map_smul]
  rfl

/-- **The reading on the chart is multiplicative**: the product of `f^*𝒜` over `W` is read as the
product of `𝒜` over the chart `W ⟶ T ⟶ X`. -/
theorem etalePointReading_mul (i j : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece i, W))
    (b : Γ((s.relativeProjPoints.algebra T f).piece j, W)) :
    s.etalePointReading f hf (i + j) W (((s.relativeProjPoints.algebra T f).mul i j).app W a b) =
      (s.algebra.mul i j).app (op (s.etalePointChart f hf W))
        (s.etalePointReading f hf i W a) (s.etalePointReading f hf j W b) :=
  (s.etalePointReading_eq f hf (i + j) W _).trans
    ((congrArg (SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra (i + j)
        (op (s.etalePointChart f hf W)))
      (etalePointPieceReading_mul s.shrink.algebra f hf i j
        ((selfOpensFunctor s.site s.base s.containsBase T).obj W) a b)).trans
    ((SheafOfModules.GradedAlgebra.smallPresentation_equiv_mul_app s.algebra i j
      (op (s.etalePointChart f hf W)) _ _).trans
      (congrArg₂ (fun x y => (s.algebra.mul i j).app _ x y)
        (s.etalePointReading_eq f hf i W a).symm (s.etalePointReading_eq f hf j W b).symm)))

/-- **The reading on the chart is unital**: it is multiplicative and onto, so it carries the unit
of `f^*𝒜` over `W` to a unit of `𝒜` over the chart. -/
theorem etalePointReading_one
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
    s.etalePointReading f hf 0 W ((s.relativeProjPoints.algebra T f).one W) =
      s.algebra.one.eval (op (s.etalePointChart f hf W)) :=
  map_one_of_map_mul (P := fun n => Γ((s.relativeProjPoints.algebra T f).piece n, W))
    (Q := fun n => (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W)))
    (fun i j a b => ((s.relativeProjPoints.algebra T f).mul i j).app W a b)
    (fun i j a b => (s.algebra.mul i j).app (op (s.etalePointChart f hf W)) a b)
    ((s.relativeProjPoints.algebra T f).one W) (s.algebra.one.eval (op (s.etalePointChart f hf W)))
    (fun n a => s.etalePointReading f hf n W a)
    (fun a => (s.relativeProjPoints.algebra T f).one_mul 0 W a)
    (fun b => s.algebra.mul_one 0 _ b)
    (fun a b => s.etalePointReading_mul f hf 0 0 W a b)
    ((s.etalePointReading f hf 0 W).surjective _)

private theorem etalePointPieceReading_relativeProjPoints_restrict (n : ℤ)
    {W' W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens} (h : W' ≤ W)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    etalePointPieceReading s.shrink.algebra f hf n
        ((selfOpensFunctor s.site s.base s.containsBase T).obj W')
        (((s.relativeProjPoints.algebra T f).piece n).presheaf.map (homOfLE h).op a) =
      etalePointPieceReading s.shrink.algebra f hf n
        ((selfOpensFunctor s.site s.base s.containsBase T).obj W')
        (((etalePointAlgebra s.shrink.algebra T f).piece n).val.map
          ((selfOpensFunctor s.site s.base s.containsBase T).map (homOfLE h)).op a) :=
  rfl

private theorem smallPieceEquiv_shrink_naturality (n : ℤ)
    {W' W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens} (h : W' ≤ W)
    (y : (s.shrink.algebra.piece n).val.obj (op (s.etalePointChart f hf W))) :
    SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n (op (s.etalePointChart f hf W'))
        ((s.shrink.algebra.piece n).val.map
          ((smallEtalePostcomp s.site s.base s.containsBase (pointHom f) hf).map
            ((selfOpensFunctor s.site s.base s.containsBase T).map (homOfLE h))).op y) =
      (s.algebra.piece n).val.map
          ((smallEtalePostcomp s.site s.base s.containsBase (pointHom f) hf).map
            ((selfOpensFunctor s.site s.base s.containsBase T).map (homOfLE h))).op
        (SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n
            (op (s.etalePointChart f hf W)) y) :=
  SheafOfModules.GradedAlgebra.smallPieceEquiv_naturality s.algebra n _ y

/-- **The reading on the chart is natural in the open**: restricting a section of `f^*𝒜_n` from `W`
to `W' ≤ W` is restricting its reading along the inclusion of charts. -/
theorem etalePointReading_restrict (n : ℤ)
    {W' W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens} (h : W' ≤ W)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointReading f hf n W'
        (((s.relativeProjPoints.algebra T f).piece n).presheaf.map (homOfLE h).op a) =
      (s.algebra.piece n).val.map
        ((smallEtalePostcomp s.site s.base s.containsBase (pointHom f) hf).map
          ((selfOpensFunctor s.site s.base s.containsBase T).map (homOfLE h))).op
        (s.etalePointReading f hf n W a) :=
  (s.etalePointReading_eq f hf n W' _).trans
    ((congrArg (SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n
        (op (s.etalePointChart f hf W')))
      ((s.etalePointPieceReading_relativeProjPoints_restrict f hf n h a).trans
        (etalePointPieceReading_naturality s.shrink.algebra f hf n
          ((selfOpensFunctor s.site s.base s.containsBase T).map (homOfLE h)) a))).trans
    ((s.smallPieceEquiv_shrink_naturality f hf n h _).trans
    (congrArg ((s.algebra.piece n).val.map
        ((smallEtalePostcomp s.site s.base s.containsBase (pointHom f) hf).map
          ((selfOpensFunctor s.site s.base s.containsBase T).map (homOfLE h))).op)
      (s.etalePointReading_eq f hf n W a).symm)))

end Situation

end RelativeProjSituation

end AlgebraicGeometry.Space
