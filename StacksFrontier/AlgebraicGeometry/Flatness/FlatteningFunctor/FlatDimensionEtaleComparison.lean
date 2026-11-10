module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatAtAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SpecializationTrdeg
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift

/-!
# Base change and étale charts for the functor of flatness in dimensions at least `n`

In Situation 05MT, let `F_n` be the functor of Stacks 05MU. This file collects the comparisons
of `F_n` with the functors of related situations that the proof of Stacks 05UG uses:

* the situation obtained by a base change `U ⟶ S`, whose functor is `F_n` restricted to schemes
  over `U`;
* the situation obtained by an étale morphism `h : X' ⟶ X`, namely `(h ≫ f, h^* F)`, whose
  functor `F'_n` contains `F_n` (the first assertion of Stacks 05UD);
* a finite family of étale morphisms `hᵢ : Xᵢ ⟶ X` whose images contain the relative assassin
  `Ass_{X/S}(F)`, for which `F_n` is the intersection of the `F^{(i)}_n`, by the flatness
  criterion at associated points of Stacks 05UA (the second assertion of Stacks 05UD).

## Main definitions

* `AlgebraicGeometry.FlatDimensionSituation.baseChange`: the base-changed situation.
* `AlgebraicGeometry.FlatDimensionSituation.etaleChart`: the situation of an étale chart.

## Main results

* `AlgebraicGeometry.isFlatOverInDimensionsGE_iff_of_isPullback`: the condition after base change
  does not depend on the chosen pullback square.
* `AlgebraicGeometry.FlatDimensionSituation.baseChange_isFlat_iff`: the functor of the
  base-changed situation is the restriction of `F_n`.
* `AlgebraicGeometry.FlatDimensionSituation.isFlat_etaleChart_of_isFlat`: `F_n ⊆ F'_n` for an
  étale chart.
* `AlgebraicGeometry.FlatDimensionSituation.isFlat_of_forall_etaleChart`: `F_n` is the
  intersection of the functors of finitely many étale charts whose images contain the relative
  assassin over the image of the test scheme.
* `AlgebraicGeometry.FlatDimensionSituation.isFlat_etaleChart_and_iff_of_relativeAssassin_subset`:
  **Stacks 05UD**.

## References

* [Stacks Project, Tag 05UD](https://stacks.math.columbia.edu/tag/05UD)
* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 06RU](https://stacks.math.columbia.edu/tag/06RU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Flatness in dimensions `≥ m` implies flatness in dimensions `≥ n` for `m ≤ n`. -/
theorem IsFlatOverInDimensionsGE.mono {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {F : X.Modules} [F.IsQuasicoherent] [F.IsFiniteType] {m n : ℕ} (hmn : m ≤ n)
    (h : IsFlatOverInDimensionsGE f F m) : IsFlatOverInDimensionsGE f F n :=
  fun s ↦ (h s).trans_le (by exact_mod_cast hmn)

/-- The pullback of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_pullback_obj' {A B : Scheme.{u}} (v : A ⟶ B) (G : B.Modules)
    [G.IsQuasicoherent] : ((Scheme.Modules.pullback v).obj G).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent A.toRingedSpace B.toRingedSpace
    v.toLRSHom.toShHom G (show G.IsQuasicoherent from inferInstance)

/-- The pullback of a module of finite type is of finite type. -/
theorem isFiniteType_pullback_obj' {A B : Scheme.{u}} (v : A ⟶ B) (G : B.Modules)
    [G.IsFiniteType] : ((Scheme.Modules.pullback v).obj G).IsFiniteType :=
  SheafOfModules.pullback_isFiniteType v.toLRSHom.toShHom G

attribute [local instance] isQuasicoherent_pullback_obj' isFiniteType_pullback_obj'

/-- The condition is unchanged by an isomorphism of modules. -/
theorem isFlatOverInDimensionsGE_iff_of_moduleIso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {F G : X.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    [G.IsQuasicoherent] [G.IsFiniteType] (e : F ≅ G) (n : ℕ) :
    IsFlatOverInDimensionsGE f F n ↔ IsFlatOverInDimensionsGE f G n :=
  ⟨IsFlatOverInDimensionsGE.of_moduleIso f e, IsFlatOverInDimensionsGE.of_moduleIso f e.symm⟩

/-- **Independence of the pullback square.** For two pullback squares of `f` along the same
`g`, flatness in dimensions `≥ n` of the two pulled-back modules over the base are equivalent. -/
theorem isFlatOverInDimensionsGE_iff_of_isPullback {X S T Y₁ Y₂ : Scheme.{u}} {f : X ⟶ S}
    {g : T ⟶ S} {p₁ : Y₁ ⟶ X} {q₁ : Y₁ ⟶ T} {p₂ : Y₂ ⟶ X} {q₂ : Y₂ ⟶ T}
    (h₁ : IsPullback p₁ q₁ f g) (h₂ : IsPullback p₂ q₂ f g) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ) :
    have : LocallyOfFiniteType q₁ := MorphismProperty.of_isPullback h₁ inferInstance
    have : LocallyOfFiniteType q₂ := MorphismProperty.of_isPullback h₂ inferInstance
    IsFlatOverInDimensionsGE q₁ ((Scheme.Modules.pullback p₁).obj F) n ↔
      IsFlatOverInDimensionsGE q₂ ((Scheme.Modules.pullback p₂).obj F) n := by
  intro _ _
  have key : ∀ {Y Y' : Scheme.{u}} {p : Y ⟶ X} {q : Y ⟶ T} {p' : Y' ⟶ X} {q' : Y' ⟶ T}
      (h : IsPullback p q f g) (h' : IsPullback p' q' f g) [LocallyOfFiniteType q]
      [LocallyOfFiniteType q'],
      IsFlatOverInDimensionsGE q ((Scheme.Modules.pullback p).obj F) n →
        IsFlatOverInDimensionsGE q' ((Scheme.Modules.pullback p').obj F) n := by
    intro Y Y' p q p' q' h h' _ _ hY
    let e : Y' ≅ Y := h'.isoIsPullback _ _ h
    have he₁ : e.hom ≫ p = p' := h'.isoIsPullback_hom_fst _ _ h
    have hsq : IsPullback e.hom q' q (𝟙 T) :=
      IsPullback.of_horiz_isIso ⟨by rw [h'.isoIsPullback_hom_snd _ _ h, Category.comp_id]⟩
    let eF : (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback p).obj F) ≅
        (Scheme.Modules.pullback p').obj F :=
      (Scheme.Modules.pullbackComp e.hom p).app F ≪≫ (Scheme.Modules.pullbackCongr he₁).app F
    exact IsFlatOverInDimensionsGE.of_moduleIso q' eF
      (IsFlatOverInDimensionsGE.of_isPullback hsq _ n hY)
  exact ⟨key h₁ h₂, key h₂ h₁⟩

namespace FlatDimensionSituation

/-- The base change of a situation along a morphism `q : U ⟶ S`. -/
abbrev baseChange (D : FlatDimensionSituation.{u}) {U : Scheme.{u}} (q : U ⟶ D.S) :
    FlatDimensionSituation.{u} where
  S := U
  X := pullback D.f q
  f := pullback.snd D.f q
  F := (Scheme.Modules.pullback (pullback.fst D.f q)).obj D.F
  n := D.n

/-- The situation with the dimension bound replaced by `m`. -/
abbrev withN (D : FlatDimensionSituation.{u}) (m : ℕ) : FlatDimensionSituation.{u} :=
  { D with n := m }

/-- The condition after base change can be computed on any pullback square. -/
theorem isFlat_iff_of_isPullback (D : FlatDimensionSituation.{u}) {Y : Scheme.{u}}
    (T : Over D.S) {p : Y ⟶ D.X} {q : Y ⟶ T.left} (h : IsPullback p q D.f T.hom) :
    have : LocallyOfFiniteType q := MorphismProperty.of_isPullback h inferInstance
    D.IsFlatInDimensionsGEAfterBaseChange T ↔
      IsFlatOverInDimensionsGE q ((Scheme.Modules.pullback p).obj D.F) D.n :=
  isFlatOverInDimensionsGE_iff_of_isPullback (IsPullback.of_hasPullback D.f T.hom) h D.F D.n

/-- **Base change.** The functor of the base-changed situation is `F_n` restricted to schemes
over `U`. -/
theorem baseChange_isFlat_iff (D : FlatDimensionSituation.{u}) {U : Scheme.{u}} (q : U ⟶ D.S)
    (V : Over U) :
    (D.baseChange q).IsFlatInDimensionsGEAfterBaseChange V ↔
      D.IsFlatInDimensionsGEAfterBaseChange ((Over.map q).obj V) := by
  let sq := (IsPullback.of_hasPullback (pullback.snd D.f q) V.hom).paste_horiz
    (IsPullback.of_hasPullback D.f q)
  let eF : (Scheme.Modules.pullback (pullback.fst (pullback.snd D.f q) V.hom)).obj
      ((Scheme.Modules.pullback (pullback.fst D.f q)).obj D.F) ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd D.f q) V.hom ≫
        pullback.fst D.f q)).obj D.F := (Scheme.Modules.pullbackComp _ _).app D.F
  exact (isFlatOverInDimensionsGE_iff_of_moduleIso _ eF D.n).trans
    (D.isFlat_iff_of_isPullback ((Over.map q).obj V) sq).symm

/-- At the identity of the base, the condition after base change is the condition itself. -/
theorem isFlat_id_iff (D : FlatDimensionSituation.{u}) :
    D.IsFlatInDimensionsGEAfterBaseChange (Over.mk (𝟙 D.S)) ↔
      IsFlatOverInDimensionsGE D.f D.F D.n := by
  refine (D.isFlat_iff_of_isPullback (Over.mk (𝟙 D.S))
    (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 D.X) D.f D.f (𝟙 D.S))).trans ?_
  let eF : (Scheme.Modules.pullback (𝟙 D.X)).obj D.F ≅ D.F :=
    (Scheme.Modules.pullbackId _).app D.F
  exact isFlatOverInDimensionsGE_iff_of_moduleIso _ eF D.n

/-- Flatness of `F` itself in dimensions `≥ n` makes `F_n` everything. -/
theorem isFlat_of_isFlatOverInDimensionsGE (D : FlatDimensionSituation.{u})
    (h : IsFlatOverInDimensionsGE D.f D.F D.n) (T : Over D.S) :
    D.IsFlatInDimensionsGEAfterBaseChange T :=
  IsFlatOverInDimensionsGE.of_isPullback (IsPullback.of_hasPullback D.f T.hom) D.F D.n h

/-- `F_n ⊆ F_{n+1}`, and more generally `F_m ⊆ F_n` for `m ≤ n`. -/
theorem isFlat_withN_mono (D : FlatDimensionSituation.{u}) {m n : ℕ} (hmn : m ≤ n)
    (T : Over D.S) (h : (D.withN m).IsFlatInDimensionsGEAfterBaseChange T) :
    (D.withN n).IsFlatInDimensionsGEAfterBaseChange T :=
  IsFlatOverInDimensionsGE.mono hmn h

/-- The situation of an étale chart `h : X' ⟶ X`: the morphism `h ≫ f` with the module `h^* F`. -/
abbrev etaleChart (D : FlatDimensionSituation.{u}) {X' : Scheme.{u}} (h : X' ⟶ D.X) [Etale h] :
    FlatDimensionSituation.{u} where
  S := D.S
  X := X'
  f := h ≫ D.f
  F := (Scheme.Modules.pullback h).obj D.F
  n := D.n

end FlatDimensionSituation

/-- Flatness in dimensions `≥ n` depends on the morphism only through its value. -/
theorem isFlatOverInDimensionsGE_congr {X S : Scheme.{u}} {f g : X ⟶ S} (e : f = g)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (n : ℕ) :
    IsFlatOverInDimensionsGE f F n ↔ IsFlatOverInDimensionsGE g F n := by
  subst e
  rfl

/-- Reading a residue field over the residue field of an equal point. -/
private theorem toENat_trdeg_residueFieldCongr {A B : Scheme.{u}} (q : A ⟶ B) (a : A) (b : B)
    (e : q a = b) :
    letI := ((B.residueFieldCongr e).inv ≫ q.residueFieldMap a).hom.toAlgebra
    letI := (q.residueFieldMap a).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (B.residueField b) (A.residueField a)) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg (B.residueField (q a)) (A.residueField a)) :
        WithBot ℕ∞) := by
  subst e
  rfl

/-- The transcendence degree of a residue field over the base is unchanged along an étale
morphism over the base. -/
theorem toENat_trdeg_residueField_eq_of_etale {A B T : Scheme.{u}} (q : A ⟶ B) [Etale q]
    (p : B ⟶ T) (a : A) :
    letI := (p.residueFieldMap (q a)).hom.toAlgebra
    letI := ((q ≫ p).residueFieldMap a).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (T.residueField ((q ≫ p) a)) (A.residueField a)) :
        WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg (T.residueField (p (q a))) (B.residueField (q a))) :
        WithBot ℕ∞) := by
  let K := T.residueField (p (q a))
  let E := B.residueField (q a)
  let L := A.residueField a
  let : Algebra K E := (p.residueFieldMap (q a)).hom.toAlgebra
  let : Algebra E L := (q.residueFieldMap a).hom.toAlgebra
  let : Algebra K L := ((q ≫ p).residueFieldMap a).hom.toAlgebra
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' (by
    change ((q ≫ p).residueFieldMap a).hom = (q.residueFieldMap a).hom.comp
      (p.residueFieldMap (q a)).hom
    rw [Scheme.residueFieldMap_comp]
    rfl)
  have : Module.Finite E L := residueField_finite_of_locallyQuasiFinite q a
  have : Algebra.IsAlgebraic E L := Algebra.IsAlgebraic.of_finite E L
  have h := trdeg_add_eq (R := K) (S := E) (A := L)
  rw [trdeg_eq_zero (R := E) (A := L), add_zero] at h
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) = Cardinal.toENat (Algebra.trdeg K E)
  rw [h]

/-- Flatness over the base at a point is unchanged along an étale morphism over the base, for
the pulled-back module. -/
theorem isFlatOverAt_iff_of_etale {A B T : Scheme.{u}} (q : A ⟶ B) [Etale q] (p : B ⟶ T)
    (G : B.Modules) (a : A) :
    IsFlatOverAt (q ≫ p).toLRSHom.toShHom ((Scheme.Modules.pullback q).obj G) a ↔
      IsFlatOverAt p.toLRSHom.toShHom G (q a) :=
  (isFlatOverAt_iff_modulePullback_isFlatOverAt q p G a (Flat.stalkMap q a)).symm

/-- **Étale localization of the condition.** Let `q : A ⟶ B` be étale and `p : B ⟶ T` locally
of finite type. If `G` is flat over `T` in dimensions `≥ n`, then so is `q^* G` over `T`. -/
theorem IsFlatOverInDimensionsGE.etale_comp {A B T : Scheme.{u}} (q : A ⟶ B) [Etale q]
    (p : B ⟶ T) [LocallyOfFiniteType p] (G : B.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    {n : ℕ} (hG : IsFlatOverInDimensionsGE p G n) :
    IsFlatOverInDimensionsGE (q ≫ p) ((Scheme.Modules.pullback q).obj G) n := by
  rw [isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt] at hG ⊢
  intro a ha
  have hb := hG (q a) fun hflat ↦ ha ((isFlatOverAt_iff_of_etale q p G a).mpr hflat)
  exact (toENat_trdeg_residueField_eq_of_etale q p a).trans_lt hb

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u})

/-- The base change of an étale chart: `X' ×_S T ⟶ X ×_S T`. -/
abbrev chartBaseChange {X' : Scheme.{u}} (h : X' ⟶ D.X) (T : Over D.S) :
    pullback (h ≫ D.f) T.hom ⟶ pullback D.f T.hom :=
  (pullbackRightPullbackFstIso D.f T.hom h).inv ≫ pullback.snd h (pullback.fst D.f T.hom)

/-- The base change of an étale chart commutes with the second projections to `T`. -/
theorem chartBaseChange_snd {X' : Scheme.{u}} (h : X' ⟶ D.X) (T : Over D.S) :
    D.chartBaseChange h T ≫ pullback.snd D.f T.hom = pullback.snd (h ≫ D.f) T.hom := by
  simp [chartBaseChange]

/-- The base change of an étale chart lies over `h` on the first projections. -/
theorem chartBaseChange_fst {X' : Scheme.{u}} (h : X' ⟶ D.X) (T : Over D.S) :
    pullback.fst (h ≫ D.f) T.hom ≫ h = D.chartBaseChange h T ≫ pullback.fst D.f T.hom := by
  simp [chartBaseChange]

/-- The base change of an étale chart is étale. -/
instance {X' : Scheme.{u}} (h : X' ⟶ D.X) [Etale h] (T : Over D.S) :
    Etale (D.chartBaseChange h T) := by
  unfold chartBaseChange
  infer_instance

/-- The base change of the chart module is the pullback of the base-changed module along the
base change of the chart. -/
def chartBaseChangeModuleIso {X' : Scheme.{u}} (h : X' ⟶ D.X) [Etale h] (T : Over D.S) :
    (D.etaleChart h).baseChangeModule T ≅
      (Scheme.Modules.pullback (D.chartBaseChange h T)).obj (D.baseChangeModule T) :=
  (Scheme.Modules.pullbackComp _ h).app D.F ≪≫
    (Scheme.Modules.pullbackCongr (D.chartBaseChange_fst h T)).app D.F ≪≫
      ((Scheme.Modules.pullbackComp _ _).app D.F).symm

/-- The condition for an étale chart, read on the base change of the chart. -/
theorem etaleChart_isFlat_iff {X' : Scheme.{u}} (h : X' ⟶ D.X) [Etale h] (T : Over D.S) :
    (D.etaleChart h).IsFlatInDimensionsGEAfterBaseChange T ↔
      IsFlatOverInDimensionsGE (D.chartBaseChange h T ≫ D.baseChangeMap T)
        ((Scheme.Modules.pullback (D.chartBaseChange h T)).obj (D.baseChangeModule T)) D.n := by
  change IsFlatOverInDimensionsGE (pullback.snd (h ≫ D.f) T.hom) _ D.n ↔ _
  refine (isFlatOverInDimensionsGE_congr (D.chartBaseChange_snd h T).symm _ D.n).trans ?_
  exact isFlatOverInDimensionsGE_iff_of_moduleIso _ (D.chartBaseChangeModuleIso h T) D.n

/-- **The first assertion of Stacks 05UD.** For an étale chart `h : X' ⟶ X`, the functor `F_n`
is contained in the functor `F'_n` of `(h ≫ f, h^* F)`. -/
theorem isFlat_etaleChart_of_isFlat {X' : Scheme.{u}} (h : X' ⟶ D.X) [Etale h] (T : Over D.S)
    (hT : D.IsFlatInDimensionsGEAfterBaseChange T) :
    (D.etaleChart h).IsFlatInDimensionsGEAfterBaseChange T :=
  (D.etaleChart_isFlat_iff h T).mpr (hT.etale_comp (D.chartBaseChange h T) _ _)

/-- An étale chart of a module flat in dimensions `≥ n` is flat in dimensions `≥ n`. -/
theorem isFlatOverInDimensionsGE_etaleChart {X' : Scheme.{u}} (h : X' ⟶ D.X) [Etale h]
    (hD : IsFlatOverInDimensionsGE D.f D.F D.n) :
    IsFlatOverInDimensionsGE (h ≫ D.f) ((Scheme.Modules.pullback h).obj D.F) D.n :=
  hD.etale_comp h D.f D.F

/-- **Étale charts whose images contain the relative assassin.** Let `hᵢ : Xᵢ ⟶ X` be étale
morphisms and let `T` be a scheme over `S` such that every point of `Ass_{X/S}(F)` lying over the
image of `T` is in the image of some `hᵢ`. If the module of each chart is flat in dimensions
`≥ n` after base change to `T`, then so is `F`. This is the argument of the second assertion of
Stacks 05UD, through the flatness criterion of Stacks 05UA. -/
theorem isFlat_of_forall_etaleChart {ι : Type*} {Y : ι → Scheme.{u}} (h : ∀ i, Y i ⟶ D.X)
    [∀ i, Etale (h i)] (T : Over D.S)
    (hcov : ∀ x ∈ Stacks.Divisors.relativeAssassin D.f D.F, D.f x ∈ Set.range T.hom →
      ∃ i, x ∈ Set.range (h i))
    (hT : ∀ i, (D.etaleChart (h i)).IsFlatInDimensionsGEAfterBaseChange T) :
    D.IsFlatInDimensionsGEAfterBaseChange T := by
  classical
  let q := D.baseChangeMap T
  let G := D.baseChangeModule T
  change IsFlatOverInDimensionsGE q G D.n
  rw [isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt]
  intro x hnflat
  -- an associated point of the fibre, generalizing `x`, at which `G` is not flat
  obtain ⟨z, hzass, hzspec, hnflatz⟩ : ∃ z : q.fiber (q x),
      z ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (q.fiberι (q x))).obj G) ∧
        q.fiberι (q x) z ⤳ x ∧ ¬ IsFlatOverAt q.toLRSHom.toShHom G (q.fiberι (q x) z) := by
    by_contra hcon
    push Not at hcon
    exact hnflat (isFlatOverAt_of_forall_isAssociatedPoint_specializes q G x hcon)
  let y := q.fiberι (q x) z
  have hyrel : y ∈ Stacks.Divisors.relativeAssassin q G :=
    (Stacks.Divisors.mem_relativeAssassin q G y).mpr ⟨q x, z, hzass, rfl⟩
  have hpre : pullback.fst D.f T.hom y ∈ Stacks.Divisors.relativeAssassin D.f D.F :=
    relativeAssassin_pullback_subset_preimage D.f T.hom D.F hyrel
  have hrange : D.f (pullback.fst D.f T.hom y) ∈ Set.range T.hom :=
    ⟨pullback.snd D.f T.hom y, by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
  obtain ⟨i, w, hw⟩ := hcov _ hpre hrange
  -- lift `y` to the base change of the chart
  obtain ⟨z', hz'₁, hz'₂⟩ := Scheme.Pullback.exists_preimage_pullback w y hw
  let y' := (pullbackRightPullbackFstIso D.f T.hom (h i)).hom z'
  have hy' : D.chartBaseChange (h i) T y' = y := by
    simpa only [y', chartBaseChange, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc] using hz'₂
  have hyx : q y = q x := by
    have hmem : q.fiberι (q x) z ∈ Set.range (q.fiberι (q x)) := ⟨z, rfl⟩
    rw [q.range_fiberι] at hmem
    exact hmem
  -- the chart is not flat at `y'`
  have hnflat' : ¬ IsFlatOverAt (D.chartBaseChange (h i) T ≫ q).toLRSHom.toShHom
      ((Scheme.Modules.pullback (D.chartBaseChange (h i) T)).obj G) y' := by
    rwa [isFlatOverAt_iff_of_etale, hy']
  have hbound := (isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt _ _ _).mp
    ((D.etaleChart_isFlat_iff (h i) T).mp (hT i)) y' hnflat'
  rw [toENat_trdeg_residueField_eq_of_etale, hy'] at hbound
  -- compare transcendence degrees along `y ⤳ x` in the fibre
  rcases eq_or_ne y x with hyx' | hne
  · exact hyx' ▸ hbound
  · have hstrict := trdeg_residueField_fiber_lt_of_specialization q hzspec hne hyx rfl
    have h1 := toENat_trdeg_residueFieldCongr q x (q x) rfl
    have h2 := toENat_trdeg_residueFieldCongr q y (q x) hyx
    have h3 := Cardinal.toENat.monotone' hstrict.le
    exact (h1.symm.trans_le (WithBot.coe_le_coe.mpr h3)).trans_lt (h2.trans_lt hbound)

/-- **Stacks Project, Tag 05UD.** In Situation 05MT, let `h : X' ⟶ X` be étale and let `F'_n` be
the functor of Stacks 05MU for `(f ∘ h, h^* F)`. Then `F_n` is a subfunctor of `F'_n`, and if
`h(X')` contains `Ass_{X/S}(F)` then `F_n = F'_n`.

Both functors are subterminal, so the first assertion is the implication between the two
conditions after every base change `T ⟶ S`, and the second is their equivalence. -/
@[stacks 05UD]
theorem isFlat_etaleChart_and_iff_of_relativeAssassin_subset {X' : Scheme.{u}} (h : X' ⟶ D.X)
    [Etale h] :
    (∀ T : Over D.S, D.IsFlatInDimensionsGEAfterBaseChange T →
      (D.etaleChart h).IsFlatInDimensionsGEAfterBaseChange T) ∧
    (Stacks.Divisors.relativeAssassin D.f D.F ⊆ Set.range h → ∀ T : Over D.S,
      D.IsFlatInDimensionsGEAfterBaseChange T ↔
        (D.etaleChart h).IsFlatInDimensionsGEAfterBaseChange T) :=
  ⟨D.isFlat_etaleChart_of_isFlat h, fun hAss T ↦ ⟨D.isFlat_etaleChart_of_isFlat h T,
    fun hT ↦ D.isFlat_of_forall_etaleChart (Y := fun _ : Unit ↦ X') (fun _ ↦ h) T
      (fun _ hx _ ↦ ⟨(), hAss hx⟩) fun _ ↦ hT⟩⟩

end FlatDimensionSituation

end AlgebraicGeometry

end
