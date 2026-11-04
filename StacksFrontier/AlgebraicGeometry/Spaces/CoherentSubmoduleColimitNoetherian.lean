module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage

/-!
# The coherent submodules of a quasi-coherent module on a Noetherian algebraic space

Let `X` be a Noetherian algebraic space over a scheme `S`.  Every quasi-coherent `𝒪_X`-module `F`
is the filtered colimit of its coherent submodules.

For an affine étale chart `V₀` of `X` and a submodule `M'` of the sections `F(V₀)`,
`AlgebraicGeometry.Space.chartSpanSubmodule F M'` is the submodule of `F` of the sections `f` over
`W` such that for every chart `Q` and every pair of morphisms `a : Q ⟶ W`, `b : Q ⟶ V₀`, the
restriction of `f` along `a` lies, locally on `Q`, in the span of the restrictions of `M'` along
`b`.  When `V₀` covers `X` and `M'` is finitely generated, it is a coherent submodule of `F`, and
these submodules exhaust `F`.

## Main definitions

* `AlgebraicGeometry.Space.chartSpan`: the span over `𝒪(Y)` of the restrictions of a submodule of
  the sections over `V` along `Y ⟶ V`.
* `AlgebraicGeometry.Space.chartSpanSections` and `AlgebraicGeometry.Space.chartSpanSubmodule`:
  the submodule described above.

## Main results

* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_chartSpanSubmodule`: the submodule is
  cartesian on affine charts.
* `AlgebraicGeometry.Space.isCoherent_chartSpanSubmodule`: the submodule is coherent.
* `AlgebraicGeometry.Space.isFiltered_and_nonempty_isColimit_coherentSubobjectCocone`: every
  quasi-coherent module on a Noetherian algebraic space is the filtered colimit of its coherent
  submodules.

## References

* [Stacks Project, Tag 07UV](https://stacks.math.columbia.edu/tag/07UV)
* [Stacks Project, Tag 07TU](https://stacks.math.columbia.edu/tag/07TU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

variable {B S hS X hX}

/-! ### Three facts about base change of modules -/

section BaseChange

open TensorProduct

/-- **Membership in a base-changed submodule across a pushout of rings.**  Let `B` be the pushout
of `S` and `A` over `R`, let `τ : N ⟶ Q` be an `A`-linear map to a `B`-module whose `B`-linear
extension `B ⊗_A N ⟶ Q` is injective, and let `L ⊆ N` be an `A`-submodule.  An element `w` of
`S ⊗_R N` whose image in `Q` lies in the `B`-span of `τ(L)` comes from `S ⊗_R L`. -/
theorem Algebra.IsPushout.mem_range_lTensor_of_liftBaseChange_mem_span
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra A B] [Algebra S B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    {Q : Type*} [AddCommGroup Q] [Module B Q] [Module A Q] [IsScalarTower A B Q]
    (τ : N →ₗ[A] Q) (hτ : Function.Injective (τ.liftBaseChange B)) (L : Submodule A N)
    (w : S ⊗[R] N)
    (hw : τ.liftBaseChange B ((Algebra.IsPushout.cancelBaseChange R S A B N).symm w) ∈
      Submodule.span B (τ '' L)) :
    w ∈ LinearMap.range (AlgebraTensorModule.lTensor S S (L.subtype.restrictScalars R)) := by
  set ΦN := (Algebra.IsPushout.cancelBaseChange R S A B N).symm with hΦN
  set ΦL := (Algebra.IsPushout.cancelBaseChange R S A B L).symm with hΦL
  have hnat : ∀ v : S ⊗[R] L,
      ΦN (AlgebraTensorModule.lTensor S S (L.subtype.restrictScalars R) v) =
        AlgebraTensorModule.lTensor B B L.subtype (ΦL v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul s l =>
      simp only [hΦN, hΦL, AlgebraTensorModule.lTensor_tmul,
        Algebra.IsPushout.cancelBaseChange_symm_tmul]
      rfl
    | add v v' hv hv' => rw [map_add, map_add, hv, hv', map_add, map_add]
  have hle : Submodule.span B (τ '' L) ≤
      LinearMap.range ((τ.liftBaseChange B).comp (AlgebraTensorModule.lTensor B B L.subtype)) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨1 ⊗ₜ ⟨l, hl⟩, by simp⟩
  obtain ⟨u, hu⟩ := hle hw
  refine ⟨ΦL.symm u, ?_⟩
  apply ΦN.injective
  rw [hnat, LinearEquiv.apply_symm_apply]
  exact hτ hu

/-- **Flat base change of a kernel, elementwise.**  If `S` is flat over `R`, an element of
`S ⊗_R M` killed by the base change of `ψ : M ⟶ P` comes from `S ⊗_R ker ψ`. -/
theorem Module.Flat.mem_range_lTensor_ker {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] {M P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (ψ : M →ₗ[R] P) {z : S ⊗[R] M}
    (hz : AlgebraTensorModule.lTensor S S ψ z = 0) :
    z ∈ LinearMap.range (AlgebraTensorModule.lTensor S S (LinearMap.ker ψ).subtype) := by
  rwa [← Module.Flat.ker_lTensor_eq]

/-- The base change of a map to a finite product vanishes on an element as soon as the base
change of each component does. -/
theorem lTensor_pi_eq_zero {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module R M]
    {P : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    (ψ : ∀ i, M →ₗ[R] P i) {z : S ⊗[R] M}
    (hz : ∀ i, AlgebraTensorModule.lTensor S S (ψ i) z = 0) :
    AlgebraTensorModule.lTensor S S (LinearMap.pi ψ) z = 0 := by
  have hcomp : ∀ i (v : S ⊗[R] M), TensorProduct.piRight R S S P
      (AlgebraTensorModule.lTensor S S (LinearMap.pi ψ) v) i =
        AlgebraTensorModule.lTensor S S (ψ i) v := by
    intro i v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul s m => simp
    | add v v' hv hv' => simp only [map_add, Pi.add_apply, hv, hv']
  apply (TensorProduct.piRight R S S P).injective
  funext i
  rw [hcomp, hz, map_zero]
  rfl

/-- The base change of a map followed by a quotient vanishes on an element whose image comes
from the base change of a map into the submodule. -/
theorem lTensor_mkQ_comp_eq_zero {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N L' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup L'] [Module R L'] (ρ : M →ₗ[R] N) (L : Submodule R N) (j : L' →ₗ[R] N)
    (hj : L.mkQ.comp j = 0) {z : S ⊗[R] M}
    (hz : AlgebraTensorModule.lTensor S S ρ z ∈
      LinearMap.range (AlgebraTensorModule.lTensor S S j)) :
    AlgebraTensorModule.lTensor S S (L.mkQ.comp ρ) z = 0 := by
  obtain ⟨v, hv⟩ := hz
  rw [AlgebraTensorModule.lTensor_comp, LinearMap.comp_apply, ← hv, ← LinearMap.comp_apply,
    ← AlgebraTensorModule.lTensor_comp, hj, map_zero, LinearMap.zero_apply]

/-- A pushout of commutative rings recognised by a linear identification of the tensor product
which multiplies the two factors. -/
theorem Algebra.isPushout_of_linearEquiv {R S A B : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra A B] [Algebra S B]
    [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B] (e : A ⊗[R] S ≃ₗ[R] B)
    (he : ∀ a s, e (a ⊗ₜ s) = algebraMap A B a * algebraMap S B s) :
    Algebra.IsPushout R S A B := by
  let e₀ : S ⊗[R] A ≃ₗ[R] B := (TensorProduct.comm R S A).trans e
  have he₀ : ∀ s a, e₀ (s ⊗ₜ a) = algebraMap A B a * algebraMap S B s := fun s a => he a s
  let e' : S ⊗[R] A ≃ₗ[S] B :=
    { e₀ with
      map_smul' := fun c x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul s a =>
          show e₀ (c • (s ⊗ₜ a)) = c • e₀ (s ⊗ₜ a)
          rw [TensorProduct.smul_tmul', he₀, he₀, smul_eq_mul, Algebra.smul_def, map_mul]
          ring
        | add x y hx hy =>
          show e₀ (c • (x + y)) = c • e₀ (x + y)
          rw [smul_add, map_add, map_add, smul_add]
          exact congrArg₂ (· + ·) hx hy }
  refine ⟨IsBaseChange.of_equiv e' fun a => ?_⟩
  show e₀ (1 ⊗ₜ a) = algebraMap A B a
  rw [he₀, map_one, mul_one]

end BaseChange

/-! ### Restriction of sections, and membership along an equation -/

/-- Membership transported along an equation of elements. -/
theorem mem_of_eq_of_mem {A M : Type*} [SetLike A M] {p : A} {x y : M} (h : x = y)
    (hy : y ∈ p) : x ∈ p :=
  h ▸ hy

/-- Restriction of sections of an `𝒪_X`-module along a morphism of étale charts, as a semilinear
map whose source and target are spelled through the charts. -/
def chartRes (F : Modules.{u, u} B S hS X hX) {V Y : SmallEtale B S hS X} (b : Y ⟶ V) :
    F.val.obj (op V) →ₛₗ[chartRestrict (hF := hX) b] F.val.obj (op Y) :=
  F.val.restrictₛₗ b.op

/-- `chartRes F b` is the restriction map `F.val.map b.op`. -/
theorem chartRes_apply (F : Modules.{u, u} B S hS X hX) {V Y : SmallEtale B S hS X} (b : Y ⟶ V)
    (x : F.val.obj (op V)) : chartRes F b x = F.val.map b.op x :=
  rfl

/-- Restricting twice is restricting along the composite. -/
theorem modules_map_map (F : Modules.{u, u} B S hS X hX) {Y Y' Y'' : SmallEtale B S hS X}
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y') (x : F.val.obj (op Y)) :
    chartRes F h (chartRes F g x) = chartRes F (h ≫ g) x :=
  (F.val.map_comp_apply g.op h.op x).symm

/-- Restriction along equal morphisms. -/
theorem modules_map_congr (F : Modules.{u, u} B S hS X hX) {Y Y' : SmallEtale B S hS X}
    {g g' : Y' ⟶ Y} (h : g = g') (x : F.val.obj (op Y)) :
    chartRes F g x = chartRes F g' x := by
  subst h
  rfl

/-! ### The span of the restrictions of a submodule -/

/-- The `𝒪(Y)`-submodule of the sections over `Y` spanned by the restrictions along `b : Y ⟶ V`
of the sections of a submodule `M'` of the sections over `V`. -/
def chartSpan (F : Modules.{u, u} B S hS X hX) {V Y : SmallEtale B S hS X} (b : Y ⟶ V)
    (M' : Submodule (chartRing B S hS X hX V) (F.val.obj (op V))) :
    Submodule (chartRing B S hS X hX Y) (F.val.obj (op Y)) :=
  Submodule.span _ ((fun m => chartRes F b m) '' (M' : Set (F.val.obj (op V))))

/-- The span of the restrictions along equal morphisms. -/
theorem chartSpan_congr (F : Modules.{u, u} B S hS X hX) {V Y : SmallEtale B S hS X}
    {b b' : Y ⟶ V} (h : b = b')
    (M' : Submodule (chartRing B S hS X hX V) (F.val.obj (op V))) :
    chartSpan F b M' = chartSpan F b' M' := by
  subst h
  rfl

/-- The restriction of a section of `M'` lies in the span of the restrictions. -/
theorem map_mem_chartSpan_of_mem (F : Modules.{u, u} B S hS X hX) {V Y : SmallEtale B S hS X}
    (b : Y ⟶ V) (M' : Submodule (chartRing B S hS X hX V) (F.val.obj (op V)))
    {m : F.val.obj (op V)} (hm : m ∈ M') :
    chartRes F b m ∈ chartSpan F b M' :=
  Submodule.subset_span ⟨m, hm, rfl⟩

/-- Restricting twice along `g` then `h` is restricting along any morphism equal to `h ≫ g`. -/
private theorem chartRes_chartRes_of_comp_eq (F : Modules.{u, u} B S hS X hX)
    {Y Y' Y'' : SmallEtale B S hS X} {g : Y' ⟶ Y} {h : Y'' ⟶ Y'} {k : Y'' ⟶ Y} (hk : h ≫ g = k)
    (x : F.val.obj (op Y)) : chartRes F h (chartRes F g x) = chartRes F k x := by
  subst hk
  exact modules_map_map F g h x

/-- Restriction carries the span of a set into the span of its image. -/
private theorem chartRes_mem_span_image (F : Modules.{u, u} B S hS X hX)
    {V Y : SmallEtale B S hS X} (b : Y ⟶ V) {s : Set (F.val.obj (op V))} {x : F.val.obj (op V)}
    (hx : x ∈ Submodule.span (chartRing B S hS X hX V) s) :
    chartRes F b x ∈ Submodule.span (chartRing B S hS X hX Y) ((fun m => chartRes F b m) '' s) :=
  Submodule.span_le (p := (Submodule.span _ ((fun m => chartRes F b m) '' s)).comap (chartRes F b))
    |>.2 (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩) hx

/-- Restriction carries the span of the restrictions along `b` into the span of the restrictions
along the composite. -/
theorem map_mem_chartSpan (F : Modules.{u, u} B S hS X hX) {V Y Y' : SmallEtale B S hS X}
    (b : Y ⟶ V) (d : Y' ⟶ Y) (M' : Submodule (chartRing B S hS X hX V) (F.val.obj (op V)))
    {x : F.val.obj (op Y)} (hx : x ∈ chartSpan F b M') :
    chartRes F d x ∈ chartSpan F (d ≫ b) M' := by
  refine Submodule.span_le.2 ?_ (chartRes_mem_span_image F d hx)
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  exact mem_of_eq_of_mem (modules_map_map F b d m) (map_mem_chartSpan_of_mem F _ M' hm)

/-- The span of the restrictions grows with the submodule. -/
theorem chartSpan_mono (F : Modules.{u, u} B S hS X hX) {V Y : SmallEtale B S hS X} (b : Y ⟶ V)
    {M₁ M₂ : Submodule (chartRing B S hS X hX V) (F.val.obj (op V))} (h : M₁ ≤ M₂) :
    chartSpan F b M₁ ≤ chartSpan F b M₂ :=
  Submodule.span_mono (Set.image_mono h)

/-! ### The sieve of local membership and the submodule it defines -/

/-- Over a test chart `Q` with morphisms `a : Q ⟶ W` and `b : Q ⟶ V₀`, the sieve of the
morphisms `c : Y ⟶ Q` along which the restriction of `f` lies in the span of the restrictions of
`M'` along `c ≫ b`. -/
def chartSpanSieve (F : Modules.{u, u} B S hS X hX) {V₀ : SmallEtale B S hS X}
    (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)))
    {W Q : SmallEtale B S hS X} (f : F.val.obj (op W)) (a : Q ⟶ W) (b : Q ⟶ V₀) : Sieve Q where
  arrows Y c := chartRes F (c ≫ a) f ∈ chartSpan F (c ≫ b) M'
  downward_closed {Y Y'} c hc d := by
    have h := map_mem_chartSpan F (c ≫ b) d M' hc
    refine (chartSpan_congr F (Category.assoc d c b).symm M').le ?_
    refine mem_of_eq_of_mem ?_ h
    exact (modules_map_congr F (Category.assoc d c a) f).trans (modules_map_map F _ d f).symm

/-- Membership in `chartSpanSieve F M' f a b`. -/
theorem mem_chartSpanSieve (F : Modules.{u, u} B S hS X hX) {V₀ : SmallEtale B S hS X}
    (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)))
    {W Q Y : SmallEtale B S hS X} (f : F.val.obj (op W)) (a : Q ⟶ W) (b : Q ⟶ V₀)
    (c : Y ⟶ Q) :
    chartSpanSieve F M' f a b c ↔ chartRes F (c ≫ a) f ∈ chartSpan F (c ≫ b) M' :=
  Iff.rfl

/-- The sections over `W` which, along every pair of morphisms `a : Q ⟶ W` and `b : Q ⟶ V₀`,
lie locally on `Q` in the span of the restrictions of `M'` along `b`. -/
def chartSpanSections (F : Modules.{u, u} B S hS X hX) {V₀ : SmallEtale B S hS X}
    (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) (W : SmallEtale B S hS X) :
    Submodule (chartRing B S hS X hX W) (F.val.obj (op W)) where
  carrier := {f | ∀ (Q : SmallEtale B S hS X) (a : Q ⟶ W) (b : Q ⟶ V₀),
    chartSpanSieve F M' f a b ∈ SmallEtale.topology B S hS X Q}
  add_mem' {f g} hf hg Q a b := by
    refine (SmallEtale.topology B S hS X).superset_covering ?_
      ((SmallEtale.topology B S hS X).intersection_covering (hf Q a b) (hg Q a b))
    rintro Y c ⟨h₁, h₂⟩
    exact mem_of_eq_of_mem (map_add _ f g) (add_mem h₁ h₂)
  zero_mem' Q a b := by
    refine (SmallEtale.topology B S hS X).superset_covering ?_
      ((SmallEtale.topology B S hS X).top_mem Q)
    intro Y c _
    exact mem_of_eq_of_mem (map_zero _) (zero_mem _)
  smul_mem' r f hf Q a b := by
    refine (SmallEtale.topology B S hS X).superset_covering ?_ (hf Q a b)
    intro Y c hc
    exact mem_of_eq_of_mem ((chartRes F (c ≫ a)).map_smulₛₗ r f) (Submodule.smul_mem _ _ hc)

/-- Membership in `chartSpanSections F M' W`. -/
theorem mem_chartSpanSections (F : Modules.{u, u} B S hS X hX) {V₀ : SmallEtale B S hS X}
    (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) {W : SmallEtale B S hS X}
    (f : F.val.obj (op W)) :
    f ∈ chartSpanSections F M' W ↔ ∀ (Q : SmallEtale B S hS X) (a : Q ⟶ W) (b : Q ⟶ V₀),
      chartSpanSieve F M' f a b ∈ SmallEtale.topology B S hS X Q :=
  Iff.rfl

/-- The sieve of a restricted section is the sieve of the section along the composite. -/
theorem chartSpanSieve_map (F : Modules.{u, u} B S hS X hX) {V₀ : SmallEtale B S hS X}
    (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)))
    {W W' Q : SmallEtale B S hS X} (f : F.val.obj (op W)) (g : W' ⟶ W) (a : Q ⟶ W')
    (b : Q ⟶ V₀) :
    chartSpanSieve F M' (chartRes F g f) a b = chartSpanSieve F M' f (a ≫ g) b := by
  ext Y c
  show chartRes F (c ≫ a) (chartRes F g f) ∈ chartSpan F (c ≫ b) M' ↔
    chartRes F (c ≫ a ≫ g) f ∈ chartSpan F (c ≫ b) M'
  have h : chartRes F (c ≫ a) (chartRes F g f) = chartRes F (c ≫ a ≫ g) f :=
    chartRes_chartRes_of_comp_eq F (Category.assoc c a g) f
  exact ⟨fun hx => mem_of_eq_of_mem h.symm hx, fun hx => mem_of_eq_of_mem h hx⟩

/-- The submodule of `F` of the sections which locally lie in the span of the restrictions of
`M'`, along every morphism to `V₀`. -/
def chartSpanSubmodule (F : Modules.{u, u} B S hS X hX) {V₀ : SmallEtale B S hS X}
    (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) : F.Submodule where
  obj W := chartSpanSections F M' W.unop
  map {W W'} g f hf Q a b := by
    change chartSpanSieve F M' (chartRes F g.unop f) a b ∈ _
    exact (chartSpanSieve_map F M' f g.unop a b).symm ▸ hf Q (a ≫ g.unop) b
  isSheaf W s hs Q a b := by
    have hpb := (SmallEtale.topology B S hS X).pullback_stable a hs
    refine (SmallEtale.topology B S hS X).transitive hpb _ ?_
    intro Y d hd
    have hmem : chartRes F (d ≫ a) s ∈ chartSpanSections F M' Y := hd
    refine (SmallEtale.topology B S hS X).superset_covering ?_ (hmem Y (𝟙 Y) (d ≫ b))
    intro Y' c hc
    have hc' : chartRes F (c ≫ 𝟙 Y) (chartRes F (d ≫ a) s) ∈
        chartSpan F (c ≫ d ≫ b) M' := hc
    change chartRes F ((c ≫ d) ≫ a) s ∈ chartSpan F ((c ≫ d) ≫ b) M'
    refine (chartSpan_congr F (Category.assoc c d b).symm M').le ?_
    refine mem_of_eq_of_mem ?_ hc'
    refine (modules_map_congr F (Category.assoc c d a) s).trans ?_
    refine (modules_map_map F (d ≫ a) c s).symm.trans ?_
    exact modules_map_congr F (Category.comp_id c).symm _

/-- The sections of `chartSpanSubmodule F M'` over `W` are `chartSpanSections F M' W`. -/
theorem mem_chartSpanSubmodule_obj (F : Modules.{u, u} B S hS X hX) {V₀ : SmallEtale B S hS X}
    (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) {W : SmallEtale B S hS X}
    (f : F.val.obj (op W)) :
    f ∈ (chartSpanSubmodule F M').obj (op W) ↔ f ∈ chartSpanSections F M' W :=
  ⟨id, id⟩

/-! ### The tests over a finite affine cover of a product -/

/-- The product of two affine charts of a quasi-separated algebraic space is covered by a finite
family of affine charts. -/
theorem exists_finite_affine_cover_prod (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) {W V : SmallEtale B S hS X}
    (hW : IsAffine (chartScheme W)) (hV : IsAffine (chartScheme V)) :
    ∃ (ι : Type u) (_ : Finite ι) (P : ι → SmallEtale B S hS X) (q : ∀ i, P i ⟶ W ⨯ V),
      (∀ i, IsAffine (chartScheme (P i))) ∧
        Sieve.ofArrows P q ∈ SmallEtale.topology B S hS X (W ⨯ V) := by
  have hc : CompactSpace (chartScheme (W ⨯ V)) :=
    SmallEtale.compactSpace_prod B S hS X hZ hqs W V inferInstance inferInstance
  have hcomp : IsCompact ((⊤ : (chartScheme (W ⨯ V)).Opens) : Set (chartScheme (W ⨯ V))) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (X := chartScheme (W ⨯ V)) (U := ⊤)).1 hcomp
  refine ⟨s, hs.to_subtype, fun i => openChart B S hS X (W ⨯ V) i.1.1,
    fun i => openChartInclusion B S hS X (W ⨯ V) i.1.1, fun i => i.1.2, ?_⟩
  apply ofArrows_openChartInclusion_mem_topology
  rw [hsU, iSup_subtype']

/-- The span of the restrictions of a span is the span of the restrictions of its generators. -/
theorem chartSpan_span (F : Modules.{u, u} B S hS X hX) {V Y : SmallEtale B S hS X} (b : Y ⟶ V)
    (t : Set (F.val.obj (op V))) :
    chartSpan F b (Submodule.span _ t) =
      Submodule.span _ ((fun m => chartRes F b m) '' t) := by
  refine le_antisymm ?_ (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rw [chartSpan, Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  exact chartRes_mem_span_image F b hm

/-- Let `F` be cartesian on affine charts and `M'` finitely generated.  If `x` lies in
`chartSpanSections F M' W`, then for every affine chart `P` with morphisms `a : P ⟶ W` and
`b : P ⟶ V₀` the restriction of `x` along `a` lies in the span of the restrictions of `M'` along
`b`. -/
theorem restrict_mem_chartSpan_of_mem (F : Modules.{u, u} B S hS X hX)
    (hF : IsCartesianOnAffineCharts F) {V₀ : SmallEtale B S hS X}
    {M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))} (hM' : M'.FG)
    {W P : SmallEtale B S hS X} (hP : IsAffine (chartScheme P)) (a : P ⟶ W) (b : P ⟶ V₀)
    {x : F.val.obj (op W)} (hx : x ∈ chartSpanSections F M' W) :
    chartRes F a x ∈ chartSpan F b M' := by
  obtain ⟨t, rfl⟩ := hM'
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS X hX hP (hx P a b)
  have hτ : Submodule.span (chartRing B S hS X hX P)
      (Set.range fun m : t => chartRes F b (m : F.val.obj (op V₀))) ≤
        chartSpan F b (Submodule.span _ (t : Set (F.val.obj (op V₀)))) := by
    refine (chartSpan_span F b _).ge.trans' (Submodule.span_mono ?_)
    rintro _ ⟨m, rfl⟩
    exact ⟨m, m.2, rfl⟩
  refine hτ (mem_span_of_forall_restrict_mem_span F hF hP φ hzaff hff
    (fun m : t => chartRes F b (m : F.val.obj (op V₀))) fun i => ?_)
  have hi : chartRes F (φ i ≫ a) x ∈
      chartSpan F (φ i ≫ b) (Submodule.span _ (t : Set (F.val.obj (op V₀)))) := hzT i
  refine mem_of_eq_of_mem (modules_map_map F a (φ i) x) ?_
  refine Submodule.span_le.2 ?_ ((chartSpan_span F (φ i ≫ b) _).le hi)
  rintro _ ⟨m, hm, rfl⟩
  exact Submodule.subset_span ⟨⟨m, hm⟩, (modules_map_map F b (φ i) m)⟩

/-- If a family of charts `P i` covers `W ⨯ V₀` and the restriction of `x` to every `P i` lies in
the span of the restrictions of `M'` along the second projection, then `x` lies in
`chartSpanSections F M' W`. -/
theorem mem_chartSpanSections_of_cover (F : Modules.{u, u} B S hS X hX)
    {V₀ : SmallEtale B S hS X} (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)))
    {W : SmallEtale B S hS X} {ι : Type*} (P : ι → SmallEtale B S hS X) (q : ∀ i, P i ⟶ W ⨯ V₀)
    (hq : Sieve.ofArrows P q ∈ SmallEtale.topology B S hS X (W ⨯ V₀)) {x : F.val.obj (op W)}
    (hx : ∀ i, chartRes F (q i ≫ prod.fst) x ∈ chartSpan F (q i ≫ prod.snd) M') :
    x ∈ chartSpanSections F M' W := by
  intro Q a b
  have hpb := (SmallEtale.topology B S hS X).pullback_stable (prod.lift a b) hq
  refine (SmallEtale.topology B S hS X).superset_covering ?_ hpb
  intro Y d hd
  obtain ⟨i, e, he⟩ := (Sieve.mem_ofArrows_iff P q (d ≫ prod.lift a b)).1 hd
  have ha : e ≫ q i ≫ prod.fst = d ≫ a := by
    rw [← Category.assoc, ← he, Category.assoc, prod.lift_fst]
  have hb : e ≫ q i ≫ prod.snd = d ≫ b := by
    rw [← Category.assoc, ← he, Category.assoc, prod.lift_snd]
  show chartRes F (d ≫ a) x ∈ chartSpan F (d ≫ b) M'
  refine (chartSpan_congr F hb M').le ?_
  refine mem_of_eq_of_mem (chartRes_chartRes_of_comp_eq F ha x).symm ?_
  exact map_mem_chartSpan F _ e M' (hx i)

/-- An element of the span of an image of `s` lies in the span of the image of a finite subset
of `s`. -/
private theorem exists_finset_subset_mem_span_image {R N M : Type*} [Semiring R]
    [AddCommMonoid N] [Module R N] (f : M → N) {s : Set M} {x : N}
    (hx : x ∈ Submodule.span R (f '' s)) :
    ∃ t : Finset M, ↑t ⊆ s ∧ x ∈ Submodule.span R (f '' (t : Set M)) := by
  classical
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  choose m hm hmg using fun j => (g j).2
  refine ⟨Finset.univ.image m, ?_, ?_⟩
  · intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact hm j
  · refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨m j, by simp, hmg j⟩

/-- For an affine chart `V₀` and a finite family of affine charts covering `W ⨯ V₀`, every
section over `W` of a module cartesian on affine charts lies in `chartSpanSections F M' W` for some
finitely generated `M'`. -/
theorem exists_fg_mem_chartSpanSections (F : Modules.{u, u} B S hS X hX)
    (hF : IsCartesianOnAffineCharts F) {V₀ : SmallEtale B S hS X}
    (hV₀ : IsAffine (chartScheme V₀)) {W : SmallEtale B S hS X} {ι : Type*} [Finite ι]
    (P : ι → SmallEtale B S hS X) (q : ∀ i, P i ⟶ W ⨯ V₀)
    (hP : ∀ i, IsAffine (chartScheme (P i)))
    (hq : Sieve.ofArrows P q ∈ SmallEtale.topology B S hS X (W ⨯ V₀)) (x : F.val.obj (op W)) :
    ∃ M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)), M'.FG ∧
      x ∈ chartSpanSections F M' W := by
  classical
  have hgen : ∀ i, ∃ t : Finset (F.val.obj (op V₀)),
      chartRes F (q i ≫ prod.fst) x ∈
        Submodule.span (chartRing B S hS X hX (P i))
          ((fun m => chartRes F (q i ≫ prod.snd) m) '' (t : Set _)) := by
    intro i
    have htop := (chartBaseChange_surjective_iff_span_eq_top F (q i ≫ prod.snd)).1
      (hF V₀ (P i) hV₀ (hP i) (q i ≫ prod.snd)).2
    have hmem : chartRes F (q i ≫ prod.fst) x ∈ Submodule.span
        (chartRing B S hS X hX (P i))
        ((fun m => chartRes F (q i ≫ prod.snd) m) '' (Set.univ : Set (F.val.obj (op V₀)))) := by
      rw [Set.image_univ]
      change _ ∈ Submodule.span _ (Set.range fun m => chartRestrictLinear F (q i ≫ prod.snd) m)
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨t, -, ht⟩ := exists_finset_subset_mem_span_image _ hmem
    exact ⟨t, ht⟩
  choose t ht using hgen
  have := Fintype.ofFinite ι
  refine ⟨Submodule.span _ (⋃ i, (t i : Set (F.val.obj (op V₀)))), ?_, ?_⟩
  · refine ⟨Finset.univ.biUnion t, ?_⟩
    simp
  · refine mem_chartSpanSections_of_cover F _ P q hq fun i => ?_
    refine (chartSpan_span F _ _).ge (Submodule.span_mono (Set.image_mono ?_) (ht i))
    exact Set.subset_iUnion (fun i => (t i : Set (F.val.obj (op V₀)))) i

/-! ### The submodule is cartesian on affine charts -/

/-- The inclusion of the sections of `chartSpanSubmodule F M'` intertwines the two base change
comparisons. -/
theorem subtype_sectionsBaseChange_chartSpanSubmodule (F : Modules.{u, u} B S hS X hX)
    {V₀ : SmallEtale B S hS X} (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)))
    {W W' : SmallEtale B S hS X} (f : W' ⟶ W)
    (u : letI := chartAlgebra (hF := hX) f
      TensorProduct (chartRing B S hS X hX W) (chartRing B S hS X hX W')
        ((chartSpanSubmodule F M').toSheafOfModules.val.obj (op W))) :
    letI := chartAlgebra (hF := hX) f
    (chartSpanSections F M' W').subtype
        (sectionsBaseChange (chartSpanSubmodule F M').toSheafOfModules f u) =
      sectionsBaseChange F f (AlgebraTensorModule.lTensor (chartRing B S hS X hX W')
        (chartRing B S hS X hX W') (chartSpanSections F M' W).subtype u) := by
  let := chartAlgebra (hF := hX) f
  induction u using TensorProduct.induction_on with
  | zero =>
    exact ((congrArg (chartSpanSections F M' W').subtype (map_zero _)).trans (map_zero _)).trans
      (((congrArg (sectionsBaseChange F f) (map_zero _)).trans (map_zero _)).symm)
  | tmul r k => rfl
  | add u v hu hv =>
    exact ((congrArg (chartSpanSections F M' W').subtype (map_add _ u v)).trans
      (map_add _ _ _)).trans ((congrArg₂ (· + ·) hu hv).trans
        (((congrArg (sectionsBaseChange F f) (map_add _ u v)).trans (map_add _ _ _)).symm))

/-- On a quasi-separated algebraic space, for `F` cartesian on affine charts, `V₀` an affine
chart and `M'` finitely generated, `chartSpanSubmodule F M'` is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_chartSpanSubmodule (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (F : Modules.{u, u} B S hS X hX)
    (hF : IsCartesianOnAffineCharts F) {V₀ : SmallEtale B S hS X}
    (hV₀ : IsAffine (chartScheme V₀))
    {M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))} (hM' : M'.FG) :
    IsCartesianOnAffineCharts (chartSpanSubmodule F M').toSheafOfModules := by
  classical
  intro W W' hW hW' f
  let := chartAlgebra (hF := hX) f
  have hflat : Module.Flat (chartRing B S hS X hX W) (chartRing B S hS X hX W') :=
    flat_chartRestrict_of_isAffine f hW hW'
  set ιW := (chartSpanSections F M' W).subtype with hιW
  set ιW' := (chartSpanSections F M' W').subtype with hιW'
  have hcomm := subtype_sectionsBaseChange_chartSpanSubmodule F M' f
  have hrange : ∀ z, sectionsBaseChange F f z ∈ chartSpanSections F M' W' →
      z ∈ LinearMap.range (AlgebraTensorModule.lTensor (chartRing B S hS X hX W')
        (chartRing B S hS X hX W') ιW) := by
    intro z hz
    obtain ⟨ι, hι, P, q, hPaff, hq⟩ := exists_finite_affine_cover_prod hZ hqs hW hV₀
    have := Fintype.ofFinite ι
    let a : ∀ i, P i ⟶ W := fun i => q i ≫ prod.fst
    let b : ∀ i, P i ⟶ V₀ := fun i => q i ≫ prod.snd
    let algP : ∀ i, Algebra (chartRing B S hS X hX W) (chartRing B S hS X hX (P i)) :=
      fun i => chartAlgebra (hF := hX) (a i)
    let modN : ∀ i, Module (chartRing B S hS X hX W) (F.val.obj (op (P i))) :=
      fun i => chartSectionsModule F (a i)
    have towN : ∀ i, IsScalarTower (chartRing B S hS X hX W) (chartRing B S hS X hX (P i))
        (F.val.obj (op (P i))) := fun i => chartSections_isScalarTower F (a i)
    let L : ∀ i, Submodule (chartRing B S hS X hX (P i)) (F.val.obj (op (P i))) :=
      fun i => chartSpan F (b i) M'
    let ρ : ∀ i, F.val.obj (op W) →ₗ[chartRing B S hS X hX W] F.val.obj (op (P i)) :=
      fun i => chartRestrictLinear F (a i)
    let ψ : ∀ i, F.val.obj (op W) →ₗ[chartRing B S hS X hX W]
        F.val.obj (op (P i)) ⧸ (L i).restrictScalars (chartRing B S hS X hX W) :=
      fun i => ((L i).restrictScalars (chartRing B S hS X hX W)).mkQ.comp (ρ i)
    have hker : LinearMap.ker (LinearMap.pi ψ) ≤
        (chartSpanSections F M' W).restrictScalars (chartRing B S hS X hX W) := by
      intro x hx
      refine mem_chartSpanSections_of_cover F M' P q hq fun i => ?_
      exact (Submodule.Quotient.mk_eq_zero _).1 (congrFun (LinearMap.mem_ker.1 hx) i : ψ i x = 0)
    have hψ : ∀ i, AlgebraTensorModule.lTensor (chartRing B S hS X hX W')
        (chartRing B S hS X hX W') (ψ i) z = 0 := by
      intro i
      have hpb := IsPullback.of_hasPullback (a i) f
      set Pi := pullback (a i) f
      set pr₁ : Pi ⟶ P i := pullback.fst (a i) f
      set pr₂ : Pi ⟶ W' := pullback.snd (a i) f
      have hPiaff : IsAffine (chartScheme Pi) :=
        SmallEtale.isAffine_of_isPullback_charts hpb hW (hPaff i) hW'
      let : Algebra (chartRing B S hS X hX (P i)) (chartRing B S hS X hX Pi) :=
        chartAlgebra (hF := hX) pr₁
      let : Algebra (chartRing B S hS X hX W') (chartRing B S hS X hX Pi) :=
        chartAlgebra (hF := hX) pr₂
      let : Algebra (chartRing B S hS X hX W) (chartRing B S hS X hX Pi) :=
        chartAlgebra (hF := hX) (pr₁ ≫ a i)
      have : IsScalarTower (chartRing B S hS X hX W) (chartRing B S hS X hX (P i))
          (chartRing B S hS X hX Pi) :=
        IsScalarTower.of_algebraMap_eq fun x =>
          RingHom.congr_fun (chartRestrict_comp (hF := hX) (a i) pr₁) x
      have : IsScalarTower (chartRing B S hS X hX W) (chartRing B S hS X hX W')
          (chartRing B S hS X hX Pi) :=
        IsScalarTower.of_algebraMap_eq fun x => by
          show chartRestrict (hF := hX) (pr₁ ≫ a i) x =
            chartRestrict (hF := hX) pr₂ (chartRestrict (hF := hX) f x)
          rw [show pr₁ ≫ a i = pr₂ ≫ f from hpb.w]
          exact RingHom.congr_fun (chartRestrict_comp (hF := hX) f pr₂) x
      obtain ⟨e, he⟩ := SmallEtale.exists_tensorEquiv_chartRing_of_isPullback (hF := hX) hpb
        hW (hPaff i) hW'
      have : Algebra.IsPushout (chartRing B S hS X hX W) (chartRing B S hS X hX W')
          (chartRing B S hS X hX (P i)) (chartRing B S hS X hX Pi) :=
        Algebra.isPushout_of_linearEquiv e he
      let : Module (chartRing B S hS X hX (P i)) (F.val.obj (op Pi)) :=
        chartSectionsModule F pr₁
      have : IsScalarTower (chartRing B S hS X hX (P i)) (chartRing B S hS X hX Pi)
          (F.val.obj (op Pi)) := chartSections_isScalarTower F pr₁
      let τ : F.val.obj (op (P i)) →ₗ[chartRing B S hS X hX (P i)] F.val.obj (op Pi) :=
        chartRestrictLinear F pr₁
      have hτ : Function.Injective (τ.liftBaseChange (chartRing B S hS X hX Pi)) :=
        (hF (P i) Pi (hPaff i) hPiaff pr₁).1
      have hΘ : ∀ v, τ.liftBaseChange (chartRing B S hS X hX Pi)
          ((Algebra.IsPushout.cancelBaseChange (chartRing B S hS X hX W)
            (chartRing B S hS X hX W') (chartRing B S hS X hX (P i)) (chartRing B S hS X hX Pi)
            (F.val.obj (op (P i)))).symm
            (AlgebraTensorModule.lTensor (chartRing B S hS X hX W') (chartRing B S hS X hX W')
              (ρ i) v)) = chartRes F pr₂ (sectionsBaseChange F f v) := by
        intro v
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul r m =>
          rw [AlgebraTensorModule.lTensor_tmul, Algebra.IsPushout.cancelBaseChange_symm_tmul,
            LinearMap.liftBaseChange_tmul, chartBaseChange_tmul, map_smulₛₗ]
          refine congrArg₂ (· • ·) rfl ?_
          show F.val.map pr₁.op (F.val.map (a i).op m) = F.val.map pr₂.op (F.val.map f.op m)
          exact (modules_map_map F (a i) pr₁ m).trans
            ((modules_map_congr F hpb.w m).trans (modules_map_map F f pr₂ m).symm)
        | add v v' hv hv' => rw [map_add, map_add, map_add, hv, hv', map_add, map_add]
      have hmem : chartRes F pr₂ (sectionsBaseChange F f z) ∈
          Submodule.span (chartRing B S hS X hX Pi) (τ '' (L i)) := by
        have h₀ := restrict_mem_chartSpan_of_mem F hF hM' hPiaff pr₂ (pr₁ ≫ b i) hz
        refine Submodule.span_le.2 ?_ h₀
        rintro _ ⟨m, hm, rfl⟩
        refine Submodule.subset_span ⟨chartRes F (b i) m, map_mem_chartSpan_of_mem F _ M' hm, ?_⟩
        exact modules_map_map F (b i) pr₁ m
      have hw := Algebra.IsPushout.mem_range_lTensor_of_liftBaseChange_mem_span τ hτ (L i)
        (AlgebraTensorModule.lTensor (chartRing B S hS X hX W') (chartRing B S hS X hX W')
          (ρ i) z) ((hΘ z).symm ▸ hmem)
      refine lTensor_mkQ_comp_eq_zero (ρ i) _ ((L i).subtype.restrictScalars _) ?_ hw
      ext l
      exact (Submodule.Quotient.mk_eq_zero _).2 l.2
    have hz0 := lTensor_pi_eq_zero ψ hψ
    obtain ⟨v, hv⟩ := Module.Flat.mem_range_lTensor_ker (LinearMap.pi ψ) hz0
    refine ⟨AlgebraTensorModule.lTensor (chartRing B S hS X hX W') (chartRing B S hS X hX W')
      (Submodule.inclusion hker) v, ?_⟩
    exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp (A := chartRing B S hS X hX W')
      (M := chartRing B S hS X hX W') ιW (Submodule.inclusion hker)) v).symm.trans hv
  refine ⟨fun u v huv => ?_, fun y => ?_⟩
  · have h := congrArg (fun t => (chartSpanSections F M' W').subtype t) huv
    simp only [hcomm] at h
    have hinj : Function.Injective (AlgebraTensorModule.lTensor (chartRing B S hS X hX W')
        (chartRing B S hS X hX W') ιW) := by
      rw [AlgebraTensorModule.coe_lTensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact hinj ((hF W W' hW hW' f).1 h)
  · obtain ⟨y, hy⟩ := y
    obtain ⟨z, hz⟩ := (hF W W' hW hW' f).2 y
    obtain ⟨u, rfl⟩ := hrange z (hz ▸ hy)
    refine ⟨u, Subtype.ext ?_⟩
    exact (hcomm u).trans hz

/-! ### Finiteness of the submodule -/

/-- The sections of `chartSpanSubmodule F M'` over a smaller affine chart are spanned by the
restrictions of its sections over a larger one, once the submodule is cartesian on affine
charts. -/
theorem chartSpanSections_le_span (F : Modules.{u, u} B S hS X hX) {V₀ : SmallEtale B S hS X}
    {M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))}
    (hcart : IsCartesianOnAffineCharts (chartSpanSubmodule F M').toSheafOfModules)
    {W Y : SmallEtale B S hS X} (hW : IsAffine (chartScheme W)) (hY : IsAffine (chartScheme Y))
    (φ : Y ⟶ W) :
    chartSpanSections F M' Y ≤ Submodule.span (chartRing B S hS X hX Y)
      ((fun x => chartRes F φ x) '' (chartSpanSections F M' W : Set (F.val.obj (op W)))) := by
  let := chartAlgebra (hF := hX) φ
  intro g hg
  obtain ⟨u, hu0⟩ := (hcart W Y hW hY φ).2 ⟨g, hg⟩
  have hgu : g = (chartSpanSections F M' Y).subtype
      (sectionsBaseChange (chartSpanSubmodule F M').toSheafOfModules φ u) := by
    rw [hu0]
    rfl
  rw [hgu, subtype_sectionsBaseChange_chartSpanSubmodule]
  clear hgu hu0
  induction u using TensorProduct.induction_on with
  | zero => exact mem_of_eq_of_mem ((congrArg _ (map_zero _)).trans (map_zero _)) (zero_mem _)
  | tmul r k =>
    refine mem_of_eq_of_mem (chartBaseChange_tmul F φ r _) ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, by exact k.2, rfl⟩)
  | add u v hu hv =>
    exact mem_of_eq_of_mem ((congrArg _ (map_add _ u v)).trans (map_add _ _ _)) (add_mem hu hv)

/-- The ring of regular functions on an affine chart of a locally Noetherian algebraic space is
Noetherian. -/
theorem isNoetherianRing_chartRing_of_isAffine
    (hLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {A : SmallEtale B S hS X} (hA : IsAffine (chartScheme A)) :
    IsNoetherianRing (chartRing B S hS X hX A) := by
  have _ := isLocallyNoetherian_chartScheme B S hS ⟨X, hX⟩ hLN A
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (chartScheme A)⟩

/-- On a locally Noetherian algebraic space covered by `V₀`, the sections of
`chartSpanSubmodule F M'` over an affine chart are spanned by finitely many of them. -/
theorem exists_span_eq_chartSpanSections (F : Modules.{u, u} B S hS X hX)
    (hF : IsCartesianOnAffineCharts F)
    (hLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {V₀ : SmallEtale B S hS X}
    (hcov : (SmallEtale.topology B S hS X).CoversTop (fun _ : PUnit.{u + 2} => V₀))
    {M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))} (hM' : M'.FG)
    (hcart : IsCartesianOnAffineCharts (chartSpanSubmodule F M').toSheafOfModules)
    {W : SmallEtale B S hS X} (hW : IsAffine (chartScheme W)) :
    ∃ (n : ℕ) (s : Fin n → F.val.obj (op W)), (∀ j, s j ∈ chartSpanSections F M' W) ∧
      chartSpanSections F M' W ≤ Submodule.span (chartRing B S hS X hX W) (Set.range s) := by
  classical
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS X hX hW (hcov W)
  have hb : ∀ k, Nonempty (z k ⟶ V₀) := fun k =>
    ((Sieve.mem_ofObjects_iff _ (φ k)).1 (hzT k)).choose_spec
  let b : ∀ k, z k ⟶ V₀ := fun k => (hb k).some
  have hfg : ∀ k, (chartSpanSections F M' (z k)).FG := by
    intro k
    have _ := isNoetherianRing_chartRing_of_isAffine (hX := hX) hLN (hzaff k)
    obtain ⟨t, ht⟩ := id hM'
    refine Submodule.FG.of_le (T := chartSpan F (b k) M') ?_ fun x hx => ?_
    · rw [← ht, chartSpan_span]
      exact Submodule.fg_span ((t.finite_toSet).image _)
    · exact mem_of_eq_of_mem (chartRestrictLinear_id F (z k) x).symm
        (restrict_mem_chartSpan_of_mem F hF hM' (hzaff k) (𝟙 _) (b k) hx)
  choose G hG using hfg
  have hgen : ∀ k (g : G k), ∃ t : Finset (F.val.obj (op W)),
      (↑t ⊆ (chartSpanSections F M' W : Set (F.val.obj (op W)))) ∧
        (g : F.val.obj (op (z k))) ∈ Submodule.span (chartRing B S hS X hX (z k))
          ((fun x => chartRes F (φ k) x) '' (t : Set (F.val.obj (op W)))) := by
    intro k g
    have hg : (g : F.val.obj (op (z k))) ∈ chartSpanSections F M' (z k) := by
      rw [← hG k]
      exact Submodule.subset_span g.2
    exact exists_finset_subset_mem_span_image _
      (chartSpanSections_le_span F hcart hW (hzaff k) (φ k) hg)
  choose t ht hgt using hgen
  let T : Finset (F.val.obj (op W)) := Finset.univ.biUnion fun k => (G k).attach.biUnion (t k)
  have hT : (↑T : Set (F.val.obj (op W))) ⊆ chartSpanSections F M' W := by
    intro y hy
    simp only [T, Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion] at hy
    obtain ⟨k, -, g, -, hy⟩ := hy
    exact ht k g hy
  refine ⟨T.card, fun j => (T.equivFin.symm j : F.val.obj (op W)), fun j => hT (by simp), ?_⟩
  intro x hx
  have hrange : Set.range (fun j => (T.equivFin.symm j : F.val.obj (op W))) = (T : Set _) := by
    ext y
    exact ⟨fun ⟨j, hj⟩ => hj ▸ (T.equivFin.symm j).2,
      fun hy => ⟨T.equivFin ⟨y, hy⟩, by simp⟩⟩
  refine mem_span_of_forall_restrict_mem_span F hF hW φ hzaff hff _ fun k => ?_
  have hxk : chartRes F (φ k) x ∈ chartSpanSections F M' (z k) := (chartSpanSubmodule F M').map
    (φ k).op hx
  rw [← hG k] at hxk
  refine Submodule.span_le.2 ?_ hxk
  intro g hg
  refine Submodule.span_mono ?_ (hgt k ⟨g, hg⟩)
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨T.equivFin ⟨y, ?_⟩, ?_⟩
  · simp only [T, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨k, ⟨g, hg⟩, Finset.mem_attach _ _, hy⟩
  · simp only [Equiv.symm_apply_apply]
    rfl

/-- On a locally Noetherian algebraic space covered by `V₀`, `chartSpanSubmodule F M'` is of
finite type. -/
theorem isFiniteType_chartSpanSubmodule (F : Modules.{u, u} B S hS X hX)
    (hF : IsCartesianOnAffineCharts F)
    (hLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {V₀ : SmallEtale B S hS X}
    (hcov : (SmallEtale.topology B S hS X).CoversTop (fun _ : PUnit.{u + 2} => V₀))
    {M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))} (hM' : M'.FG)
    (hcart : IsCartesianOnAffineCharts (chartSpanSubmodule F M').toSheafOfModules) :
    PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS X hX).J
      (chartSpanSubmodule F M').toSheafOfModules.val := by
  classical
  refine ⟨⟨{A : SmallEtale B S hS X // IsAffine (chartScheme A)}, Subtype.val, ?_, ?_⟩⟩
  · intro Y
    obtain ⟨Sv, hSv, hfac⟩ := exists_covering_through_noetherianAffine B S hS X hX hLN Y
    refine (SmallEtale.topology B S hS X).superset_covering ?_ hSv
    intro Z h hh
    obtain ⟨A, l, -, ⟨hA, -⟩, -⟩ := hfac h hh
    exact ⟨⟨A, hA⟩, ⟨l⟩⟩
  · rintro ⟨A, hA⟩
    obtain ⟨n, s, hs, hle⟩ := exists_span_eq_chartSpanSections F hF hLN hcov hM' hcart hA
    refine ⟨n, fun j => (⟨s j, hs j⟩ : chartSpanSections F M' A), ?_⟩
    intro V f t
    obtain ⟨Sv, hSv, hfac⟩ := exists_covering_through_noetherianAffine B S hS X hX hLN V
    refine ⟨Sv, hSv, fun W g hg => ?_⟩
    obtain ⟨A', l, m, ⟨hA', -⟩, rfl⟩ := hfac g hg
    have h1 : chartRes F m ((chartSpanSections F M' V).subtype t) ∈
        chartSpanSections F M' A' := (chartSpanSubmodule F M').map m.op t.2
    have h2 := chartSpanSections_le_span F hcart hA hA' (m ≫ f) h1
    have h3 : Submodule.span (chartRing B S hS X hX A')
        ((fun x => chartRes F (m ≫ f) x) '' (chartSpanSections F M' A : Set (F.val.obj (op A)))) ≤
          Submodule.span (chartRing B S hS X hX A')
            (Set.range fun j => chartRes F (m ≫ f) (s j)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      have hx' := map_mem_chartSpan_of_mem F (m ≫ f) _ (hle hx)
      rw [chartSpan_span, ← Set.range_comp] at hx'
      exact hx'
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (h3 h2)
    refine ⟨fun j => chartRestrict (hF := hX) l (c j), ?_⟩
    refine (chartSpanSections F M' W).injective_subtype ?_
    refine ((map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => map_smul _ _ _)).trans ?_
    show ∑ j, chartRestrict (hF := hX) l (c j) • chartRes F ((l ≫ m) ≫ f) (s j) =
      chartRes F (l ≫ m) ((chartSpanSections F M' V).subtype t)
    refine Eq.trans ?_ ((modules_map_map F m l _).symm.trans (congrArg (chartRes F l) hc.symm)).symm
    refine Eq.trans ?_ (map_sum (chartRes F l) _ _).symm
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Eq.trans ?_ (map_smulₛₗ (chartRes F l) _ _).symm
    refine congrArg₂ (· • ·) rfl ?_
    exact (chartRes_chartRes_of_comp_eq F (Category.assoc l m f).symm (s j)).symm

/-- On a Noetherian algebraic space covered by the affine chart `V₀`, for `F` cartesian on
affine charts and `M'` finitely generated, `chartSpanSubmodule F M'` is coherent. -/
theorem isCoherent_chartSpanSubmodule (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (F : Modules.{u, u} B S hS X hX)
    (hF : IsCartesianOnAffineCharts F)
    (hLN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {V₀ : SmallEtale B S hS X} (hV₀ : IsAffine (chartScheme V₀))
    (hcov : (SmallEtale.topology B S hS X).CoversTop (fun _ : PUnit.{u + 2} => V₀))
    {M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))} (hM' : M'.FG) :
    IsCoherent B S hS X hX (chartSpanSubmodule F M').toSheafOfModules := by
  have : Fact (HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
    ⟨hLN⟩
  have hcart := isCartesianOnAffineCharts_chartSpanSubmodule hZ hqs F hF hV₀ hM'
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType_of_isCartesian_of_isLocallyNoetherian
    B S hS X hX _ hcart).2
      ⟨(isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX _).2 hcart,
        isFiniteType_chartSpanSubmodule F hF hLN hcov hM' hcart⟩

/-! ### The colimit of the coherent submodules -/

section Colimit

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- Let `X` be a Noetherian algebraic space over a scheme `S`.  Every quasi-coherent
`𝒪_X`-module `F` is the filtered colimit of its coherent submodules: the coherent submodules of `F`
form a filtered category, and the cocone of their inclusions into `F` is a colimit cocone. -/
@[stacks 07UV]
theorem isFiltered_and_nonempty_isColimit_coherentSubobjectCocone
    (terminal_mem : B.Contains (⊤_ Scheme.{u})) (noetherian : IsNoetherian B S hS terminal_mem X)
    (F : Modules.{u, u} B S hS X hX) [hFq : F.IsQuasicoherentOnSite] :
    IsFiltered (CoherentSubobject B S hS X hX F) ∧
      Nonempty (IsColimit (coherentSubobjectCocone B S hS X hX F)) := by
  have _ : Fact (HasEtaleLocalProperty B S hS X
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨noetherian.2.2⟩
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X hX).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS X)
    infer_instance
  have _ : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X hX) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have hfil : IsFiltered (CoherentSubobject B S hS X hX F) :=
    isFiltered_coherentSubobject B S hS X hX F
  have htop : (⨆ G : CoherentSubobject B S hS X hX F, G.obj) = ⊤ := by
    classical
    obtain ⟨V₀, hV₀N, hsurjP, -⟩ :=
      exists_surjective_isNoetherianAffineChart B S hS terminal_mem ⟨X, hX⟩ noetherian
    have hV₀ : IsAffine (chartScheme V₀) := hV₀N.1
    have hcov := SmallEtale.coversTop_of_isSurjective B S hS X hX V₀
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX _ _).1 hsurjP)
    have hF := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX F hFq
    set T := ⨆ G : CoherentSubobject B S hS X hX F, G.obj with hT
    have hle : ∀ (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))), M'.FG →
        Subobject.mk (chartSpanSubmodule F M').ι ≤ T := fun M' hM' =>
      le_iSup_of_le (⟨Subobject.mk (chartSpanSubmodule F M').ι,
          isCoherent_of_iso B S hS hX (Subobject.underlyingIso (chartSpanSubmodule F M').ι).symm
          (isCoherent_chartSpanSubmodule terminal_mem noetherian.2.1 F hF noetherian.2.2 hV₀ hcov
            hM')⟩ :
          CoherentSubobject B S hS X hX F) le_rfl
    have hfac : ∀ (M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) (hM' : M'.FG),
        ((Subobject.underlyingIso (chartSpanSubmodule F M').ι).inv ≫
          Subobject.ofLE _ T (hle M' hM')) ≫ T.arrow = (chartSpanSubmodule F M').ι := by
      intro M' hM'
      rw [Category.assoc, Subobject.ofLE_arrow, Subobject.underlyingIso_arrow]
    have hepi : Epi T.arrow := by
      refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {Z} x => ?_⟩
      obtain ⟨Sv, hSv, hfacS⟩ :=
        exists_covering_through_noetherianAffine B S hS X hX noetherian.2.2 Z
      refine (SmallEtale.topology B S hS X).superset_covering ?_ hSv
      intro Y g hg
      obtain ⟨A, l, m, ⟨hA, -⟩, rfl⟩ := hfacS g hg
      refine Sieve.downward_closed _ ?_ l
      obtain ⟨ι, hι, P, q, hP, hq⟩ :=
        exists_finite_affine_cover_prod terminal_mem noetherian.2.1 hA hV₀
      obtain ⟨M', hM', hmem⟩ :=
        exists_fg_mem_chartSpanSections F hF hV₀ P q hP hq (chartRes F m x)
      let k : (chartSpanSubmodule F M').toSheafOfModules.val.obj (op A) :=
        (⟨chartRes F m x, hmem⟩ : chartSpanSections F M' A)
      refine ⟨(((Subobject.underlyingIso (chartSpanSubmodule F M').ι).inv ≫
        Subobject.ofLE _ T (hle M' hM')).val.app (op A)) k, ?_⟩
      exact congrArg (fun φ => φ.val.app (op A) k) (hfac M' hM')
    have : IsIso T.arrow := isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow T
  exact ⟨hfil, ⟨isColimitSubobjectCocone_of_iSup_eq_top (coherentSubobjectProperty B S hS X hX F)
    htop⟩⟩

end Colimit

end AlgebraicGeometry.Space

end
