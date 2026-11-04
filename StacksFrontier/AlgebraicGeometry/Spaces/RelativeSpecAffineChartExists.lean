module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecAffineChartHom

/-!
# Every algebra map out of the sections over an affine chart comes from a morphism of algebras

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `𝒜` a quasi-coherent sheaf of
commutative `𝒪_X`-algebras, `V` an affine étale chart of `X`, and `x` a point of `X` with values
in `T` which factors through `v : T ⟶ V`.  A ring map `β : 𝒜(V) ⟶ Γ(T)` which is `v^*` on `Γ(V)`
is the chart reading (`AlgebraicGeometry.Space.chartEval`) of a morphism of `𝒪_X`-algebras
`α : 𝒜 ⟶ x_* 𝒪_T`.  This is the existence half of the identification of such morphisms with the
`Γ(V)`-algebra maps `𝒜(V) ⟶ Γ(T)`; the uniqueness half is
`AlgebraicGeometry.Space.algebraHom_ext_of_chartEval`.

## Implementation notes

At a chart `W` of `X` the value of `α` on a section `s ∈ 𝒜(W)` is a function on `T ×_X W`,
glued for the big fppf topology.  The two maps `T ×_X W ⟶ V` and `T ×_X W ⟶ W` factor through the
chart `V ×_X W` (`AlgebraicGeometry.Space.pairChartMap`), and on a covering sieve that map factors
through affine charts `U` of `X` mapping to `V ×_X W`
(`AlgebraicGeometry.Space.exists_fibreDatum_sieve`).  On such a member the value is the local
ring map `AlgebraicGeometry.Space.chartPsi` of `U` — the unique ring map `𝒜(U) ⟶ Γ` which is the
pullback of functions on `𝒪(U)` and `β` followed by pullback on the sections restricted from `V`,
which exists because `𝒜(U) = 𝒪(U) ⊗_{𝒪(V)} 𝒜(V)`
(`AlgebraicGeometry.Space.AlgebraSheaf.exists_chartLift`) — applied to `s|_U`.  Two such local
values at the same point agree, by comparing both on affine charts covering the fibre product of
the two charts over `V ×_X W` (`AlgebraicGeometry.Space.FibreDatum.val_eq`), so they glue
(`AlgebraicGeometry.Space.fibreGlue`).  Naturality in `W`, compatibility with the structure maps,
and the reading at `V` itself (through the diagonal `V ⟶ V ×_X V`) are each checked on the same
local values.

## Main results

* `AlgebraicGeometry.Space.chartExtension`: the morphism of algebras `𝒜 ⟶ x_* 𝒪_T`.
* `AlgebraicGeometry.Space.chartEval_chartExtension`: its reading at `V` is `β`.
* `AlgebraicGeometry.Space.exists_chartEval_eq`: the existence statement.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section LocalMap

variable {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
  (hA : A.IsQuasicoherent) {V : SmallEtale B S hS X.1} [hV : IsAffine (chartScheme V)]
  {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
  (β : A.right.obj.obj (op V) ⟶ Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  (hβ : ∀ r : (structureSheaf B S hS X.1 X.2).obj.obj (op V),
    β (A.algebraMap (op V) r) = ((BigFppfOver.toScheme B S hS).map v).appTop r)

omit hV in
include hβ in
/-- For an affine chart `U` mapping to `V` by `κ` and a point `c : T'' ⟶ U` over `e ≫ v`, the
functions `c^*(r|_U)` and `e^*(β(r))` agree for every regular function `r` on `V`. -/
theorem chartPsi_compat {U : SmallEtale B S hS X.1} (κ : U ⟶ V) {T'' : BigFppfOver B S hS}
    (e : T'' ⟶ T) (c : T'' ⟶ U.obj.left) (w : c ≫ κ.hom.left = e ≫ v)
    (r : chartRing B S hS X.1 X.2 V) :
    ((BigFppfOver.toScheme B S hS).map c).appTop (chartRestrict (hF := X.2) κ r) =
      ((BigFppfOver.toScheme B S hS).map e).appTop (β (A.algebraMap (op V) r)) := by
  have h2 : ((BigFppfOver.toScheme B S hS).map c).appTop (chartRestrict (hF := X.2) κ r) =
      ((BigFppfOver.toScheme B S hS).map (c ≫ κ.hom.left)).appTop
        (r : Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤)) := rfl
  rw [h2, w]
  exact congrArg (((BigFppfOver.toScheme B S hS).map e).appTop) (hβ r).symm

/-- **The local ring map** `𝒜(U) ⟶ Γ(T'')` attached to an affine chart `U` mapping to `V` by `κ`
and a point `c : T'' ⟶ U` over the point `e ≫ v` of `V`: the unique ring map which is `c^*` on
the regular functions on `U` and `e^* ∘ β` on the sections restricted from `V`. -/
def chartPsi {U : SmallEtale B S hS X.1} [hU : IsAffine (chartScheme U)] (κ : U ⟶ V)
    {T'' : BigFppfOver B S hS} (e : T'' ⟶ T) (c : T'' ⟶ U.obj.left)
    (w : c ≫ κ.hom.left = e ≫ v) :
    A.right.obj.obj (op U) →+* Γ((BigFppfOver.toScheme B S hS).obj T'', ⊤) :=
  Classical.choose (AlgebraSheaf.exists_chartLift hA hU hV κ
    ((BigFppfOver.toScheme B S hS).map c).appTop.hom
    (((BigFppfOver.toScheme B S hS).map e).appTop.hom.comp β.hom)
    (chartPsi_compat B S hS A v β hβ κ e c w))

/-- On the image of a regular function `b` on `U`, the local ring map `chartPsi` is `c^* b`. -/
theorem chartPsi_algebraMap {U : SmallEtale B S hS X.1} [hU : IsAffine (chartScheme U)]
    (κ : U ⟶ V) {T'' : BigFppfOver B S hS} (e : T'' ⟶ T) (c : T'' ⟶ U.obj.left)
    (w : c ≫ κ.hom.left = e ≫ v) (b : (structureSheaf B S hS X.1 X.2).obj.obj (op U)) :
    chartPsi B S hS A hA v β hβ κ e c w (A.algebraMap (op U) b) =
      ((BigFppfOver.toScheme B S hS).map c).appTop b :=
  (Classical.choose_spec (AlgebraSheaf.exists_chartLift hA hU hV κ
    ((BigFppfOver.toScheme B S hS).map c).appTop.hom
    (((BigFppfOver.toScheme B S hS).map e).appTop.hom.comp β.hom)
    (chartPsi_compat B S hS A v β hβ κ e c w))).1 b

/-- On the restriction `a|_U` of a section `a ∈ 𝒜(V)`, the local ring map `chartPsi` is
`e^*(β(a))`. -/
theorem chartPsi_map {U : SmallEtale B S hS X.1} [hU : IsAffine (chartScheme U)]
    (κ : U ⟶ V) {T'' : BigFppfOver B S hS} (e : T'' ⟶ T) (c : T'' ⟶ U.obj.left)
    (w : c ≫ κ.hom.left = e ≫ v) (a : A.right.obj.obj (op V)) :
    chartPsi B S hS A hA v β hβ κ e c w (A.right.obj.map κ.op a) =
      ((BigFppfOver.toScheme B S hS).map e).appTop (β a) :=
  (Classical.choose_spec (AlgebraSheaf.exists_chartLift hA hU hV κ
    ((BigFppfOver.toScheme B S hS).map c).appTop.hom
    (((BigFppfOver.toScheme B S hS).map e).appTop.hom.comp β.hom)
    (chartPsi_compat B S hS A v β hβ κ e c w))).2 a

/-- `chartPsi` is characterised by its values on the two kinds of generators. -/
theorem chartPsi_unique {U : SmallEtale B S hS X.1} [hU : IsAffine (chartScheme U)]
    (κ : U ⟶ V) {T'' : BigFppfOver B S hS} (e : T'' ⟶ T) (c : T'' ⟶ U.obj.left)
    (w : c ≫ κ.hom.left = e ≫ v)
    (ψ : A.right.obj.obj (op U) →+* Γ((BigFppfOver.toScheme B S hS).obj T'', ⊤))
    (h₁ : ∀ b, ψ (A.algebraMap (op U) b) = ((BigFppfOver.toScheme B S hS).map c).appTop b)
    (h₂ : ∀ a, ψ (A.right.obj.map κ.op a) = ((BigFppfOver.toScheme B S hS).map e).appTop (β a)) :
    ψ = chartPsi B S hS A hA v β hβ κ e c w :=
  AlgebraSheaf.ringHom_ext_chart hA hU hV κ
    (fun b => (h₁ b).trans (chartPsi_algebraMap B S hS A hA v β hβ κ e c w b).symm)
    (fun a => (h₂ a).trans (chartPsi_map B S hS A hA v β hβ κ e c w a).symm)

/-- The local ring map `chartPsi` depends only on `κ`, `e` and `c`, not on the proof of
compatibility. -/
theorem chartPsi_congr {U : SmallEtale B S hS X.1} [hU : IsAffine (chartScheme U)]
    {κ κ' : U ⟶ V} (hκ : κ = κ') {T'' : BigFppfOver B S hS} {e e' : T'' ⟶ T} (he : e = e')
    {c c' : T'' ⟶ U.obj.left} (hc : c = c') (w : c ≫ κ.hom.left = e ≫ v)
    (w' : c' ≫ κ'.hom.left = e' ≫ v) :
    chartPsi B S hS A hA v β hβ κ e c w = chartPsi B S hS A hA v β hβ κ' e' c' w' := by
  subst hκ he hc
  rfl

/-- **Restriction**: the local ring map at `c' ≫ ν` is the local ring map at `c'` composed with
restriction along `ν`. -/
theorem chartPsi_restrict {U U' : SmallEtale B S hS X.1} [IsAffine (chartScheme U)]
    [IsAffine (chartScheme U')] (κ : U ⟶ V) (ν : U' ⟶ U) {T'' : BigFppfOver B S hS}
    (e : T'' ⟶ T) (c' : T'' ⟶ U'.obj.left) (w : (c' ≫ ν.hom.left) ≫ κ.hom.left = e ≫ v)
    (w' : c' ≫ (ν ≫ κ).hom.left = e ≫ v) (s : A.right.obj.obj (op U)) :
    chartPsi B S hS A hA v β hβ κ e (c' ≫ ν.hom.left) w s =
      chartPsi B S hS A hA v β hβ (ν ≫ κ) e c' w' (A.right.obj.map ν.op s) := by
  have := chartPsi_unique B S hS A hA v β hβ κ e (c' ≫ ν.hom.left) w
    ((chartPsi B S hS A hA v β hβ (ν ≫ κ) e c' w').comp (A.right.obj.map ν.op).hom)
    (fun b => by
      show chartPsi B S hS A hA v β hβ (ν ≫ κ) e c' w'
        (A.right.obj.map ν.op (A.algebraMap (op U) b)) = _
      rw [A.algebraMap_natural, chartPsi_algebraMap]
      rfl)
    (fun a => by
      show chartPsi B S hS A hA v β hβ (ν ≫ κ) e c' w'
        (A.right.obj.map ν.op (A.right.obj.map κ.op a)) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, chartPsi_map])
  exact (RingHom.congr_fun this s).symm

/-- **Pullback**: pulling the local ring map back along `g : T''' ⟶ T''` is the local ring map of
the pulled-back point. -/
theorem chartPsi_pullback {U : SmallEtale B S hS X.1} [IsAffine (chartScheme U)] (κ : U ⟶ V)
    {T'' T''' : BigFppfOver B S hS} (g : T''' ⟶ T'') (e : T'' ⟶ T) (c : T'' ⟶ U.obj.left)
    (w : c ≫ κ.hom.left = e ≫ v) (w' : (g ≫ c) ≫ κ.hom.left = (g ≫ e) ≫ v)
    (s : A.right.obj.obj (op U)) :
    ((BigFppfOver.toScheme B S hS).map g).appTop (chartPsi B S hS A hA v β hβ κ e c w s) =
      chartPsi B S hS A hA v β hβ κ (g ≫ e) (g ≫ c) w' s := by
  have := chartPsi_unique B S hS A hA v β hβ κ (g ≫ e) (g ≫ c) w'
    (((BigFppfOver.toScheme B S hS).map g).appTop.hom.comp (chartPsi B S hS A hA v β hβ κ e c w))
    (fun b => by
      show ((BigFppfOver.toScheme B S hS).map g).appTop
        (chartPsi B S hS A hA v β hβ κ e c w (A.algebraMap (op U) b)) = _
      rw [chartPsi_algebraMap]
      rfl)
    (fun a => by
      show ((BigFppfOver.toScheme B S hS).map g).appTop
        (chartPsi B S hS A hA v β hβ κ e c w (A.right.obj.map κ.op a)) = _
      rw [chartPsi_map]
      rfl)
  exact RingHom.congr_fun this s

/-- Restricting a section of `𝒜` along `b` and then along `a` is restricting it along `a ≫ b`. -/
theorem map_map_apply {U₁ U₂ U₃ : SmallEtale B S hS X.1} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃)
    (s : A.right.obj.obj (op U₃)) :
    A.right.obj.map a.op (A.right.obj.map b.op s) = A.right.obj.map (a ≫ b).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

/-! ### The fibre product with a chart and its local data -/

variable (x : X.1.obj (op T)) (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)

/-- The chart of `X` through which both projections of `T ×_X W` factor: `V ×_X W`. -/
abbrev pairChart (W : SmallEtale B S hS X.1) : SmallEtale B S hS X.1 :=
  SmallEtale.prodObj B S hS X.1 V W

omit hV in
include hxv in
/-- The maps `T ×_X W ⟶ V` and `T ×_X W ⟶ W` agree after composing to `X`. -/
theorem pairChart_cond (W : SmallEtale B S hS X.1) :
    yoneda.map ((relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom ≫ v) ≫ V.obj.hom =
      yoneda.map ((relativelyRepresentable_specPointOver B S hS T x).snd W.obj.hom) ≫
        W.obj.hom := by
  rw [Functor.map_comp, Functor.relativelyRepresentable.map_fst', Category.assoc, ← hxv]
  exact (relativelyRepresentable_specPointOver B S hS T x).w W.obj.hom

/-- The map `T ×_X W ⟶ V ×_X W`. -/
def pairChartMap (W : SmallEtale B S hS X.1) :
    (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom ⟶
      (pairChart (V := V) B S hS W).obj.left :=
  V.property.rep.lift' _ _ (pairChart_cond B S hS v x hxv W)

omit hV in
/-- The map `T ×_X W ⟶ V ×_X W` followed by the first projection is `T ×_X W ⟶ T ⟶ V`. -/
theorem pairChartMap_fst (W : SmallEtale B S hS X.1) :
    pairChartMap B S hS v x hxv W ≫ (SmallEtale.prodFst B S hS X.1 V W).hom.left =
      (relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom ≫ v :=
  Functor.relativelyRepresentable.lift'_fst _ _ _ _

omit hV in
/-- The map `T ×_X W ⟶ V ×_X W` followed by the second projection is the projection
`T ×_X W ⟶ W`. -/
theorem pairChartMap_snd (W : SmallEtale B S hS X.1) :
    pairChartMap B S hS v x hxv W ≫ (SmallEtale.prodSnd B S hS X.1 V W).hom.left =
      (relativelyRepresentable_specPointOver B S hS T x).snd W.obj.hom :=
  Functor.relativelyRepresentable.lift'_snd _ _ _ _

/-- **A local datum** for a point `k` of `T ×_X W`: an affine chart `U` over `V ×_X W` and a lift
`c` of `k` to it. -/
structure FibreDatum (W : SmallEtale B S hS X.1) {T'' : BigFppfOver B S hS}
    (k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom) where
  /-- The affine chart. -/
  U : SmallEtale B S hS X.1
  hU : IsAffine (chartScheme U)
  /-- Its map to `V ×_X W`. -/
  μ : U ⟶ pairChart (V := V) B S hS W
  /-- The lift. -/
  c : T'' ⟶ U.obj.left
  hc : k ≫ pairChartMap B S hS v x hxv W = c ≫ μ.hom.left

omit hV in
/-- The lift of a datum, composed with `U ⟶ V ×_X W ⟶ V`, is the point `k` followed by
`T ×_X W ⟶ T ⟶ V`. -/
theorem FibreDatum.w {W : SmallEtale B S hS X.1} {T'' : BigFppfOver B S hS}
    {k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom}
    (d : FibreDatum B S hS v x hxv W k) :
    d.c ≫ (d.μ ≫ SmallEtale.prodFst B S hS X.1 V W).hom.left =
      (k ≫ (relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom) ≫ v := by
  show d.c ≫ d.μ.hom.left ≫ _ = _
  rw [← Category.assoc, ← d.hc, Category.assoc, pairChartMap_fst, Category.assoc]

/-- **The local value** of a section `s ∈ 𝒜(W)` at a datum: the local ring map at the affine chart,
applied to the restriction of `s`. -/
def FibreDatum.val {W : SmallEtale B S hS X.1} {T'' : BigFppfOver B S hS}
    {k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom}
    (d : FibreDatum B S hS v x hxv W k) (s : A.right.obj.obj (op W)) :
    Γ((BigFppfOver.toScheme B S hS).obj T'', ⊤) :=
  have := d.hU
  chartPsi B S hS A hA v β hβ (d.μ ≫ SmallEtale.prodFst B S hS X.1 V W) _ d.c (d.w B S hS v x hxv)
    (A.right.obj.map (d.μ ≫ SmallEtale.prodSnd B S hS X.1 V W).op s)

/-- The pullback of a datum along `g : T₃ ⟶ T''`. -/
def FibreDatum.pull {W : SmallEtale B S hS X.1} {T'' T₃ : BigFppfOver B S hS}
    {k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom}
    (d : FibreDatum B S hS v x hxv W k) (g : T₃ ⟶ T'') :
    FibreDatum B S hS v x hxv W (g ≫ k) where
  U := d.U
  hU := d.hU
  μ := d.μ
  c := g ≫ d.c
  hc := by rw [Category.assoc, d.hc, Category.assoc]

/-- Pulling the local value of a datum back along `g` gives the local value of the pulled-back
datum. -/
theorem FibreDatum.appTop_val {W : SmallEtale B S hS X.1} {T'' T₃ : BigFppfOver B S hS}
    {k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom}
    (d : FibreDatum B S hS v x hxv W k) (g : T₃ ⟶ T'') (s : A.right.obj.obj (op W)) :
    ((BigFppfOver.toScheme B S hS).map g).appTop (d.val B S hS A hA v β hβ x hxv s) =
      (d.pull B S hS v x hxv g).val B S hS A hA v β hβ x hxv s := by
  have := d.hU
  refine (chartPsi_pullback B S hS A hA v β hβ _ g _ d.c (d.w B S hS v x hxv)
    (by rw [Category.assoc, d.w]; simp only [Category.assoc]) _).trans ?_
  exact RingHom.congr_fun (chartPsi_congr B S hS A hA v β hβ rfl (Category.assoc _ _ _).symm rfl
    _ _) _

/-- The local value of a datum pulled back along `g` is the local ring map at any affine chart
`U₃` through which `g ≫ d.c` factors along `ν : U₃ ⟶ d.U`. -/
private theorem fibreDatum_pull_val_eq {W : SmallEtale B S hS X.1} {T'' T₃ : BigFppfOver B S hS}
    {k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom}
    (d : FibreDatum B S hS v x hxv W k) (g : T₃ ⟶ T'') {U₃ : SmallEtale B S hS X.1}
    [IsAffine (chartScheme U₃)] (ν : U₃ ⟶ d.U) (c₃ : T₃ ⟶ U₃.obj.left)
    (e : g ≫ d.c = c₃ ≫ ν.hom.left) (s : A.right.obj.obj (op W)) :
    ∃ w, (d.pull B S hS v x hxv g).val B S hS A hA v β hβ x hxv s =
      chartPsi B S hS A hA v β hβ (ν ≫ d.μ ≫ SmallEtale.prodFst B S hS X.1 V W)
        ((g ≫ k) ≫ (relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom) c₃ w
        (A.right.obj.map (ν ≫ d.μ ≫ SmallEtale.prodSnd B S hS X.1 V W).op s) := by
  have := d.hU
  have w' : (c₃ ≫ ν.hom.left) ≫ (d.μ ≫ SmallEtale.prodFst B S hS X.1 V W).hom.left =
      ((g ≫ k) ≫ (relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom) ≫ v := by
    rw [← e]; exact (d.pull B S hS v x hxv g).w B S hS v x hxv
  have w'' : c₃ ≫ (ν ≫ d.μ ≫ SmallEtale.prodFst B S hS X.1 V W).hom.left =
      ((g ≫ k) ≫ (relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom) ≫ v := by
    rw [← w']; simp only [Category.assoc]; rfl
  refine ⟨w'', ?_⟩
  refine Eq.trans (b := chartPsi B S hS A hA v β hβ (d.μ ≫ SmallEtale.prodFst B S hS X.1 V W) _
    (c₃ ≫ ν.hom.left) w' (A.right.obj.map (d.μ ≫ SmallEtale.prodSnd B S hS X.1 V W).op s))
    (RingHom.congr_fun (chartPsi_congr B S hS A hA v β hβ rfl rfl e _ _) _) ?_
  rw [chartPsi_restrict B S hS A hA v β hβ _ _ _ c₃ w' w'', map_map_apply]

/-- **Independence of the datum**: two data for the same point give the same local value. -/
theorem FibreDatum.val_eq {W : SmallEtale B S hS X.1} {T'' : BigFppfOver B S hS}
    {k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom}
    (d₁ d₂ : FibreDatum B S hS v x hxv W k) (s : A.right.obj.obj (op W)) :
    d₁.val B S hS A hA v β hβ x hxv s = d₂.val B S hS A hA v β hβ x hxv s := by
  have := d₁.hU
  have := d₂.hU
  have hP := (IsPullback.of_hasPullback d₁.μ d₂.μ).map (SmallEtale.toOver B S hS X.1)
  have hcc : d₁.c ≫ (SmallEtale.toOver B S hS X.1).map d₁.μ =
      d₂.c ≫ (SmallEtale.toOver B S hS X.1).map d₂.μ := by
    show d₁.c ≫ d₁.μ.hom.left = d₂.c ≫ d₂.μ.hom.left
    rw [← d₁.hc, ← d₂.hc]
  let ℓ := hP.lift d₁.c d₂.c hcc
  obtain ⟨R, hR, hRf⟩ := exists_covering_affineChart_factor B S hS (Limits.pullback d₁.μ d₂.μ) ℓ
  refine eq_of_appTop_eq_of_mem_topology B S hS hR fun T₃ g hg => ?_
  obtain ⟨U₃, ν, hU₃, c₃, hc₃⟩ := hRf g hg
  have : IsAffine (chartScheme U₃) := hU₃
  rw [d₁.appTop_val, d₂.appTop_val]
  have hl₁ : ℓ ≫ (SmallEtale.toOver B S hS X.1).map (Limits.pullback.fst d₁.μ d₂.μ) = d₁.c :=
    hP.lift_fst d₁.c d₂.c hcc
  have hl₂ : ℓ ≫ (SmallEtale.toOver B S hS X.1).map (Limits.pullback.snd d₁.μ d₂.μ) = d₂.c :=
    hP.lift_snd d₁.c d₂.c hcc
  have e₁ : g ≫ d₁.c = c₃ ≫ (ν ≫ Limits.pullback.fst d₁.μ d₂.μ).hom.left := by
    rw [← hl₁, ← Category.assoc, hc₃, Category.assoc]
    rfl
  have e₂ : g ≫ d₂.c = c₃ ≫ (ν ≫ Limits.pullback.snd d₁.μ d₂.μ).hom.left := by
    rw [← hl₂, ← Category.assoc, hc₃, Category.assoc]
    rfl
  have hcond := Limits.pullback.condition (f := d₁.μ) (g := d₂.μ)
  have hk : (ν ≫ Limits.pullback.fst d₁.μ d₂.μ) ≫ d₁.μ ≫ SmallEtale.prodFst B S hS X.1 V W =
      (ν ≫ Limits.pullback.snd d₁.μ d₂.μ) ≫ d₂.μ ≫ SmallEtale.prodFst B S hS X.1 V W := by
    simp only [Category.assoc, reassoc_of% hcond]
  have hm : (ν ≫ Limits.pullback.fst d₁.μ d₂.μ) ≫ d₁.μ ≫ SmallEtale.prodSnd B S hS X.1 V W =
      (ν ≫ Limits.pullback.snd d₁.μ d₂.μ) ≫ d₂.μ ≫ SmallEtale.prodSnd B S hS X.1 V W := by
    simp only [Category.assoc, reassoc_of% hcond]
  obtain ⟨w₁, h₁⟩ := fibreDatum_pull_val_eq B S hS A hA v β hβ x hxv d₁ g
    (ν ≫ Limits.pullback.fst d₁.μ d₂.μ) c₃ e₁ s
  obtain ⟨w₂, h₂⟩ := fibreDatum_pull_val_eq B S hS A hA v β hβ x hxv d₂ g
    (ν ≫ Limits.pullback.snd d₁.μ d₂.μ) c₃ e₂ s
  rw [h₁, h₂, hm]
  exact RingHom.congr_fun (chartPsi_congr B S hS A hA v β hβ hk rfl rfl _ _) _


/-! ### Gluing the local values over `T ×_X W` -/

omit hV in
/-- There is a covering sieve of `T ×_X W` for the big fppf topology at each of whose members a
local datum exists. -/
theorem exists_fibreDatum_sieve (W : SmallEtale B S hS X.1) :
    ∃ R ∈ BigFppfOver.topology B S hS ((relativelyRepresentable_specPointOver B S hS T x).pullback
      W.obj.hom), ∀ ⦃T'' : BigFppfOver B S hS⦄ (k : T'' ⟶ _), R.arrows k →
        Nonempty (FibreDatum B S hS v x hxv W k) := by
  obtain ⟨R, hR, hRf⟩ := exists_covering_affineChart_factor B S hS (pairChart (V := V) B S hS W)
    (pairChartMap B S hS v x hxv W)
  refine ⟨R, hR, fun T'' k hk => ?_⟩
  obtain ⟨Vj, κ, hVj, kk, hkk⟩ := hRf k hk
  exact ⟨⟨Vj, hVj, κ, kk, hkk⟩⟩

/-- The covering sieve of `T ×_X W` on whose members local data exist. -/
def fibreSieve (W : SmallEtale B S hS X.1) :
    Sieve ((relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom) :=
  Classical.choose (exists_fibreDatum_sieve B S hS v x hxv W)

omit hV in
/-- The sieve `fibreSieve` is a covering sieve for the big fppf topology. -/
theorem fibreSieve_mem (W : SmallEtale B S hS X.1) :
    fibreSieve B S hS v x hxv W ∈ BigFppfOver.topology B S hS _ :=
  (Classical.choose_spec (exists_fibreDatum_sieve B S hS v x hxv W)).1

/-- The chosen datum at a member of the sieve. -/
def fibreSieveDatum (W : SmallEtale B S hS X.1) {T'' : BigFppfOver B S hS}
    {k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom}
    (hk : (fibreSieve B S hS v x hxv W).arrows k) : FibreDatum B S hS v x hxv W k :=
  Classical.choice ((Classical.choose_spec (exists_fibreDatum_sieve B S hS v x hxv W)).2 k hk)

/-- The family of local values of `s` on the sieve. -/
def fibreFamily (W : SmallEtale B S hS X.1) (s : A.right.obj.obj (op W)) :
    Presieve.FamilyOfElements ((BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat)
      (fibreSieve B S hS v x hxv W).arrows :=
  fun _ _ hk => (fibreSieveDatum B S hS v x hxv W hk).val B S hS A hA v β hβ x hxv s

/-- The family of local values of `s` is compatible. -/
theorem fibreFamily_compatible (W : SmallEtale B S hS X.1) (s : A.right.obj.obj (op W)) :
    (fibreFamily B S hS A hA v β hβ x hxv W s).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z k g hk
  show _ = ((BigFppfOver.toScheme B S hS).map g).appTop
    ((fibreSieveDatum B S hS v x hxv W hk).val B S hS A hA v β hβ x hxv s)
  rw [FibreDatum.appTop_val]
  exact FibreDatum.val_eq B S hS A hA v β hβ x hxv _ _ s

/-- **The glued function** of `s ∈ 𝒜(W)` on `T ×_X W`. -/
def fibreGlue (W : SmallEtale B S hS X.1) (s : A.right.obj.obj (op W)) :
    Γ((BigFppfOver.toScheme B S hS).obj
      ((relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom), ⊤) :=
  ((isSheaf_gammaBigFppfOver B S hS) _ (fibreSieve_mem B S hS v x hxv W)).amalgamate
    (fibreFamily B S hS A hA v β hβ x hxv W s) (fibreFamily_compatible B S hS A hA v β hβ x hxv W s)

/-- **The glued function restricts to every local value**, for any datum at any point. -/
theorem appTop_fibreGlue (W : SmallEtale B S hS X.1) {T'' : BigFppfOver B S hS}
    (k : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom)
    (d : FibreDatum B S hS v x hxv W k) (s : A.right.obj.obj (op W)) :
    ((BigFppfOver.toScheme B S hS).map k).appTop (fibreGlue B S hS A hA v β hβ x hxv W s) =
      d.val B S hS A hA v β hβ x hxv s := by
  have hR := (BigFppfOver.topology B S hS).pullback_stable k (fibreSieve_mem B S hS v x hxv W)
  refine eq_of_appTop_eq_of_mem_topology B S hS hR fun T₃ g hg => ?_
  have hamal :=
    ((isSheaf_gammaBigFppfOver B S hS) _ (fibreSieve_mem B S hS v x hxv W)).isAmalgamation
      (fibreFamily_compatible B S hS A hA v β hβ x hxv W s) (g ≫ k) hg
  rw [d.appTop_val]
  refine Eq.trans ?_ ((hamal.trans (FibreDatum.val_eq B S hS A hA v β hβ x hxv _ _ s)))
  show _ = ((BigFppfOver.toScheme B S hS).map (g ≫ k)).appTop _
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

omit hV in
/-- Two functions on `T ×_X W` are equal if their pullbacks to every member of `fibreSieve`
are. -/
theorem fibreGlue_ext (W : SmallEtale B S hS X.1)
    {f g : Γ((BigFppfOver.toScheme B S hS).obj
      ((relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom), ⊤)}
    (h : ∀ ⦃T'' : BigFppfOver B S hS⦄ (k : T'' ⟶ _), (fibreSieve B S hS v x hxv W).arrows k →
      ((BigFppfOver.toScheme B S hS).map k).appTop f =
        ((BigFppfOver.toScheme B S hS).map k).appTop g) : f = g :=
  eq_of_appTop_eq_of_mem_topology B S hS (fibreSieve_mem B S hS v x hxv W) h

/-- The glued function as a ring map `𝒜(W) ⟶ Γ(T ×_X W)`. -/
def fibreGlueHom (W : SmallEtale B S hS X.1) :
    A.right.obj.obj (op W) →+*
      Γ((BigFppfOver.toScheme B S hS).obj
        ((relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom), ⊤) where
  toFun := fibreGlue B S hS A hA v β hβ x hxv W
  map_one' := fibreGlue_ext B S hS v x hxv W fun _ k hk => by
    rw [appTop_fibreGlue B S hS A hA v β hβ x hxv W k (fibreSieveDatum B S hS v x hxv W hk),
      map_one, FibreDatum.val, map_one, map_one]
  map_mul' s s' := fibreGlue_ext B S hS v x hxv W fun _ k hk => by
    rw [map_mul,
      appTop_fibreGlue B S hS A hA v β hβ x hxv W k (fibreSieveDatum B S hS v x hxv W hk),
      appTop_fibreGlue B S hS A hA v β hβ x hxv W k (fibreSieveDatum B S hS v x hxv W hk),
      appTop_fibreGlue B S hS A hA v β hβ x hxv W k (fibreSieveDatum B S hS v x hxv W hk),
      FibreDatum.val, FibreDatum.val, FibreDatum.val, map_mul, map_mul]
  map_zero' := fibreGlue_ext B S hS v x hxv W fun _ k hk => by
    rw [appTop_fibreGlue B S hS A hA v β hβ x hxv W k (fibreSieveDatum B S hS v x hxv W hk),
      map_zero, FibreDatum.val, map_zero, map_zero]
  map_add' s s' := fibreGlue_ext B S hS v x hxv W fun _ k hk => by
    rw [map_add,
      appTop_fibreGlue B S hS A hA v β hβ x hxv W k (fibreSieveDatum B S hS v x hxv W hk),
      appTop_fibreGlue B S hS A hA v β hβ x hxv W k (fibreSieveDatum B S hS v x hxv W hk),
      appTop_fibreGlue B S hS A hA v β hβ x hxv W k (fibreSieveDatum B S hS v x hxv W hk),
      FibreDatum.val, FibreDatum.val, FibreDatum.val, map_add, map_add]

/-! ### Naturality, structure maps, and the morphism of algebras -/

/-- The morphism `V ×_X W' ⟶ V ×_X W` induced by a morphism of charts `w : W' ⟶ W`. -/
def pairChartHom {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W) :
    pairChart (V := V) B S hS W' ⟶ pairChart (V := V) B S hS W :=
  (Limits.BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 V W)
    (SmallEtale.prodFst B S hS X.1 V W') (SmallEtale.prodSnd B S hS X.1 V W' ≫ w)).1

omit hV in
/-- The morphism `V ×_X W' ⟶ V ×_X W` commutes with the first projections. -/
theorem pairChartHom_fst {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W) :
    pairChartHom B S hS w ≫ SmallEtale.prodFst B S hS X.1 V W =
      SmallEtale.prodFst B S hS X.1 V W' :=
  (Limits.BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 V W)
    (SmallEtale.prodFst B S hS X.1 V W') (SmallEtale.prodSnd B S hS X.1 V W' ≫ w)).2.1

omit hV in
/-- The morphism `V ×_X W' ⟶ V ×_X W` followed by the second projection is the second
projection followed by `w`. -/
theorem pairChartHom_snd {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W) :
    pairChartHom B S hS w ≫ SmallEtale.prodSnd B S hS X.1 V W =
      SmallEtale.prodSnd B S hS X.1 V W' ≫ w :=
  (Limits.BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 V W)
    (SmallEtale.prodFst B S hS X.1 V W') (SmallEtale.prodSnd B S hS X.1 V W' ≫ w)).2.2

omit hV in
/-- Points of `V ×_X W` are determined by their two projections. -/
theorem pairChart_hom_ext (W : SmallEtale B S hS X.1) {T'' : BigFppfOver B S hS}
    {a b : T'' ⟶ (pairChart (V := V) B S hS W).obj.left}
    (h₁ : a ≫ (SmallEtale.prodFst B S hS X.1 V W).hom.left =
      b ≫ (SmallEtale.prodFst B S hS X.1 V W).hom.left)
    (h₂ : a ≫ (SmallEtale.prodSnd B S hS X.1 V W).hom.left =
      b ≫ (SmallEtale.prodSnd B S hS X.1 V W).hom.left) : a = b :=
  Functor.relativelyRepresentable.hom_ext' _ h₁ h₂

/-- The base change `T ×_X W' ⟶ T ×_X W` of a morphism of charts. -/
def fibreHom {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W) :
    (relativelyRepresentable_specPointOver B S hS T x).pullback W'.obj.hom ⟶
      (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom :=
  (relativelyRepresentable_specPointOver B S hS T x).lift
    ((relativelyRepresentable_specPointOver B S hS T x).fst W'.obj.hom)
    ((relativelyRepresentable_specPointOver B S hS T x).snd W'.obj.hom ≫ w.hom.left) (by
      refine ((relativelyRepresentable_specPointOver B S hS T x).isPullback W'.obj.hom).w.trans ?_
      rw [Functor.map_comp, Category.assoc, CostructuredArrow.w w.hom])

/-- The morphism `T ×_X W' ⟶ T ×_X W` commutes with the projections to `T`, as morphisms of
presheaves. -/
theorem fibreHom_fst {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W) :
    yoneda.map (fibreHom B S hS x w) ≫
        (relativelyRepresentable_specPointOver B S hS T x).fst W.obj.hom =
      (relativelyRepresentable_specPointOver B S hS T x).fst W'.obj.hom :=
  Functor.relativelyRepresentable.lift_fst _ _ _ _

/-- The morphism `T ×_X W' ⟶ T ×_X W` followed by the projection to `W` is the projection to `W'`
followed by `w`. -/
theorem fibreHom_snd {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W) :
    fibreHom B S hS x w ≫ (relativelyRepresentable_specPointOver B S hS T x).snd W.obj.hom =
      (relativelyRepresentable_specPointOver B S hS T x).snd W'.obj.hom ≫ w.hom.left :=
  Functor.relativelyRepresentable.lift_snd _ _ _ _

/-- The morphism `T ×_X W' ⟶ T ×_X W` commutes with the projections to `T`. -/
theorem fibreHom_fst' {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W) :
    fibreHom B S hS x w ≫ (relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom =
      (relativelyRepresentable_specPointOver B S hS T x).fst' W'.obj.hom := by
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, Functor.relativelyRepresentable.map_fst',
    Functor.relativelyRepresentable.map_fst', fibreHom_fst]

omit hV in
/-- The maps `T ×_X W ⟶ V ×_X W` are natural in the chart `W`. -/
theorem fibreHom_pairChartMap {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W) :
    fibreHom B S hS x w ≫ pairChartMap B S hS v x hxv W =
      pairChartMap B S hS v x hxv W' ≫ (pairChartHom B S hS (V := V) w).hom.left := by
  refine pairChart_hom_ext B S hS W ?_ ?_
  · rw [Category.assoc, pairChartMap_fst, Category.assoc,
      show (pairChartHom B S hS (V := V) w).hom.left ≫
          (SmallEtale.prodFst B S hS X.1 V W).hom.left =
        (SmallEtale.prodFst B S hS X.1 V W').hom.left from
        congrArg (fun f => f.hom.left) (pairChartHom_fst B S hS (V := V) w),
      pairChartMap_fst, ← Category.assoc, fibreHom_fst']
  · rw [Category.assoc, pairChartMap_snd, Category.assoc,
      show (pairChartHom B S hS (V := V) w).hom.left ≫
          (SmallEtale.prodSnd B S hS X.1 V W).hom.left =
        (SmallEtale.prodSnd B S hS X.1 V W').hom.left ≫ w.hom.left from
        congrArg (fun f => f.hom.left) (pairChartHom_snd B S hS (V := V) w),
      ← Category.assoc, pairChartMap_snd, fibreHom_snd]

/-- **Naturality of the glued functions in the chart.** -/
theorem appTop_fibreHom_fibreGlue {W' W : SmallEtale B S hS X.1} (w : W' ⟶ W)
    (s : A.right.obj.obj (op W)) :
    ((BigFppfOver.toScheme B S hS).map (fibreHom B S hS x w)).appTop
        (fibreGlue B S hS A hA v β hβ x hxv W s) =
      fibreGlue B S hS A hA v β hβ x hxv W' (A.right.obj.map w.op s) := by
  refine fibreGlue_ext B S hS v x hxv W' fun T'' k hk => ?_
  let d' := fibreSieveDatum B S hS v x hxv W' hk
  let d : FibreDatum B S hS v x hxv W (k ≫ fibreHom B S hS x w) :=
    { U := d'.U
      hU := d'.hU
      μ := d'.μ ≫ pairChartHom B S hS w
      c := d'.c
      hc := by
        rw [Category.assoc, fibreHom_pairChartMap, ← Category.assoc, d'.hc, Category.assoc]
        rfl }
  rw [appTop_fibreGlue B S hS A hA v β hβ x hxv W' k d', ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, ← Functor.map_comp,
    appTop_fibreGlue B S hS A hA v β hβ x hxv W _ d]
  have := d'.hU
  show chartPsi B S hS A hA v β hβ ((d'.μ ≫ pairChartHom B S hS w) ≫
      SmallEtale.prodFst B S hS X.1 V W) _ d'.c _
      (A.right.obj.map ((d'.μ ≫ pairChartHom B S hS w) ≫ SmallEtale.prodSnd B S hS X.1 V W).op s) =
    chartPsi B S hS A hA v β hβ (d'.μ ≫ SmallEtale.prodFst B S hS X.1 V W') _ d'.c _
      (A.right.obj.map (d'.μ ≫ SmallEtale.prodSnd B S hS X.1 V W').op (A.right.obj.map w.op s))
  rw [map_map_apply]
  have h₁ : (d'.μ ≫ pairChartHom B S hS w) ≫ SmallEtale.prodFst B S hS X.1 V W =
      d'.μ ≫ SmallEtale.prodFst B S hS X.1 V W' := by
    rw [Category.assoc, pairChartHom_fst]
  have h₂ : (d'.μ ≫ pairChartHom B S hS w) ≫ SmallEtale.prodSnd B S hS X.1 V W =
      (d'.μ ≫ SmallEtale.prodSnd B S hS X.1 V W') ≫ w := by
    rw [Category.assoc, pairChartHom_snd, Category.assoc]
  rw [h₂]
  exact RingHom.congr_fun (chartPsi_congr B S hS A hA v β hβ h₁
    (by rw [Category.assoc, fibreHom_fst']) rfl _ _) _

/-- **The glued functions are compatible with the structure maps.** -/
theorem fibreGlue_algebraMap (W : SmallEtale B S hS X.1)
    (r : (structureSheaf B S hS X.1 X.2).obj.obj (op W)) :
    fibreGlue B S hS A hA v β hβ x hxv W (A.algebraMap (op W) r) =
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_specPointOver B S hS T x).snd W.obj.hom)).appTop r := by
  refine fibreGlue_ext B S hS v x hxv W fun T'' k hk => ?_
  let d := fibreSieveDatum B S hS v x hxv W hk
  have := d.hU
  rw [appTop_fibreGlue B S hS A hA v β hβ x hxv W k d]
  show chartPsi B S hS A hA v β hβ _ _ d.c _
      (A.right.obj.map (d.μ ≫ SmallEtale.prodSnd B S hS X.1 V W).op (A.algebraMap (op W) r)) = _
  rw [A.algebraMap_natural, chartPsi_algebraMap]
  have : d.c ≫ (d.μ ≫ SmallEtale.prodSnd B S hS X.1 V W).hom.left =
      k ≫ (relativelyRepresentable_specPointOver B S hS T x).snd W.obj.hom := by
    show d.c ≫ d.μ.hom.left ≫ _ = _
    rw [← Category.assoc, ← d.hc, Category.assoc, pairChartMap_snd]
  exact congrArg (fun m => ((BigFppfOver.toScheme B S hS).map m).appTop r) this

/-- **The morphism of algebras `𝒜 ⟶ x_* 𝒪_T`** glued from the local values. -/
def chartExtension : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x) where
  right := ObjectProperty.homMk
    { app := fun W => CommRingCat.ofHom (fibreGlueHom B S hS A hA v β hβ x hxv W.unop) ≫
        (pointSectionsIso B S hS T x W.unop).inv
      naturality := fun W₂ W₁ f => by
        ext s
        have hnat := map_comp_pointSectionsIso B S hS x f.unop (fibreHom B S hS x f.unop)
          (fibreHom_fst B S hS x f.unop) (fibreHom_snd B S hS x f.unop)
        have hnat' : (pointSectionsIso B S hS T x W₂.unop).inv ≫
            (pushforwardAlgebra B S hS (specPointOver B S hS T x)).right.obj.map f.unop.op =
            ((BigFppfOver.toScheme B S hS).map (fibreHom B S hS x f.unop)).appTop ≫
              (pointSectionsIso B S hS T x W₁.unop).inv := by
          rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
          exact hnat
        change (pointSectionsIso B S hS T x W₁.unop).inv
            (fibreGlue B S hS A hA v β hβ x hxv W₁.unop (A.right.obj.map f.unop.op s)) =
          (pushforwardAlgebra B S hS (specPointOver B S hS T x)).right.obj.map f.unop.op
            ((pointSectionsIso B S hS T x W₂.unop).inv
              (fibreGlue B S hS A hA v β hβ x hxv W₂.unop s))
        rw [← appTop_fibreHom_fibreGlue]
        exact (ConcreteCategory.congr_hom hnat' _).symm }
  comm U r := by
    change (pointSectionsIso B S hS T x U.unop).inv
        (fibreGlue B S hS A hA v β hβ x hxv U.unop (A.algebraMap U r)) = _
    rw [fibreGlue_algebraMap]
    have h := fSharp_app_comp_pointSectionsIso B S hS T x U.unop
    have h' : (smallEtaleRingedToposHom B S hS (specPointOver B S hS T x).hom).fSharp.hom.app U =
        ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_specPointOver B S hS T x).snd U.unop.obj.hom)).appTop ≫
          (pointSectionsIso B S hS T x U.unop).inv :=
      (Iso.eq_comp_inv _).2 h
    exact (ConcreteCategory.congr_hom h' r).symm

/-- The diagonal chart `V ⟶ V ×_X V`. -/
def pairChartDiag : V ⟶ pairChart (V := V) B S hS V :=
  (Limits.BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 V V) (𝟙 V) (𝟙 V)).1

omit hV in
/-- The diagonal `V ⟶ V ×_X V` followed by the first projection is the identity. -/
theorem pairChartDiag_fst :
    pairChartDiag B S hS (V := V) ≫ SmallEtale.prodFst B S hS X.1 V V = 𝟙 V :=
  (Limits.BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 V V) (𝟙 V) (𝟙 V)).2.1

omit hV in
/-- The diagonal `V ⟶ V ×_X V` followed by the second projection is the identity. -/
theorem pairChartDiag_snd :
    pairChartDiag B S hS (V := V) ≫ SmallEtale.prodSnd B S hS X.1 V V = 𝟙 V :=
  (Limits.BinaryFan.IsLimit.lift' (SmallEtale.prodIsLimit B S hS X.1 V V) (𝟙 V) (𝟙 V)).2.2

omit hV in
/-- The graph `T ⟶ T ×_X V` of `v` followed by the projection to `T` is the identity. -/
theorem chartGraph_fst' :
    chartGraph B S hS V v x hxv ≫
        (relativelyRepresentable_specPointOver B S hS T x).fst' V.obj.hom =
      𝟙 T := by
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, Functor.relativelyRepresentable.map_fst', chartGraph_fst,
    CategoryTheory.Functor.map_id]

/-- **The reading of the glued morphism at `V` is `β`.** -/
theorem chartEval_chartExtension :
    chartEval B S hS A V v x hxv (chartExtension B S hS A hA v β hβ x hxv) = β := by
  ext s
  let d : FibreDatum B S hS v x hxv V (chartGraph B S hS V v x hxv) :=
    { U := V
      hU := hV
      μ := pairChartDiag B S hS
      c := v
      hc := by
        refine pairChart_hom_ext B S hS V ?_ ?_
        · rw [Category.assoc, pairChartMap_fst, ← Category.assoc, chartGraph_fst',
            Category.id_comp, Category.assoc]
          show v = v ≫ (pairChartDiag B S hS ≫ SmallEtale.prodFst B S hS X.1 V V).hom.left
          rw [pairChartDiag_fst]
          rfl
        · rw [Category.assoc, pairChartMap_snd, chartGraph_snd, Category.assoc]
          show v = v ≫ (pairChartDiag B S hS ≫ SmallEtale.prodSnd B S hS X.1 V V).hom.left
          rw [pairChartDiag_snd]
          rfl }
  show ((BigFppfOver.toScheme B S hS).map (chartGraph B S hS V v x hxv)).appTop
      ((pointSectionsIso B S hS T x V).hom ((pointSectionsIso B S hS T x V).inv
        (fibreGlue B S hS A hA v β hβ x hxv V s))) = β s
  rw [Iso.inv_hom_id_apply, appTop_fibreGlue B S hS A hA v β hβ x hxv V _ d]
  show chartPsi B S hS A hA v β hβ
      (pairChartDiag B S hS ≫ SmallEtale.prodFst B S hS X.1 V V) _ v _
      (A.right.obj.map (pairChartDiag B S hS ≫ SmallEtale.prodSnd B S hS X.1 V V).op s) = β s
  rw [RingHom.congr_fun (chartPsi_congr B S hS A hA v β hβ (pairChartDiag_fst B S hS)
    (chartGraph_fst' B S hS v x hxv) rfl _ (by rw [Category.id_comp]; rfl)) _,
    pairChartDiag_snd, chartPsi_map, CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
  rfl

end LocalMap

/-- **Every `Γ(V)`-algebra map out of the sections over an affine chart comes from a morphism of
algebras.**  Let `𝒜` be a quasi-coherent `𝒪_X`-algebra, `V` an affine étale chart of `X` and
`x` a point of `X` with values in `T` through `v : T ⟶ V`.  Every ring map `β : 𝒜(V) ⟶ Γ(T)`
which is `v^*` on `Γ(V)` is the chart reading `AlgebraicGeometry.Space.chartEval` of a morphism of
`𝒪_X`-algebras `𝒜 ⟶ x_* 𝒪_T`.

With `AlgebraicGeometry.Space.algebraHom_ext_of_chartEval` this says that the chart reading is a
bijection onto those ring maps. -/
theorem exists_chartEval_eq {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (V : SmallEtale B S hS X.1) [IsAffine (chartScheme V)]
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (β : A.right.obj.obj (op V) ⟶ Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (hβ : chartAlgebraMap B S hS A V ≫ β = ((BigFppfOver.toScheme B S hS).map v).appTop) :
    ∃ α, AlgebraicGeometry.Space.chartEval B S hS A V v x hxv α = β :=
  ⟨chartExtension B S hS A hA v β (fun r => ConcreteCategory.congr_hom hβ r) x hxv,
    chartEval_chartExtension B S hS A hA v β (fun r => ConcreteCategory.congr_hom hβ r) x hxv⟩

end AlgebraicGeometry.Space

end
