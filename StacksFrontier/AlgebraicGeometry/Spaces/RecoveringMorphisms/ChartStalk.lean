module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.InverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.TwoIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# Stalks of chart maps over a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `x̄` a geometric point of `X`.  For an
étale chart `V` of `Y`, the presheaf `AlgebraicGeometry.Space.chartFiber` of chart maps over `f`
into `V` has a stalk at `x̄`: germs of chart maps `U ⟶ V` over `f` on étale neighbourhoods of
`x̄`.  A germ lands in a member of any open cover of the image of a representative, and germs
into a fibre product of charts are pairs of germs.

## Main definitions

* `AlgebraicGeometry.Space.chartStalk`: the stalk at `x̄` of the chart maps over `f` into `V`.

## Main results

* `AlgebraicGeometry.Space.exists_chartStalkMap_eq_of_cover`: a germ whose representative has
  image in the union of a family of opens comes from the restriction of the chart to one of them.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The scheme-level factorization of a morphism into a chart scheme through an open containing
its image. -/
def schemeLiftToOpen {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : SmallEtale B S hS F)
    (O : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens) {T : BigFppfOver B S hS}
    (w : T ⟶ V.obj.left) (h : Set.range ((BigFppfOver.toScheme B S hS).map w) ⊆ O) :
    (BigFppfOver.toScheme B S hS).obj T ⟶ O.toScheme :=
  AlgebraicGeometry.IsOpenImmersion.lift O.ι ((BigFppfOver.toScheme B S hS).map w)
    (by rwa [Scheme.Opens.range_ι])

/-- The factorization `schemeLiftToOpen` composed with the inclusion of the open is the original
morphism. -/
theorem schemeLiftToOpen_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : SmallEtale B S hS F)
    (O : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens) {T : BigFppfOver B S hS}
    (w : T ⟶ V.obj.left) (h : Set.range ((BigFppfOver.toScheme B S hS).map w) ⊆ O) :
    schemeLiftToOpen V O w h ≫ O.ι = (BigFppfOver.toScheme B S hS).map w :=
  AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _

/-- A morphism of the big fppf site into the object underlying an étale chart, whose image lies
in an open of the chart scheme, factors through the restriction of the chart to that open. -/
def liftToOpenRestriction {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : SmallEtale B S hS F)
    (O : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens) {T : BigFppfOver B S hS}
    (w : T ⟶ V.obj.left) (h : Set.range ((BigFppfOver.toScheme B S hS).map w) ⊆ O) :
    T ⟶ (chartOpenRestriction B S hS F V O).obj.left :=
  BigFppfOver.homOfCompEq B S hS (schemeLiftToOpen V O w h) (by
    have h1 := Over.w (chartOpenRestrictionHom B S hS F V O).hom.left
    have h2 : B.inclusion.map (chartOpenRestrictionHom B S hS F V O).hom.left.left = O.ι :=
      chartOpenRestrictionHom_toScheme B S hS F V O
    have h3 : B.inclusion.map w.left ≫ B.inclusion.map V.obj.left.hom =
        B.inclusion.map T.hom := by
      rw [← Functor.map_comp, Over.w w]
    rw [← h1, Functor.map_comp, h2]
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ B.inclusion.map V.obj.left.hom) (schemeLiftToOpen_ι V O w h)).trans h3)

/-- The factorization `liftToOpenRestriction` composed with the restriction morphism of the chart
is the original morphism. -/
@[simp]
theorem liftToOpenRestriction_comp {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : SmallEtale B S hS F) (O : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens)
    {T : BigFppfOver B S hS} (w : T ⟶ V.obj.left)
    (h : Set.range ((BigFppfOver.toScheme B S hS).map w) ⊆ O) :
    liftToOpenRestriction V O w h ≫ (chartOpenRestrictionHom B S hS F V O).hom.left = w := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp]
  refine (congrArg (_ ≫ ·) (chartOpenRestrictionHom_toScheme B S hS F V O)).trans ?_
  rw [liftToOpenRestriction]
  exact (congrArg (· ≫ O.ι) (BigFppfOver.toScheme_map_homOfCompEq B S hS _ _)).trans
    (schemeLiftToOpen_ι V O w h)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- A chart map over `f` into `V` whose image lies in an open `O` of the chart scheme, as a chart
map over `f` into the restriction of `V` to `O`. -/
def chartFiberLiftToOpen (V : SmallEtale B S hS Y.1)
    (O : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens) {U : SmallEtale B S hS X.1}
    (c : (chartFiber B S hS f V).toFunctor.obj (op U))
    (h : Set.range ((BigFppfOver.toScheme B S hS).map c.1) ⊆ O) :
    (chartFiber B S hS f (chartOpenRestriction B S hS Y.1 V O)).toFunctor.obj (op U) :=
  ⟨liftToOpenRestriction V O c.1 h, by
    change U.1.hom ≫ f.hom = yoneda.map (liftToOpenRestriction V O c.1 h) ≫
      (yoneda.map (chartOpenRestrictionHom B S hS Y.1 V O).hom.left ≫ V.1.hom)
    rw [← Category.assoc, ← Functor.map_comp, liftToOpenRestriction_comp]
    exact c.2⟩

/-- Postcomposing `chartFiberLiftToOpen f V O c h` with the restriction morphism of `V` to `O`
recovers `c`. -/
theorem chartFiberMap_chartFiberLiftToOpen (V : SmallEtale B S hS Y.1)
    (O : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens) {U : SmallEtale B S hS X.1}
    (c : (chartFiber B S hS f V).toFunctor.obj (op U))
    (h : Set.range ((BigFppfOver.toScheme B S hS).map c.1) ⊆ O) :
    (chartFiberMap f (chartOpenRestrictionHom B S hS Y.1 V O)).app (op U)
      (chartFiberLiftToOpen f V O c h) = c :=
  Subtype.ext (liftToOpenRestriction_comp V O c.1 h)

variable (x : GeometricPoint B S hS X.1)

/-- The stalk at `x̄` of the chart maps over `f` into an étale chart `V` of `Y`. -/
abbrev chartStalk (V : SmallEtale B S hS Y.1) : Type u :=
  (sitePt x).presheafFiber.obj (chartFiber B S hS f V).toFunctor

/-- Postcomposition with a morphism of charts of `Y`, on stalks. -/
abbrev chartStalkMap {V V' : SmallEtale B S hS Y.1} (j : V' ⟶ V) :
    chartStalk f x V' → chartStalk f x V :=
  (sitePt x).presheafFiber.map (chartFiberMap f j)

/-- **A germ of a chart map lands in a member of any open cover of its image.** If a chart map
`c : U ⟶ V` over `f` has image in the union of the opens `Oᵢ` of the chart scheme of `V`, then
its germ at a lift of `x̄` comes from the restriction of `V` to one of the `Oᵢ`. -/
theorem exists_chartStalkMap_eq_of_cover (V : SmallEtale B S hS Y.1) {U : SmallEtale B S hS X.1}
    (y : (sitePt x).fiber.obj U) (c : (chartFiber B S hS f V).toFunctor.obj (op U))
    {ι : Type u} (O : ι → ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens)
    (hO : ∀ z, ((BigFppfOver.toScheme B S hS).map c.1).base z ∈ ⨆ i, O i) :
    ∃ (i : ι) (t : chartStalk f x (chartOpenRestriction B S hS Y.1 V (O i))),
      chartStalkMap f x (chartOpenRestrictionHom B S hS Y.1 V (O i)) t =
        (sitePt x).toPresheafFiber U y (chartFiber B S hS f V).toFunctor c := by
  let T : Sieve U :=
    { arrows := fun _ k ↦ ∃ i, Set.range ((BigFppfOver.toScheme B S hS).map
        (k.hom.left ≫ c.1)) ⊆ O i
      downward_closed := by
        rintro W W' k ⟨i, hi⟩ k'
        refine ⟨i, ?_⟩
        rintro _ ⟨z, rfl⟩
        refine hi ⟨((BigFppfOver.toScheme B S hS).map k'.hom.left).base z, ?_⟩
        simp only [ObjectProperty.FullSubcategory.comp_hom, CostructuredArrow.comp_left,
          Functor.map_comp, Scheme.Hom.comp_apply] }
  have hT : T ∈ SmallEtale.topology B S hS X.1 U := by
    refine smallEtale_sieve_of_pointwise_covering B S hS X.1 U T fun z ↦ ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hO z)
    let O' := ((BigFppfOver.toScheme B S hS).map c.1) ⁻¹ᵁ (O i)
    have hk : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
        (chartOpenRestrictionHom B S hS X.1 U O')) = O'.ι :=
      chartOpenRestrictionHom_toScheme B S hS X.1 U O'
    refine ⟨chartOpenRestriction B S hS X.1 U O', chartOpenRestrictionHom B S hS X.1 U O',
      ⟨i, ?_⟩, ⟨z, hi⟩, ?_⟩
    · rintro _ ⟨w, rfl⟩
      show ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
        (chartOpenRestrictionHom B S hS X.1 U O') ≫ c.1)).base w ∈ O i
      rw [Functor.map_comp, Scheme.Hom.comp_apply, hk]
      exact w.2
    · rw [hk]
      rfl
  obtain ⟨W, k, ⟨i, hi⟩, y', hy'⟩ := (sitePt x).jointly_surjective T hT y
  let c' : (chartFiber B S hS f V).toFunctor.obj (op W) :=
    (chartFiber B S hS f V).toFunctor.map k.op c
  have hi' : Set.range ((BigFppfOver.toScheme B S hS).map c'.1) ⊆ O i := hi
  refine ⟨i, (sitePt x).toPresheafFiber W y'
    (chartFiber B S hS f (chartOpenRestriction B S hS Y.1 V (O i))).toFunctor
    (chartFiberLiftToOpen f V (O i) c' hi'), ?_⟩
  show ((sitePt x).toPresheafFiber W y' _ ≫ (sitePt x).presheafFiber.map (chartFiberMap f
    (chartOpenRestrictionHom B S hS Y.1 V (O i)))) (chartFiberLiftToOpen f V (O i) c' hi') = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality, types_comp_apply,
    chartFiberMap_chartFiberLiftToOpen]
  show ((chartFiber B S hS f V).toFunctor.map k.op ≫ (sitePt x).toPresheafFiber W y' _) c = _
  rw [GrothendieckTopology.Point.toPresheafFiber_w, hy']

/-! ### Fibre products of charts -/

/-- The pair of two chart maps over `f`, as a chart map over `f` into the fibre product of the two
charts. -/
def chartFiberPair (V V' : SmallEtale B S hS Y.1) {U : SmallEtale B S hS X.1}
    (c : (chartFiber B S hS f V).toFunctor.obj (op U))
    (c' : (chartFiber B S hS f V').toFunctor.obj (op U)) :
    (chartFiber B S hS f (SmallEtale.prodObj B S hS Y.1 V V')).toFunctor.obj (op U) :=
  ⟨V.property.rep.lift' c.1 c'.1 (c.2.symm.trans c'.2), by
    change U.1.hom ≫ f.hom = yoneda.map (V.property.rep.lift' c.1 c'.1 _) ≫
      (yoneda.map (V.property.rep.snd V'.obj.hom) ≫ V'.obj.hom)
    rw [← Category.assoc, ← Functor.map_comp, Functor.relativelyRepresentable.lift'_snd]
    exact c'.2⟩

/-- The first projection of `chartFiberPair f V V' c c'` is `c`. -/
theorem chartFiberMap_prodFst_chartFiberPair (V V' : SmallEtale B S hS Y.1)
    {U : SmallEtale B S hS X.1} (c : (chartFiber B S hS f V).toFunctor.obj (op U))
    (c' : (chartFiber B S hS f V').toFunctor.obj (op U)) :
    (chartFiberMap f (SmallEtale.prodFst B S hS Y.1 V V')).app (op U)
      (chartFiberPair f V V' c c') = c :=
  Subtype.ext (Functor.relativelyRepresentable.lift'_fst _ _ _ _)

/-- The second projection of `chartFiberPair f V V' c c'` is `c'`. -/
theorem chartFiberMap_prodSnd_chartFiberPair (V V' : SmallEtale B S hS Y.1)
    {U : SmallEtale B S hS X.1} (c : (chartFiber B S hS f V).toFunctor.obj (op U))
    (c' : (chartFiber B S hS f V').toFunctor.obj (op U)) :
    (chartFiberMap f (SmallEtale.prodSnd B S hS Y.1 V V')).app (op U)
      (chartFiberPair f V V' c c') = c' :=
  Subtype.ext (Functor.relativelyRepresentable.lift'_snd _ _ _ _)

/-- **Germs into a fibre product of charts: existence.** Two germs of chart maps over `f` into
`V` and `V'` are the projections of a germ into the fibre product of `V` and `V'`. -/
theorem exists_chartStalk_prod (V V' : SmallEtale B S hS Y.1) (t : chartStalk f x V)
    (t' : chartStalk f x V') :
    ∃ p : chartStalk f x (SmallEtale.prodObj B S hS Y.1 V V'),
      chartStalkMap f x (SmallEtale.prodFst B S hS Y.1 V V') p = t ∧
        chartStalkMap f x (SmallEtale.prodSnd B S hS Y.1 V V') p = t' := by
  obtain ⟨U, y, c, rfl⟩ := (sitePt x).toPresheafFiber_jointly_surjective
    (P := (chartFiber B S hS f V).toFunctor) t
  obtain ⟨U', y', c', rfl⟩ := (sitePt x).toPresheafFiber_jointly_surjective
    (P := (chartFiber B S hS f V').toFunctor) t'
  let e : (sitePt x).fiber.Elements := ⟨U, y⟩
  let e' : (sitePt x).fiber.Elements := ⟨U', y'⟩
  let m := IsCofiltered.min e e'
  let a := IsCofiltered.minToLeft e e'
  let b := IsCofiltered.minToRight e e'
  refine ⟨(sitePt x).toPresheafFiber m.1 m.2
    (chartFiber B S hS f (SmallEtale.prodObj B S hS Y.1 V V')).toFunctor (chartFiberPair f V V'
    ((chartFiber B S hS f V).toFunctor.map a.1.op c)
    ((chartFiber B S hS f V').toFunctor.map b.1.op c')), ?_, ?_⟩
  · show ((sitePt x).toPresheafFiber m.1 m.2
      (chartFiber B S hS f (SmallEtale.prodObj B S hS Y.1 V V')).toFunctor ≫
        (sitePt x).presheafFiber.map (chartFiberMap f (SmallEtale.prodFst B S hS Y.1 V V')))
      (chartFiberPair f V V' _ _) = _
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality, types_comp_apply,
      chartFiberMap_prodFst_chartFiberPair]
    show ((chartFiber B S hS f V).toFunctor.map a.1.op ≫
      (sitePt x).toPresheafFiber m.1 m.2 (chartFiber B S hS f V).toFunctor) c = _
    rw [GrothendieckTopology.Point.toPresheafFiber_w, a.2]
  · show ((sitePt x).toPresheafFiber m.1 m.2
      (chartFiber B S hS f (SmallEtale.prodObj B S hS Y.1 V V')).toFunctor ≫
        (sitePt x).presheafFiber.map (chartFiberMap f (SmallEtale.prodSnd B S hS Y.1 V V')))
      (chartFiberPair f V V' _ _) = _
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality, types_comp_apply,
      chartFiberMap_prodSnd_chartFiberPair]
    show ((chartFiber B S hS f V').toFunctor.map b.1.op ≫
      (sitePt x).toPresheafFiber m.1 m.2 (chartFiber B S hS f V').toFunctor) c' = _
    rw [GrothendieckTopology.Point.toPresheafFiber_w, b.2]

/-- **Germs into a fibre product of charts: uniqueness.** A germ of a chart map over `f` into the
fibre product of `V` and `V'` is determined by its two projections. -/
theorem chartStalk_prod_ext (V V' : SmallEtale B S hS Y.1)
    {p p' : chartStalk f x (SmallEtale.prodObj B S hS Y.1 V V')}
    (h₁ : chartStalkMap f x (SmallEtale.prodFst B S hS Y.1 V V') p =
      chartStalkMap f x (SmallEtale.prodFst B S hS Y.1 V V') p')
    (h₂ : chartStalkMap f x (SmallEtale.prodSnd B S hS Y.1 V V') p =
      chartStalkMap f x (SmallEtale.prodSnd B S hS Y.1 V V') p') : p = p' := by
  let P := (chartFiber B S hS f (SmallEtale.prodObj B S hS Y.1 V V')).toFunctor
  let Q := (chartFiber B S hS f V).toFunctor ⨯ (chartFiber B S hS f V').toFunctor
  let φ : P ⟶ Q := prod.lift (chartFiberMap f (SmallEtale.prodFst B S hS Y.1 V V'))
    (chartFiberMap f (SmallEtale.prodSnd B S hS Y.1 V V'))
  have hinj : ∀ U, Function.Injective (φ.app U) := by
    intro U c c' hcc'
    have e₁ := congrArg (fun z ↦ ((prod.fst : Q ⟶ _).app U z).1) hcc'
    have e₂ := congrArg (fun z ↦ ((prod.snd : Q ⟶ _).app U z).1) hcc'
    simp only [φ, ← types_comp_apply, ← NatTrans.comp_app, prod.lift_fst, prod.lift_snd] at e₁ e₂
    exact Subtype.ext (Functor.relativelyRepresentable.hom_ext' _ e₁ e₂)
  have : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS X.1) φ :=
    Presheaf.isLocallyInjective_of_injective _ φ hinj
  apply (sitePt x).toPresheafFiber_map_injective φ
  refine Functor.prodObjMk_ext (P := (sitePt x).presheafFiber (A := Type u)) ?_ ?_
  · rwa [← types_comp_apply ((sitePt x).presheafFiber.map φ), ← Functor.map_comp,
      ← types_comp_apply ((sitePt x).presheafFiber.map φ), ← Functor.map_comp, prod.lift_fst]
  · rwa [← types_comp_apply ((sitePt x).presheafFiber.map φ), ← Functor.map_comp,
      ← types_comp_apply ((sitePt x).presheafFiber.map φ), ← Functor.map_comp, prod.lift_snd]

/-- Postcomposition with a morphism of charts of `Y` whose underlying morphism of schemes is a
monomorphism (for instance an open immersion) is injective on stalks. -/
theorem chartStalkMap_injective {V V' : SmallEtale B S hS Y.1} (j : V' ⟶ V)
    [hj : Mono ((BigFppfOver.toScheme B S hS).map j.hom.left)] :
    Function.Injective (chartStalkMap f x j) := by
  have hinj : ∀ U, Function.Injective ((chartFiberMap f j).app U) := by
    intro U c c' hcc'
    have e := congrArg (fun z ↦ (BigFppfOver.toScheme B S hS).map z.1) hcc'
    simp only [chartFiberMap_app_val, Functor.map_comp] at e
    exact Subtype.ext ((BigFppfOver.toScheme B S hS).map_injective ((cancel_mono _).1 e))
  have : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS X.1) (chartFiberMap f j) :=
    Presheaf.isLocallyInjective_of_injective _ _ hinj
  exact (sitePt x).toPresheafFiber_map_injective _

/-- The morphism of schemes underlying the restriction of a chart to an open is a monomorphism. -/
instance mono_toScheme_chartOpenRestrictionHom (V : SmallEtale B S hS Y.1)
    (O : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens) :
    Mono ((BigFppfOver.toScheme B S hS).map (chartOpenRestrictionHom B S hS Y.1 V O).hom.left) := by
  have h : (BigFppfOver.toScheme B S hS).map (chartOpenRestrictionHom B S hS Y.1 V O).hom.left =
      Scheme.Opens.ι O := chartOpenRestrictionHom_toScheme B S hS Y.1 V O
  have : Mono (Scheme.Opens.ι O) := AlgebraicGeometry.IsOpenImmersion.mono _
  rw [h]
  exact this

/-- Two germs whose images under postcomposition with two chart maps agree have representatives
on a common neighbourhood whose two composites agree. -/
theorem exists_rep_of_chartStalkMap_eq {V V' P : SmallEtale B S hS Y.1} (j : V ⟶ P) (j' : V' ⟶ P)
    (t : chartStalk f x V) (t' : chartStalk f x V')
    (h : chartStalkMap f x j t = chartStalkMap f x j' t') :
    ∃ (U : SmallEtale B S hS X.1) (y : (sitePt x).fiber.obj U)
      (c : (chartFiber B S hS f V).toFunctor.obj (op U))
      (c' : (chartFiber B S hS f V').toFunctor.obj (op U)),
      (sitePt x).toPresheafFiber U y (chartFiber B S hS f V).toFunctor c = t ∧
        (sitePt x).toPresheafFiber U y (chartFiber B S hS f V').toFunctor c' = t' ∧
          c.1 ≫ j.hom.left = c'.1 ≫ j'.hom.left := by
  obtain ⟨U₁, y₁, c₁, rfl⟩ := (sitePt x).toPresheafFiber_jointly_surjective
    (P := (chartFiber B S hS f V).toFunctor) t
  obtain ⟨U₂, y₂, c₂, rfl⟩ := (sitePt x).toPresheafFiber_jointly_surjective
    (P := (chartFiber B S hS f V').toFunctor) t'
  let e₁ : (sitePt x).fiber.Elements := ⟨U₁, y₁⟩
  let e₂ : (sitePt x).fiber.Elements := ⟨U₂, y₂⟩
  let m := IsCofiltered.min e₁ e₂
  let a := IsCofiltered.minToLeft e₁ e₂
  let b := IsCofiltered.minToRight e₁ e₂
  let d₁ := (chartFiber B S hS f V).toFunctor.map a.1.op c₁
  let d₂ := (chartFiber B S hS f V').toFunctor.map b.1.op c₂
  have hd₁ : (sitePt x).toPresheafFiber m.1 m.2 (chartFiber B S hS f V).toFunctor d₁ =
      (sitePt x).toPresheafFiber U₁ y₁ (chartFiber B S hS f V).toFunctor c₁ := by
    show ((chartFiber B S hS f V).toFunctor.map a.1.op ≫
      (sitePt x).toPresheafFiber m.1 m.2 (chartFiber B S hS f V).toFunctor) c₁ = _
    rw [GrothendieckTopology.Point.toPresheafFiber_w, a.2]
  have hd₂ : (sitePt x).toPresheafFiber m.1 m.2 (chartFiber B S hS f V').toFunctor d₂ =
      (sitePt x).toPresheafFiber U₂ y₂ (chartFiber B S hS f V').toFunctor c₂ := by
    show ((chartFiber B S hS f V').toFunctor.map b.1.op ≫
      (sitePt x).toPresheafFiber m.1 m.2 (chartFiber B S hS f V').toFunctor) c₂ = _
    rw [GrothendieckTopology.Point.toPresheafFiber_w, b.2]
  rw [← hd₁, ← hd₂] at h ⊢
  have h' : (sitePt x).toPresheafFiber m.1 m.2 (chartFiber B S hS f P).toFunctor
        ((chartFiberMap f j).app _ d₁) =
      (sitePt x).toPresheafFiber m.1 m.2 (chartFiber B S hS f P).toFunctor
        ((chartFiberMap f j').app _ d₂) := by
    have k₁ := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toPresheafFiber_naturality (sitePt x) (chartFiberMap f j)
        m.1 m.2) d₁
    have k₂ := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toPresheafFiber_naturality (sitePt x) (chartFiberMap f j')
        m.1 m.2) d₂
    exact k₁.symm.trans (h.trans k₂)
  obtain ⟨U, k, y, hy, hk⟩ := (GrothendieckTopology.Point.toPresheafFiber_eq_iff' _ _ _ _ _).1 h'
  refine ⟨U, y, (chartFiber B S hS f V).toFunctor.map k.op d₁,
    (chartFiber B S hS f V').toFunctor.map k.op d₂, ?_, ?_, ?_⟩
  · show ((chartFiber B S hS f V).toFunctor.map k.op ≫
      (sitePt x).toPresheafFiber U y (chartFiber B S hS f V).toFunctor) d₁ = _
    rw [GrothendieckTopology.Point.toPresheafFiber_w, hy]
  · show ((chartFiber B S hS f V').toFunctor.map k.op ≫
      (sitePt x).toPresheafFiber U y (chartFiber B S hS f V').toFunctor) d₂ = _
    rw [GrothendieckTopology.Point.toPresheafFiber_w, hy]
  · have := congrArg Subtype.val hk
    change k.hom.left ≫ (d₁.1 ≫ j.hom.left) = k.hom.left ≫ (d₂.1 ≫ j'.hom.left) at this
    show (k.hom.left ≫ d₁.1) ≫ j.hom.left = (k.hom.left ≫ d₂.1) ≫ j'.hom.left
    rwa [Category.assoc, Category.assoc]

end AlgebraicGeometry.Space
