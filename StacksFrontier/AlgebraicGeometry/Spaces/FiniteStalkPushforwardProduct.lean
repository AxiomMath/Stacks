module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteBaseChangePartition
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeAlmostCocontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteStalkPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullback
public import StacksFrontier.CategoryTheory.Sites.Point.DirectImageFiber

/-!
# The stalk of the small étale direct image along a finite morphism is a product

Let `π : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` and let `y` be a
geometric point of `Y` with lifts `x₁, …, xₙ` in `X` (`AlgebraicGeometry.Space.GeometricLifts`).
Stacks 0DK3 computes the stalk of the direct image of a sheaf of sets on `X_étale` as
`(π_*F)_y = ∏ᵢ F_{xᵢ}`. This file proves it on the small étale sites, with no comparison to
schemes carried as data.

## Main definitions

* `AlgebraicGeometry.Space.geometricFiberBaseChangeIso`: for a representable `π` and a lift `v`
  of `y`, the fibre functor of `y` on étale charts of `Y` is the fibre functor of `v` composed
  with base change of étale charts along `π`.
* `AlgebraicGeometry.Space.stalkInverseImageIsoOfLift`: the resulting identification of the
  stalk functor at `y` with the inverse image followed by the stalk functor at `v`, at the
  universe of the structure rings.

## Main results

* `AlgebraicGeometry.Space.exists_partition_smallBaseChange`: étale neighbourhoods of the lifts
  of `y` over a base-changed chart are refined by a partition of a smaller base-changed chart.
* `AlgebraicGeometry.Space.bijective_presheafFiberCompToPi_of_isFinite`: **Stacks 0DK3**, for
  sheaves of sets valued in any universe containing `Type u`.
* `AlgebraicGeometry.Space.bijective_pushforwardFiberMap_of_isFinite`: the same statement for
  the canonical maps `(π_*M)_y ⟶ M_{xᵢ}` of the morphism of small étale topoi, the form in which
  Stacks 0DK4 consumes it.

## Implementation notes

Stalks are fibres at the points `AlgebraicGeometry.Space.etaleSitePoint` of the small étale
sites, whose fibre functors are valued in `Type u`; a sheaf of sets may be valued in any universe
`Type (max u w)` above it. The direct image is that along base change of étale charts, which is
the direct image of the morphism of small étale topoi by Stacks 03G8
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`); through that comparison,
at `Type u`, the comparison map is the family of maps `MorphismOfTopoi.pushforwardFiberMap` for
the identification `AlgebraicGeometry.Space.stalkInverseImageIsoOfLift`.

The source's proof replaces `Y` by an étale chart `V` through `y`, `X` by `V ×_Y X`, and quotes
Stacks 03QP. The proof here follows the proof of Stacks 03QP itself, read on the small étale
sites: the criterion `CategoryTheory.GrothendieckTopology.Point.bijective_presheafFiberCompToPi`
reduces bijectivity to refining neighbourhoods of the lifts to partitions, and the partition is
supplied, on a base-changed chart `V ×_Y X ⟶ V` — a finite morphism of schemes, by
`AlgebraicGeometry.Space.isFinite_toScheme_map_snd` — by
`AlgebraicGeometry.exists_etale_partition_refining_of_isFinite`.

## References

* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (π : X ⟶ Y)

open CategoryTheory.Limits Opposite

variable (hrep : yoneda.relativelyRepresentable π.hom)

/-- The compatibility making a lift of a geometric point and a lift into an étale chart of the
target define a lift into the base-changed chart. -/
theorem geometricLift_comp_eq (y : GeometricPoint B S hS Y.1) (v : GeometricLifts B S hS π y)
    (V : SmallEtale B S hS Y.1) (t : GeometricFiber B S hS Y.1 y V) :
    yonedaEquiv.symm v.1 ≫ π.hom = yoneda.map t.1 ≫ V.1.hom := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]
  exact v.2.trans t.2.symm

/-- **Lifting the geometric fibre along a representable base change.** For a lift `v` of a
geometric point `y` of `Y` to `X`, a lift of `y` into an étale chart `V` of `Y` is the same as a
lift of `v` into the base change `V ×_Y X`: the first is recovered by the projection to `V`, the
second is the pair of `v` and the given lift. -/
def geometricFiberBaseChangeEquiv (y : GeometricPoint B S hS Y.1)
    (v : GeometricLifts B S hS π y) (V : SmallEtale B S hS Y.1) :
    GeometricFiber B S hS Y.1 y V ≃
      GeometricFiber B S hS X.1 (geometricLiftPoint B S hS π y v)
        ((smallBaseChange B S hS π hrep).obj V) where
  toFun t := ⟨hrep.lift (yonedaEquiv.symm v.1) t.1 (geometricLift_comp_eq B S hS π y v V t),
    ((yonedaEquiv_comp _ _).trans (congrArg _ (yonedaEquiv_yoneda_map _))).symm.trans
      ((congrArg yonedaEquiv (hrep.lift_fst (yonedaEquiv.symm v.1) t.1
        (geometricLift_comp_eq B S hS π y v V t))).trans (yonedaEquiv.apply_symm_apply _))⟩
  invFun q := ⟨q.1 ≫ hrep.snd V.1.hom, by
    have hw := congrArg (fun α : yoneda.obj (hrep.pullback V.1.hom) ⟶ Y.1 =>
      α.app (op y.val.siteObject) q.1) (hrep.w V.1.hom)
    have hq : (hrep.fst V.1.hom).app (op y.val.siteObject) q.1 = v.1 := q.2
    have h2 : π.hom.app (op y.val.siteObject) ((hrep.fst V.1.hom).app (op y.val.siteObject) q.1)
        = y.val.value := (congrArg (π.hom.app (op y.val.siteObject)) hq).trans v.2
    exact hw.symm.trans h2⟩
  left_inv t := Subtype.ext (hrep.lift_snd _ _ _)
  right_inv q := Subtype.ext (hrep.hom_ext ((hrep.lift_fst _ _ _).trans
      (yonedaEquiv.injective ((yonedaEquiv.apply_symm_apply _).trans (q.2.symm.trans
        ((yonedaEquiv_comp _ _).trans (congrArg _ (yonedaEquiv_yoneda_map _))).symm))))
      (hrep.lift_snd _ _ _))

/-- The lift of `v` into `V ×_Y X` attached to a lift `t` of `y` into `V` projects to `t`. -/
theorem geometricFiberBaseChangeEquiv_snd (y : GeometricPoint B S hS Y.1)
    (v : GeometricLifts B S hS π y) (V : SmallEtale B S hS Y.1)
    (t : GeometricFiber B S hS Y.1 y V) :
    (geometricFiberBaseChangeEquiv B S hS π hrep y v V t).1 ≫ hrep.snd V.1.hom = t.1 :=
  hrep.lift_snd (yonedaEquiv.symm v.1) t.1 (geometricLift_comp_eq B S hS π y v V t)

/-- The inverse of `AlgebraicGeometry.Space.geometricFiberBaseChangeEquiv` is the projection to
the chart of `Y`. -/
theorem geometricFiberBaseChangeEquiv_symm_apply (y : GeometricPoint B S hS Y.1)
    (v : GeometricLifts B S hS π y) (V : SmallEtale B S hS Y.1)
    (q : GeometricFiber B S hS X.1 (geometricLiftPoint B S hS π y v)
      ((smallBaseChange B S hS π hrep).obj V)) :
    ((geometricFiberBaseChangeEquiv B S hS π hrep y v V).symm q).1 = q.1 ≫ hrep.snd V.1.hom :=
  rfl

/-- The fibre functor of `y` is the fibre functor of a lift `v` of `y` pulled back along the
base change of étale charts. -/
def geometricFiberBaseChangeIso (y : GeometricPoint B S hS Y.1)
    (v : GeometricLifts B S hS π y) :
    geometricFiber B S hS Y.1 y ≅
      smallBaseChange B S hS π hrep ⋙ geometricFiber B S hS X.1 (geometricLiftPoint B S hS π y v) :=
  (NatIso.ofComponents (fun V => (geometricFiberBaseChangeEquiv B S hS π hrep y v V).symm.toIso)
    (fun {V W} k => by
      ext q
      refine Subtype.ext ?_
      change (q.1 ≫ ((smallBaseChange B S hS π hrep).map k).hom.left) ≫ hrep.snd W.1.hom =
        (q.1 ≫ hrep.snd V.1.hom) ≫ k.hom.left
      exact (Category.assoc _ _ _).trans ((congrArg (fun m => q.1 ≫ m)
        (smallBaseChange_map_snd B S hS π hrep k)).trans (Category.assoc _ _ _).symm))).symm

/-- The components of `AlgebraicGeometry.Space.geometricFiberBaseChangeIso` are the bijections
`AlgebraicGeometry.Space.geometricFiberBaseChangeEquiv`. -/
theorem geometricFiberBaseChangeIso_hom_app (y : GeometricPoint B S hS Y.1)
    (v : GeometricLifts B S hS π y) (V : SmallEtale B S hS Y.1)
    (t : GeometricFiber B S hS Y.1 y V) :
    (geometricFiberBaseChangeIso B S hS π hrep y v).hom.app V t =
      geometricFiberBaseChangeEquiv B S hS π hrep y v V t := rfl


/-- **Stacks 03ZQ, read on charts.** For a finite morphism `π : X ⟶ Y` of algebraic spaces the
base change of `π` to an étale chart of `Y` is a finite morphism of schemes. -/
theorem isFinite_toScheme_map_snd (hπ : IsFinite B S hS π.hom) (V : SmallEtale B S hS Y.1) :
    _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hrep.snd V.1.hom)) :=
  ((isFinite_iff_representable B S hS π.hom X.2 Y.2).1 hπ).2.property V.1.hom _ _
    (hrep.isPullback V.1.hom)

/-- **The lifts of a geometric point into a base-changed chart are the scheme lifts.** For a lift
`t` of `y` into an étale chart `V` of `Y`, the lifts of `y` to `X` correspond bijectively, through
the base change of `t`, to the lifts of the geometric point of the scheme of `V` given by `t`
along the base change `V ×_Y X ⟶ V` of `π`. -/
theorem bijective_toScheme_map_geometricFiberBaseChangeEquiv (y : GeometricPoint B S hS Y.1)
    (V : SmallEtale B S hS Y.1) (t : GeometricFiber B S hS Y.1 y V)
    (Λ : GeometricLifts B S hS π y → {g : (BigFppfOver.toScheme B S hS).obj y.val.siteObject ⟶
      chartScheme ((smallBaseChange B S hS π hrep).obj V) //
        g ≫ (BigFppfOver.toScheme B S hS).map (hrep.snd V.1.hom) =
          (BigFppfOver.toScheme B S hS).map t.1})
    (hΛ : ∀ v, (Λ v).1 = (BigFppfOver.toScheme B S hS).map
      (geometricFiberBaseChangeEquiv B S hS π hrep y v V t).1) :
    Function.Bijective Λ := by
  let H := BigFppfOver.toScheme B S hS
  constructor
  · intro v v' h
    have h1 : (geometricFiberBaseChangeEquiv B S hS π hrep y v V t).1 =
        (geometricFiberBaseChangeEquiv B S hS π hrep y v' V t).1 :=
      H.map_injective ((hΛ v).symm.trans ((congrArg Subtype.val h).trans (hΛ v')))
    exact Subtype.ext ((geometricFiberBaseChangeEquiv B S hS π hrep y v V t).2.symm.trans
      ((congrArg (fun p => (hrep.fst V.1.hom).app (op y.val.siteObject) p) h1).trans
        (geometricFiberBaseChangeEquiv B S hS π hrep y v' V t).2))
  · rintro ⟨g, hg⟩
    let p : y.val.siteObject ⟶ hrep.pullback V.1.hom :=
      Over.homMk (ObjectProperty.homMk g) (by
        apply ObjectProperty.hom_ext
        have hs : B.inclusion.map (hrep.snd V.1.hom).left ≫ B.inclusion.map V.1.left.hom =
            B.inclusion.map (hrep.pullback V.1.hom).hom :=
          (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w _))
        have ht : B.inclusion.map t.1.left ≫ B.inclusion.map V.1.left.hom =
            B.inclusion.map y.val.siteObject.hom :=
          (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w _))
        exact (congrArg (g ≫ ·) hs).symm.trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ B.inclusion.map V.1.left.hom) hg).trans ht)))
    have hp : p ≫ hrep.snd V.1.hom = t.1 := H.map_injective ((H.map_comp _ _).trans hg)
    let v₀ := (hrep.fst V.1.hom).app (op y.val.siteObject) p
    have hv₀ : π.hom.app (op y.val.siteObject) v₀ = y.val.value := by
      have hw := congrArg (fun α : yoneda.obj (hrep.pullback V.1.hom) ⟶ Y.1 =>
        α.app (op y.val.siteObject) p) (hrep.w V.1.hom)
      exact hw.trans ((congrArg (V.1.hom.app (op y.val.siteObject)) hp).trans t.2)
    refine ⟨⟨v₀, hv₀⟩, Subtype.ext ((hΛ _).trans (congrArg H.map (?_ : _ = p)))⟩
    refine hrep.hom_ext ((hrep.lift_fst _ _ _).trans
      (yonedaEquiv.injective ((yonedaEquiv.apply_symm_apply _).trans
        ((yonedaEquiv_comp _ _).trans (congrArg _ (yonedaEquiv_yoneda_map _))).symm)))
      ((hrep.lift_snd _ _ _).trans hp.symm)

/-- A morphism `P : T ⟶ A` whose composite with `r : A ⟶ Z` factors through an open `U` of `Z`
factors through the preimage `r ⁻¹ᵁ U`, compatibly with the restriction `r ∣_ U`. -/
theorem _root_.AlgebraicGeometry.exists_lift_preimage_of_comp_eq {T A Z : Scheme} (P : T ⟶ A)
    (r : A ⟶ Z) (U : Z.Opens) (n : T ⟶ U) (h : P ≫ r = n ≫ U.ι) :
    ∃ n' : T ⟶ r ⁻¹ᵁ U, n' ≫ (r ⁻¹ᵁ U).ι = P ∧ n' ≫ (r ∣_ U) = n := by
  have hrange : Set.range P ⊆ Set.range (r ⁻¹ᵁ U).ι := by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨P p, ?_⟩, rfl⟩
    show r (P p) ∈ U
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact (n p).2
  refine ⟨IsOpenImmersion.lift _ P hrange, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    IsOpenImmersion.lift_fac, h]

open TopologicalSpace in
/-- **Refining neighbourhoods of the lifts to a partition (the geometric input to Stacks 0DK3).**
Let `π : X ⟶ Y` be finite, `y` a geometric point of `Y` and `t` a lift of `y` into an étale
chart `V` of `Y`. Given for every lift `v` of `y` an étale neighbourhood `W v` of `v` over the base
change `V ×_Y X`, some smaller étale neighbourhood `V'` of `y` has `V' ×_Y X` covered by pairwise
disjoint open subcharts `N v`, each an étale neighbourhood of `v` mapping to `W v` over
`V ×_Y X`. -/
theorem exists_partition_smallBaseChange (hπ : IsFinite B S hS π.hom)
    (y : GeometricPoint B S hS Y.1) (V : SmallEtale B S hS Y.1)
    (t : GeometricFiber B S hS Y.1 y V)
    (W : GeometricLifts B S hS π y → SmallEtale B S hS X.1)
    (w : ∀ v, GeometricFiber B S hS X.1 (geometricLiftPoint B S hS π y v) (W v))
    (a : ∀ v, W v ⟶ (smallBaseChange B S hS π hrep).obj V)
    (hw : ∀ v, (geometricFiber B S hS X.1 (geometricLiftPoint B S hS π y v)).map (a v) (w v) =
      (geometricFiberBaseChangeIso B S hS π hrep y v).hom.app V t) :
    ∃ (V' : SmallEtale B S hS Y.1) (t' : GeometricFiber B S hS Y.1 y V') (g : V' ⟶ V)
      (N : GeometricLifts B S hS π y → SmallEtale B S hS X.1)
      (n : ∀ v, GeometricFiber B S hS X.1 (geometricLiftPoint B S hS π y v) (N v))
      (c : ∀ v, N v ⟶ (smallBaseChange B S hS π hrep).obj V') (b : ∀ v, N v ⟶ W v),
      (geometricFiber B S hS Y.1 y).map g t' = t ∧
      (∀ v, c v ≫ (smallBaseChange B S hS π hrep).map g = b v ≫ a v) ∧
      (∀ v, (geometricFiber B S hS X.1 (geometricLiftPoint B S hS π y v)).map (c v) (n v) =
        (geometricFiberBaseChangeIso B S hS π hrep y v).hom.app V' t') ∧
      (∀ v, (geometricFiber B S hS X.1 (geometricLiftPoint B S hS π y v)).map (b v) (n v) =
        w v) ∧
      Sieve.ofArrows N c ∈ SmallEtale.topology B S hS X.1
        ((smallBaseChange B S hS π hrep).obj V') ∧
      (∀ v, Mono (c v)) ∧
      (∀ i j, i ≠ j → ∀ (T : SmallEtale B S hS X.1) (p : T ⟶ N i) (q : T ⟶ N j),
        p ≫ c i = q ≫ c j → (⊥ : Sieve T) ∈ SmallEtale.topology B S hS X.1 T) := by
  classical
  let H := BigFppfOver.toScheme B S hS
  let O := SmallEtale.toOver B S hS X.1
  let uf := smallBaseChange B S hS π hrep
  let E := fun v => geometricFiberBaseChangeEquiv B S hS π hrep y v
  have : IsAlgClosed y.val.carrier := y.property
  let ysch : _root_.AlgebraicGeometry.GeometricPoint (chartScheme V) :=
    { residueField := y.val.carrier, hom := H.map t.1 }
  let f : chartScheme (uf.obj V) ⟶ chartScheme V := H.map (hrep.snd V.1.hom)
  have : _root_.AlgebraicGeometry.IsFinite f := isFinite_toScheme_map_snd B S hS π hrep hπ V
  let Λ (v : GeometricLifts B S hS π y) : {g : ysch.source ⟶ chartScheme (uf.obj V) //
      g ≫ f = ysch.hom} :=
    ⟨H.map (E v V t).1, (H.map_comp _ _).symm.trans
      (congrArg H.map (geometricFiberBaseChangeEquiv_snd B S hS π hrep y v V t))⟩
  have hEt (v : GeometricLifts B S hS π y) : Etale (H.map (O.map (a v))) :=
    etale_toScheme_toOver_map B S hS X.1 (a v)
  obtain ⟨Vs, hVs, e, he, q, hq, Nsc, bsc, hb, hn, hdis, hcov⟩ :=
    exists_etale_partition_refining_of_isFinite f ysch Λ
      (bijective_toScheme_map_geometricFiberBaseChangeEquiv B S hS π hrep y V t Λ fun _ => rfl)
      (fun v => chartScheme (W v))
      (fun v => H.map (O.map (a v))) (fun v => H.map (w v).1)
      (fun v => (H.map_comp _ _).symm.trans (congrArg (fun p => H.map p.1) (hw v)))
  have hT : B.Contains Vs :=
    (Scheme.size_le_of_locallyOfFiniteType e).trans_lt V.1.left.left.property
  let V' := chartOfEtaleSchemeHom B S hS V hT e he
  let g : V' ⟶ V := chartOfEtaleSchemeHomMap B S hS V hT e he
  obtain ⟨t', ht', hqt'⟩ := exists_geometricFiber_chartOfEtaleSchemeHom B S hS V hT e he y t q hq
  have hr : H.map (O.map (uf.map g)) ≫ f = H.map (hrep.snd V'.1.hom) ≫ e :=
    (H.map_comp _ _).symm.trans ((congrArg H.map (smallBaseChange_map_snd B S hS π hrep g)).trans
      (H.map_comp _ _))
  let r : chartScheme (uf.obj V') ⟶ pullback f e := pullback.lift _ _ hr
  let N' (v : GeometricLifts B S hS π y) : (chartScheme (uf.obj V')).Opens := r ⁻¹ᵁ Nsc v
  have hNc (v : GeometricLifts B S hS π y) : B.Contains (N' v) :=
    Scheme.size_lt_of_isOpenImmersion (N' v).ι (uf.obj V').1.left.left.property
  let Nc (v : GeometricLifts B S hS π y) : SmallEtale B S hS X.1 :=
    chartOfEtaleSchemeHom B S hS (uf.obj V') (hNc v) (N' v).ι inferInstance
  let c (v : GeometricLifts B S hS π y) : Nc v ⟶ uf.obj V' :=
    chartOfEtaleSchemeHomMap B S hS (uf.obj V') (hNc v) (N' v).ι inferInstance
  have hβ (v : GeometricLifts B S hS π y) :
      ((r ∣_ Nsc v) ≫ bsc v) ≫ H.map (O.map (a v)) =
        (N' v).ι ≫ H.map (O.map (uf.map g)) := by
    rw [Category.assoc, hb v, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    exact congrArg ((N' v).ι ≫ ·) (pullback.lift_fst _ _ hr)
  choose b hbcomm hbH using fun v => exists_chartOfEtaleSchemeHom_hom B S hS
    (uf.obj V') (hNc v) (N' v).ι inferInstance (a v) (uf.map g) ((r ∣_ Nsc v) ≫ bsc v) (hβ v)
  -- the points
  let P (v : GeometricLifts B S hS π y) : ysch.source ⟶ chartScheme (uf.obj V') :=
    H.map (E v V' t').1
  have hnat (v : GeometricLifts B S hS π y) : (E v V' t').1 ≫ O.map (uf.map g) = (E v V t).1 := by
    have h := congrArg Subtype.val (ConcreteCategory.congr_hom
      ((geometricFiberBaseChangeIso B S hS π hrep y v).hom.naturality g) t')
    exact h.symm.trans (congrArg (fun z => (E v V z).1) ht')
  have hpt (v : GeometricLifts B S hS π y) : ∃ n' : ysch.source ⟶ N' v,
      n' ≫ (N' v).ι = P v ∧ n' ≫ (r ∣_ Nsc v) ≫ bsc v = H.map (w v).1 := by
    obtain ⟨nsc, hn1, hn2, hn3⟩ := hn v
    have hPr : P v ≫ r = nsc ≫ (Nsc v).ι := by
      apply pullback.hom_ext
      · exact ((Category.assoc _ _ _).trans (congrArg (P v ≫ ·) (pullback.lift_fst _ _ hr))).trans
          (((H.map_comp _ _).symm.trans (congrArg H.map (hnat v))).trans
            (hn1.symm.trans (Category.assoc _ _ _).symm))
      · exact ((Category.assoc _ _ _).trans (congrArg (P v ≫ ·) (pullback.lift_snd _ _ hr))).trans
          (((H.map_comp _ _).symm.trans ((congrArg H.map
            (geometricFiberBaseChangeEquiv_snd B S hS π hrep y v V' t')).trans hqt')).trans
            (hn2.symm.trans (Category.assoc _ _ _).symm))
    obtain ⟨n', hn', hnr⟩ := exists_lift_preimage_of_comp_eq (P v) r (Nsc v) nsc hPr
    exact ⟨n', hn', by rw [← Category.assoc, hnr, hn3]⟩
  choose n' hn'ι hn'b using hpt
  choose n hnc hnH using fun v => exists_geometricFiber_chartOfEtaleSchemeHom B S hS
    (uf.obj V') (hNc v) (N' v).ι inferInstance (geometricLiftPoint B S hS π y v)
    ((geometricFiberBaseChangeIso B S hS π hrep y v).hom.app V' t') (n' v) (hn'ι v)
  refine ⟨V', t', g, Nc, n, c, b, ht', fun v => (hbcomm v).symm, hnc, fun v => ?_, ?_,
    fun v => ?_, fun i j hij T p p' hpp' => ?_⟩
  · refine Subtype.ext (H.map_injective ?_)
    show H.map ((n v).1 ≫ O.map (b v)) = H.map (w v).1
    rw [H.map_comp, hnH v, hbH v]
    exact hn'b v
  · refine smallEtale_sieve_of_pointwise_covering B S hS X.1 (uf.obj V') _ fun z => ?_
    obtain ⟨v, hv⟩ := hcov (r z)
    exact ⟨Nc v, c v, Sieve.ofArrows_mk _ _ v, ⟨z, hv⟩, rfl⟩
  · exact (O ⋙ H).mono_of_mono_map (inferInstanceAs (Mono (N' v).ι))
  · refine SmallEtale.bot_mem_topology B S hS X.1 T ⟨fun z => ?_⟩
    have he := congrArg (fun m => H.map (O.map m) z) hpp'
    simp only [Functor.map_comp, Scheme.Hom.comp_apply] at he
    have h1 : r (H.map (O.map (c i)) (H.map (O.map p) z)) ∈ Nsc i := (H.map (O.map p) z).2
    have h2 : r (H.map (O.map (c j)) (H.map (O.map p') z)) ∈ Nsc j := (H.map (O.map p') z).2
    rw [he] at h1
    exact Set.disjoint_left.mp (hdis hij) h1 h2

/-- **Stacks 0DK3.** Let `π : X ⟶ Y` be a finite morphism of algebraic spaces and `y` a geometric
point of `Y` with lifts `x₁, …, xₙ` in `X`. For every sheaf of sets `F` on `X_étale` the stalk of
the direct image `π_*F` at `y` is the product `∏ᵢ F_{xᵢ}`: the canonical map
`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompToPi`, sending the germ at `y` of a
section of `F` over a base-changed chart `V ×_Y X` to the family of its germs at the lifts, is
bijective.

The direct image is that along base change of étale charts (`π` is representable, being finite,
`AlgebraicGeometry.Space.relativelyRepresentable_hom_of_isFinite`),
which is the direct image of the morphism of small étale topoi of Stacks 03G2, part (3)
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`); sheaves are valued in an
arbitrary universe containing `Type u`, the universe of the fibres of the points
`AlgebraicGeometry.Space.etaleSitePoint` at which stalks are taken. -/
@[stacks 0DK3]
theorem bijective_presheafFiberCompToPi_of_isFinite (hπ : IsFinite B S hS π.hom)
    (y : GeometricPoint B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (max u w))) :
    Function.Bijective (GrothendieckTopology.Point.presheafFiberCompToPi.{u, w, u, u + 1, u, u + 1}
      (smallBaseChange B S hS π (relativelyRepresentable_hom_of_isFinite B S hS π hπ))
      (etaleSitePoint B S hS Y.1 y Y.2)
      (fun v => etaleSitePoint B S hS X.1 (geometricLiftPoint B S hS π y v) X.2)
      (geometricFiberBaseChangeIso B S hS π (relativelyRepresentable_hom_of_isFinite B S hS π hπ) y)
      F.obj) :=
  GrothendieckTopology.Point.bijective_presheafFiberCompToPi.{u, w, u, u + 1, u, u + 1} _ _ _ _ F
    (exists_partition_smallBaseChange B S hS π _ hπ y)

/-- The identification of the stalk at a geometric point `y` of `Y` with the stalk of the
inverse image at a lift `v` of `y`, for a representable morphism `π : X ⟶ Y`: the fibre functor
of `y` is that of `v` pulled back along base change of étale charts, and the inverse image of the
morphism of small étale topoi is left adjoint to direct image along that base change. -/
def stalkInverseImageIsoOfLift (y : GeometricPoint B S hS Y.1)
    (v : GeometricLifts B S hS π y) :
    (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber (A := Type u) ≅
      (smallToposMorphismTypeU B S hS π).inverseImage ⋙
        (etaleSitePoint B S hS X.1 (geometricLiftPoint B S hS π y v) X.2).sheafFiber :=
  letI := (smallBaseChange_isMorphismOfSites B S hS π hrep).toIsContinuous
  Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj
    (etaleSitePoint B S hS X.1 (geometricLiftPoint B S hS π y v) X.2)
    (smallBaseChange B S hS π hrep)
    ((smallToposMorphismTypeU B S hS π).adj.ofNatIsoRight
      (smallEtaleRingedToposHom_representable B S hS π hrep))
    (etaleSitePoint B S hS Y.1 y Y.2) (geometricFiberBaseChangeIso B S hS π hrep y v)

/-- **Stacks 0DK3 for the morphism of small étale topoi.** At the universe of the structure
rings, the canonical maps `(π_*M)_y ⟶ M_{xᵢ}` of the morphism of small étale topoi
`AlgebraicGeometry.Space.smallToposMorphismTypeU` (`MorphismOfTopoi.pushforwardFiberMap` for the
identification of stalks `AlgebraicGeometry.Space.stalkInverseImageIsoOfLift`) assemble to a
bijection `(π_*M)_y ⟶ ∏ᵢ M_{xᵢ}`. This is
`AlgebraicGeometry.Space.bijective_presheafFiberCompToPi_of_isFinite` read through the
comparison of direct images of Stacks 03G8. -/
theorem bijective_pushforwardFiberMap_of_isFinite (hπ : IsFinite B S hS π.hom)
    (y : GeometricPoint B S hS Y.1)
    (M : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    Function.Bijective (fun z (v : GeometricLifts B S hS π y) =>
      ((smallToposMorphismTypeU B S hS π).pushforwardFiberMap
        (etaleSitePoint B S hS X.1 (geometricLiftPoint B S hS π y v) X.2)
        (etaleSitePoint B S hS Y.1 y Y.2)
        (stalkInverseImageIsoOfLift B S hS π hrep y v)).app M z) := by
  let := (smallBaseChange_isMorphismOfSites B S hS π hrep).toIsContinuous
  exact (GrothendieckTopology.Point.bijective_pushforwardFiberMap_iff
    (smallBaseChange B S hS π hrep) (etaleSitePoint B S hS Y.1 y Y.2)
    (fun v => etaleSitePoint B S hS X.1 (geometricLiftPoint B S hS π y v) X.2)
    (geometricFiberBaseChangeIso B S hS π hrep y) (smallToposMorphismTypeU B S hS π)
    (smallEtaleRingedToposHom_representable B S hS π hrep) M).2
    (bijective_presheafFiberCompToPi_of_isFinite.{u, u} B S hS π hπ y M)

end AlgebraicGeometry.Space

end
