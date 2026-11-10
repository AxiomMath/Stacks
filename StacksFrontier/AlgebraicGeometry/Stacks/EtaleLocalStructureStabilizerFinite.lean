module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureStack
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChart
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOfFlatInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType

/-!
# A finite automorphism group gives finitely many stabilizer points over the chart point

The second step of the proof of **Stacks 0DU4**: "Our assumption on `G_x` implies that `G_u` is
finite over `u`." Let `[U/R] ⟶ 𝒳` be a quotient chart of an algebraic stack (fully faithful and
étale, `AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid`) and let `u ∈ U` be a point
over `x ∈ |𝒳|`. If the automorphism group of `𝒳` at `x` is finite (Remark 0DTU, read with the
property `AlgebraicGeometry.Stack.EtaleLocalStructure.IsFiniteOverBase`), then only finitely many
points of the stabilizer `G = R ×_{U ×_S U} U` of the groupoid lie over `u`.

## Main results

* `AlgebraicGeometry.Stack.nonempty_isomSpace_smallQuotientStackCFG_iso`: the automorphism space
  of a presented object of (the small model of) a quotient stack `[U/R]` is the slice presheaf
  `arrowFiberOver` of arrows with source and target the presenting point (Stacks 044V).
* `Stacks.Groupoids.GroupoidScheme.finite_stabilizer_of_iso_arrowFiberOver`: if that presheaf is
  represented by a scheme with finitely many points, then finitely many stabilizer points lie over
  the presenting point.
* `AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.finite_stabilizer`: the statement
  above.

## Implementation notes

Write `T` for the field spectrum of a field-valued point of `U` over `u` and `a : T ⟶ U` for that
point. The automorphism space `G_p` of its image in `𝒳` is, through the fully faithful chart and
Stacks 044V, the presheaf on schemes over `T` of arrows `r` of `R` with `s ∘ r = t ∘ r = a`. The
finiteness hypothesis represents it by a scheme `V'` finite over `T`, hence with finitely many
points. The universal arrow `r₀ : V' ⟶ R` then receives, by the Yoneda lemma, every such arrow
`r : X ⟶ R`; taking for `X` the fibre product `G ×_U T` shows that the arrow of every stabilizer
point over `u` lies in the image of `r₀`, and the stabilizer embeds in `R`.

## References

* [Stacks Project, Tag 0DU4](https://stacks.math.columbia.edu/tag/0DU4)
* [Stacks Project, Tag 0DTU](https://stacks.math.columbia.edu/tag/0DTU)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

/-! ### Arrows of the slice presheaf of arrows over a presented point -/

open AlgebraicGeometry AlgebraicGeometry.Space AlgebraicGeometry.Stack

namespace Stacks.Groupoids.GroupoidScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} (hS : B.Contains S) (G : GroupoidScheme S)
  (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
  (hP : B.Contains (pullback G.source G.target).left)
  {T : BigFppfOver B S hS} (a : (G.realization B hS hU hR hP).objects.obj.obj (op T))

/-- The arrow of a section of the slice presheaf `arrowFiberOver` of arrows from `a` to `a`. -/
noncomputable def arrowFiberOverArrow {W : Over T}
    (s : (arrowFiberOver (G.realization B hS hU hR hP) T a a).obj (op W)) :
    (G.realization B hS hU hR hP).arrows.obj.obj (op W.left) :=
  (pullback.snd (prod.lift (yonedaEquiv.symm a) (yonedaEquiv.symm a))
    (prod.lift (G.realization B hS hU hR hP).target.hom
      (G.realization B hS hU hR hP).source.hom)).app
    (op W.left) s.1

/-- The arrow of a restricted section is the restricted arrow. -/
theorem arrowFiberOverArrow_map {W₁ W₂ : Over T} (m : W₁ ⟶ W₂)
    (s : (arrowFiberOver (G.realization B hS hU hR hP) T a a).obj (op W₂)) :
    arrowFiberOverArrow hS G hU hR hP a
        ((arrowFiberOver (G.realization B hS hU hR hP) T a a).map m.op s) =
      (G.realization B hS hU hR hP).arrows.obj.map m.left.op
        (arrowFiberOverArrow hS G hU hR hP a s) :=
  NatTrans.naturality_apply (pullback.snd (prod.lift (yonedaEquiv.symm a) (yonedaEquiv.symm a))
      (prod.lift (G.realization B hS hU hR hP).target.hom (G.realization B hS hU hR hP).source.hom))
    m.left.op s.1

/-- A section of `arrowFiberOver` from an arrow with source and target the restriction of `a`. -/
noncomputable def arrowFiberOverMk {W : Over T}
    (r : (G.realization B hS hU hR hP).arrows.obj.obj (op W.left))
    (ht : (G.realization B hS hU hR hP).target.hom.app (op W.left) r =
      (G.realization B hS hU hR hP).objects.obj.map W.hom.op a)
    (hs : (G.realization B hS hU hR hP).source.hom.app (op W.left) r =
      (G.realization B hS hU hR hP).objects.obj.map W.hom.op a) :
    (arrowFiberOver (G.realization B hS hU hR hP) T a a).obj (op W) :=
  ⟨yonedaEquiv (pullback.lift (yonedaEquiv.symm W.hom) (yonedaEquiv.symm r) (by
      apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst]
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact ht.symm
      · simp only [Category.assoc, prod.lift_snd]
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hs.symm)), by
    rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
    rfl⟩

/-- The arrow of `AlgebraicGeometry.Stack.arrowFiberOverMk` is the given arrow. -/
theorem arrowFiberOverArrow_mk {W : Over T}
    (r : (G.realization B hS hU hR hP).arrows.obj.obj (op W.left))
    (ht : (G.realization B hS hU hR hP).target.hom.app (op W.left) r =
      (G.realization B hS hU hR hP).objects.obj.map W.hom.op a)
    (hs : (G.realization B hS hU hR hP).source.hom.app (op W.left) r =
      (G.realization B hS hU hR hP).objects.obj.map W.hom.op a) :
    arrowFiberOverArrow hS G hU hR hP a (arrowFiberOverMk hS G hU hR hP a r ht hs) = r := by
  change (pullback.snd (prod.lift (yonedaEquiv.symm a) (yonedaEquiv.symm a))
      (prod.lift (G.realization B hS hU hR hP).target.hom
        (G.realization B hS hU hR hP).source.hom)).app (op W.left)
    (yonedaEquiv (pullback.lift _ _ _)) = r
  rw [← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- The arrow of a point of the stabilizer, as a morphism of schemes over `S`: it is injective on
points, the stabilizer being the base change of the diagonal, a monomorphism. -/
theorem injective_stabilizerArrow :
    Function.Injective (AlgebraicGeometry.stabilizerArrow G) := by
  have : IsSplitMono (AlgebraicGeometry.diagonal G) :=
    IsSplitMono.mk' ⟨CartesianMonoidalCategory.fst _ _, CartesianMonoidalCategory.lift_fst _ _⟩
  have : Mono (pullback.fst (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G)) :=
    inferInstance
  exact (AlgebraicGeometry.stabilizerArrow G).injective

/-- The arrow of a point of the stabilizer has its point of the object scheme as target. -/
alias stabilizerArrow_target := stabilizerFst_comp_target

/-- The arrow of a point of the stabilizer has its point of the object scheme as source. -/
alias stabilizerArrow_source := stabilizerFst_comp_source

/-- **Finitely many stabilizer points over a point, from a finite representing scheme.** Let `a`
be a generalized point of the object scheme of `G` over a nonempty test object `T`, all of whose
points map to `u`. If the slice presheaf of arrows of `G` from `a` to `a` is represented by an
object `V'` of the site of `T` with finitely many points, then only finitely many points of the
stabilizer of `G` lie over `u`. -/
theorem finite_stabilizer_of_iso_arrowFiberOver (u : G.objects.left)
    (τ : ((siteToOver B hS).obj T).left)
    (ha : ∀ τ, (yonedaSchemePointEquiv B hS hU (op T) a).left τ = u)
    (V' : BigFppfOver B T.left.1 T.left.2) [Finite V'.left.1]
    (e : yoneda.obj V' ≅
      (Over.iteratedSliceBackward T).op ⋙ arrowFiberOver (G.realization B hS hU hR hP) T a a) :
    Set.Finite {y : (AlgebraicGeometry.stabilizer G).left |
      (AlgebraicGeometry.stabilizer G).hom y = u} := by
  let GR := G.realization B hS hU hR hP
  let â := yonedaSchemePointEquiv B hS hU (op T) a
  let π := pullback.snd (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G)
  let ρ := pullback.fst (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G)
  have hSt : B.Contains (AlgebraicGeometry.stabilizerOverBase G).left :=
    BigFppfSite.contains_pullback_left B _ _ hR hU
  have hPb : B.Contains (pullback π â).left :=
    BigFppfSite.contains_pullback_left B π â hSt T.left.2
  -- the test object `X = G ×_U T` over `T`
  let X : BigFppfOver B T.left.1 T.left.2 :=
    Over.mk (⟨(pullback.snd π â).left⟩ : B.obj hPb ⟶ B.obj T.left.2)
  let Xs := (Over.iteratedSliceBackward T).obj X
  let ι : (siteToOver B hS).obj Xs.left ⟶ pullback π â :=
    Over.homMk (𝟙 (pullback π â).left)
      ((Category.id_comp _).trans (Over.w (pullback.snd π â)).symm)
  have hι : ι ≫ pullback.snd π â = (siteToOver B hS).map Xs.hom :=
    Over.OverMorphism.ext (Category.id_comp _)
  let r : GR.arrows.obj.obj (op Xs.left) :=
    (yonedaSchemePointEquiv B hS hR (op Xs.left)).symm (ι ≫ pullback.fst π â ≫ ρ)
  have hr : yonedaSchemePointEquiv B hS hR (op Xs.left) r = ι ≫ pullback.fst π â ≫ ρ :=
    Equiv.apply_symm_apply _ _
  have hobj : yonedaSchemePointEquiv B hS hU (op Xs.left) (GR.objects.obj.map Xs.hom.op a) =
      (siteToOver B hS).map Xs.hom ≫ â :=
    show (siteToOver B hS).map (Xs.hom ≫ a) = _ from Functor.map_comp _ _ _
  obtain ⟨hrt, hrs⟩ : GR.target.hom.app (op Xs.left) r = GR.objects.obj.map Xs.hom.op a ∧
      GR.source.hom.app (op Xs.left) r = GR.objects.obj.map Xs.hom.op a := by
    constructor <;>
    · apply (yonedaSchemePointEquiv B hS hU (op Xs.left)).injective
      refine (yonedaSchemePointEquiv_map B hS hR hU _ (op Xs.left) r).trans ?_
      rw [hr, hobj, ← hι, Category.assoc, Category.assoc, Category.assoc]
      first
        | rw [stabilizerArrow_target, pullback.condition]
        | rw [stabilizerArrow_source, pullback.condition]
  let sX := arrowFiberOverMk hS G hU hR hP a r hrt hrs
  -- the universal arrow
  let V's := (Over.iteratedSliceBackward T).obj V'
  let ε : (arrowFiberOver GR T a a).obj (op V's) := e.hom.app (op V') (𝟙 V')
  let r₀ : GR.arrows.obj.obj (op V's.left) := arrowFiberOverArrow hS G hU hR hP a ε
  let m : X ⟶ V' := e.inv.app (op X) sX
  have hm : sX = (arrowFiberOver GR T a a).map ((Over.iteratedSliceBackward T).map m).op ε := by
    have h1 : e.hom.app (op X) m = sX := e.inv_hom_id_app_apply (op X) sX
    have h2 := NatTrans.naturality_apply e.hom m.op (𝟙 V')
    have h3 : (yoneda.obj V').map m.op (𝟙 V') = m := Category.comp_id m
    rw [h3, h1] at h2
    exact h2
  have hr₀ : r = GR.arrows.obj.map ((Over.iteratedSliceBackward T).map m).left.op r₀ := by
    rw [← arrowFiberOverArrow_mk hS G hU hR hP a r hrt hrs]
    change arrowFiberOverArrow hS G hU hR hP a sX = _
    rw [hm, arrowFiberOverArrow_map]
  have hr' : ι ≫ pullback.fst π â ≫ ρ =
      (siteToOver B hS).map ((Over.iteratedSliceBackward T).map m).left ≫
        yonedaSchemePointEquiv B hS hR (op V's.left) r₀ := by
    rw [← hr, hr₀]
    exact (siteToOver B hS).map_comp _ _
  -- every stabilizer point over `u` has its arrow in the image of the universal arrow
  have hsub : (AlgebraicGeometry.stabilizerArrow G) ''
      {y | (AlgebraicGeometry.stabilizer G).hom y = u} ⊆
      Set.range (yonedaSchemePointEquiv B hS hR (op V's.left) r₀).left := by
    rintro _ ⟨y, hy, rfl⟩
    have hsq : IsPullback (pullback.fst π â).left (pullback.snd π â).left π.left â.left :=
      (IsPullback.of_hasPullback π â).map (Over.forget S)
    obtain ⟨ξ, hξ, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π.left) (g := â.left)
      y τ (hy.trans (ha τ).symm)
    refine ⟨((siteToOver B hS).map ((Over.iteratedSliceBackward T).map m).left).left
      (hsq.isoPullback.inv ξ), ?_⟩
    have hpt := congrArg (fun k => k.left (hsq.isoPullback.inv ξ)) hr'
    simp only [Over.comp_left] at hpt
    refine hpt.symm.trans ?_
    change ρ.left ((pullback.fst π â).left (hsq.isoPullback.inv ξ)) = ρ.left y
    rw [← Scheme.Hom.comp_apply hsq.isoPullback.inv, IsPullback.isoPullback_inv_fst, hξ]
  have : Finite ((siteToOver B hS).obj V's.left).left := inferInstanceAs (Finite V'.left.1)
  have hfin : (Set.range (yonedaSchemePointEquiv B hS hR (op V's.left) r₀).left).Finite :=
    Set.finite_range _
  exact Set.Finite.of_finite_image (hfin.subset hsub)
    (injective_stabilizerArrow G).injOn

end Stacks.Groupoids.GroupoidScheme

/-! ### The automorphism space of a presented object of a quotient stack -/

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS A)

/-- **The automorphism space of a presented object of the small model of `[U/R]`** is the slice
presheaf of arrows of `R` from the presenting point to itself (Stacks 044V), read on the site of
the base of the object. The small model has the same objects as `[U/R]`, and the comparison
`[U/R]_{small} ⟶ [U/R]` is fully faithful, so the two isomorphism presheaves agree after a universe
lift, which is then cancelled. -/
theorem nonempty_isomSpace_smallQuotientStackCFG_iso (T : BigFppfOver B S hS)
    (a : G.objects.obj.obj (op T)) (x : (smallQuotientStackCFG G).val.p.Fiber T)
    (hx : x.1 = (pointwiseToQuotientStack G).obj ⟨T, a⟩) :
    Nonempty (isomSpace B S hS (smallQuotientStackCFG G) T x x ≅
      (Over.iteratedSliceBackward T).op ⋙ arrowFiberOver G T a a) := by
  let : (smallQuotientStackCFG G).val.p.IsFibered :=
    (smallQuotientStackCFG G).isFiberedInGroupoids.isFibered
  have hQ := isFiberedInGroupoids_quotientStack G
  let : (quotientStack G).p.IsFibered := hQ.isFibered
  let F := (smallQuotientStackEquivalence G).functor
  have hF : (smallQuotientStackCFG G).val.p.IsFibredOneMorphism (quotientStack G).p
      F.toFunctor :=
    { comp_eq := F.w
      map_isStronglyCartesian := by
        intro A A' g a b k hk
        have : (quotientStack G).p.IsHomLift g (F.toFunctor.map k) :=
          Functor.isHomLift_map_of_comp_eq F.w g k
        exact hQ.isStronglyCartesian_homLift g _ }
  have : F.toFunctor.Full := inferInstance
  have : F.toFunctor.Faithful := inferInstance
  let e₁ := liftedIsomPresheafIso.{_, _, _, _, _, u + 1} hF
    (smallQuotientStackCFG G).isFiberedInGroupoids hQ x x
  let e₂ := isomPresheafPullbackIso G T a a ((Functor.fiberFunctorOfCompEq hF.comp_eq T).obj x)
    ((Functor.fiberFunctorOfCompEq hF.comp_eq T).obj x) hx hx
  let e₃ := ((fullyFaithfulULiftFunctor.{u + 1, u}).whiskeringRight _).preimageIso (e₁ ≪≫ e₂.symm)
  exact ⟨Functor.isoWhiskerLeft (Over.iteratedSliceBackward T).op e₃⟩

end AlgebraicGeometry.Stack

/-! ### The stabilizer of a quotient chart at a point with finite automorphism group -/

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A finite algebraic space over a finite affine base is represented by a scheme with finitely
many points.** Read at the identity of the base, the finiteness of
`AlgebraicGeometry.Stack.EtaleLocalStructure.IsFiniteOverBase` represents the algebraic space by
an object of the site finite over the base. -/
theorem exists_iso_yoneda_of_isFiniteOverBase (U : BigFppfOver B S hS) [IsAffine U.left.1]
    [Finite U.left.1] (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsFiniteOverBase B S hS U G) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, Finite V.left.1 ∧ Nonempty (yoneda.obj V ≅ G) := by
  let U' : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  have hU' : IsAffine ((BigFppfOver.toScheme B U.left.1 U.left.2).obj U') :=
    inferInstanceAs (IsAffine U.left.1)
  let ξ : yoneda.obj U' ⟶ siteTerminalSpace B S hS U := yoneda.map (terminal.from U')
  have : IsIso ξ := by
    have : IsIso (terminal.from U') :=
      isIso_of_isTerminal (Over.mkIdTerminal) terminalIsTerminal _
    infer_instance
  obtain ⟨V', q, i, -, -, hpb⟩ := hG U' hU' ξ
  have : IsIso i := hpb.isIso_fst_of_isIso
  exact ⟨V', finite_of_isFiniteOverBase_of_iso B S hS U G V' (asIso i).symm hG, ⟨asIso i⟩⟩

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **A finite automorphism group gives finitely many stabilizer points over the chart point.**
For a quotient chart `[U/R] ⟶ 𝒳` and a point `z ∈ |U|` at whose image `x ∈ |𝒳|` the automorphism
group of `𝒳` is finite (Remark 0DTU), only finitely many points of the stabilizer of the groupoid
`(U, R, s, t, c)` lie over the point of `U` underlying `z`. This is the step "our assumption on
`G_x` implies that `G_u` is finite over `u`" of the proof of Stacks 0DU4. -/
theorem ChartGroupoid.finite_stabilizer (K : ChartGroupoid B S hS 𝒳)
    (z : Space.points B S hS (yoneda.obj K.U))
    (hAut : AutomorphismGroupHasProperty B S hS (IsFiniteOverBase B S hS)
      (AlgebraicStacks.pointsMap B S hS K.map (K.point z))) :
    Set.Finite {y : (AlgebraicGeometry.stabilizer K.groupoid).left |
      (AlgebraicGeometry.stabilizer K.groupoid).hom y = Space.pointsToScheme B S hS K.U z} := by
  let q := Quot.out z
  let p₀ := spaceFieldValuedPoint B S hS (yoneda.obj K.U) q
  let p₁ := fieldValuedPointMap B S hS _ (smallQuotientStackProjection K.realization).hom p₀
  let p := fieldValuedPointMap B S hS _ K.map.hom.hom p₁
  have hfin : IsFiniteOverBase B S hS p.base (pointAutomorphismSpace B S hS 𝒳.val p) :=
    hAut p rfl
  let T := q.siteObject
  have : IsAffine T.left.1 := inferInstanceAs (IsAffine (Spec (.of q.carrier)))
  have : Finite T.left.1 := inferInstanceAs (Finite (PrimeSpectrum q.carrier))
  obtain ⟨V', hV', ⟨i⟩⟩ := exists_iso_yoneda_of_isFiniteOverBase T _ hfin
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let : K.quotient.val.val.p.IsFibered := K.quotient.val.isFiberedInGroupoids.isFibered
  have := K.full
  have := K.faithful
  let x : K.quotient.val.val.p.Fiber T := Functor.Fiber.mk p₁.over
  obtain ⟨e₁⟩ := nonempty_isomSpace_iso_of_fullyFaithful B S hS K.map T x
  obtain ⟨e₂⟩ := nonempty_isomSpace_smallQuotientStackCFG_iso K.realization T q.value x rfl
  have hz : Space.pointsToScheme B S hS K.U z =
      (BigFppfOver.toScheme B S hS).map q.value (IsLocalRing.closedPoint q.carrier) :=
    (congrArg (Space.pointsToScheme B S hS K.U) (Quot.out_eq z)).symm
  have ha : ∀ τ, (Space.yonedaSchemePointEquiv B hS K.contains_objects (op T) q.value).left τ =
      Space.pointsToScheme B S hS K.U z := by
    intro τ
    have : Subsingleton ((Space.siteToOver B hS).obj T).left :=
      inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
    rw [hz, Subsingleton.elim τ (IsLocalRing.closedPoint q.carrier)]
    rfl
  exact Stacks.Groupoids.GroupoidScheme.finite_stabilizer_of_iso_arrowFiberOver hS K.groupoid
    K.contains_objects K.contains_arrows K.contains_pullback q.value _
    (IsLocalRing.closedPoint q.carrier) ha V' (i ≪≫ e₁.symm ≪≫ e₂)

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
