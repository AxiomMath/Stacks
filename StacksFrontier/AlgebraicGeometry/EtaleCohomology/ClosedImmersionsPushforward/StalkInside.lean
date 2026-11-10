module

public import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.LiftingMorphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BaseChangeFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.Basic

/-!
# Stalks of a direct image along a closed immersion, inside the closed subscheme

Let `i : T ⟶ S` be a closed immersion in a big étale site and let `s` be a geometric point of
`T`. The stalk at `s` of the direct image of a sheaf on the small étale site of `T` is
canonically the stalk of that sheaf at `s`, naturally in the sheaf.

## Main definitions

* `AlgebraicGeometry.pullbackNeighborhoodFunctor` — base change of pointed étale neighbourhoods
  along `i`, from the neighbourhoods of the image point to the neighbourhoods of `s`.

## Main results

* `AlgebraicGeometry.pullbackNeighborhoodFunctor_initial` — that functor is initial, so the two
  colimits defining the stalks agree.
* `AlgebraicGeometry.stalkPushforwardIso` identifies the two stalk functors naturally in the
  sheaf, and `AlgebraicGeometry.stalkPushforwardIso_germ` identifies its action on germs.

## Implementation notes

Base change of étale neighbourhoods is the functor on categories of elements induced by
`AlgebraicGeometry.geometricPointFiberBaseChangeIso`. Initiality has two halves. Every pointed
étale neighbourhood of `s` is dominated by a base change: that is Stacks 04FW, which produces a
Zariski cover of the neighbourhood by base changes of étale schemes over `S`, and an affine
member of that cover containing the image of the point is the required neighbourhood of the
image point. Two maps out of a base change are equalized after a further shrinking: the
equalizer of the two maps is an open subscheme of the base change, and since `i` is a closed
immersion that open extends to an open of the ambient étale neighbourhood, which is the
required shrinking.

Initiality turns the colimit over the neighbourhoods of the image point into the colimit over
the neighbourhoods of `s`, and the two diagrams agree on the nose because the sections of a
direct image over an object are the sections of the sheaf over its base change. The resulting
isomorphism is therefore the canonical one, which
`AlgebraicGeometry.stalkPushforwardIso_germ` records by its effect on germs.

## References

* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The lift of a geometric point along base change composes with the first projection to give
back the original lift. -/
public theorem geometricPointFiberBaseChangeEquiv_val_fst (B : BigEtaleSite.{u})
    {S T : B.Scheme} (i : T ⟶ S) (s : GeometricPoint T.1)
    (U : SmallEtale B S.1 S.property)
    (p : (geometricPointFiber B S.1 S.property (s.map (B.inclusion.map i))).obj U) :
    (geometricPointFiberBaseChangeEquiv B i s U p).1 ≫
      B.inclusion.map (pullback.fst (Over.hom U.obj) i) = p.1 := by
  have hid : eqToHom (smallEtaleBaseChange_toScheme_obj_eq B i U).symm = 𝟙 _ := rfl
  rw [geometricPointFiberBaseChangeEquiv_apply_val, hid]
  simp

/-- The lift of a geometric point along base change composes with the second projection to give
the geometric point itself. -/
public theorem geometricPointFiberBaseChangeEquiv_val_snd (B : BigEtaleSite.{u})
    {S T : B.Scheme} (i : T ⟶ S) (s : GeometricPoint T.1)
    (U : SmallEtale B S.1 S.property)
    (p : (geometricPointFiber B S.1 S.property (s.map (B.inclusion.map i))).obj U) :
    (geometricPointFiberBaseChangeEquiv B i s U p).1 ≫
      B.inclusion.map (pullback.snd (Over.hom U.obj) i) = s.hom :=
  (geometricPointFiberBaseChangeEquiv B i s U p).2

/-- Base change along `i` of the pointed étale neighbourhoods of the image of a geometric
point of `T`, landing in the pointed étale neighbourhoods of the point itself. -/
public def pullbackNeighborhoodFunctor (B : BigEtaleSite.{u}) {S T : B.Scheme} (i : T ⟶ S)
    (s : GeometricPoint T.1) :
    (geometricPointFiber B S.1 S.property (s.map (B.inclusion.map i))).Elements ⥤
      (geometricPointFiber B T.1 T.property s).Elements :=
  NatTrans.mapElements (geometricPointFiberBaseChangeIso B i s).hom ⋙
    { obj x := Functor.elementsMk _ ((smallEtaleBaseChange B i).obj x.1) x.2
      map f := ⟨(smallEtaleBaseChange B i).map f.1, f.2⟩ }

/-- The range of a map out of the source of a geometric point lies in the range of `g` as soon as
the point does. -/
private theorem range_subset_range_of_default_mem {Y X Z : Scheme.{u}} (s : GeometricPoint Y)
    {f : s.source ⟶ X} (g : Z ⟶ X) (h : f.base default ∈ Set.range g.base) :
    Set.range f.base ⊆ Set.range g.base := by
  rintro _ ⟨a, rfl⟩
  rwa [Subsingleton.elim a default]

/-- Two morphisms out of the base change of a pointed étale neighbourhood are equalized after
shrinking the neighbourhood of the image point. -/
private theorem pullbackNeighborhoodFunctor_equalize
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (i : T ⟶ S)
    [IsClosedImmersion (B.inclusion.map i)] (s : GeometricPoint T.1)
    (U : (geometricPointFiber B S.1 S.property
      (s.map (B.inclusion.map i))).Elements)
    (V : (geometricPointFiber B T.1 T.property s).Elements)
    (a b : (pullbackNeighborhoodFunctor B i s).obj U ⟶ V) :
    ∃ (U' : (geometricPointFiber B S.1 S.property
      (s.map (B.inclusion.map i))).Elements) (t : U' ⟶ U),
      (pullbackNeighborhoodFunctor B i s).map t ≫ a =
        (pullbackNeighborhoodFunctor B i s).map t ≫ b := by
  classical
  -- Two morphisms over `S` to an étale `S`-scheme which agree after composing with `q` agree on an
  -- open subscheme containing the image of `q`.
  have exists_opens_range_subset_forall_comp_eq {S A Y Q : Scheme.{u}} (pA : A ⟶ S)
      (pY : Y ⟶ S) [Etale pY] (f g : A ⟶ Y) (hf : f ≫ pY = pA) (hg : g ≫ pY = pA)
      (q : Q ⟶ A) (hq : q ≫ f = q ≫ g) :
      ∃ W : A.Opens, Set.range q.base ⊆ ↑W ∧
        ∀ {Z : Scheme.{u}} (r : Z ⟶ A), Set.range r.base ⊆ ↑W → r ≫ f = r ≫ g := by
    let fOver : Over.mk pA ⟶ Over.mk pY := Over.homMk f hf
    let gOver : Over.mk pA ⟶ Over.mk pY := Over.homMk g hg
    let qOver : Over.mk (q ≫ pA) ⟶ Over.mk pA := Over.homMk q
    have hqOver : qOver ≫ fOver = qOver ≫ gOver := Over.OverMorphism.ext hq
    have : Etale (Over.mk pY).hom := ‹Etale pY›
    have : IsOpenImmersion (Limits.equalizer.ι fOver gOver).left :=
      isOpenImmersion_equalizer_ι_left fOver gOver
    refine ⟨(Limits.equalizer.ι fOver gOver).left.opensRange, ?_, fun r hr => ?_⟩
    · rintro _ ⟨z, rfl⟩
      have hfac : (Limits.equalizer.lift qOver hqOver).left ≫
          (Limits.equalizer.ι fOver gOver).left = q :=
        congrArg CommaMorphism.left (Limits.equalizer.lift_ι qOver hqOver)
      exact Scheme.Hom.mem_opensRange.2 ⟨_, by
        simpa [Scheme.Hom.comp_base] using
          congrArg (fun k : Scheme.Hom _ _ => k.base z) hfac⟩
    · have hrE : Set.range r.base ⊆ Set.range (Limits.equalizer.ι fOver gOver).left.base :=
        fun z hz => Scheme.Hom.mem_opensRange.1 (hr hz)
      have he : (Limits.equalizer.ι fOver gOver).left ≫ f =
          (Limits.equalizer.ι fOver gOver).left ≫ g := by
        simpa [fOver, gOver] using
          congrArg CommaMorphism.left (Limits.equalizer.condition fOver gOver)
      rw [← IsOpenImmersion.lift_fac _ r hrE, Category.assoc, Category.assoc, he]
  -- A pointed étale neighbourhood can be shrunk into any open subscheme containing the image of the
  -- point.
  have exists_hom_range_subset_of_mem (B : BigEtaleSite.{u}) {X : Scheme.{u}}
      {hX : B.Contains X} {x : GeometricPoint X} {U : (geometricPointFiber B X hX x).Elements}
      {O : ((SmallEtale.toScheme B X hX).obj U.1).Opens} (hO : U.2.1.base default ∈ O) :
      ∃ (U' : (geometricPointFiber B X hX x).Elements) (t : U' ⟶ U),
        Set.range ((SmallEtale.toScheme B X hX).map t.1).base ⊆ ↑O := by
    have hjRange : Set.range U.2.1.base ⊆ Set.range O.ι.base :=
      range_subset_range_of_default_mem _ _ ⟨⟨U.2.1.base default, hO⟩, rfl⟩
    let qNew := IsOpenImmersion.lift O.ι U.2.1 hjRange
    have hSize : B.Contains O.toScheme :=
      (Scheme.size_coe_opens_le ((SmallEtale.toScheme B X hX).obj U.1) O).trans_lt
        U.1.obj.left.property
    let Osite := B.obj O.toScheme hSize
    let jSite : Osite ⟶ U.1.obj.left := B.inclusion.preimage
      (show B.inclusion.obj Osite ⟶ B.inclusion.obj U.1.obj.left from O.ι)
    let Unew : SmallEtale B X hX :=
      ⟨Over.mk (jSite ≫ U.1.obj.hom), by
        change Etale (B.inclusion.map (jSite ≫ U.1.obj.hom))
        rw [Functor.map_comp, B.inclusion.map_preimage]
        infer_instance⟩
    have hqNew : qNew ≫ B.inclusion.map (Over.hom Unew.obj) = x.hom := by
      change qNew ≫ B.inclusion.map (jSite ≫ U.1.obj.hom) = _
      rw [Functor.map_comp, B.inclusion.map_preimage]
      change qNew ≫ O.ι ≫ B.inclusion.map (Over.hom U.1.obj) = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact U.2.2
    let tSite : Unew ⟶ U.1 := ObjectProperty.homMk (Over.homMk jSite (by rfl))
    have hmap : (SmallEtale.toScheme B X hX).map tSite = O.ι := by
      dsimp [SmallEtale.toScheme, SmallEtale.inclusion,
        BigEtaleOver.toScheme, BigEtaleOver.forget, tSite]
      change B.inclusion.map jSite = O.ι
      exact B.inclusion.map_preimage _
    refine ⟨Functor.elementsMk _ Unew ⟨qNew, hqNew⟩, ⟨tSite, Subtype.ext ?_⟩, ?_⟩
    · change qNew ≫ (SmallEtale.toScheme B X hX).map tSite = U.2.1
      rw [hmap]
      exact IsOpenImmersion.lift_fac O.ι U.2.1 hjRange
    · rintro _ ⟨z, rfl⟩
      have hz : O.ι.base z ∈ O.ι.opensRange := Scheme.Hom.mem_opensRange.2 ⟨z, rfl⟩
      rw [Scheme.Opens.opensRange_ι] at hz
      change ((SmallEtale.toScheme B X hX).map tSite).base z ∈ O
      rwa [hmap]
  -- The closed immersion from the base change of a pointed étale neighbourhood `U` to `U` restricts
  -- every open containing the point to an open of `U` containing the image point.
  have exists_opens_mem_preimage_eq (B : BigEtaleSite.{u}) {S T : B.Scheme}
      (i : T ⟶ S) [IsClosedImmersion (B.inclusion.map i)] (s : GeometricPoint T.1)
      (U : (geometricPointFiber B S.1 S.property (s.map (B.inclusion.map i))).Elements)
      (W : ((SmallEtale.toScheme B T.1 T.property).obj
        ((pullbackNeighborhoodFunctor B i s).obj U).1).Opens)
      (hW : ((pullbackNeighborhoodFunctor B i s).obj U).2.1.base default ∈ W) :
      ∃ O : ((SmallEtale.toScheme B S.1 S.property).obj U.1).Opens, U.2.1.base default ∈ O ∧
        (eqToHom (smallEtaleBaseChange_toScheme_obj_eq B i U.1) ≫
          B.inclusion.map (pullback.fst U.1.obj.hom i)) ⁻¹ᵁ O = W := by
    let x := (pullbackNeighborhoodFunctor B i s).obj U
    have hobj := smallEtaleBaseChange_toScheme_obj_eq B i U.1
    have hpi : IsClosedImmersion
        (B.inclusion.map (pullback.fst U.1.obj.hom i)) :=
      MorphismProperty.of_isPullback ((IsPullback.of_hasPullback U.1.obj.hom i).map
        B.inclusion).flip (by infer_instance)
    let π : (SmallEtale.toScheme B T.1 T.property).obj x.1 ⟶
        (SmallEtale.toScheme B S.1 S.property).obj U.1 :=
      eqToHom hobj ≫ B.inclusion.map (pullback.fst U.1.obj.hom i)
    have : IsClosedImmersion π :=
      (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
        (eqToHom hobj) (B.inclusion.map (pullback.fst U.1.obj.hom i))).2 hpi
    obtain ⟨O, hO⟩ := exists_open_extension_of_closedImmersion π W
    refine ⟨O, ?_, hO⟩
    have hproj : x.2.1 ≫ π = U.2.1 := by
      dsimp [π, x, pullbackNeighborhoodFunctor]
      exact geometricPointFiberBaseChangeEquiv_val_fst B i s U.1 U.2
    have hmem : x.2.1.base default ∈ π ⁻¹ᵁ O := by
      rw [hO]
      exact hW
    change π.base (x.2.1.base default) ∈ O at hmem
    have hbase : (x.2.1 ≫ π).base default = (U.2.1).base default := by
      simpa [Scheme.Hom.comp_base] using congrArg (fun z : Scheme.Hom _ _ =>
        z.base default) hproj
    change π.base (x.2.1.base default) = (U.2.1).base default at hbase
    rwa [hbase] at hmem
  -- Base change along `i` of a morphism `t` of the small étale site of `S` commutes with the first
  -- projections of the base changes.
  have smallEtaleBaseChange_map_comp_fst (B : BigEtaleSite.{u}) {S T : B.Scheme}
      (i : T ⟶ S) {U' U : SmallEtale B S.1 S.property} (t : U' ⟶ U) :
      (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B i).map t) ≫
          eqToHom (smallEtaleBaseChange_toScheme_obj_eq B i U) ≫
            B.inclusion.map (pullback.fst U.obj.hom i) =
        B.inclusion.map (pullback.fst U'.obj.hom i) ≫
          (SmallEtale.toScheme B S.1 S.property).map t := by
    have hobj := smallEtaleBaseChange_toScheme_obj_eq B i U
    have hr : (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B i).map t) ≫
        eqToHom hobj = B.inclusion.map ((Over.pullback i).map t.hom).left := by
      dsimp [SmallEtale.toScheme, SmallEtale.inclusion,
        BigEtaleOver.toScheme, BigEtaleOver.forget, smallEtaleBaseChange]
      cases hobj
      rfl
    have hj : (SmallEtale.toScheme B S.1 S.property).map t = B.inclusion.map t.hom.left := rfl
    rw [hj, ← B.inclusion.map_comp, ← Category.assoc, hr]
    refine (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map ?_)
    simp [Over.pullback_map_left]
  let H := pullbackNeighborhoodFunctor B i s
  let x := H.obj U
  let A := (SmallEtale.toScheme B T.1 T.property).obj x.1
  let f := (a.1.hom.left).hom
  let g := (b.1.hom.left).hom
  let pA := B.inclusion.map (Over.hom x.1.obj)
  let pY := B.inclusion.map (Over.hom V.1.obj)
  -- A morphism of neighbourhoods `x ⟶ V` is compatible with the points and the structure maps.
  have hom_spec (c : x ⟶ V) : x.2.1 ≫ c.1.hom.left.hom = V.2.1 ∧ c.1.hom.left.hom ≫ pY = pA :=
    ⟨by simpa [x, H, geometricPointFiber] using congrArg Subtype.val c.2,
      congrArg (fun z => z.hom) (Over.w c.1.hom)⟩
  obtain ⟨hfa, hfb⟩ := hom_spec a
  obtain ⟨hgb, hgb'⟩ := hom_spec b
  have : Etale pY := V.1.property
  obtain ⟨W, hqW, hW⟩ :=
    exists_opens_range_subset_forall_comp_eq pA pY f g hfb hgb' x.2.1 (hfa.trans hgb.symm)
  have hobj := smallEtaleBaseChange_toScheme_obj_eq B i U.1
  let π : A ⟶ (SmallEtale.toScheme B S.1 S.property).obj U.1 :=
    eqToHom hobj ≫ B.inclusion.map (pullback.fst U.1.obj.hom i)
  obtain ⟨O, hpointO, hO⟩ := exists_opens_mem_preimage_eq B i s U W (hqW ⟨default, rfl⟩)
  obtain ⟨U', t, ht⟩ := exists_hom_range_subset_of_mem B hpointO
  refine ⟨U', t, ?_⟩
  apply Functor.Elements.hom_ext
  apply (SmallEtale.toScheme B T.1 T.property).map_injective
  let r : (SmallEtale.toScheme B T.1 T.property).obj
      ((smallEtaleBaseChange B i).obj U'.1) ⟶ A :=
    (SmallEtale.toScheme B T.1 T.property).map
      ((smallEtaleBaseChange B i).map t.1)
  change r ≫ f = r ≫ g
  refine hW r ?_
  rw [← hO]
  rintro _ ⟨z, rfl⟩
  have hpoint : π.base (r.base z) = ((SmallEtale.toScheme B S.1 S.property).map t.1).base
      ((B.inclusion.map (pullback.fst U'.1.obj.hom i)).base z) :=
    congrArg (fun k : Scheme.Hom _ _ => k.base z) (smallEtaleBaseChange_map_comp_fst B i t.1)
  change π.base (r.base z) ∈ O
  rw [hpoint]
  exact ht ⟨_, rfl⟩

/-- Every pointed étale neighbourhood of a geometric point of the closed subscheme receives a
morphism from the base change of a pointed étale neighbourhood of its image. -/
private theorem exists_pullback_neighborhood_map
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (i : T ⟶ S)
    [IsClosedImmersion (B.inclusion.map i)] (s : GeometricPoint T.1)
    (V : (geometricPointFiber B T.1 T.property s).Elements) :
    ∃ U : (geometricPointFiber B S.1 S.property
        (s.map (B.inclusion.map i))).Elements,
      Nonempty ((pullbackNeighborhoodFunctor B i s).obj U ⟶ V) := by
  -- A map `x` from the point of `s` to an étale `S`-scheme `X` factors through an object of the
  -- small étale site of `S` that maps to `X` over `S`.
  have exists_smallEtale_lift_of_etale (B : BigEtaleSite.{u}) {S : B.Scheme}
      {Y X : Scheme.{u}} (s : GeometricPoint Y) (g : X ⟶ S.1) [Etale g] (x : s.source ⟶ X) :
      ∃ (U : SmallEtale B S.1 S.property)
        (qX : s.source ⟶ (SmallEtale.toScheme B S.1 S.property).obj U)
        (a₀ : (SmallEtale.toScheme B S.1 S.property).obj U ⟶ X),
        qX ≫ a₀ = x ∧ B.inclusion.map U.obj.hom = a₀ ≫ g := by
    obtain ⟨R, a₀, _, hpoint, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := x default) (U := ⊤) (by simp)
    have hx : Set.range x.base ⊆ Set.range a₀.base :=
      range_subset_range_of_default_mem s _ (by simpa using hpoint)
    have hUsize : B.Contains (Spec R) :=
      (Scheme.size_le_of_locallyOfFiniteType (a₀ ≫ g)).trans_lt S.property
    refine ⟨⟨Over.mk (ObjectProperty.homMk (a₀ ≫ g) : B.obj (Spec R) hUsize ⟶ B.obj S.1 S.property),
      by
        change Etale (a₀ ≫ g)
        infer_instance⟩, IsOpenImmersion.lift a₀ x hx, a₀, IsOpenImmersion.lift_fac _ _ _, rfl⟩
  -- A pointed étale neighbourhood of `s` receives a morphism from the base change of a pointed
  -- étale neighbourhood `U` of the image point as soon as the base change of `U` maps to it
  -- compatibly with the points.
  have nonempty_pullbackNeighborhoodFunctor_obj_hom_of_lift
      (B : BigEtaleSite.{u}) {S T : B.Scheme} (i : T ⟶ S) (s : GeometricPoint T.1)
      (V : (geometricPointFiber B T.1 T.property s).Elements) (U : SmallEtale B S.1 S.property)
      (qX : s.source ⟶ (SmallEtale.toScheme B S.1 S.property).obj U)
      (hqX : qX ≫ B.inclusion.map U.obj.hom = (s.map (B.inclusion.map i)).hom)
      (m : pullback (B.inclusion.map U.obj.hom) (B.inclusion.map i) ⟶
        B.inclusion.obj V.1.obj.left)
      (hm : m ≫ B.inclusion.map V.1.obj.hom =
        pullback.snd (B.inclusion.map U.obj.hom) (B.inclusion.map i))
      (hqm : pullback.lift qX s.hom hqX ≫ m = V.2.1) :
      Nonempty ((pullbackNeighborhoodFunctor B i s).obj
        (Functor.elementsMk _ U ⟨qX, hqX⟩) ⟶ V) := by
    let fU := B.inclusion.map U.obj.hom
    let qP := geometricPointFiberBaseChangeEquiv B i s U ⟨qX, hqX⟩
    have hobj := smallEtaleBaseChange_toScheme_obj_eq B i U
    let β : B.inclusion.obj (pullback U.obj.hom i) ⟶ pullback fU (B.inclusion.map i) :=
      pullback.lift (B.inclusion.map (pullback.fst U.obj.hom i))
        (B.inclusion.map (pullback.snd U.obj.hom i))
        (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])
    have hqP : qP.1 ≫ eqToHom hobj ≫ β = pullback.lift qX s.hom hqX := by
      have hid : eqToHom hobj = 𝟙 _ := by cases hobj; rfl
      simp only [hid]
      dsimp [qP]
      apply pullback.hom_ext
      · calc
          _ = (geometricPointFiberBaseChangeEquiv B i s U ⟨qX, hqX⟩).1 ≫
              B.inclusion.map (pullback.fst U.obj.hom i) := by
                dsimp [β]
                simp only [Category.id_comp, Category.assoc, pullback.lift_fst]
          _ = qX := geometricPointFiberBaseChangeEquiv_val_fst B i s U ⟨qX, hqX⟩
          _ = _ := (pullback.lift_fst qX s.hom _).symm
      · calc
          _ = (geometricPointFiberBaseChangeEquiv B i s U ⟨qX, hqX⟩).1 ≫
              B.inclusion.map (pullback.snd U.obj.hom i) := by
                dsimp [β]
                simp only [Category.id_comp, Category.assoc, pullback.lift_snd]
          _ = s.hom := geometricPointFiberBaseChangeEquiv_val_snd B i s U ⟨qX, hqX⟩
          _ = _ := (pullback.lift_snd qX s.hom _).symm
    let a : (smallEtaleBaseChange B i).obj U ⟶ V.1 := by
      refine ObjectProperty.homMk (Over.homMk (B.inclusion.preimage (β ≫ m)) ?_)
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      change (β ≫ m) ≫ B.inclusion.map V.1.obj.hom = B.inclusion.map (pullback.snd U.obj.hom i)
      rw [Category.assoc, hm]
      exact pullback.lift_snd _ _ _
    refine ⟨⟨a, ?_⟩⟩
    apply Subtype.ext
    dsimp [a]
    change qP.1 ≫ eqToHom hobj ≫ B.inclusion.map (B.inclusion.preimage (β ≫ m)) = V.2.1
    rw [B.inclusion.map_preimage, reassoc_of% hqP, hqm]
  let p := B.inclusion.map V.1.obj.hom
  let q := V.2.1
  have hq : q ≫ p = s.hom := V.2.2
  obtain ⟨W, U₀, f, hf, he⟩ :=
    Stacks.Etale.exists_etale_openCover_isomorphic_pullback_of_isClosedImmersion.{u, u}
      (i := B.inclusion.map i) p
  let j := W.idx (q default)
  obtain ⟨w, hw⟩ := W.covers (q default)
  have hq_range : Set.range q.base ⊆ Set.range (W.f j).base :=
    range_subset_range_of_default_mem s _ ⟨w, hw⟩
  let qW : s.source ⟶ W.X j := IsOpenImmersion.lift (W.f j) q hq_range
  have hqW : qW ≫ W.f j = q := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e, heT⟩ := he j
  have := hf j
  obtain ⟨Usite, qX, a₀, hqa, hU⟩ := exists_smallEtale_lift_of_etale B s (f j)
    (qW ≫ e.hom ≫ pullback.fst (f j) (B.inclusion.map i))
  have hqX : qX ≫ B.inclusion.map Usite.obj.hom = (s.map (B.inclusion.map i)).hom := by
    change _ = s.hom ≫ B.inclusion.map i
    simp only [hU, reassoc_of% hqa, pullback.condition]
    rw [reassoc_of% heT, reassoc_of% hqW, reassoc_of% hq]
  let fU := B.inclusion.map Usite.obj.hom
  let qPB : s.source ⟶ pullback fU (B.inclusion.map i) := pullback.lift qX s.hom hqX
  let k : pullback fU (B.inclusion.map i) ⟶ pullback (f j) (B.inclusion.map i) :=
    pullback.lift (pullback.fst fU (B.inclusion.map i) ≫ a₀)
      (pullback.snd fU (B.inclusion.map i)) (by
        rw [Category.assoc, ← hU]
        exact pullback.condition)
  have hk : qPB ≫ k = qW ≫ e.hom := by
    apply (IsPullback.of_hasPullback (f j) (B.inclusion.map i)).hom_ext
    · calc
        qPB ≫ k ≫ pullback.fst (f j) (B.inclusion.map i) =
            (qPB ≫ pullback.fst fU (B.inclusion.map i)) ≫ a₀ := by
          simp only [k, pullback.lift_fst, Category.assoc]
        _ = qX ≫ a₀ := by
          dsimp [qPB]
          rw [pullback.lift_fst]
        _ = _ := hqa.trans (Category.assoc _ _ _).symm
    · calc
        qPB ≫ k ≫ pullback.snd (f j) (B.inclusion.map i) =
            qPB ≫ pullback.snd fU (B.inclusion.map i) := by
          simp only [k, pullback.lift_snd]
        _ = s.hom := pullback.lift_snd _ _ _
        _ = qW ≫ e.hom ≫ pullback.snd (f j) (B.inclusion.map i) := by
          rw [heT, reassoc_of% hqW, hq]
  refine ⟨Functor.elementsMk _ Usite ⟨qX, hqX⟩,
    nonempty_pullbackNeighborhoodFunctor_obj_hom_of_lift B i s V Usite
      qX hqX (k ≫ e.inv ≫ W.f j) ?_ ?_⟩
  · rw [Category.assoc, Category.assoc, ← heT, Iso.inv_hom_id_assoc]
    exact pullback.lift_snd _ _ _
  · refine (reassoc_of% hk) (e.inv ≫ W.f j) |>.trans ?_
    simp only [Iso.hom_inv_id_assoc, hqW]
    rfl

/-- Base change of pointed étale neighbourhoods along a closed immersion is an initial
functor, so the colimits computing the two stalks agree. -/
public theorem pullbackNeighborhoodFunctor_initial
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (i : T ⟶ S)
    [IsClosedImmersion (B.inclusion.map i)] (s : GeometricPoint T.1) :
    (pullbackNeighborhoodFunctor B i s).Initial := by
  classical
  let H := pullbackNeighborhoodFunctor B i s
  refine ⟨fun V => ?_⟩
  obtain ⟨U, ⟨g⟩⟩ := exists_pullback_neighborhood_map B i s V
  have : Nonempty (CostructuredArrow H V) := ⟨CostructuredArrow.mk g⟩
  apply CategoryTheory.zigzag_isConnected
  intro A₁ A₂
  obtain ⟨c, hc⟩ := IsCofiltered.inf_objs_exists {A₁.left, A₂.left}
  have f₁ : c ⟶ A₁.left := (hc (by simp)).some
  have f₂ : c ⟶ A₂.left := (hc (by simp)).some
  obtain ⟨c', t, ht⟩ := pullbackNeighborhoodFunctor_equalize B i s c V
    (H.map f₁ ≫ A₁.hom) (H.map f₂ ≫ A₂.hom)
  let C : CostructuredArrow H V := CostructuredArrow.mk (H.map (t ≫ f₁) ≫ A₁.hom)
  have hA : C ⟶ A₁ := CostructuredArrow.homMk (t ≫ f₁) (by simp [C, H, Category.assoc])
  have hB : C ⟶ A₂ := CostructuredArrow.homMk (t ≫ f₂)
    (by simpa [C, H, Category.assoc] using ht.symm)
  exact (CategoryTheory.Zigzag.of_inv hA).trans (CategoryTheory.Zigzag.of_hom hB)

/-- The diagram computing the stalk of a direct image at the image point is, after
reindexing along base change, the diagram computing the stalk of the sheaf itself. -/
public noncomputable def stalkPushforwardDiagramIso
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (i : T ⟶ S)
    [IsClosedImmersion (B.inclusion.map i)] (s : GeometricPoint T.1)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1))) :
    ((Functor.Elements.π (geometricPointFiber B S.1 S.property
      (s.map (B.inclusion.map i)))).op ⋙
      (sheafToPresheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))).obj
        (((smallEtaleBaseChange B i).sheafPushforwardContinuous
          (Type (u + 1)) (SmallEtale.topology B S.1 S.property)
          (SmallEtale.topology B T.1 T.property)).obj F)) ≅
    (pullbackNeighborhoodFunctor B i s).op ⋙
      (Functor.Elements.π (geometricPointFiber B T.1 T.property s)).op ⋙ F.obj := by
  classical
  let P := smallEtaleBaseChange B i
  let H := pullbackNeighborhoodFunctor B i s
  let JX := geometricPointFiber B S.1 S.property
    (s.map (B.inclusion.map i))
  let JZ := geometricPointFiber B T.1 T.property s
  let D := (Functor.Elements.π JX).op ⋙
    (sheafToPresheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))).obj
      ((P.sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).obj F)
  let E := H.op ⋙ (Functor.Elements.π JZ).op ⋙ F.obj
  have hobj : ∀ U, D.obj U = E.obj U := fun U => by
    simp [D, E, P, H, JX, JZ, pullbackNeighborhoodFunctor,
      Functor.Elements.π, geometricPointFiber,
      Functor.sheafPushforwardContinuous_obj_obj_obj]
  refine NatIso.ofComponents (fun U => eqToIso (hobj U)) ?_
  intro U V f
  have hU := hobj U
  have hV := hobj V
  have hmap : D.map f ≍ E.map f := by
    dsimp [D, E, P, H, JX, JZ]
    exact HEq.rfl
  have hconj : D.map f = eqToHom hU ≫ E.map f ≫ eqToHom hV.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ hU hV).2 hmap
  calc
    D.map f ≫ eqToHom hV =
        (eqToHom hU ≫ E.map f ≫ eqToHom hV.symm) ≫ eqToHom hV := by
      rw [← hconj]
    _ = eqToHom hU ≫ E.map f := by simp [Category.assoc]

/-- The comparison of the two stalks, for a fixed sheaf. -/
public noncomputable def stalkPushforwardIsoAt
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (i : T ⟶ S)
    [IsClosedImmersion (B.inclusion.map i)] (s : GeometricPoint T.1)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1))) :
    colimit ((Functor.Elements.π (geometricPointFiber B S.1 S.property
      (s.map (B.inclusion.map i)))).op ⋙
      (sheafToPresheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))).obj
        (((smallEtaleBaseChange B i).sheafPushforwardContinuous
          (Type (u + 1)) (SmallEtale.topology B S.1 S.property)
          (SmallEtale.topology B T.1 T.property)).obj F)) ≅
    colimit ((Functor.Elements.π (geometricPointFiber B T.1 T.property s)).op ⋙ F.obj) := by
  let H := pullbackNeighborhoodFunctor B i s
  let G := (Functor.Elements.π (geometricPointFiber B T.1 T.property s)).op ⋙ F.obj
  have : H.Initial := pullbackNeighborhoodFunctor_initial B i s
  have : H.op.Final := Functor.final_op_of_initial H
  exact (colim.mapIso (stalkPushforwardDiagramIso B i s F)) ≪≫
    Functor.Final.colimitIso H.op G

/-- At a geometric point of the closed subscheme, direct image on the small
étale site does not change the stalk. This is natural in the sheaf. -/
@[stacks 04FX "stalk_pushforward_inside"]
public noncomputable def stalkPushforwardIso (B : BigEtaleSite.{u})
    {S T : B.Scheme} (i : T ⟶ S) [IsClosedImmersion (B.inclusion.map i)]
    (s : GeometricPoint T.1) :
    (smallEtaleBaseChange B i).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S.1 S.property) (SmallEtale.topology B T.1 T.property) ⋙
      sheafToPresheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1)) ⋙
      etaleStalkPresheafFunctor B S.1 S.property
        (s.map (B.inclusion.map i)) (Type (u + 1)) ≅
      sheafToPresheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)) ⋙
      etaleStalkPresheafFunctor B T.1 T.property s (Type (u + 1)) := by
  refine NatIso.ofComponents (fun F => stalkPushforwardIsoAt B i s F) ?_
  intro F G φ
  let H := pullbackNeighborhoodFunctor B i s
  let P := smallEtaleBaseChange B i
  let JX := geometricPointFiber B S.1 S.property
    (s.map (B.inclusion.map i))
  let JZ := geometricPointFiber B T.1 T.property s
  let πX := (Functor.Elements.π JX).op
  let πZ := (Functor.Elements.π JZ).op
  let ShX := sheafToPresheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))
  let ShZ := sheafToPresheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1))
  let αX := ShX.map ((P.sheafPushforwardContinuous (Type (u + 1))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).map φ)
  let αZ := ShZ.map φ
  let sourceMap := πX.whiskerLeft αX
  let targetMap := πZ.whiskerLeft αZ
  have hdiag : sourceMap ≫ (stalkPushforwardDiagramIso B i s G).hom =
      (stalkPushforwardDiagramIso B i s F).hom ≫ H.op.whiskerLeft targetMap := by
    ext U
    simp [H, P, JX, JZ, πX, πZ, ShX, ShZ, αX, αZ, sourceMap, targetMap,
      stalkPushforwardDiagramIso, pullbackNeighborhoodFunctor,
      geometricPointFiber, Functor.Elements.π]
    rfl
  have : H.Initial := pullbackNeighborhoodFunctor_initial B i s
  have : H.op.Final := Functor.final_op_of_initial H
  let EF := πZ ⋙ ShZ.obj F
  let EG := πZ ⋙ ShZ.obj G
  have hcolim : colim.map sourceMap ≫
      colim.map (stalkPushforwardDiagramIso B i s G).hom =
      colim.map (stalkPushforwardDiagramIso B i s F).hom ≫
        colim.map (H.op.whiskerLeft targetMap) := by
    simpa only [Functor.map_comp] using congrArg colim.map hdiag
  calc
    colim.map sourceMap ≫ colim.map (stalkPushforwardDiagramIso B i s G).hom ≫
        colimit.pre EG H.op =
      colim.map (stalkPushforwardDiagramIso B i s F).hom ≫
        colim.map (H.op.whiskerLeft targetMap) ≫ colimit.pre EG H.op := by
      rw [← Category.assoc, hcolim, Category.assoc]
    _ = colim.map (stalkPushforwardDiagramIso B i s F).hom ≫
          (colimit.pre EF H.op ≫ colim.map targetMap) :=
        congrArg (fun k => colim.map (stalkPushforwardDiagramIso B i s F).hom ≫ k)
          (colimit.pre_map targetMap H.op).symm

/-- The canonical comparison takes the germ of a section over an étale
neighborhood of the image point to the germ of the same section over its
base change. The compatibility of the two chosen lifts is expressed by the
first pullback projection. -/
@[stacks 04FX "stalk_pushforward_inside"]
public theorem stalkPushforwardIso_germ (B : BigEtaleSite.{u})
    {S T : B.Scheme} (i : T ⟶ S) [IsClosedImmersion (B.inclusion.map i)]
    (s : GeometricPoint T.1)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (N : (geometricPointFiber B S.1 S.property
      (s.map (B.inclusion.map i))).Elements)
    (q : (geometricPointFiber B T.1 T.property s).obj
      ((smallEtaleBaseChange B i).obj N.1))
    (hq : q.1 ≫ B.inclusion.map (pullback.fst N.1.obj.hom i) = N.2.1)
    (σ : (((smallEtaleBaseChange B i).sheafPushforwardContinuous
        (Type (u + 1)) (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).obj F).obj.obj (Opposite.op N.1)) :
    ((stalkPushforwardIso B i s).hom.app F).hom
      ((colimit.ι
        ((Functor.Elements.π (geometricPointFiber B S.1 S.property
          (s.map (B.inclusion.map i)))).op ⋙
          (((smallEtaleBaseChange B i).sheafPushforwardContinuous
            (Type (u + 1)) (SmallEtale.topology B S.1 S.property)
            (SmallEtale.topology B T.1 T.property)).obj F).obj)
        (Opposite.op N)).hom σ) =
      (colimit.ι
        ((Functor.Elements.π (geometricPointFiber B T.1 T.property s)).op ⋙
          F.obj)
        (Opposite.op (Functor.elementsMk _ ((smallEtaleBaseChange B i).obj N.1) q))).hom σ := by
  classical
  let P := smallEtaleBaseChange B i
  let H := pullbackNeighborhoodFunctor B i s
  let JZ := geometricPointFiber B T.1 T.property s
  let G := (Functor.Elements.π JZ).op ⋙ F.obj
  let E := H.op ⋙ (Functor.Elements.π JZ).op ⋙ F.obj
  let D := (Functor.Elements.π
      (geometricPointFiber B S.1 S.property
        (s.map (B.inclusion.map i)))).op ⋙
      (sheafToPresheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))).obj
        ((P.sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S.1 S.property)
          (SmallEtale.topology B T.1 T.property)).obj F)
  have hq_eq : (Functor.elementsMk JZ (P.obj N.1) q) = H.obj N := by
    have hbase : P.obj N.1 = (H.obj N).1 := by
      dsimp [H, pullbackNeighborhoodFunctor]
    refine Functor.Elements.ext _ _ hbase ?_
    cases hbase
    dsimp [H, pullbackNeighborhoodFunctor]
    change q = geometricPointFiberBaseChangeEquiv B i s N.1 N.2
    apply Subtype.ext
    apply ((IsPullback.of_hasPullback N.1.obj.hom i).map B.inclusion).hom_ext
    · exact hq.trans (geometricPointFiberBaseChangeEquiv_val_fst B i s N.1 N.2).symm
    · exact q.2.trans (geometricPointFiberBaseChangeEquiv_val_snd B i s N.1 N.2).symm
  change (stalkPushforwardIsoAt B i s F).hom
      ((colimit.ι D (Opposite.op N)).hom σ) =
    (colimit.ι G (Opposite.op (Functor.elementsMk JZ (P.obj N.1) q))).hom σ
  dsimp [stalkPushforwardIsoAt, P, H, G, D]
  simp only [colimit.ι_map_apply]
  have : H.Initial := pullbackNeighborhoodFunctor_initial B i s
  have : H.op.Final := Functor.final_op_of_initial H
  let δ := (stalkPushforwardDiagramIso B i s F).hom.app (Opposite.op N)
  have hEq : D.obj (Opposite.op N) = E.obj (Opposite.op N) := by
    simp [D, E, P, H, JZ, pullbackNeighborhoodFunctor,
      geometricPointFiber, Functor.Elements.π,
      Functor.sheafPushforwardContinuous_obj_obj_obj]
  have hsection : δ σ = σ := by
    dsimp [δ, stalkPushforwardDiagramIso]
    cases hEq
    rfl
  change (Functor.Final.colimitIso (pullbackNeighborhoodFunctor B i s).op G).hom
      ((colimit.ι ((pullbackNeighborhoodFunctor B i s).op ⋙ G)
        (Opposite.op N)).hom (δ σ)) =
    (colimit.ι G (Opposite.op (Functor.elementsMk JZ (P.obj N.1) q))).hom σ
  calc
    _ = (colimit.ι G (Opposite.op (H.obj N))).hom (δ σ) :=
      congrArg (fun f => f (δ σ)) (Functor.Final.ι_colimitIso_hom H.op G (Opposite.op N))
    _ = (colimit.ι G (Opposite.op (Functor.elementsMk JZ (P.obj N.1) q))).hom σ := by
      cases hq_eq
      exact congrArg
        (fun τ => (colimit.ι G (Opposite.op (H.obj N))).hom τ) hsection

end AlgebraicGeometry
