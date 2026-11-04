module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections

/-!
# Stalks of a direct image along an integral morphism, at the lifts of a geometric point

Let `f : X ⟶ Y` be a morphism of a big étale site and `y` a geometric point of `Y`. For a finite
`f`, `StacksFrontier/AlgebraicGeometry/EtaleCohomology/FinitePushforwardStalk.lean` decomposes the
stalk of `f_* F` at `y` as the product of the stalks of `F` at the lifts of `y`. This file proves
the half of that statement which holds for every *integral* `f`: an element of the stalk of
`f_* F` at `y` is determined by its images at the lifts of `y`.

The input from geometry is that every point of the fibre of `f` over `y` is the image of a lift of
`y`: the fibre is integral over the algebraically closed residue field of the geometric point, so
each of its points is closed with residue field that field. Together with universal closedness
of `f`, this makes an open of the source containing every lift of `y` contain the full preimage of
a Zariski neighbourhood of `y`.

## Main results

* `AlgebraicGeometry.exists_open_base_of_geometricLifts_of_isIntegralHom` — for an integral
  morphism, an open containing every lift of a geometric point contains the preimage of a Zariski
  neighbourhood of the point.
* `AlgebraicGeometry.finitePushforwardStalkComponent_injective_of_isIntegralHom` — for an
  integral morphism the comparison of the stalk of `f_* F` with the product of the stalks of `F`
  over the lifts is injective.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

/-- Every point of the fibre of an integral morphism over a geometric point is hit by a lift of
that geometric point. The fibre is integral over the algebraically closed field `Ω` of the point,
so it is affine and each of its points is closed, its ring being integral over a field; the
residue field at a point is then an integral, hence trivial, extension of `Ω`, which gives a
`Ω`-point through it. -/
private theorem exists_geometricLift_of_mem_fiber_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (y : GeometricPoint Y) (x : X) (hx : f x = y.hom default) :
    ∃ g : {g : y.source ⟶ X // g ≫ f = y.hom}, g.1 default = x := by
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := y.hom) x default hx
  let P := pullback f y.hom
  let q : P ⟶ Spec (.of y.residueField) := pullback.snd f y.hom
  have : IsAffine P := isAffine_of_isAffineHom q
  have hzc : IsClosed ({z} : Set P) := by
    let p : PrimeSpectrum Γ(P, ⊤) := P.isoSpec.hom z
    rw [← show P.isoSpec.hom ⁻¹' {p} = {z} by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, p]
      exact P.isoSpec.hom.homeomorph.injective.eq_iff]
    refine ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 ?_).preimage
      P.isoSpec.hom.continuous
    let := ((Scheme.ΓSpecIso (.of y.residueField)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField y.residueField)).toField
    apply @Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ _ _ _
      q.appTop.hom (isIntegral_appTop_of_universallyClosed q) p.asIdeal p.2
    rw [(Ideal.eq_bot_or_top _).resolve_right (p.2.comap q.appTop.hom).ne_top]
    exact Ideal.bot_isMaximal
  rw [isClosed_singleton_iff_isClosedImmersion] at hzc
  have : IsIso (Spec.preimage (P.fromSpecResidueField z ≫ q)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  let e : P.residueField z ≅ .of y.residueField :=
    (asIso (Spec.preimage (P.fromSpecResidueField z ≫ q))).symm
  let s : Spec (.of y.residueField) ⟶ P := Spec.map e.hom ≫ P.fromSpecResidueField z
  have hs : s ≫ q = 𝟙 _ := by
    have he : Spec.map e.inv = P.fromSpecResidueField z ≫ q := Spec.map_preimage _
    simp only [s, Category.assoc]
    rw [← he, ← Spec.map_comp, e.inv_hom_id, Spec.map_id]
  have hsz : s default = z := by simp [s]
  refine ⟨⟨s ≫ pullback.fst f y.hom, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ y.hom) hs).trans (Category.id_comp _)
  · show (pullback.fst f y.hom) (s default) = x
    rw [hsz, hz]

/-- For an integral morphism, an open of the source containing every lift of a geometric point
of the target contains the full preimage of a Zariski neighbourhood of that point: the complement
of the open has closed image, which misses the point because every point over it is hit by a
lift. -/
public theorem exists_open_base_of_geometricLifts_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (y : GeometricPoint Y) (U : X.Opens)
    (hU : ∀ g : {g : y.source ⟶ X // g ≫ f = y.hom}, g.1 default ∈ U) :
    ∃ V : Y.Opens, y.hom default ∈ V ∧ f ⁻¹' (V : Set Y) ⊆ U := by
  let V : Y.Opens := ⟨(f '' (U : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨g, hg⟩ := exists_geometricLift_of_mem_fiber_of_isIntegralHom f y x hxy
    exact hx (hg ▸ hU g)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩

private theorem exists_baseChange_refinement_range_subset_of_isIntegralHom
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsIntegralHom (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (V : (geometricPointFiber B Y.1 Y.property y).Elements)
    (O : ((SmallEtale.toScheme B X.1 X.property).obj
      ((smallEtaleBaseChange B f).obj V.1)).Opens)
    (hO : ∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
      (liftedEtaleNeighborhood B f y x V).2.1 default ∈ O) :
    ∃ (V' : (geometricPointFiber B Y.1 Y.property y).Elements)
      (a : V' ⟶ V),
      Set.range ((SmallEtale.toScheme B X.1 X.property).map
        ((smallEtaleBaseChange B f).map a.1)) ⊆ O := by
  let T := SmallEtale.toScheme B X.1 X.property
  let P := (IsPullback.of_hasPullback V.1.obj.hom f).map B.inclusion
  let π := B.inclusion.map (pullback.fst V.1.obj.hom f)
  let ρ := B.inclusion.map (pullback.snd V.1.obj.hom f)
  let yV : GeometricPoint V.1.obj.left.1 :=
    { residueField := y.residueField, hom := V.2.1 }
  have : IsIntegralHom π := MorphismProperty.of_isPullback P.flip
    (inferInstance : IsIntegralHom (B.inclusion.map f))
  obtain ⟨O', hyO', hO'⟩ := exists_open_base_of_geometricLifts_of_isIntegralHom π yV O (by
    intro g
    let x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom} :=
      ⟨g.1 ≫ ρ, by
        rw [Category.assoc, ← P.w, ← Category.assoc, g.2]
        exact V.2.2⟩
    have hg : g.1 = (liftedEtaleNeighborhood B f y x V).2.1 :=
      P.hom_ext (g.2.trans (liftedEtaleNeighborhood_point_fst B f y x V).symm)
        (liftedEtaleNeighborhood B f y x V).2.2.symm
    rw [hg]
    exact hO x)
  have hsize : B.Contains O' :=
    (Scheme.size_coe_opens_le _ O').trans_lt V.1.obj.left.property
  let j : B.obj O' hsize ⟶ V.1.obj.left := ObjectProperty.homMk O'.ι
  let V' : SmallEtale B Y.1 Y.property :=
    ⟨Over.mk (j ≫ V.1.obj.hom), by
      show Etale (O'.ι ≫ B.inclusion.map V.1.obj.hom)
      infer_instance⟩
  have hrange : Set.range V.2.1 ⊆ Set.range O'.ι := by
    rintro _ ⟨a, rfl⟩
    refine ⟨⟨V.2.1 a, ?_⟩, rfl⟩
    change V.2.1 default ∈ O' at hyO'
    simpa only [Subsingleton.elim a default] using hyO'
  let v' := IsOpenImmersion.lift O'.ι V.2.1 hrange
  have hv' : v' ≫ O'.ι = V.2.1 := IsOpenImmersion.lift_fac _ _ _
  let N : (geometricPointFiber B Y.1 Y.property y).Elements :=
    ⟨V', ⟨v', by
      show v' ≫ (O'.ι ≫ B.inclusion.map V.1.obj.hom) = y.hom
      rw [← Category.assoc, hv']
      exact V.2.2⟩⟩
  let a : N ⟶ V := ⟨ObjectProperty.homMk (Over.homMk j rfl), Subtype.ext hv'⟩
  refine ⟨N, a, ?_⟩
  rintro _ ⟨z, rfl⟩
  apply hO'
  have hπ : T.map ((smallEtaleBaseChange B f).map a.1) ≫ π =
      B.inclusion.map (pullback.fst V'.obj.hom f) ≫ O'.ι := by
    show B.inclusion.map ((Over.pullback f).map a.1.hom).left ≫ _ =
      B.inclusion.map (pullback.fst V'.obj.hom f) ≫ B.inclusion.map j
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact pullback.lift_fst _ _ _
  have hz := congrArg (fun k => k z) hπ
  show π (T.map ((smallEtaleBaseChange B f).map a.1) z) ∈ O'
  change π (T.map ((smallEtaleBaseChange B f).map a.1) z) =
    O'.ι (B.inclusion.map (pullback.fst V'.obj.hom f) z) at hz
  rw [hz]
  exact (B.inclusion.map (pullback.fst V'.obj.hom f) z).property

/-- **Sections of a sheaf on a small étale site are separated by families covering a range.** If
two sections of `F` over `U` agree on each member of a family `b i : W i ⟶ U`, they agree on any
`a : V ⟶ U` whose image is contained in the union of the images of the `b i`: the base changes of
the `b i` along `a` form an étale covering of `V`. -/
private theorem map_eq_of_range_subset_iUnion
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    {U V : SmallEtale B S hS} (a : V ⟶ U)
    {I : Type*} (W : I → SmallEtale B S hS) (b : ∀ i, W i ⟶ U)
    (hcover : Set.range ((SmallEtale.toScheme B S hS).map a) ⊆
      ⋃ i, Set.range ((SmallEtale.toScheme B S hS).map (b i)))
    (t t' : F.obj.obj (op U))
    (h : ∀ i, F.obj.map (b i).op t = F.obj.map (b i).op t') :
    F.obj.map a.op t = F.obj.map a.op t' := by
  let T := SmallEtale.toScheme B S hS
  have hcov : Sieve.ofArrows (fun i ↦ pullback (b i) a) (fun i ↦ pullback.snd (b i) a) ∈
      SmallEtale.topology B S hS V := by
    refine Stacks.EtaleCohomology.ofArrows_mem_topology B hS _ _ fun v ↦ ?_
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self v))
    obtain ⟨p, -, hp'⟩ := Scheme.exists_preimage_of_isPullback
      ((IsPullback.of_hasPullback (b i) a).map T) w v hw
    exact ⟨i, p, hp'⟩
  let e₁ : PUnit.{u + 2} ⟶ F.obj.obj (op V) := ↾fun _ ↦ F.obj.map a.op t
  let e₂ : PUnit.{u + 2} ⟶ F.obj.obj (op V) := ↾fun _ ↦ F.obj.map a.op t'
  have he : e₁ = e₂ := F.property.hom_ext_ofArrows _ hcov fun i ↦ by
    ext z
    show F.obj.map (pullback.snd (b i) a).op (F.obj.map a.op t) =
      F.obj.map (pullback.snd (b i) a).op (F.obj.map a.op t')
    have hsq : a.op ≫ (pullback.snd (b i) a).op = (b i).op ≫ (pullback.fst (b i) a).op :=
      congrArg Quiver.Hom.op (pullback.condition (f := b i) (g := a)).symm
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hsq]
    simp only [Functor.map_comp, ConcreteCategory.comp_apply]
    exact congrArg (fun z ↦ F.obj.map (pullback.fst (b i) a).op z) (h i)
  exact ConcreteCategory.congr_hom he PUnit.unit

/-- Two sections of `f_* F` over an étale neighbourhood `V` of `y` whose germs have the same
image at a lift `x` of `y` agree on some pointed étale neighbourhood of `x` over `V ×_Y X`. -/
private theorem exists_eq_of_finitePushforwardStalkComponent_germ_eq
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (V : (geometricPointFiber B Y.1 Y.property y).Elements)
    (t t' : F.obj.obj (op ((smallEtaleBaseChange B f).obj V.1)))
    (h : let D := (CategoryOfElements.π
      (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj
    finitePushforwardStalkComponent B f y F x (colimit.ι D (op V) t) =
      finitePushforwardStalkComponent B f y F x (colimit.ι D (op V) t')) :
    ∃ (W : (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).Elements)
      (a : W ⟶ liftedEtaleNeighborhood B f y x V),
      F.obj.map a.1.op t = F.obj.map a.1.op t' := by
  dsimp only at h
  rw [finitePushforwardStalkComponent_germ, finitePushforwardStalkComponent_germ] at h
  obtain ⟨W, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit
    ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj))
    (i := op (liftedEtaleNeighborhood B f y x V)) t t').mp h
  exact ⟨W.unop, a.unop, ha⟩

/-- **Germs of a direct image along an integral morphism are detected at the lifts.** For an
integral morphism `f` and a geometric point `y` of the target, an element of the stalk of
`f_* F` at `y` is determined by its images in the stalks of `F` at the lifts of `y`.

Two sections over an étale neighbourhood `V` of `y` with the same images agree near every lift;
the neighbourhoods on which they agree cover the fibre over `y`, so, `f` being universally closed,
they cover the whole base change over a Zariski neighbourhood of `y` in `V`, where the two
sections therefore agree. -/
public theorem finitePushforwardStalkComponent_injective_of_isIntegralHom
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsIntegralHom (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    Function.Injective (fun z x => finitePushforwardStalkComponent B f y F x z) := by
  classical
  intro z z' hz
  let D := (CategoryOfElements.π
    (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj
  obtain ⟨V, t, t', rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit D) z z'
  choose W a ha using fun x => exists_eq_of_finitePushforwardStalkComponent_germ_eq
    B f y F x V.unop t t' (congrFun hz x)
  let T := SmallEtale.toScheme B X.1 X.property
  have he (x) : Etale (T.map (a x).1) := SmallEtale.etale_toScheme_map B X.1 X.property _
  let O : (T.obj ((smallEtaleBaseChange B f).obj V.unop.1)).Opens :=
    ⟨⋃ x, Set.range (T.map (a x).1), isOpen_iUnion fun x =>
      (T.map (a x).1).isOpenMap.isOpen_range⟩
  have hO (x) : (liftedEtaleNeighborhood B f y x V.unop).2.1 default ∈ O := by
    refine Set.mem_iUnion.mpr ⟨x, (W x).2.1 default, ?_⟩
    exact congrArg (fun k => k default) (congrArg Subtype.val (a x).2)
  obtain ⟨V', b, hb⟩ := exists_baseChange_refinement_range_subset_of_isIntegralHom B f y V.unop O hO
  have ht : F.obj.map ((smallEtaleBaseChange B f).map b.1).op t =
      F.obj.map ((smallEtaleBaseChange B f).map b.1).op t' :=
    map_eq_of_range_subset_iUnion B X.1 X.property F ((smallEtaleBaseChange B f).map b.1)
      (fun x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom} => (W x).1)
      (fun x => (a x).1) hb t t' ha
  exact (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit D) t t').mpr
    ⟨op V', b.op, ht⟩

end AlgebraicGeometry

end
