module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.ComparisonMap
import all Mathlib.CategoryTheory.Limits.HasLimits
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber

/-!
# Injectivity of the comparison map for a finite direct image

Germ computations at a lift, sheaf-theoretic separation lemmas over étale coverings, and the
injectivity of each component of the comparison map from the stalk of a direct image to the
stalks over the lifts of a geometric point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

section Bijectivity

/-- The chosen point of `AlgebraicGeometry.liftedEtaleNeighborhood` lies over the chosen point
of the étale neighborhood of `y` it is the base change of. -/
public theorem liftedEtaleNeighborhood_point_fst (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : X ⟶ Y) (y : GeometricPoint Y.1)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (V : (geometricPointFiber B Y.1 Y.property y).Elements) :
    (liftedEtaleNeighborhood B f y x V).2.1 ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1 := by
  simp [liftedEtaleNeighborhood]

/-- **The comparison on germs at a lift, along an arbitrary morphism of neighborhoods.** The
germ at `y` of a section of `f_* F` over an étale neighborhood `V` is sent to the germ at the
lift `x` of its restriction to any pointed étale neighborhood of `x` over `V ×_Y X`. -/
private theorem finitePushforwardStalkComponent_germ_of_hom
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (U : (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements)
    (V : (geometricPointFiber B Y.1 Y.property y).Elements)
    (a : U.1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (ha : U.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1)
    (t : F.obj.obj (op ((smallEtaleBaseChange B f).obj V.1))) :
    finitePushforwardStalkComponent B f y F x
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj F).obj) (op V) t) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj) (op U)
        (F.obj.map a.op t) :=
  pushforwardEtaleStalkComponent_germ B f (geometricPointLift (B.inclusion.map f) y x) y
    (geometricPointLift_map (B.inclusion.map f) y x) F V U a (by simpa using ha) t

private theorem finitePushforwardStalkComponent_germ_eq_iff
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (V : (geometricPointFiber B Y.1 Y.property y).Elements)
    (t t' : F.obj.obj (op ((smallEtaleBaseChange B f).obj V.1))) :
    (let D := (CategoryOfElements.π
      (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj
    finitePushforwardStalkComponent B f y F x (colimit.ι D (op V) t) =
      finitePushforwardStalkComponent B f y F x (colimit.ι D (op V) t')) ↔
    ∃ (W : (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).Elements)
      (a : W ⟶ liftedEtaleNeighborhood B f y x V),
      F.obj.map a.1.op t = F.obj.map a.1.op t' := by
  dsimp only
  rw [finitePushforwardStalkComponent_germ,
    finitePushforwardStalkComponent_germ]
  let D := (CategoryOfElements.π (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj
  refine (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit D)
    (i := op (liftedEtaleNeighborhood B f y x V)) t t').trans ?_
  constructor
  · rintro ⟨W, a, ha⟩
    exact ⟨W.unop, a.unop, ha⟩
  · rintro ⟨W, a, ha⟩
    exact ⟨op W, a.op, ha⟩

open CategoryTheory.Limits in
private theorem exists_geometricLift_of_mem_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : GeometricPoint Y) (x : X) (hx : f x = y.hom default) :
    ∃ g : {g : y.source ⟶ X // g ≫ f = y.hom}, g.1 default = x := by
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := y.hom) x default hx
  let : IsLocallyArtinian (pullback f y.hom) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd f y.hom)
  let p := pointOfClosedPoint (pullback.snd f y.hom) z isClosed_singleton
  refine ⟨⟨p ≫ pullback.fst f y.hom, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (fun a => a ≫ y.hom)
      (pointOfClosedPoint_comp (pullback.snd f y.hom) z isClosed_singleton)).trans
        (Category.id_comp _)
  · show (pullback.fst f y.hom) (p default) = x
    rw [pointOfClosedPoint_apply, hz]

private theorem exists_open_base_of_geometricLifts
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : GeometricPoint Y) (U : X.Opens)
    (hU : ∀ g : {g : y.source ⟶ X // g ≫ f = y.hom}, g.1 default ∈ U) :
    ∃ V : Y.Opens, y.hom default ∈ V ∧ f ⁻¹' (V : Set Y) ⊆ U := by
  let V : Y.Opens := ⟨(f '' (U : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨g, hg⟩ := exists_geometricLift_of_mem_fiber f y x hxy
    exact hx (hg ▸ hU g)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩

private theorem combinatoriallyEquivalent_map
    {C : Type*} [Category C] {D : Type*} [Category D]
    {U : C} {E F : PreZeroHypercover U}
    (h : E.CombinatoriallyEquivalent F) (G : C ⥤ D) :
    (E.map G).CombinatoriallyEquivalent (F.map G) := by
  constructor <;> [obtain ⟨α, hα, eα⟩ := h.1; obtain ⟨α, hα, eα⟩ := h.2] <;>
    exact ⟨α, fun i => congrArg G.obj (hα i), fun i =>
      (congrArg G.map (eα i)).trans (by rw [G.map_comp, eqToHom_map]; rfl)⟩

private theorem smallEtale_generate_covering
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : SmallEtale B S hS) (E : PreZeroHypercover.{u + 1} U)
    (hE : (E.map (SmallEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B S hS).obj U)) :
    Sieve.generate E.presieve₀ ∈ SmallEtale.topology B S hS U := by
  let G := SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)
  obtain ⟨⟨T, C⟩, hC, hEC⟩ := B.exists_covering_rep
    ⟨G.obj U, E.map G⟩ hE
  obtain ⟨hT, hEC⟩ := hEC
  change G.obj U = T at hT
  subst T
  obtain ⟨β, hβ, eβ⟩ := hEC.2
  let D : PreZeroHypercover.{u + 1} U :=
    { I₀ := C.I₀, X := fun j => E.X (β j), f := fun j => E.f (β j) }
  have hDC : (D.map G).CombinatoriallyEquivalent C := by
    constructor
    · refine ⟨id, fun j => (hβ j).symm, ?_⟩
      intro j
      show G.map (E.f (β j)) = eqToHom (hβ j).symm ≫ C.f j
      rw [eβ j, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      rfl
    · exact ⟨id, hβ, eβ⟩
  have hD : SmallEtale.IsCovering B S hS ⟨U, D⟩ := by
    refine ⟨?_, hC.2⟩
    show ((D.map G).map B.inclusion).presieve₀ ∈ _
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
      (combinatoriallyEquivalent_map hDC B.inclusion)]
    exact hC.1
  apply (SmallEtale.topology B S hS).superset_covering
    (show Sieve.generate D.presieve₀ ≤ Sieve.generate E.presieve₀ from
      Sieve.generate_mono (by rintro _ _ ⟨j⟩; exact ⟨β j⟩))
  exact Precoverage.generate_mem_toGrothendieck ⟨D, rfl, hD⟩

open Opposite in
private theorem sections_ext_of_etale_covering
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (U : SmallEtale B S hS) (E : PreZeroHypercover.{u + 1} U)
    (hE : (E.map (SmallEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B S hS).obj U))
    (t t' : F.obj.obj (op U))
    (h : ∀ i, F.obj.map (E.f i).op t = F.obj.map (E.f i).op t') : t = t' := by
  let a : PUnit.{u + 2} ⟶ F.obj.obj (op U) := ↾fun _ => t
  let b : PUnit.{u + 2} ⟶ F.obj.obj (op U) := ↾fun _ => t'
  have hab : a = b := F.property.hom_ext_ofArrows E.f
    (smallEtale_generate_covering B S hS U E hE) (fun i => by
      ext z
      exact h i)
  exact ConcreteCategory.congr_hom hab PUnit.unit

private theorem etale_smallEtale_map
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : SmallEtale B S hS} (a : U ⟶ V) :
    Etale ((SmallEtale.toScheme B S hS).map a) := by
  have h : (SmallEtale.toScheme B S hS).map a ≫ B.inclusion.map V.obj.hom =
      B.inclusion.map U.obj.hom := by
    show B.inclusion.map a.hom.left ≫ _ = _
    rw [← Functor.map_comp, Over.w]
  have : Etale ((SmallEtale.toScheme B S hS).map a ≫ B.inclusion.map V.obj.hom) :=
    h.symm ▸ U.property
  exact Etale.of_comp _ (B.inclusion.map V.obj.hom)

open CategoryTheory.Limits Opposite in
private theorem sections_ext_of_range_subset
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    {U V : SmallEtale B S hS} (a : V ⟶ U)
    {I : Type (u + 1)} (W : I → SmallEtale B S hS) (b : ∀ i, W i ⟶ U)
    (hcover : Set.range ((SmallEtale.toScheme B S hS).map a) ⊆
      ⋃ i, Set.range ((SmallEtale.toScheme B S hS).map (b i)))
    (t t' : F.obj.obj (op U))
    (h : ∀ i, F.obj.map (b i).op t = F.obj.map (b i).op t') :
    F.obj.map a.op t = F.obj.map a.op t' := by
  let T := SmallEtale.toScheme B S hS
  let E : PreZeroHypercover.{u + 1} V :=
    { I₀ := I, X := fun i => pullback (b i) a, f := fun i => pullback.snd (b i) a }
  apply sections_ext_of_etale_covering B S hS F V E
  · show (E.map T).presieve₀ ∈ Scheme.precoverage @Etale (T.obj V)
    refine (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) (E.map T)).2
      ⟨fun v => ?_, fun i => etale_smallEtale_map B S hS (E.f i)⟩
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self v))
    obtain ⟨p, hp, hp'⟩ := Scheme.exists_preimage_of_isPullback
      ((IsPullback.of_hasPullback (b i) a).map T) w v hw
    exact ⟨i, p, hp'⟩
  · intro i
    show F.obj.map (pullback.snd (b i) a).op (F.obj.map a.op t) =
      F.obj.map (pullback.snd (b i) a).op (F.obj.map a.op t')
    have he : a.op ≫ (pullback.snd (b i) a).op =
        (b i).op ≫ (pullback.fst (b i) a).op :=
      congrArg Quiver.Hom.op (pullback.condition (f := b i) (g := a)).symm
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, he]
    simp only [Functor.map_comp, ConcreteCategory.comp_apply]
    exact congrArg (fun z => F.obj.map (pullback.fst (b i) a).op z) (h i)

open CategoryTheory.Limits in
private theorem exists_baseChange_refinement_range_subset
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
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
  have : IsFinite π := MorphismProperty.of_isPullback P.flip
    (inferInstance : IsFinite (B.inclusion.map f))
  obtain ⟨O', hyO', hO'⟩ := exists_open_base_of_geometricLifts π yV O (by
    intro g
    let x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom} :=
      ⟨g.1 ≫ ρ, by
        rw [Category.assoc, ← P.w, ← Category.assoc, g.2]
        exact V.2.2⟩
    have hg : g.1 = (liftedEtaleNeighborhood B f y x V).2.1 := by
      apply P.hom_ext
      · exact g.2.trans (liftedEtaleNeighborhood_point_fst B f y x V).symm
      · exact (liftedEtaleNeighborhood B f y x V).2.2.symm
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

open CategoryTheory.Limits Opposite in
private theorem finitePushforwardStalkComponent_injective
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
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
  have hx := fun x => (finitePushforwardStalkComponent_germ_eq_iff
    B f y F x V.unop t t').mp (congrFun hz x)
  choose W a ha using hx
  let T := SmallEtale.toScheme B X.1 X.property
  have he (x) : Etale (T.map (a x).1) := etale_smallEtale_map B X.1 X.property _
  let O : (T.obj ((smallEtaleBaseChange B f).obj V.unop.1)).Opens :=
    ⟨⋃ x, Set.range (T.map (a x).1), isOpen_iUnion fun x =>
      (T.map (a x).1).isOpenMap.isOpen_range⟩
  have hO (x) : (liftedEtaleNeighborhood B f y x V.unop).2.1 default ∈ O := by
    refine Set.mem_iUnion.mpr ⟨x, (W x).2.1 default, ?_⟩
    have h := congrArg Subtype.val (a x).2
    exact congrArg (fun k => k default) h
  obtain ⟨V', b, hb⟩ := exists_baseChange_refinement_range_subset B f y V.unop O hO
  have ht : F.obj.map ((smallEtaleBaseChange B f).map b.1).op t =
      F.obj.map ((smallEtaleBaseChange B f).map b.1).op t' := by
    apply sections_ext_of_range_subset B X.1 X.property F
      ((smallEtaleBaseChange B f).map b.1)
      (fun x : ULift.{u + 1} {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}
        => (W x.down).1) (fun x => (a x.down).1) _ t t' (fun x => ha x.down)
    intro p hp
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hb hp)
    exact Set.mem_iUnion.mpr ⟨⟨x⟩, hx⟩
  exact (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit D) t t').mpr
    ⟨op V', b.op, ht⟩

end Bijectivity

end AlgebraicGeometry

end
