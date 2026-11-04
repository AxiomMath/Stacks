module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PushforwardPushforwardAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalDual
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedComparison
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcomposeBaseChangeAdjunction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonUnivLE
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves

/-!
# The comparison map along an étale arrow, for modules (Stacks 075D (2))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `β : z ⟶ x` an arrow of `𝒳`
lying over an étale morphism of schemes `e : U_z ⟶ U_x`. **Stacks 075D** part (2) says that the
comparison map `c_β : e_{small}^*(F|_{U_x,ét}) ⟶ F|_{U_z,ét}` of **Stacks 06WC** is an
isomorphism. This file proves it for presheaves of modules, with `e_{small}^*` the inverse image
of presheaves of modules, and deduces that local bijectivity of a morphism of modules on the
small étale site of `U_x` can be checked after inverse image along a jointly surjective family
of étale arrows into `x`.

## Main definitions

* `AlgebraicGeometry.Stack.etaleChartModuleAdjunction`: post-composition with the chart of `β`
  and base change along `e` induce adjoint direct images of presheaves of modules.
* `AlgebraicGeometry.Stack.etaleChartPullbackIso`: hence the inverse image along the map of
  structure sheaves below `β` is restriction along post-composition with the chart.

## Main results

* `AlgebraicGeometry.SmallEtale.isLocallyBijective_of_postcompose`: local bijectivity on the
  small étale site is étale-local.
* `AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparisonUnivLE_of_etale`:
  **Stacks 075D (2)** for the comparison map of a presheaf of modules.
* `AlgebraicGeometry.Stack.isLocallyBijective_of_pullback_etaleChart`: local bijectivity after
  inverse image along a jointly surjective family of étale arrows.

## Implementation notes

The inverse image `e_{small}^*` of presheaves of modules is a left adjoint with no formula. The
base change functor along `e` between small étale sites has post-composition with `e` as its left
adjoint, and so the direct image along post-composition is a second left adjoint of the direct
image along base change (`PresheafOfModules.pushforwardPushforwardAdjunction`); the uniqueness of
left adjoints identifies the two. Read through that identification, the comparison map is on each
small étale object restriction of the module along a single arrow of `𝒳` whose image in schemes
is an isomorphism, and such an arrow is an isomorphism since `p` is fibred in groupoids.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m

namespace AlgebraicGeometry.SmallEtale

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- **Local bijectivity on the small étale site is étale-local.** If the objects `V i` cover the
final object of the small étale site of `X`, a morphism of presheaves `c` on that site is
locally injective and locally surjective as soon as its restriction along post-composition with
each `V i`, to the small étale site of `V i`, is. -/
theorem isLocallyBijective_of_postcompose (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) {I : Type*} (V : I → SmallEtale B X hX)
    (hV : (topology B X hX).CoversTop V) {P Q : (SmallEtale B X hX)ᵒᵖ ⥤ A} (c : P ⟶ Q)
    (hc : ∀ i, Presheaf.IsLocallyInjective (topology B (V i).obj.left.obj (V i).obj.left.property)
        (Functor.whiskerLeft (smallEtalePostcompose B X hX (V i)).op c) ∧
      Presheaf.IsLocallySurjective (topology B (V i).obj.left.obj (V i).obj.left.property)
        (Functor.whiskerLeft (smallEtalePostcompose B X hX (V i)).op c)) :
    Presheaf.IsLocallyInjective (topology B X hX) c ∧
      Presheaf.IsLocallySurjective (topology B X hX) c := by
  have key : ∀ i, Presheaf.IsLocallyInjective ((topology B X hX).over (V i))
        (Functor.whiskerLeft (Over.forget (V i)).op c) ∧
      Presheaf.IsLocallySurjective ((topology B X hX).over (V i))
        (Functor.whiskerLeft (Over.forget (V i)).op c) := by
    intro i
    let e := localizationEquivalence B X hX (V i)
    have hcp := Functor.IsDenseSubsite.coverPreserving
      (topology B (V i).obj.left.obj (V i).obj.left.property) ((topology B X hX).over (V i))
      e.functor
    have := Functor.IsDenseSubsite.isCoverDense
      (topology B (V i).obj.left.obj (V i).obj.left.property) ((topology B X hX).over (V i))
      e.functor
    exact ⟨(Presheaf.isLocallyInjective_whisker_iff _ _ e.functor _ hcp).1 (hc i).1,
      (Presheaf.isLocallySurjective_whisker_iff _ _ e.functor _ hcp).1 (hc i).2⟩
  exact ⟨Presheaf.isLocallyInjective_of_coversTop _ c hV (fun i => (key i).1),
    Presheaf.isLocallySurjective_of_coversTop _ c hV (fun i => (key i).2)⟩

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {z x : 𝒳} (β : z ⟶ x) (hβ : Etale (B.inclusion.map (p.map β).left))

/-- For an arrow `β : z ⟶ x` lying over an étale morphism of schemes, post-composition with its
chart is left adjoint to base change along the morphism of schemes below `β`
(`AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction`). -/
noncomputable def etaleChartAdjunction :
    smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
        (etaleChart B E h S hS p β hβ) ⊣
      smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p β) :=
  SmallEtale.postcomposeBaseChangeAdjunction E (p.obj x).left.1 (contains_base B E h S hS p x)
    (etaleChart B E h S hS p β hβ)

/-- The counit of `AlgebraicGeometry.Stack.etaleChartAdjunction` is the first projection of the
fibre product. -/
theorem etaleChartAdjunction_counit_app_left
    (W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    ((etaleChartAdjunction B E h S hS p β hβ).counit.app W).hom.left =
      pullback.fst W.obj.hom (smallEtaleBaseMorphism B E h S hS p β) := by
  simp [etaleChartAdjunction, SmallEtale.postcomposeBaseChangeAdjunction,
    Adjunction.restrictFullyFaithful, Over.mapPullbackAdj, Functor.FullyFaithful.homEquiv]
  rfl

/-- The unit of `AlgebraicGeometry.Stack.etaleChartAdjunction` is a section of the first
projection of the fibre product. -/
theorem etaleChartAdjunction_unit_app_left
    (V : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z)) :
    ((etaleChartAdjunction B E h S hS p β hβ).unit.app V).hom.left ≫
      pullback.fst (V.obj.hom ≫ smallEtaleBaseMorphism B E h S hS p β)
        (smallEtaleBaseMorphism B E h S hS p β) = 𝟙 _ := by
  simp only [Functor.id_obj, Functor.comp_obj, smallEtaleBaseChange_obj_obj, Over.pullback_obj_left,
    etaleChartAdjunction, SmallEtale.postcomposeBaseChangeAdjunction,
    Adjunction.restrictFullyFaithful, ObjectProperty.ι_obj, Functor.FullyFaithful.homEquiv,
    Equiv.trans_def, Over.mapPullbackAdj, Over.map_obj_left, Adjunction.mkOfHomEquiv_homEquiv,
    Adjunction.mkOfHomEquiv_unit_app, Equiv.trans_apply, Equiv.coe_fn_mk, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, Iso.homCongr_apply, Iso.app_inv, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id]
  exact pullback.lift_fst _ _ _

/-- The unit of `AlgebraicGeometry.Stack.etaleChartAdjunction`, followed by the first projection,
is the identity after inclusion into schemes. -/
private theorem etaleChartAdjunction_unit_app_left_inclusion
    (V : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z)) :
    E.inclusion.map ((etaleChartAdjunction B E h S hS p β hβ).unit.app V).hom.left ≫
      E.inclusion.map (pullback.fst (V.obj.hom ≫ smallEtaleBaseMorphism B E h S hS p β)
        (smallEtaleBaseMorphism B E h S hS p β)) = 𝟙 _ :=
  (E.inclusion.map_comp _ _).symm.trans ((congrArg E.inclusion.map
    (etaleChartAdjunction_unit_app_left B E h S hS p β hβ V)).trans (E.inclusion.map_id _))

/-- The map of structure sheaves below an étale arrow is restriction along the counit of
`AlgebraicGeometry.Stack.etaleChartAdjunction`. -/
theorem etaleChart_structureSheaf_counit :
    Functor.whiskerRight (NatTrans.op (etaleChartAdjunction B E h S hS p β hβ).counit)
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj =
      smallEtaleStructureComparison B E h S hS p hp β (etaleTopology B)
          (etaleTopology_le_topology B) ≫
        Functor.whiskerLeft (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p β)).op
          (eqToHom (by rfl) : (SmallEtale.structureSheaf E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj ⟶
            (smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
              (etaleChart B E h S hS p β hβ)).op ⋙
            (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj) := by
  rw [smallEtaleStructureComparison_eq_smallEtaleStructureMapRing]
  ext W : 2
  induction W with | op W => ?_
  simp only [Functor.whiskerRight_app, NatTrans.op_app]
  have key : (etaleChartAdjunction B E h S hS p β hβ).counit.app W =
      ObjectProperty.homMk (Over.homMk
        (pullback.fst W.obj.hom (smallEtaleBaseMorphism B E h S hS p β))
        (by simpa [etaleChartAdjunction_counit_app_left] using
          ((etaleChartAdjunction B E h S hS p β hβ).counit.app W).hom.w)) :=
    ObjectProperty.hom_ext _
      (Over.OverMorphism.ext (etaleChartAdjunction_counit_app_left B E h S hS p β hβ W))
  rw [key]
  rfl

/-- The map of structure sheaves below an étale arrow, transported along post-composition and
followed by restriction along the unit of `AlgebraicGeometry.Stack.etaleChartAdjunction`, is
the identity. -/
theorem etaleChart_structureSheaf_unit :
    (eqToHom (by rfl) : (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z)).obj ⟶
        (smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
          (etaleChart B E h S hS p β hβ)).op ⋙
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj) ≫
      Functor.whiskerLeft (smallEtalePostcompose E (p.obj x).left.1
          (contains_base B E h S hS p x) (etaleChart B E h S hS p β hβ)).op
        (smallEtaleStructureComparison B E h S hS p hp β (etaleTopology B)
          (etaleTopology_le_topology B)) ≫
      Functor.whiskerRight (NatTrans.op (etaleChartAdjunction B E h S hS p β hβ).unit)
        (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj =
      𝟙 _ := by
  rw [smallEtaleStructureComparison_eq_smallEtaleStructureMapRing]
  ext V : 2
  induction V with | op V => ?_
  simp only [NatTrans.comp_app, eqToHom_app, Functor.whiskerRight_app,
    NatTrans.op_app, NatTrans.id_app]
  change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (E.inclusion.map
      (pullback.fst (V.obj.hom ≫ smallEtaleBaseMorphism B E h S hS p β)
        (smallEtaleBaseMorphism B E h S hS p β))).op) ≫
    (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (E.inclusion.map
      ((etaleChartAdjunction B E h S hS p β hβ).unit.app V).hom.left).op) = 𝟙 _
  have h2 := congrArg (fun k => (forget₂ CommRingCat RingCat).map (Scheme.Γ.map k.op))
    (etaleChartAdjunction_unit_app_left_inclusion B E h S hS p β hβ V)
  simp only [op_comp, Functor.map_comp, op_id] at h2
  exact h2

/-- The adjunction between the direct images of presheaves of modules along post-composition with
the chart of an étale arrow and along base change, over the map of structure sheaves below the
arrow. -/
noncomputable def etaleChartModuleAdjunction [UnivLE.{u, m}] :
    PresheafOfModules.pushforward.{m}
        (F := smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
          (etaleChart B E h S hS p β hβ)) (eqToHom (by rfl)) ⊣
      PresheafOfModules.pushforward.{m}
        (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p β))
        (smallEtaleStructureComparison B E h S hS p hp β (etaleTopology B)
          (etaleTopology_le_topology B)) :=
  PresheafOfModules.pushforwardPushforwardAdjunction (etaleChartAdjunction B E h S hS p β hβ)
    _ _ (etaleChart_structureSheaf_counit B E h S hS p hp β hβ)
    (etaleChart_structureSheaf_unit B E h S hS p hp β hβ)

include hp in
/-- Since `p` is fibred in groupoids, an arrow of `𝒳` is an isomorphism as soon as the morphism of
schemes below it, followed by an isomorphism, is an isomorphism. -/
private theorem isIso_of_isIso_inclusion_map_left_comp {a b : 𝒳} (θ : a ⟶ b) {T : Scheme.{u}}
    (g : B.inclusion.obj (p.obj b).left ⟶ T) (hg : IsIso g)
    (hθg : IsIso (B.inclusion.map (p.map θ).left ≫ g)) : IsIso θ := by
  have : IsIso (B.inclusion.map (p.map θ).left) := IsIso.of_isIso_comp_right _ g
  have : IsIso (p.map θ).left := isIso_of_reflects_iso _ B.inclusion
  have : IsIso ((Over.forget (B.obj hS)).map (p.map θ)) := this
  have : IsIso (p.map θ) := isIso_of_reflects_iso _ (Over.forget _)
  have : p.IsStronglyCartesian (p.map θ) θ := hp.isStronglyCartesian_homLift _ _
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map θ) θ

private theorem comp_comp_eq_of_comp_eq_of_retraction {C : Type*} [Category C]
    {a b c d e : C} {ν : a ⟶ b} {φ : b ⟶ c} {εx : c ⟶ e} {εz' : b ⟶ d} {f : d ⟶ e}
    {εz : a ⟶ e} {u : e ⟶ d} (hφ : φ ≫ εx = εz' ≫ f) (hν : ν ≫ εz' = εz ≫ u)
    (hu : u ≫ f = 𝟙 e) : (ν ≫ φ) ≫ εx = εz := by
  rw [Category.assoc, hφ, ← Category.assoc, hν, Category.assoc, hu, Category.comp_id]

/-- The transpose, under `AlgebraicGeometry.Stack.etaleChartModuleAdjunction`, of the comparison
of **Stacks 06W2** for a presheaf of modules along an étale arrow is an isomorphism: on each small
étale object it is restriction along an arrow of `𝒳` lying over an isomorphism of schemes. -/
theorem isIso_etaleChartModuleAdjunction_homEquiv_symm [UnivLE.{u, m}]
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    IsIso (((etaleChartModuleAdjunction B E h S hS p hp β hβ).homEquiv _ _).symm
      (restrictModulePushforwardComparison B E h S hS p hp β (etaleTopology B)
        (etaleTopology_le_topology B) F)) := by
  rw [Adjunction.homEquiv_counit, ← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro W
  induction W with | op W => ?_
  let L := smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
    (etaleChart B E h S hS p β hβ)
  obtain ⟨φ', hfac, hproj⟩ := exists_restrictionComparisonLift B E h S hS p hp β (L.obj W)
  change IsIso ((restrictionPushforwardComparison B E h S hS p hp β F.presheaf).app
      (Opposite.op (L.obj W)) ≫ (restrictToSmallEtale B E h S hS p hp z F.presheaf).map
        ((etaleChartAdjunction B E h S hS p β hβ).unit.app W).op)
  rw [restrictionPushforwardComparison_app B E h S hS p hp β F.presheaf (L.obj W) φ' hfac hproj]
  let Pz := Over.post (X := z) (p ⋙ Over.forget (B.obj hS))
  let Qx := Over.post (X := x) (p ⋙ Over.forget (B.obj hS))
  let : Pz.IsEquivalence := isEquivalence_overPost B S hS p hp z
  let : Qx.IsEquivalence := isEquivalence_overPost B S hS p hp x
  let iz := smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z)
  let ix := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)
  let u := (etaleChartAdjunction B E h S hS p β hβ).unit.app W
  let ν := (Pz.inv.map (iz.map u)).left
  change IsIso (F.presheaf.map φ'.op ≫ F.presheaf.map ν.op)
  rw [← Functor.map_comp, ← op_comp]
  suffices hθ : IsIso (ν ≫ φ') from Functor.map_isIso _ _
  have hA := congrArg (fun k => B.inclusion.map k.left)
    (Pz.asEquivalence.counit.naturality (iz.map u))
  simp only [Functor.comp_map, Functor.id_map, Over.comp_left, Functor.map_comp] at hA
  let εz := Pz.asEquivalence.counit.app (iz.obj W)
  let εz' := Pz.asEquivalence.counit.app (iz.obj ((smallEtaleBaseChange E
    (smallEtaleBaseMorphism B E h S hS p β)).obj (L.obj W)))
  let εx := Qx.asEquivalence.counit.app (ix.obj (L.obj W))
  have hA' : B.inclusion.map (p.map ν).left ≫ B.inclusion.map εz'.left =
      B.inclusion.map εz.left ≫ E.inclusion.map u.hom.left := hA
  have hu : E.inclusion.map u.hom.left ≫ E.inclusion.map
      (pullback.fst (L.obj W).obj.hom (smallEtaleBaseMorphism B E h S hS p β)) = 𝟙 _ :=
    etaleChartAdjunction_unit_app_left_inclusion B E h S hS p β hβ W
  have key : B.inclusion.map (p.map (ν ≫ φ')).left ≫ B.inclusion.map εx.left =
      B.inclusion.map εz.left := by
    rw [Functor.map_comp, Over.comp_left, Functor.map_comp]
    exact comp_comp_eq_of_comp_eq_of_retraction hproj hA' hu
  have hεz : IsIso (B.inclusion.map εz.left) :=
    inferInstanceAs (IsIso (B.inclusion.map ((Over.forget _).map εz)))
  have hεx : IsIso (B.inclusion.map εx.left) :=
    inferInstanceAs (IsIso (B.inclusion.map ((Over.forget _).map εx)))
  exact isIso_of_isIso_inclusion_map_left_comp B S hS p hp (ν ≫ φ') _ hεx (key ▸ hεz)

/-- The inverse image of presheaves of modules along the map of structure sheaves below an arrow
lying over an étale morphism is restriction along post-composition with its chart. -/
noncomputable def etaleChartPullbackIso [UnivLE.{u, m}] :
    PresheafOfModules.pullback.{m}
        (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p β))
        (smallEtaleStructureComparison B E h S hS p hp β (etaleTopology B)
          (etaleTopology_le_topology B)) ≅
      PresheafOfModules.pushforward.{m}
        (F := smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
          (etaleChart B E h S hS p β hβ)) (eqToHom (by rfl)) :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{m} _).leftAdjointUniq
    (etaleChartModuleAdjunction B E h S hS p hp β hβ)

/-- **Stacks 075D (2) for the comparison map of Stacks 06WC.** Along an arrow lying over an
étale morphism of schemes the comparison map of a presheaf of modules is an isomorphism. -/
theorem isIso_restrictModulePullbackComparisonUnivLE_of_etale [UnivLE.{u, m}]
    (hβ : Etale (B.inclusion.map (p.map β).left))
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    IsIso (restrictModulePullbackComparisonUnivLE B E h S hS p hp β (etaleTopology B)
      (etaleTopology_le_topology B) F) := by
  have := isIso_etaleChartModuleAdjunction_homEquiv_symm B E h S hS p hp β hβ F
  change IsIso (((PresheafOfModules.pullbackPushforwardAdjunction.{m} _).homEquiv _ _).symm _)
  rw [Adjunction.homEquiv_symm_eq_leftAdjointUniq_hom_app_comp _
    (etaleChartModuleAdjunction B E h S hS p hp β hβ)]
  infer_instance

/-- The charts of a jointly surjective family of arrows into `x` lying over étale morphisms of
schemes cover the final object of the small étale site of the scheme below `x`. -/
theorem coversTop_etaleChart_of_jointlySurjective {I : Type (u + 1)} (z : I → 𝒳)
    (β : ∀ i, z i ⟶ x)
    (hβ : ∀ i, Etale (B.inclusion.map (p.map (β i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (β i)).left)) :
    (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)).CoversTop
      (fun i => etaleChart B E h S hS p (β i) (hβ i)) := by
  let hx := contains_base B E h S hS p x
  let W := SmallEtale.final E (p.obj x).left.1 hx
  apply (GrothendieckTopology.coversTop_iff_of_isTerminal _ W
    (SmallEtale.finalIsTerminal E (p.obj x).left.1 hx) _).2
  refine (SmallEtale.topology E (p.obj x).left.1 hx).superset_covering ?_
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective E (p.obj x).left.1 hx
      (fun i => etaleChart B E h S hS p (β i) (hβ i))
      (fun i => ObjectProperty.homMk (Over.homMk (etaleChart B E h S hS p (β i) (hβ i)).obj.hom
        (by simp [W, SmallEtale.final]))) (fun t => by
        obtain ⟨i, hi⟩ := hcov t
        exact ⟨i, hi⟩))
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact ⟨i, ⟨𝟙 _⟩⟩

/-- **A local isomorphism of modules on the small étale site can be checked after inverse image
along a jointly surjective family of étale arrows.** For a morphism `c` of presheaves of modules
on the small étale site of the scheme below `x`, if its inverse images along the maps of
structure sheaves below a jointly surjective family of étale arrows `β i : z i ⟶ x` are local
isomorphisms, so is `c`. -/
theorem isLocallyBijective_of_pullback_etaleChart [UnivLE.{u, m}]
    {M N : PresheafOfModules.{m}
      (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj}
    (c : M ⟶ N) {I : Type (u + 1)} (z : I → 𝒳) (β : ∀ i, z i ⟶ x)
    (hβ : ∀ i, Etale (B.inclusion.map (p.map (β i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (β i)).left))
    (hc : ∀ i, Presheaf.IsLocallyInjective
        (SmallEtale.topology E (p.obj (z i)).left.1 (contains_base B E h S hS p (z i)))
        ((PresheafOfModules.toPresheaf _).map ((PresheafOfModules.pullback.{m}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (β i)))
          (smallEtaleStructureComparison B E h S hS p hp (β i) (etaleTopology B)
            (etaleTopology_le_topology B))).map c)) ∧
      Presheaf.IsLocallySurjective
        (SmallEtale.topology E (p.obj (z i)).left.1 (contains_base B E h S hS p (z i)))
        ((PresheafOfModules.toPresheaf _).map ((PresheafOfModules.pullback.{m}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (β i)))
          (smallEtaleStructureComparison B E h S hS p hp (β i) (etaleTopology B)
            (etaleTopology_le_topology B))).map c))) :
    Presheaf.IsLocallyInjective
        (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
        ((PresheafOfModules.toPresheaf _).map c) ∧
      Presheaf.IsLocallySurjective
        (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
        ((PresheafOfModules.toPresheaf _).map c) := by
  refine SmallEtale.isLocallyBijective_of_postcompose E (p.obj x).left.1
    (contains_base B E h S hS p x) _
    (coversTop_etaleChart_of_jointlySurjective B E h S hS p z β hβ hcov) _
    fun i => ?_
  let e := etaleChartPullbackIso.{u, v, w, m} B E h S hS p hp (β i) (hβ i)
  obtain ⟨h₁, h₂⟩ := hc i
  let T := PresheafOfModules.toPresheaf
    (SmallEtale.structureSheaf E (p.obj (z i)).left.1 (contains_base B E h S hS p (z i))).obj
  let L := smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
    (etaleChart B E h S hS p (β i) (hβ i))
  let φ0 : (SmallEtale.structureSheaf E (p.obj (z i)).left.1
        (contains_base B E h S hS p (z i))).obj ⟶
      L.op ⋙ (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
    eqToHom (by rfl)
  let iso := PresheafOfModules.pushforwardCompToPresheaf.{m} (F := L) φ0
  have hfac : T.map (e.inv.app M) ≫ T.map ((PresheafOfModules.pullback.{m}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (β i)))
          (smallEtaleStructureComparison B E h S hS p hp (β i) (etaleTopology B)
            (etaleTopology_le_topology B))).map c) ≫ T.map (e.hom.app N) =
      (PresheafOfModules.pushforward.{m} φ0 ⋙ PresheafOfModules.toPresheaf _).map c := by
    rw [← Functor.map_comp, ← Functor.map_comp, e.hom.naturality c, ← Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
    rfl
  change Presheaf.IsLocallyInjective
      (SmallEtale.topology E (p.obj (z i)).left.1 (contains_base B E h S hS p (z i)))
      ((PresheafOfModules.toPresheaf _ ⋙ (Functor.whiskeringLeft _ _ _).obj L.op).map c) ∧
    Presheaf.IsLocallySurjective
      (SmallEtale.topology E (p.obj (z i)).left.1 (contains_base B E h S hS p (z i)))
      ((PresheafOfModules.toPresheaf _ ⋙ (Functor.whiskeringLeft _ _ _).obj L.op).map c)
  rw [← NatIso.naturality_1 iso c, ← hfac]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Stack

end
