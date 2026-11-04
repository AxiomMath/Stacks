module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AssociatedModuleBaseChangeFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSmallEtaleIsoComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonTransposeSquare
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasiIso

/-!
# The sheafified comparison map of Stacks 06WC along étale arrows

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `φ : x ⟶ y` an arrow of `𝒳`
lying over an *étale* morphism of schemes `a : U ⟶ V`. Base change along `a` from the small étale
site of `V` to that of `U` has a left adjoint, composition with `a` (Stacks 03S3), so the pullback
of sheaves of modules along `a` is restriction along composition with `a`: an étale `U`-scheme has
the same global functions whether it is read over `U` or over `V`.

Through that identification the sheafified Stacks 06WC pullback along `φ` is, on the sections over
an étale `U`-scheme, the value over the same scheme read over `V`. Hence a morphism of sheaves of
modules on the small étale site below `z` is an isomorphism as soon as its sheafified pullbacks
along a family of arrows lying over étale morphisms are, provided the objects of the small étale
site mapping to the charts of the family cover the final object.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtalePostcomposeModules`: restriction of a sheaf of modules on the
  small étale site of `T` along composition with an étale morphism `f : T' ⟶ T`.
* `AlgebraicGeometry.Stack.smallEtalePostcomposeModulesAdjunction`: it is left adjoint to the
  pushforward along the morphism of ringed small étale sites of `f`.

## Main results

* `AlgebraicGeometry.Stack.isIso_of_isIso_sheafifiedPullbackComparison_map_of_coversTop`: the
  sheafified Stacks 06WC pullbacks along a family of étale arrows whose charts cover detect
  isomorphisms of sheaves of modules.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The morphism of the big étale site below an arrow lying over an étale morphism is étale. -/
theorem etale_smallEtaleBaseMorphism {x y : 𝒳} (φ : x ⟶ y)
    (hφ : Etale (B.inclusion.map (p.map φ).left)) :
    Etale (E.inclusion.map (smallEtaleBaseMorphism B E h S hS p φ)) := by
  simpa [smallEtaleBaseMorphism] using hφ

/-- The counit of the adjunction of Stacks 03S3 is the counit of the slice adjunction, after
forgetting the étale condition. -/
theorem smallEtalePostcomposeBaseChangeAdjunction_counit_map {T' T : E.Scheme} (f : T' ⟶ T)
    [Etale (E.inclusion.map f)] (W : SmallEtale E T.1 T.property) :
    (SmallEtale.inclusion E T.1 T.property).map
        ((smallEtalePostcomposeBaseChangeAdjunction E f).counit.app W) =
      (Over.mapPullbackAdj f).counit.app ((SmallEtale.inclusion E T.1 T.property).obj W) := by
  dsimp only [smallEtalePostcomposeBaseChangeAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  exact (Category.id_comp _).trans (Category.id_comp _)

/-! ### Restriction along composition with an étale morphism -/

section Postcompose

variable {T' T : E.Scheme} (f : T' ⟶ T) [Etale (E.inclusion.map f)]

/-- The structure sheaf of the small étale site of `T'` is the restriction of that of `T` along
composition with the étale morphism `f`: an étale `T'`-scheme has the same global functions
whether it is read over `T'` or over `T`. -/
noncomputable def smallEtalePostcomposeStructureMap :
    SmallEtale.structureSheaf E T'.1 T'.property ⟶
      ((smallEtalePostcompose E T.1 T.property
        (SmallEtale.ofEtaleHom E f)).sheafPushforwardContinuous
        RingCat.{u} (SmallEtale.topology E T'.1 T'.property)
        (SmallEtale.topology E T.1 T.property)).obj (SmallEtale.structureSheaf E T.1 T.property) :=
  ObjectProperty.homMk (𝟙 _)

/-- Restriction of sheaves of modules along composition with the étale morphism `f`: the
pushforward along the morphism of ringed sites whose underlying functor is composition with `f`
and whose structure map is `AlgebraicGeometry.Stack.smallEtalePostcomposeStructureMap`. -/
noncomputable def smallEtalePostcomposeModules :
    SheafOfModules.{u} (SmallEtale.structureSheaf E T.1 T.property) ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf E T'.1 T'.property) :=
  @SheafOfModules.pushforward _ _ _ _ _ _ _ _ _
    (isContinuous_smallEtalePostcompose_ofEtaleHom E f) (smallEtalePostcomposeStructureMap E f)

/-- **Stacks 03S3 for sheaves of modules.** Restriction of sheaves of modules along composition
with the étale morphism `f` is left adjoint to the pushforward along the morphism of ringed sites
`ε_f` of Stacks 070R (2): the adjunction of sites of Stacks 03S3 is compatible with the two
structure maps. -/
noncomputable def smallEtalePostcomposeModulesAdjunction :
    smallEtalePostcomposeModules E f ⊣
      SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E f) :=
  @SheafOfModules.pushforwardPushforwardAdj _ _ _ _ _ _ _ _ _ _
    (isContinuous_smallEtalePostcompose_ofEtaleHom E f) (smallEtaleBaseChange_isContinuous E f)
    (smallEtalePostcomposeBaseChangeAdjunction E f)
    (smallEtalePostcomposeStructureMap E f) (SmallEtale.smallEtaleStructureMapRing E f)
    (by
      ext W : 2
      have hc := congrArg (fun g => E.inclusion.map (Over.Hom.left g))
        (smallEtalePostcomposeBaseChangeAdjunction_counit_map E f W.unop)
      simp only [Over.mapPullbackAdj_counit_app, Over.homMk_left] at hc
      change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (E.inclusion.map
          (Over.Hom.left ((SmallEtale.inclusion E T.1 T.property).map
            ((smallEtalePostcomposeBaseChangeAdjunction E f).counit.app W.unop)))).op) =
        (forget₂ CommRingCat RingCat).map (Scheme.Γ.map
          (E.inclusion.map (pullback.fst W.unop.obj.hom f)).op) ≫ 𝟙 _
      rw [hc, Category.comp_id]
      rfl)
    (by
      ext W : 2
      change 𝟙 _ ≫ (forget₂ CommRingCat RingCat).map (Scheme.Γ.map
          (E.inclusion.map (pullback.fst (W.unop.obj.hom ≫ f) f)).op) ≫
          (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (E.inclusion.map
            (Over.Hom.left ((SmallEtale.inclusion E T'.1 T'.property).map
              ((smallEtalePostcomposeBaseChangeAdjunction E f).unit.app W.unop)))).op) = 𝟙 _
      rw [smallEtalePostcomposeBaseChangeAdjunction_unit_app, Category.id_comp]
      have hcomp : E.inclusion.map (Over.Hom.left ((SmallEtale.inclusion E T'.1 T'.property).map
            (smallEtaleBaseChangeLift E f
              ((smallEtalePostcompose E T.1 T.property (SmallEtale.ofEtaleHom E f)).obj W.unop)
              W.unop (𝟙 _) (by simp [smallEtalePostcompose])))) ≫
          E.inclusion.map (pullback.fst (W.unop.obj.hom ≫ f) f) = 𝟙 _ := by
        refine (E.inclusion.map_comp _ _).symm.trans ?_
        refine (congrArg E.inclusion.map ?_).trans (E.inclusion.map_id _)
        exact pullback.lift_fst _ _ _
      have := congrArg (fun g => (forget₂ CommRingCat RingCat).map (Scheme.Γ.map g.op)) hcomp
      simp only [op_comp, Functor.map_comp, op_id] at this
      exact this)

/-- **The transpose along `AlgebraicGeometry.Stack.smallEtalePostcomposeModulesAdjunction`, on
sections.** For a morphism `g : M ⟶ (ε_f)_* N`, the morphism out of the restriction of `M` along
composition with `f` that it corresponds to is, over an étale `T'`-scheme `W`, the value of `g`
over `W ⟶ T' ⟶ T` followed by restriction along the unit `W ⟶ f^{-1}(W ⟶ T)` of Stacks 03S3. -/
theorem toPresheaf_map_smallEtalePostcomposeModulesAdjunction_homEquiv_symm_val_app
    {M : SheafOfModules.{u} (SmallEtale.structureSheaf E T.1 T.property)}
    {N : SheafOfModules.{u} (SmallEtale.structureSheaf E T'.1 T'.property)}
    (g : M ⟶ (SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E f)).obj N)
    (W : SmallEtale E T'.1 T'.property) :
    ((PresheafOfModules.toPresheaf _).map
        (((smallEtalePostcomposeModulesAdjunction E f).homEquiv M N).symm g).val).app (op W) =
      ((PresheafOfModules.toPresheaf _).map g.val).app
          (op ((smallEtalePostcompose E T.1 T.property (SmallEtale.ofEtaleHom E f)).obj W)) ≫
        N.val.presheaf.map ((smallEtalePostcomposeBaseChangeAdjunction E f).unit.app W).op := by
  rw [Adjunction.homEquiv_counit]
  rfl

end Postcompose

attribute [local irreducible] AlgebraicGeometry.Stack.smallEtaleStructureComparison
  AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing in
/-- The transpose of the comparison map `c_ι` of Stacks 06WC along the adjunction between the
sheafified Stacks 06WC pullback and the pushforward along `ε_a` is, on sections, the comparison
of Stacks 06W2. -/
theorem toPresheaf_map_sheafifiedPullbackComparisonAdjunction_homEquiv_val_app {x z : 𝒳}
    (ι : z ⟶ x)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (W : (SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x))ᵒᵖ) :
    ((PresheafOfModules.toPresheaf _).map
        ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ι).homEquiv
          (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) F x hMx)
          (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) F z hMz)
          (sheafifiedRestrictComparison B E h S hS p hp F ι hMz)).val).app W =
      (restrictionPushforwardComparison B E h S hS p hp ι F.presheaf).app W := by
  unfold sheafifiedRestrictComparison
  have key := congrArg (fun t => ((PresheafOfModules.toPresheaf _).map t).app W)
    (sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val_at B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ι
      (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx)
      (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F z hMz)
      (restrictModulePullbackComparison B E h S hS p hp ι (etaleTopology B)
        (etaleTopology_le_topology B) F))
  refine key.trans ?_
  refine Eq.trans (toPresheaf_map_comp_app _ _ _) ?_
  refine ((congrArg (fun x => _ ≫ x) ?_).trans (Category.comp_id _)).trans ?_
  · exact Stacks.PresheafOfModules.toPresheaf_map_eqToIso_pushforward_hom_app_app
      (smallEtaleStructureComparison_eq_structureMapRingAt B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) ι)
      (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F z hMz).val W
  · exact congrArg (fun t => ((PresheafOfModules.toPresheaf _).map t).app W)
      (restrictModulePullbackComparison_adjunct B E h S hS p hp ι (etaleTopology B)
        (etaleTopology_le_topology B) F)

/-! ### Locality along étale arrows -/

/-- A morphism of sheaves is an isomorphism as soon as it is an isomorphism on the sections over
every object admitting a morphism to a member of a family covering the final object. -/
theorem _root_.CategoryTheory.Sheaf.isIso_of_isIso_app_of_coversTop {C : Type*} [Category C]
    {K : GrothendieckTopology C} {A : Type*} [Category A] {ι : Type*} {X : ι → C}
    (hX : K.CoversTop X) {F G : Sheaf K A} (f : F ⟶ G)
    (h : ∀ (i : ι) (Z : C), (Z ⟶ X i) → IsIso (f.hom.app (op Z))) : IsIso f := by
  refine Sheaf.isIso_of_coversTop hX fun i => ?_
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  exact h i W.unop.left W.unop.hom

/-- A morphism of sheaves of modules is an isomorphism as soon as it is bijective on the sections
over every object admitting a morphism to a member of a family covering the final object. -/
theorem _root_.SheafOfModules.isIso_of_bijective_app_of_coversTop {C : Type*} [Category C]
    {K : GrothendieckTopology C} {R : Sheaf K RingCat.{u}} {ι : Type*} {X : ι → C}
    (hX : K.CoversTop X) {P Q : SheafOfModules.{u} R} (α : P ⟶ Q)
    (h : ∀ (i : ι) (Z : C), (Z ⟶ X i) → Function.Bijective (α.val.app (op Z))) : IsIso α := by
  have hs : IsIso ((SheafOfModules.toSheaf R).map α) :=
    Sheaf.isIso_of_isIso_app_of_coversTop hX _ fun i Z g =>
      (ConcreteCategory.isIso_iff_bijective _).2 (h i Z g)
  have h1 : IsIso ((PresheafOfModules.toPresheaf _).map α.val) :=
    (ObjectProperty.isIso_hom_iff _).2 hs
  have h2 : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map α)) := h1
  have : IsIso ((SheafOfModules.forget _).map α) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso α (SheafOfModules.forget _)

/-- **A morphism of sheaves of modules on the small étale site below `z` is an isomorphism as soon
as its sheafified Stacks 06WC pullbacks along a family of arrows lying over étale morphisms are,
provided the family covers.** The family is presented by a family `X` of objects of the small
étale site covering the final object, each mapping to the chart of one of the arrows.

The sheafified Stacks 06WC pullback along an arrow lying over an étale morphism is restriction
along composition with that morphism, by
`AlgebraicGeometry.Stack.smallEtalePostcomposeModulesAdjunction`, so the hypothesis says that the
morphism is bijective on the sections over every object mapping to a chart; those objects cover.
-/
theorem isIso_of_isIso_sheafifiedPullbackComparison_map_of_coversTop {z : 𝒳}
    {P Q : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z))} (α : P ⟶ Q) {I : Type*}
    (X : I → SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))
    (hX : (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z)).CoversTop X)
    (w : I → 𝒳) (ι : ∀ i, w i ⟶ z) (hét : ∀ i, Etale (B.inclusion.map (p.map (ι i)).left))
    (hmap : ∀ i, Nonempty (X i ⟶ etaleChart B E h S hS p (ι i) (hét i)))
    (hα : ∀ i, IsIso ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) (ι i)).map α)) : IsIso α := by
  refine SheafOfModules.isIso_of_bijective_app_of_coversTop hX α fun i Z g => ?_
  obtain ⟨g'⟩ := hmap i
  have := etale_smallEtaleBaseMorphism B E h S hS p (ι i) (hét i)
  let f := smallEtaleBaseMorphism B E h S hS p (ι i)
  let θ := (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) (ι i)).leftAdjointUniq
      (smallEtalePostcomposeModulesAdjunction E f)
  have hM : IsIso ((smallEtalePostcomposeModules E f).map α) := by
    have hnat := θ.hom.naturality α
    have := hα i
    have : IsIso (θ.hom.app P ≫ (smallEtalePostcomposeModules E f).map α) := by
      rw [← hnat]
      infer_instance
    exact IsIso.of_isIso_comp_left (θ.hom.app P) _
  let k : Z.obj.left ⟶ E.obj (p.obj (w i)).left.1 (contains_base B E h S hS p (w i)) :=
    (g ≫ g').hom.left
  have hk : k ≫ f = Z.obj.hom := Over.w (g ≫ g').hom
  let T : SmallEtale E (p.obj (w i)).left.1 (contains_base B E h S hS p (w i)) :=
    ⟨Over.mk k, BigEtaleSite.etale_map_of_postcomp E k f Z.obj.hom Z.property inferInstance hk⟩
  let Mf := smallEtalePostcompose E (p.obj z).left.1 (contains_base B E h S hS p z)
    (SmallEtale.ofEtaleHom E f)
  let e : Mf.obj T ≅ Z :=
    ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) ((Category.id_comp _).trans hk.symm))
  have hT : IsIso (((PresheafOfModules.toPresheaf _).map α.val).app (op (Mf.obj T))) :=
    NatIso.isIso_app_of_isIso ((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget _).map ((smallEtalePostcomposeModules E f).map α))) (op T)
  have hnat := ((PresheafOfModules.toPresheaf _).map α.val).naturality e.hom.op
  have hZ : IsIso (((PresheafOfModules.toPresheaf _).map α.val).app (op Z)) := by
    have : IsIso (((PresheafOfModules.toPresheaf _).map α.val).app (op Z) ≫
        ((PresheafOfModules.toPresheaf _).obj Q.val).map e.hom.op) := by
      rw [← hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (((PresheafOfModules.toPresheaf _).obj Q.val).map e.hom.op)
  exact (ConcreteCategory.isIso_iff_bijective
    (((PresheafOfModules.toPresheaf _).map α.val).app (op Z))).1 hZ

end AlgebraicGeometry.Stack

end
