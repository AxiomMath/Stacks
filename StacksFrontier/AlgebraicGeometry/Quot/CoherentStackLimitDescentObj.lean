module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitModules
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints

/-!
# Descent of objects for `Coh_{X/Y}`, given the descent of flatness and of proper support

In Situation 08KB assume `Y` locally of finite presentation over `S`, and let `T = lim T_j` be a
cofiltered limit of affine schemes of the site, taken in schemes. Every object `(T, g, F)` of
`Coh_{X/Y}` over `T` is the pullback of an object over some stage `T_j`. This is the descent
condition `Deformation.Artin.DescentObj` of Stacks 07XL that makes the comparison functor
`colim Coh_{X/Y, T_j} ⥤ Coh_{X/Y, T}` essentially surjective, and it is the essential
surjectivity part of the proof of Stacks 08KD:

* `g : T ⟶ Y` comes from a stage `g_i : T_i ⟶ Y`, because `Y` is limit preserving (Stacks 05N0);
* `F` comes from a finitely presented module on `X_{T_k} = X ×_Y T_k`, by the essential
  surjectivity clause of Stacks 07V7 for the system of base changes above `i`;
* that module is flat over `T_j` with support proper over `T_j` at some later stage, by Stacks
  08K0 and 08K2.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.IsFlatWithProperSupport`: the two conditions on a
  finitely presented module on `X_T` that make it an object of `Coh_{X/Y}` over `T`.
* `AlgebraicGeometry.Space.CoherentSituation.FlatProperSupportDescends`: the third step above for
  the system of base changes `X_{T_k}`, as a proposition.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_stage_structureMap` and
  `AlgebraicGeometry.Space.CoherentSituation.exists_stage_structureMap_eq`: Stacks 05N0 at a
  cofiltered limit of affine schemes of the site — the structure morphism `T ⟶ Y` of an object
  over the limit factors through a stage, and two morphisms from a stage which agree on the limit
  agree on a later stage.
* `AlgebraicGeometry.Space.CoherentSituation.descentObj_coherent`: the condition
  `Deformation.Artin.DescentObj` for `Coh_{X/Y}`, assembled from Stacks 05N0, the essential
  surjectivity clause of Stacks 07V7 for the system of base changes, and
  `AlgebraicGeometry.Space.CoherentSituation.FlatProperSupportDescends`, taken as a hypothesis.

## Implementation notes

**This file carries no tag.** `FlatProperSupportDescends` is the conclusion of Stacks 08K0
(flatness of a module) and Stacks 08K2 (properness of its support) for the system of base changes
`X ×_Y T_k ⟶ T_k` of an arbitrary cofiltered system of affine schemes of the site whose limit
lies in the site. The forms of 08K0 and 08K2 in this development bound the index of the system
(`AlgebraicGeometry.Space.MorphismDescentSystem` carries `#I < cf(cutoff)`), which Artin's Axioms,
Definition 07XL does not; the forms over the chapter's convention 07SD, with no condition on the
index, are what discharges it. The inputs they need for this system are proved in
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackStageSystem.lean` (the system of test schemes
satisfies the convention, its limit is a limit of presheaves) and
`StacksFrontier/CategoryTheory/Filtered/CofilteredDirectedInitial.lean` (the reindexing of a
cofiltered system by a directed set).

Morphisms of modules are only ever formed between modules on syntactically equal algebraic spaces;
see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackLimitDescentEq.lean`.

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry.Space.QuasiCoherentDescent (pullbackComparison)

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-- The two conditions on a module on `X_T` beyond finite presentation which make it, with `T`, an
object of `Coh_{X/Y}`: flatness over `T` and properness of its support over `T`. -/
def IsFlatWithProperSupport (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) : Prop :=
  IsFlatOver B S hS (D.space T).2 (D.projection T).hom F ∧
    ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T F)),
      IsProperOver B S hS (D.space T).2
        ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom hp (D.support T F) hU

/-- The flatness and the proper support of an object of `Coh_{X/Y}`. -/
theorem CoherentObject.isFlatWithProperSupport (A : CoherentObject D) :
    D.IsFlatWithProperSupport A.T A.F :=
  ⟨A.flat, A.properSupport⟩

variable {I : Type u} [Category.{u} I] (E : I ⥤ BigAffineFppf B S hS) (c : Cone E)

/-- **Stacks 08K0 and 08K2 for the system of base changes `X_{T_k} = X ×_Y T_k`**, as a
proposition. Let `A₀` be an object of `Coh_{X/Y}` over the limit `T`, `g : T_i ⟶ Y` a structure
morphism on a stage, `β : A₀.T ⟶ T_k` a morphism of test schemes over `Y` lying over the
projection `T ⟶ T_k`, and `Q` a finitely presented module on `X_{T_k}` whose inverse image to
`X_T` is the module of `A₀`. Then `Q` is flat with proper support after pullback to some later
stage `T_j`. -/
def FlatProperSupportDescends : Prop :=
  ∀ (A₀ : CoherentObject D) (hA₀ : A₀.T.left = ((BigAffineFppf.inclusion B S hS).mapCone c).pt)
    {i : I}
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    (k : Over i) (β : A₀.T ⟶ (D.stageTestSystem E g).obj k)
    (_ : β.left = eqToHom hA₀ ≫ ((BigAffineFppf.inclusion B S hS).mapCone c).π.app k.left)
    (Q : Modules.{u, u} B S hS (D.space ((D.stageTestSystem E g).obj k)).1
      (D.space ((D.stageTestSystem E g).obj k)).2)
    (_ : Q.IsFinitePresentationOnSite)
    (_ : (modulePullback B S hS (D.relativeMap β)).obj Q ≅ A₀.F),
    ∃ (j : Over i) (e : j ⟶ k), D.IsFlatWithProperSupport ((D.stageTestSystem E g).obj j)
      ((modulePullback B S hS (D.relativeMap ((D.stageTestSystem E g).map e))).obj Q)

/-- The presheaf `Y` of a locally finitely presented space sends a limit of affine schemes of the
site to a colimit. -/
private theorem nonempty_isColimit_mapCocone [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) :
    Nonempty (IsColimit (D.Y.1.mapCocone ((BigAffineFppf.inclusion B S hS).mapCone c).op)) := by
  obtain ⟨hcol⟩ := limitPreserving_of_isLocallyOfFinitePresentation B S hS D.Y.2 hY I
    (E ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) hc
    (fun j => (E.obj j).property) c.pt.property
  exact ⟨hcol⟩

/-- **Stacks 05N0 at a cofiltered limit of affine schemes of the site.** If `Y` is locally of
finite presentation over `S`, every morphism `T ⟶ Y` from the limit factors through a stage. -/
theorem exists_stage_structureMap [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    {U : BigFppfOver B S hS} (hU : U = ((BigAffineFppf.inclusion B S hS).mapCone c).pt)
    (gU : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    ∃ (i : I) (g : (schemeSpaceFunctor B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y),
      gU = (schemeSpaceFunctor B S hS).map
        (eqToHom hU ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g := by
  subst hU
  obtain ⟨hcol⟩ := D.nonempty_isColimit_mapCocone E c hc hY
  obtain ⟨⟨i⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit hcol (yonedaEquiv gU.hom)
  refine ⟨i, ObjectProperty.homMk (yonedaEquiv.symm y), ?_⟩
  apply ObjectProperty.hom_ext
  apply yonedaEquiv.injective
  simp only [eqToHom_refl, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom]
  change _ = yonedaEquiv (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫
    yonedaEquiv.symm y)
  rw [yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply, ← hy]
  rfl

/-- **Stacks 05N0 at a cofiltered limit of affine schemes of the site, injectivity.** If `Y` is
locally of finite presentation over `S`, two morphisms `T_i ⟶ Y` from a stage which agree on the
limit `T` already agree on a later stage. -/
theorem exists_stage_structureMap_eq [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) {i : I}
    (g g' : (schemeSpaceFunctor B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    (h : (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g =
      (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g') :
    ∃ (k : I) (s : k ⟶ i),
      (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (E.map s)) ≫ g =
        (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (E.map s)) ≫ g' := by
  obtain ⟨hcol⟩ := D.nonempty_isColimit_mapCocone E c hc hY
  have hyo : ∀ {U V : BigFppfOver B S hS} (a : V ⟶ U)
      (g₀ : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y),
      yonedaEquiv ((schemeSpaceFunctor B S hS).map a ≫ g₀).hom =
        D.Y.1.map a.op (yonedaEquiv g₀.hom) :=
    fun {U _} a g₀ => (yonedaEquiv_naturality (F := D.Y.1) (X := U) g₀.hom a).symm
  let x : D.Y.1.obj (op ((BigAffineFppf.inclusion B S hS).obj (E.obj i))) :=
    yonedaEquiv (F := D.Y.1) (X := (BigAffineFppf.inclusion B S hS).obj (E.obj i)) g.hom
  let x' : D.Y.1.obj (op ((BigAffineFppf.inclusion B S hS).obj (E.obj i))) :=
    yonedaEquiv (F := D.Y.1) (X := (BigAffineFppf.inclusion B S hS).obj (E.obj i)) g'.hom
  have hx : (D.Y.1.mapCocone ((BigAffineFppf.inclusion B S hS).mapCone c).op).ι.app (op i) x =
      (D.Y.1.mapCocone ((BigAffineFppf.inclusion B S hS).mapCone c).op).ι.app (op i) x' := by
    change D.Y.1.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)).op x =
      D.Y.1.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)).op x'
    rw [← hyo, ← hyo, h]
  obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol _ _).1 hx
  refine ⟨k.unop, f.unop, ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)⟩
  rwa [hyo, hyo]

section Descent

variable [IsCofiltered I] (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

include hc in
/-- The system of base changes above a stage, with its limit `X_T` taken at a test scheme
isomorphic to the limit `T` of the stages, is a limit of presheaves. -/
noncomputable def isLimit_stageSpaceCone_extend {i : I}
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    {T₀ : SchemesOver D.Y} (v : T₀ ≅ (D.stageTestCone E c g).pt) :
    IsLimit ((baseChangeOver D.f ⋙ Over.forget D.X ⋙ ObjectProperty.ι _).mapCone
      ((D.stageTestCone E c g).extend v.hom)) :=
  IsLimit.ofIsoLimit (D.isLimit_stageSpaceCone E c g hc)
    ((Cone.functoriality _ (baseChangeOver D.f ⋙ Over.forget D.X ⋙ ObjectProperty.ι _)).mapIso
      (Cone.extendIso _ v.symm))

/-- **The limit `T` of the test schemes above a stage, at a test scheme isomorphic to it**: the
cone of the test schemes `T_k` with vertex `T₀ ≅ T` and projections `T₀ ≅ T ⟶ T_k`. -/
noncomputable def stageTestConeAt {i : I}
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    {T₀ : SchemesOver D.Y} (v : T₀ ≅ (D.stageTestCone E c g).pt) :
    Cone (D.stageTestSystem E g) where
  pt := T₀
  π :=
    { app := fun k => v.hom ≫ (D.stageTestCone E c g).π.app k
      naturality := fun k k' m => by
        dsimp
        rw [Category.id_comp, Category.assoc, Cone.w] }

include hc in
/-- The system of base changes above a stage, with its limit `X_T` taken at a test scheme
isomorphic to the limit `T` of the stages, is a limit of presheaves. -/
noncomputable def isLimit_stageSpaceConeAt {i : I}
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    {T₀ : SchemesOver D.Y} (v : T₀ ≅ (D.stageTestCone E c g).pt) :
    IsLimit ((baseChangeOver D.f ⋙ Over.forget D.X ⋙ ObjectProperty.ι _).mapCone
      (D.stageTestConeAt E c g v)) :=
  IsLimit.ofIsoLimit (D.isLimit_stageSpaceCone E c g hc)
    ((Cone.functoriality _ (baseChangeOver D.f ⋙ Over.forget D.X ⋙ ObjectProperty.ι _)).mapIso
      (Cone.ext v.symm (fun k => by
        change _ = v.inv ≫ v.hom ≫ _
        rw [Iso.inv_hom_id_assoc])))

include hc in
/-- **The descent of objects of Stacks 07XL for `Coh_{X/Y}`, given the descent of flatness and of
proper support.** Let `Y` be locally of finite presentation over `S` and let `T = lim T_j` be a
cofiltered limit of affine schemes of the site, taken in schemes. Every object `(T, g, F)` of
`Coh_{X/Y}` over `T` receives a morphism over a projection `T ⟶ T_j` to an object over a stage:
`g` comes from a stage by Stacks 05N0, `F` from a finitely presented module on a later stage by
the essential surjectivity clause of Stacks 07V7, and that module is flat with proper support at a
yet later stage by `hdesc` (Stacks 08K0, 08K2). This is the essential surjectivity half of the
proof of Stacks 08KD. -/
theorem descentObj_coherent (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (hdesc : D.FlatProperSupportDescends E c) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.DescentObj (coherentSiteProjection D.categoryData)
      (E ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let p := coherentSiteProjection D.categoryData
  let incl := BigAffineFppf.inclusion B S hS
  have hZ := B.contains_terminal
  rintro ⟨A₀, hA₀⟩
  change A₀.T.left = (incl.mapCone c).pt at hA₀
  obtain ⟨i, g, hg⟩ := D.exists_stage_structureMap E c hc hY hA₀ A₀.T.hom
  let v : A₀.T ≅ (D.stageTestCone E c g).pt := CostructuredArrow.isoMk (eqToIso hA₀) (by
    change (schemeSpaceFunctor B S hS).map (eqToHom hA₀) ≫
      ((schemeSpaceFunctor B S hS).map (incl.map (c.π.app i)) ≫ g) = A₀.T.hom
    rw [hg, Functor.map_comp, Category.assoc])
  let cT := (D.stageTestCone E c g).extend v.hom
  obtain ⟨-, -, hES⟩ := D.finitePresentationModule_isColimit_baseChange (D.stageTestSystem E g)
    cT hZ (fun e => D.isAffineHom_stageSpaceSystem_map E g e)
    (D.isQuasiCompactSpace_stageSpaceSystem E g)
    (D.isAbsolutelyQuasiSeparated_stageSpaceSystem E g hZ)
    (D.isLimit_stageSpaceCone_extend E c hc g v)
    (D.siteContainsBaseChangeLimits_stageSpaceSystem E c g hc)
  obtain ⟨k, Q, hQ, ⟨α⟩⟩ := hES A₀.F A₀.finitePresentation
  have hβ : (cT.π.app k).left = eqToHom hA₀ ≫ (incl.mapCone c).π.app k.left := rfl
  obtain ⟨j, e, hfps⟩ := hdesc A₀ hA₀ g k (cT.π.app k) hβ Q hQ α.symm
  have hFj := isFinitePresentationOnSite_modulePullback B S hS
    (D.relativeMap ((D.stageTestSystem E g).map e)) Q hQ
  let xi : CoherentObject D :=
    { T := (D.stageTestSystem E g).obj j
      F := (modulePullback B S hS (D.relativeMap ((D.stageTestSystem E g).map e))).obj Q
      quasicoherent := by
        have := hFj
        infer_instance
      finitePresentation := hFj
      flat := hfps.1
      properSupport := hfps.2 }
  let δ : CoherentHom A₀ xi :=
    { base := cT.π.app j
      fibre := (pullbackComparison B S hS (D.relativeMap (cT.π.app j))
          (D.relativeMap ((D.stageTestSystem E g).map e)) (D.relativeMap (cT.π.app k))
          (D.relativeMap_cone_comp _ cT e) Q).inv ≫ α.inv
      isIso_fibre := inferInstance }
  refine ⟨j.left, ⟨xi, rfl⟩, δ, ?_⟩
  refine IsHomLift.of_fac' p _ _ hA₀ rfl ?_
  change (cT.π.app j).left = _
  rfl

end Descent

end AlgebraicGeometry.Space.CoherentSituation

end
