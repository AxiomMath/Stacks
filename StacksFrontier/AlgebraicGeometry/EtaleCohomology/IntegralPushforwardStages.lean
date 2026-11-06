module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.LimitPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkIntegral

/-!
# Germs along restriction to an étale scheme, and sections over empty objects

Two pieces of bookkeeping for the stalks of small étale sheaves on the sites of a big étale site,
used in the proof of base change for an integral morphism.

*Restriction.* For an étale morphism `k : T' ⟶ T` of a big étale site, composition with `k`
sends étale schemes over `T'` to étale schemes over `T`; the direct image along this functor is
the restriction `H|_{T'}` of a sheaf `H` on the small étale site of `T`, whose sections over an
étale `T'`-scheme `A` are the sections of `H` over `A` viewed over `T`. A pointed étale
neighbourhood of a geometric point `x` of `T'` is, after composition with `k`, a pointed étale
neighbourhood of its image in `T`, and so there is a
canonical map from the stalk of `H|_{T'}` at `x` to the stalk of `H` at the image of `x`,
sending a germ to the germ of the same section.

*Empty objects.* A sheaf of sets has a section over an object of the small étale site with
empty underlying scheme, the empty family covering it. Consequently the stalk of a direct image
along an integral morphism at a geometric point with no lift is nonempty: the image of the
source is closed and misses the point.

## Main definitions

* `AlgebraicGeometry.smallEtaleRestrictionAlong` — restriction of sheaves along an étale morphism.
* `AlgebraicGeometry.smallEtaleRestrictionNeighborhoods` — composition with an étale morphism, on
  pointed étale neighbourhoods.
* `AlgebraicGeometry.smallEtaleRestrictionStalkMap` — the map from the stalk of a restriction to
  the stalk of the sheaf.

## Main results

* `AlgebraicGeometry.smallEtaleRestrictionStalkMap_germ` — that map on germs.
* `AlgebraicGeometry.nonempty_sections_of_isEmpty` — sections over an empty object.
* `AlgebraicGeometry.nonempty_etaleStalk_pushforward_of_isEmpty_lifts` — nonemptiness of the
  stalk of an integral direct image at a geometric point with no lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section Restriction

variable {T' T : B.Scheme} (k : T' ⟶ T) [Etale (B.inclusion.map k)]

/-- Restriction of sheaves along an étale morphism `k : T' ⟶ T`: the direct image along
composition with `k`, so that the sections over an étale `T'`-scheme `A` are the sections over
`A` regarded as an étale `T`-scheme. -/
abbrev smallEtaleRestrictionAlong (A : Type*) [Category A] :
    Sheaf (SmallEtale.topology B T.1 T.property) A ⥤
      Sheaf (SmallEtale.topology B T'.1 T'.property) A :=
  (smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B k)).sheafPushforwardContinuous
    A (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property)

/-- Composition with an étale morphism `k : T' ⟶ T`, on pointed étale neighbourhoods: a
neighbourhood of a geometric point `x` of `T'` is a neighbourhood of any geometric point `z` of `T`
with the same residue field and `x ∘ k = z`, with the same chosen lift. -/
@[simps]
def smallEtaleRestrictionNeighborhoods {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ B.inclusion.obj T') (z : Spec (.of K) ⟶ B.inclusion.obj T)
    (hz : x ≫ B.inclusion.map k = z) :
    (geometricPointFiber B T'.1 T'.property ⟨K, x⟩).Elements ⥤
      (geometricPointFiber B T.1 T.property ⟨K, z⟩).Elements where
  obj A := Functor.elementsMk _
    ((smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B k)).obj A.1)
    ⟨A.2.1, by
      calc _ = A.2.1 ≫ (B.inclusion.map A.1.obj.hom ≫ B.inclusion.map k) := by
            simp [smallEtalePostcompose]
        _ = z := by
            rw [← Category.assoc]
            exact (congrArg (· ≫ B.inclusion.map k) A.2.2).trans hz⟩
  map {A A'} φ := ⟨(smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B k)).map φ.1, by
    apply Subtype.ext
    change A.2.1 ≫ (SmallEtale.toScheme B T.1 T.property).map
      ((smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B k)).map φ.1) = A'.2.1
    exact congrArg Subtype.val φ.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical map from the stalk at `x` of the restriction of a sheaf along an étale
morphism `k` to the stalk of the sheaf at `z = x ∘ k`, sending a germ to the germ of the same
section. -/
def smallEtaleRestrictionStalkMap {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ B.inclusion.obj T') (z : Spec (.of K) ⟶ B.inclusion.obj T)
    (hz : x ≫ B.inclusion.map k = z)
    (H : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1))) :
    etaleStalk B T'.1 T'.property ⟨K, x⟩ ((smallEtaleRestrictionAlong B k _).obj H).obj ⟶
      etaleStalk B T.1 T.property ⟨K, z⟩ H.obj :=
  colimit.pre ((CategoryOfElements.π (geometricPointFiber B T.1 T.property ⟨K, z⟩)).op ⋙ H.obj)
    (smallEtaleRestrictionNeighborhoods B k x z hz).op

/-- **The restriction stalk map on germs.** The germ at a neighbourhood `A` of `x` of a section
of the restriction is the germ, at `A` regarded as a neighbourhood of `z`, of the same section. -/
theorem smallEtaleRestrictionStalkMap_germ {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ B.inclusion.obj T') (z : Spec (.of K) ⟶ B.inclusion.obj T)
    (hz : x ≫ B.inclusion.map k = z)
    (H : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (A : (geometricPointFiber B T'.1 T'.property ⟨K, x⟩).Elements)
    (s : H.obj.obj (op ((smallEtalePostcompose B T.1 T.property
      (SmallEtale.ofEtaleHom B k)).obj A.1))) :
    smallEtaleRestrictionStalkMap B k x z hz H
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B T'.1 T'.property ⟨K, x⟩)).op ⋙
          ((smallEtaleRestrictionAlong B k _).obj H).obj) (op A) s) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B T.1 T.property ⟨K, z⟩)).op ⋙ H.obj)
        (op ((smallEtaleRestrictionNeighborhoods B k x z hz).obj A)) s :=
  ConcreteCategory.congr_hom (colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B T.1
    T.property ⟨K, z⟩)).op ⋙ H.obj) (smallEtaleRestrictionNeighborhoods B k x z hz).op (op A)) s

end Restriction

section Empty

/-- **A sheaf of sets has a section over an empty object.** The empty sieve covers an object with
empty underlying scheme (`Stacks.EtaleCohomology.bot_mem_topology`), so the sections over it form
a terminal object. -/
theorem nonempty_sections_of_isEmpty (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (U : SmallEtale B S hS) (hU : IsEmpty ((SmallEtale.toScheme B S hS).obj U)) :
    Nonempty (F.obj.obj (op U)) :=
  ⟨(F.isTerminalOfBotCover U (Stacks.EtaleCohomology.bot_mem_topology B hS hU)).from
    PUnit.{u + 2} PUnit.unit⟩

/-- **The stalk of an integral direct image at a geometric point with no lift is nonempty.**
The image of the source is closed and misses the point, so the point has an open neighbourhood
over which the base change is empty, and the sheaf has a section over that empty base change. -/
theorem nonempty_etaleStalk_pushforward_of_isEmpty_lifts {X Y : B.Scheme} (k : X ⟶ Y)
    [IsIntegralHom (B.inclusion.map k)] (z : GeometricPoint Y.1)
    (hz : IsEmpty {a : z.source ⟶ X.1 // a ≫ B.inclusion.map k = z.hom})
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    Nonempty (etaleStalk B Y.1 Y.property z ((B.smallPushforward k _).obj F).obj) := by
  obtain ⟨O, hzO, hO⟩ :=
    exists_open_base_of_geometricLifts_of_isIntegralHom (B.inclusion.map k) z ⊥
    (fun a => (hz.false a).elim)
  have hsize : B.Contains O := (Scheme.size_coe_opens_le _ O).trans_lt Y.property
  let W : SmallEtale B Y.1 Y.property :=
    ⟨Over.mk (ObjectProperty.homMk O.ι : B.obj O hsize ⟶ Y), by
      show Etale O.ι
      infer_instance⟩
  have hrange : Set.range z.hom ⊆ Set.range O.ι := by
    rintro _ ⟨a, rfl⟩
    refine ⟨⟨z.hom a, ?_⟩, rfl⟩
    rwa [Subsingleton.elim a default]
  let w : (geometricPointFiber B Y.1 Y.property z).obj W :=
    ⟨IsOpenImmersion.lift O.ι z.hom hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have hempty : IsEmpty ((SmallEtale.toScheme B X.1 X.property).obj
      ((smallEtaleBaseChange B k).obj W)) := by
    refine ⟨fun p => ?_⟩
    let p' : B.inclusion.obj (pullback W.obj.hom k) := p
    have hw := (isPullback_smallEtaleBaseChange_inclusion B k W).w
    have hp : (B.inclusion.map (pullback.snd W.obj.hom k) ≫ B.inclusion.map k) p' ∈ O := by
      rw [← hw, Scheme.Hom.comp_apply]
      exact (B.inclusion.map (pullback.fst W.obj.hom k) p').2
    rw [Scheme.Hom.comp_apply] at hp
    exact hO hp
  obtain ⟨s⟩ := nonempty_sections_of_isEmpty B X.1 X.property F _ hempty
  exact ⟨colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property z)).op ⋙
    ((B.smallPushforward k _).obj F).obj) (op (Functor.elementsMk _ W w)) s⟩

end Empty

section Stages

/-- **A presentation of a morphism of a big étale site as a limit of finite morphisms.** A
directed inverse system of objects of the site, a cone from `X` exhibiting `X` as the limit of
the underlying system of schemes, and structure morphisms to `Y`, finite as morphisms of schemes,
through which `f` factors at every stage. An integral morphism to an affine scheme has one,
by Stacks 09YZ (`AlgebraicGeometry.SmallEtaleIntegralStages.ofIsAffine`). -/
structure SmallEtaleIntegralStages {X Y : B.Scheme} (f : X ⟶ Y) where
  /-- The index set. -/
  index : Type u
  /-- The order on the index set. -/
  [preorder : Preorder index]
  /-- The index set is nonempty. -/
  [nonempty : Nonempty index]
  /-- The index set is directed. -/
  [directed : IsDirected index (· ≤ ·)]
  /-- The inverse system of stages. -/
  diagram : indexᵒᵖ ⥤ B.Scheme
  /-- The projections from `X` to the stages. -/
  proj : (Functor.const indexᵒᵖ).obj X ⟶ diagram
  /-- The structure morphisms of the stages to `Y`. -/
  str : diagram ⟶ (Functor.const indexᵒᵖ).obj Y
  /-- The morphism `f` factors through every stage. -/
  fac : ∀ i, proj.app i ≫ str.app i = f
  /-- `X` is the limit of the underlying system of schemes. -/
  isLimit : IsLimit (B.inclusion.mapCone (Cone.mk X proj))
  /-- Every stage is finite over `Y`. -/
  finite : ∀ i, IsFinite (B.inclusion.map (str.app i))

namespace SmallEtaleIntegralStages

attribute [instance] preorder nonempty directed

variable {B} {X Y : B.Scheme} {f : X ⟶ Y} (P : SmallEtaleIntegralStages B f)

/-- A stage is finite over `Y`. -/
instance (i : P.indexᵒᵖ) : IsFinite (B.inclusion.map (P.str.app i)) := P.finite i

/-- The transition morphisms between the stages are finite, being morphisms between schemes
finite over `Y`. -/
theorem isFinite_map {i j : P.indexᵒᵖ} (a : i ⟶ j) :
    IsFinite (B.inclusion.map (P.diagram.map a)) := by
  have h : B.inclusion.map (P.diagram.map a) ≫ B.inclusion.map (P.str.app j) =
      B.inclusion.map (P.str.app i) := by
    rw [← Functor.map_comp]
    exact congrArg B.inclusion.map ((P.str.naturality a).trans (Category.comp_id _))
  have : IsFinite (B.inclusion.map (P.diagram.map a) ≫ B.inclusion.map (P.str.app j)) := by
    rw [h]
    infer_instance
  exact IsFinite.of_comp _ (B.inclusion.map (P.str.app j))

/-- The transition morphisms between the stages are affine. -/
instance isAffineHom_map {i j : P.indexᵒᵖ} (a : i ⟶ j) :
    IsAffineHom ((P.diagram ⋙ B.inclusion).map a) := by
  have := P.isFinite_map a
  change IsAffineHom (B.inclusion.map (P.diagram.map a))
  infer_instance

/-- The projections to the stages are integral when `f` is. -/
theorem isIntegralHom_proj [IsIntegralHom (B.inclusion.map f)] (i : P.indexᵒᵖ) :
    IsIntegralHom (B.inclusion.map (P.proj.app i)) := by
  have : IsIntegralHom (B.inclusion.map (P.proj.app i) ≫ B.inclusion.map (P.str.app i)) := by
    rw [← Functor.map_comp, P.fac i]
    infer_instance
  exact IsIntegralHom.of_comp _ (B.inclusion.map (P.str.app i))

/-- The cone of projections commutes with the transition morphisms. -/
theorem proj_comp_map {i j : P.indexᵒᵖ} (a : i ⟶ j) :
    P.proj.app i ≫ P.diagram.map a = P.proj.app j :=
  (P.proj.naturality a).symm.trans (Category.id_comp _)

/-- **Étale neighbourhoods of a point of the limit descend to a stage.** Every pointed étale
neighbourhood `U` of a geometric point `x` of `X` receives, over `X`, a morphism from the base
change of a pointed étale neighbourhood `W` of the image of `x` in some stage, compatible with the
points. -/
theorem exists_stage_neighborhood (x : GeometricPoint X.1)
    (U : (geometricPointFiber B X.1 X.property x).Elements) :
    ∃ (i : P.indexᵒᵖ)
      (W : (geometricPointFiber B (P.diagram.obj i).1 (P.diagram.obj i).property
        (x.map (B.inclusion.map (P.proj.app i)))).Elements)
      (φ : (smallEtaleBaseChange B (P.proj.app i)).obj W.1 ⟶ U.1),
      baseChangeEtalePointHom B (P.proj.app i) rfl W.1 W.2 ≫
        (SmallEtale.toScheme B X.1 X.property).map φ = U.2.1 := by
  obtain ⟨b, hbaff, ⟨r⟩⟩ := exists_isAffine_refinement_geometricPointFiber B X.1 X.property x U
  let A : Over (B.inclusion.obj X) := Over.mk (B.inclusion.map b.1.obj.hom)
  have : IsAffine A.left := hbaff
  have : Etale A.hom := b.1.property
  obtain ⟨i, Ai, hAaff, hAet, ⟨e⟩⟩ := Stacks.EtaleCohomology.exists_affine_etale_model_of_isLimit
    (P.diagram ⋙ B.inclusion) (B.inclusion.mapCone (Cone.mk X P.proj)) P.isLimit A
  have hsize : B.Contains Ai.left :=
    (Scheme.size_le_of_locallyOfFiniteType Ai.hom).trans_lt (P.diagram.obj i).property
  let Wi : SmallEtale B (P.diagram.obj i).1 (P.diagram.obj i).property :=
    ⟨Over.mk (ObjectProperty.homMk Ai.hom : B.obj Ai.left hsize ⟶ P.diagram.obj i), hAet⟩
  let ai : (SmallEtale.toScheme B (P.diagram.obj i).1 (P.diagram.obj i).property).obj Wi ⟶
      B.inclusion.obj (P.diagram.obj i) := B.inclusion.map Wi.obj.hom
  let pi : B.inclusion.obj X ⟶ B.inclusion.obj (P.diagram.obj i) := B.inclusion.map (P.proj.app i)
  let eL : A.left ≅ pullback ai pi := (Over.forget _).mapIso e
  have he : eL.hom ≫ pullback.snd ai pi = B.inclusion.map b.1.obj.hom := Over.w e.hom
  have hb : b.2.1 ≫ B.inclusion.map b.1.obj.hom = x.hom := b.2.2
  let w : x.source ⟶
      (SmallEtale.toScheme B (P.diagram.obj i).1 (P.diagram.obj i).property).obj Wi :=
    b.2.1 ≫ eL.hom ≫ pullback.fst ai pi
  have hw : w ≫ ai = x.hom ≫ pi := by
    simp only [w, Category.assoc, pullback.condition, reassoc_of% he, reassoc_of% hb]
  let W : (geometricPointFiber B (P.diagram.obj i).1 (P.diagram.obj i).property
      (x.map (B.inclusion.map (P.proj.app i)))).Elements := Functor.elementsMk _ Wi ⟨w, hw⟩
  have hpb : IsPullback (B.inclusion.map (pullback.fst Wi.obj.hom (P.proj.app i)))
      (B.inclusion.map (pullback.snd Wi.obj.hom (P.proj.app i))) ai pi :=
    isPullback_smallEtaleBaseChange_inclusion B (P.proj.app i) Wi
  let ι₀ : (SmallEtale.toScheme B X.1 X.property).obj
      ((smallEtaleBaseChange B (P.proj.app i)).obj Wi) ≅ pullback ai pi := hpb.isoPullback
  have hι₁ : ι₀.hom ≫ pullback.fst ai pi = _ := hpb.isoPullback_hom_fst
  have hι₂ : ι₀.hom ≫ pullback.snd ai pi = _ := hpb.isoPullback_hom_snd
  let m : (SmallEtale.toScheme B X.1 X.property).obj
      ((smallEtaleBaseChange B (P.proj.app i)).obj Wi)
      ⟶ (SmallEtale.toScheme B X.1 X.property).obj b.1 := ι₀.hom ≫ eL.inv
  have hm : m ≫ B.inclusion.map b.1.obj.hom =
      B.inclusion.map (pullback.snd Wi.obj.hom (P.proj.app i)) := by
    rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, hι₂]
  let φ₀ : (smallEtaleBaseChange B (P.proj.app i)).obj Wi ⟶ b.1 :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk m) (ObjectProperty.hom_ext _ hm))
  refine ⟨i, W, φ₀ ≫ r.1, ?_⟩
  have hlift : baseChangeEtalePointHom B (P.proj.app i) rfl Wi ⟨w, hw⟩ ≫ ι₀.hom =
      b.2.1 ≫ eL.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hι₁]
      exact (baseChangeEtalePointHom_fst B (P.proj.app i) rfl Wi ⟨w, hw⟩).trans (by simp [w])
    · rw [Category.assoc, hι₂, Category.assoc, he, hb]
      exact baseChangeEtalePointHom_snd B (P.proj.app i) rfl Wi ⟨w, hw⟩
  show baseChangeEtalePointHom B (P.proj.app i) rfl Wi ⟨w, hw⟩ ≫
    ((ι₀.hom ≫ eL.inv) ≫ (SmallEtale.toScheme B X.1 X.property).map r.1) = U.2.1
  rw [Category.assoc, reassoc_of% hlift, Iso.hom_inv_id_assoc]
  exact congrArg Subtype.val r.2

/-- **Stacks 09YZ, over an affine base, inside a big étale site.** An integral morphism of a big
étale site with affine target is a limit of finite morphisms whose stages are again objects of the
site. The stages are the spectra of the finitely generated subalgebras, finite over the affine
target, so their size is bounded by that of the target. -/
def ofIsAffine (f : X ⟶ Y) [IsIntegralHom (B.inclusion.map f)] [IsAffine (B.inclusion.obj Y)] :
    SmallEtaleIntegralStages B f :=
  let p := Stacks.EtaleCohomology.integralLimitPresentation (B.inclusion.map f)
  let := p.indexPreorder
  let := p.indexNonempty
  let := p.indexDirected
  have hsize : ∀ i, B.Contains (p.diagram.obj i) := fun i => by
    have := p.stageFinite i
    have : IsAffine (((Functor.const p.indexTypeᵒᵖ).obj (B.inclusion.obj Y)).obj i) :=
      inferInstanceAs (IsAffine (B.inclusion.obj Y))
    have : IsAffine (p.diagram.obj i) := isAffine_of_isAffineHom (p.structureMap.app i)
    exact (Scheme.size_le_of_locallyOfFiniteType (p.structureMap.app i)).trans_lt Y.property
  { index := p.indexType
    diagram := (schemeSizeBelow B.cutoff).lift p.diagram hsize
    proj :=
      { app := fun i => ObjectProperty.homMk (p.limitCone.app i)
        naturality := fun _ _ a => ObjectProperty.hom_ext _ (p.limitCone.naturality a) }
    str :=
      { app := fun i => ObjectProperty.homMk (p.structureMap.app i)
        naturality := fun _ _ a => ObjectProperty.hom_ext _ (p.structureMap.naturality a) }
    fac := fun i => ObjectProperty.hom_ext _ (p.compatible i).symm
    isLimit := p.isLimit
    finite := p.stageFinite }

end SmallEtaleIntegralStages

end Stages

end AlgebraicGeometry
