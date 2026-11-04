module

public import Mathlib.RingTheory.Nullstellensatz
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Criterion
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.AffineSpaceOrbits
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleAffineSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.JacobianCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Precomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Étale-smooth locality from locality hypotheses: the locality condition

Consequences of étale locality on the source and smooth locality on the target for a property of
morphisms of algebraic spaces over `S`, the locality condition of Stacks 0CFZ and its variant with
neighbourhoods represented by objects of the site, and the reduction of the descent half of
Stacks 0CG2 to morphisms of represented algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- A property étale local on the source descends along a single étale morphism which is
surjective on points. -/
private theorem of_comp_surjective_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, v} .etale B S hS)]
    {U X Y : AlgebraicSpaces B S hS} (a : U ⟶ X) (f : X ⟶ Y)
    (ha : Space.IsEtale B S hS a.hom)
    (hsurj : Function.Surjective (Space.pointsMap B S hS U.obj a.hom))
    (hf : P (a ≫ f)) : P f := by
  let R := Presieve.ofArrows (fun _ : PUnit.{v + 1} => U) (fun _ => a)
  have hR : R ∈ Space.Topology.precoverage.{u, v} .etale B S hS X := by
    refine ⟨PUnit.{v + 1}, (fun _ => U), (fun _ => a), rfl,
      X.property, (fun _ => U.property), X.property, (fun _ => U.property),
      (fun _ => ha), ?_⟩
    simpa only [Set.iUnion_const] using hsurj.range_eq
  exact MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hR fun _ _ ⟨_⟩ => hf

/-- A morphism of presheaves which is relatively representable by étale morphisms of schemes is
étale as a morphism of algebraic spaces. -/
theorem etale_of_presheaf_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    Space.IsEtale B S hS f := by
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : Q.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Q
  intro T g hg
  exact MorphismProperty.comp_mem Q.presheaf g f hg hf

/-- Every algebraic space over `S` admits an étale atlas by a single object of the site whose
induced map on points is surjective. -/
private theorem exists_surjective_etale_atlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) :
    ∃ (U : BigFppfOver B S hS)
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) ⟶ X),
      Space.IsEtale B S hS a.hom ∧
      Function.Surjective (Space.pointsMap B S hS (yoneda.obj U) a.hom) := by
  obtain ⟨U, a, hsurj, hetale⟩ := X.property.exists_atlas
  exact ⟨U, ObjectProperty.homMk a, etale_of_presheaf_etale B S hS a hetale,
    (Space.presheafSurjective_iff_isSurjective_yoneda B S hS X.obj X.property U a).mp
      hsurj⟩

/-- A property étale local on the source holds for a morphism as soon as it holds after
precomposition with every étale morphism from a represented algebraic space. -/
private theorem of_forall_etale_scheme_source
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, v} .etale B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : ∀ (U : BigFppfOver B S hS)
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) ⟶ X),
      Space.IsEtale B S hS a.hom → P (a ≫ f)) : P f := by
  obtain ⟨U, a, ha, hsurj⟩ := exists_surjective_etale_atlas B S hS X
  exact of_comp_surjective_etale B S hS P a f ha hsurj (hf U a ha)

/-- A property local at the target for the smooth topology is stable under base change along a
smooth morphism, stated for the chosen fibre product. -/
theorem prop_pullbackSnd_of_smooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, w} .smooth B S hS)]
    {X Y Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : P f) (b : Y' ⟶ Y)
    (hb : Space.IsSmooth B S hS b.hom) :
    P (ObjectProperty.homMk (Limits.pullback.snd f.hom b.hom) :
      AlgebraicSpaces.fiberProduct B S hS f b ⟶ Y') := by
  have hpb := Space.prop_fiberProduct_fst_of_isLocalAtTarget B S hS .smooth P f b hf hb
  let σ : AlgebraicSpaces.fiberProduct B S hS f b ⟶
      AlgebraicSpaces.fiberProduct B S hS b f :=
    ObjectProperty.homMk (Limits.pullbackSymmetry f.hom b.hom).hom
  have : IsIso σ := (ObjectProperty.isIso_hom_iff σ).mp (by
    show IsIso (Limits.pullbackSymmetry f.hom b.hom).hom
    infer_instance)
  have hcomp : σ ≫ ObjectProperty.homMk (Limits.pullback.fst b.hom f.hom) =
      ObjectProperty.homMk (Limits.pullback.snd f.hom b.hom) :=
    ObjectProperty.hom_ext _ (Limits.pullbackSymmetry_hom_comp_fst f.hom b.hom)
  have hq : P (σ ≫ ObjectProperty.homMk (Limits.pullback.fst b.hom f.hom)) :=
    (P.cancel_left_of_respectsIso σ _).2 hpb
  rwa [hcomp] at hq

/-- A property local at the target for the smooth topology holds for the left vertical arrow of
any cartesian square whose base morphism is smooth. -/
theorem property_of_isPullback_smooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, w} .smooth B S hS)]
    {X' X Y' Y : AlgebraicSpaces B S hS}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    (sq : IsPullback a f' f b)
    (hb : Space.IsSmooth B S hS b.hom) (hf : P f) : P f' := by
  let target := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  have hcomp := (P.cancel_left_of_respectsIso (sq.isoIsPullback _ _ target).hom
    (ObjectProperty.homMk (Limits.pullback.snd f.hom b.hom))).mpr
    (prop_pullbackSnd_of_smooth B S hS P f hf b hb)
  rwa [sq.isoIsPullback_hom_snd _ _ target] at hcomp

/-- An isomorphism of algebraic spaces over `S` is étale. -/
private theorem etale_of_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [IsIso f] :
    Space.IsEtale B S hS f.hom :=
  (Space.isEtaleCovering_of_isIso
    B S hS f.hom Y.property).etale ()

/-- The composite of an étale morphism of algebraic spaces with an isomorphism is étale. -/
private theorem isEtale_comp_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (e : X ⟶ Y) (i : Y ⟶ Z) [IsIso i]
    (he : Space.IsEtale B S hS e.hom) : Space.IsEtale B S hS (e ≫ i).hom := by
  simpa only [ObjectProperty.FullSubcategory.comp_hom] using
    Space.isEtale_comp B S hS he (etale_of_isIso B S hS i)

/-- An étale morphism to the apex of a cartesian square over `f` and `b` factors through an étale
morphism to the chosen fibre product, compatibly with both projections. -/
private theorem exists_etale_to_fiberProduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y V P U : AlgebraicSpaces B S hS} (f : X ⟶ Y) (b : V ⟶ Y) (s : P ⟶ X) (t : P ⟶ V)
    (sq : IsPullback s t f b) (e : U ⟶ P) (he : Space.IsEtale B S hS e.hom) :
    ∃ e' : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b, Space.IsEtale B S hS e'.hom ∧
      e' ≫ (ObjectProperty.homMk (Limits.pullback.fst f.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS f b ⟶ X) = e ≫ s ∧
      e' ≫ (ObjectProperty.homMk (Limits.pullback.snd f.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS f b ⟶ V) = e ≫ t := by
  let target := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  exact ⟨e ≫ (sq.isoIsPullback _ _ target).hom,
    isEtale_comp_isIso B S hS e _ he, by rw [Category.assoc, sq.isoIsPullback_hom_fst _ _ target],
    by rw [Category.assoc, sq.isoIsPullback_hom_snd _ _ target]⟩

/-- An étale postcomposition may be cancelled from a property which is étale local on the source
and smooth local on the target. -/
theorem of_postcomp_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, v} .etale B S hS)]
    [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, w} .smooth B S hS)]
    {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (b : Y ⟶ Z)
    (hb : Space.IsEtale B S hS b.hom) (hf : P (f ≫ b)) : P f := by
  let Q := AlgebraicSpaces.fiberProduct B S hS (f ≫ b) b
  let p : Q ⟶ X := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let q : Q ⟶ Y := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sq := AlgebraicSpaces.isPullback_fiberProduct B S hS (f ≫ b) b
  let a := sq.lift (𝟙 X) f (by simp)
  have ha : Space.IsEtale B S hS a.hom := by
    apply Space.isEtale_of_isEtale_over B S hS X.property Q.property X.property
      a.hom (𝟙 X.obj) p.hom
    · intro T φ hφ
      simpa using hφ
    · exact Space.isEtale_of_isPullback B S hS q p b (f ≫ b) sq.flip hb
    · exact congrArg (fun t : X ⟶ X => t.hom) (sq.lift_fst (𝟙 X) f (by simp))
  have hq : P q := prop_pullbackSnd_of_smooth B S hS P (f ≫ b) hf b
    (Space.isSmooth_of_isEtale B S hS Z.property hb)
  rw [← show a ≫ q = f from sq.lift_snd _ _ _]
  exact Space.comp_isEtale (P := P) a q ha hq

/-- The locality condition of Stacks 0CFZ for a morphism of algebraic spaces: above every point of
the source there is an étale neighbourhood over a smooth target neighbourhood with the property. -/
abbrev HasEtaleSmoothNeighborhoods
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  ∀ x : Space.points B S hS X.obj,
    ∃ (V U : AlgebraicSpaces B S hS) (b : V ⟶ Y)
      (e : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b)
      (u : Space.points B S hS U.obj),
      Space.IsSmooth B S hS b.hom ∧ Space.IsEtale B S hS e.hom ∧
      Space.pointsMap B S hS U.obj
        (e ≫ (ObjectProperty.homMk (Limits.pullback.fst f.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS f b ⟶ X)).hom u = x ∧
      P (e ≫ (ObjectProperty.homMk (Limits.pullback.snd f.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS f b ⟶ V))

/-- The locality condition is stable under precomposition with an étale morphism. -/
private theorem neighborhoods_precomp_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, v} .etale B S hS)]
    {X' X Y : AlgebraicSpaces B S hS} (a : X' ⟶ X) (f : X ⟶ Y)
    (ha : Space.IsEtale B S hS a.hom)
    (hf : HasEtaleSmoothNeighborhoods B S hS P f) :
    HasEtaleSmoothNeighborhoods B S hS P (a ≫ f) := by
  intro x'
  obtain ⟨V, U, b, e, u, hb, he, hu, hh⟩ := hf (Space.pointsMap B S hS X'.obj a.hom x')
  let Q := AlgebraicSpaces.fiberProduct B S hS f b
  let p : Q ⟶ X := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let q : Q ⟶ V := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  let Q' := AlgebraicSpaces.fiberProduct B S hS a p
  let s : Q' ⟶ X' := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let r : Q' ⟶ Q := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sq' := AlgebraicSpaces.isPullback_fiberProduct B S hS a p
  let outer : IsPullback s (r ≫ q) (a ≫ f) b := (sq'.flip.paste_horiz sq.flip).flip
  let U' := AlgebraicSpaces.fiberProduct B S hS e r
  let c : U' ⟶ U := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let d : U' ⟶ Q' := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sqU := AlgebraicSpaces.isPullback_fiberProduct B S hS e r
  have hr : Space.IsEtale B S hS r.hom :=
    Space.isEtale_of_isPullback B S hS s r a p sq' ha
  have hc : Space.IsEtale B S hS c.hom :=
    Space.isEtale_of_isPullback B S hS d c r e sqU.flip hr
  have hd : Space.IsEtale B S hS d.hom :=
    Space.isEtale_of_isPullback B S hS c d e r sqU he
  have hmatch : Space.pointsMap B S hS X'.obj a.hom x' =
      Space.pointsMap B S hS Q.obj p.hom
        (Space.pointsMap B S hS U.obj e.hom u) := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, Space.pointsMap_comp,
      Function.comp_apply] using hu.symm
  obtain ⟨z, hzs, hzr⟩ := Space.exists_point_of_isPullback B S hS sq' x'
    (Space.pointsMap B S hS U.obj e.hom u) hmatch
  obtain ⟨u', huc, hud⟩ := Space.exists_point_of_isPullback B S hS sqU u z hzr.symm
  obtain ⟨e', he', h₁, h₂⟩ := exists_etale_to_fiberProduct B S hS (a ≫ f) b s (r ≫ q) outer d hd
  refine ⟨V, U', b, e', u', hb, he', ?_, ?_⟩
  · rw [h₁]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Space.pointsMap_comp,
      Function.comp_apply]
    change Space.pointsMap B S hS U'.obj d.hom u' = z at hud
    rwa [hud]
  · have hcomp : d ≫ r ≫ q = c ≫ e ≫ q := by
      rw [← Category.assoc, ← sqU.w, Category.assoc]
    rw [h₂, hcomp]
    exact Space.comp_isEtale (P := P) c (e ≫ q) hc hh

/-- The locality condition for a morphism follows from the locality condition for its composite
with an étale morphism. -/
private theorem neighborhoods_of_postcomp_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, v} .etale B S hS)]
    [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, w} .smooth B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (c : Y ⟶ Z)
    (hc : Space.IsEtale B S hS c.hom)
    (hf : HasEtaleSmoothNeighborhoods B S hS P (f ≫ c)) :
    HasEtaleSmoothNeighborhoods B S hS P f := by
  intro x
  obtain ⟨V, U, b, e, u, hb, he, hu, hh⟩ := hf x
  let Q := AlgebraicSpaces.fiberProduct B S hS (f ≫ c) b
  let p : Q ⟶ X := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let q : Q ⟶ V := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sq := AlgebraicSpaces.isPullback_fiberProduct B S hS (f ≫ c) b
  let V' := AlgebraicSpaces.fiberProduct B S hS b c
  let r : V' ⟶ V := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let s : V' ⟶ Y := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sqV := AlgebraicSpaces.isPullback_fiberProduct B S hS b c
  have hcomm : q ≫ b = (p ≫ f) ≫ c := sq.w.symm.trans (Category.assoc _ _ _).symm
  let k := sqV.lift q (p ≫ f) hcomm
  have hkr : k ≫ r = q := sqV.lift_fst _ _ _
  have hks : k ≫ s = p ≫ f := sqV.lift_snd _ _ _
  have outer : IsPullback (k ≫ r) p b (f ≫ c) := by
    rw [hkr]
    exact sq.flip
  let sq' := (outer.of_right hks sqV).flip
  have hr : Space.IsEtale B S hS r.hom :=
    Space.isEtale_of_isPullback B S hS s r c b sqV.flip hc
  have hs : Space.IsSmooth B S hS s.hom :=
    (Space.isSmooth_isStableUnderBaseChange B S hS).of_isPullback sqV hb
  obtain ⟨e', he', h₁, h₂⟩ := exists_etale_to_fiberProduct B S hS f s _ _ sq' e he
  refine ⟨V', U, s, e', u, hs, he', ?_, ?_⟩
  · rwa [h₁]
  · rw [h₂]
    apply of_postcomp_etale B S hS P (e ≫ k) r hr
    simpa only [Category.assoc, hkr] using hh

/-- The locality condition of Stacks 0CFZ with the two neighbourhoods required to be represented by
objects of the site. -/
abbrev HasEtaleSmoothSchemeNeighborhoods
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  ∀ x : Space.points B S hS X.obj,
    ∃ (V U : BigFppfOver B S hS)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ :
        AlgebraicSpaces B S hS) ⟶ Y)
      (e : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) ⟶ AlgebraicSpaces.fiberProduct B S hS f b)
      (u : Space.points B S hS (yoneda.obj U)),
      Space.IsSmooth B S hS b.hom ∧ Space.IsEtale B S hS e.hom ∧
      Space.pointsMap B S hS (yoneda.obj U)
        (e ≫ (ObjectProperty.homMk (Limits.pullback.fst f.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS f b ⟶ X)).hom u = x ∧
      P (e ≫ (ObjectProperty.homMk (Limits.pullback.snd f.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS f b ⟶ _))

/-- The neighbourhoods in the locality condition may be taken to be represented by objects of the
site, by refining each of them by an étale atlas. -/
private theorem scheme_neighborhoods_of_neighborhoods
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, v} .etale B S hS)]
    [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, w} .smooth B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : HasEtaleSmoothNeighborhoods B S hS P f) :
    HasEtaleSmoothSchemeNeighborhoods B S hS P f := by
  intro x
  obtain ⟨V, U, b, e, u, hb, he, hu, hh⟩ := hf x
  obtain ⟨T, c, hc, hcs⟩ := exists_surjective_etale_atlas B S hS V
  let V' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let Q := AlgebraicSpaces.fiberProduct B S hS f b
  let p : Q ⟶ X := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let q : Q ⟶ V := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  let Q' := AlgebraicSpaces.fiberProduct B S hS c q
  let r : Q' ⟶ V' := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let s : Q' ⟶ Q := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sqQ := AlgebraicSpaces.isPullback_fiberProduct B S hS c q
  let outer : IsPullback (s ≫ p) r f (c ≫ b) := sqQ.flip.paste_horiz sq
  let U' := AlgebraicSpaces.fiberProduct B S hS e s
  let j : U' ⟶ U := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let d : U' ⟶ Q' := ObjectProperty.homMk (Limits.pullback.snd _ _)
  let sqU := AlgebraicSpaces.isPullback_fiberProduct B S hS e s
  have hd : Space.IsEtale B S hS d.hom := Space.isEtale_of_isPullback B S hS j d e s sqU he
  have hcsmooth : Space.IsSmooth B S hS c.hom := Space.isSmooth_of_isEtale B S hS V.property hc
  have hP : P (d ≫ r) := property_of_isPullback_smooth B S hS P
    j (d ≫ r) (e ≫ q) c (sqU.paste_vert sqQ.flip) hcsmooth hh
  obtain ⟨v', hv'⟩ :=
    hcs (Space.pointsMap B S hS Q.obj q.hom (Space.pointsMap B S hS U.obj e.hom u))
  obtain ⟨z, hzr, hzs⟩ := Space.exists_point_of_isPullback B S hS sqQ v' _ hv'
  obtain ⟨u', huj, hud⟩ := Space.exists_point_of_isPullback B S hS sqU u z hzs.symm
  obtain ⟨A, a, ha, has⟩ := exists_surjective_etale_atlas B S hS U'
  obtain ⟨u'', hua⟩ := has u'
  have hcb : Space.IsSmooth B S hS (c ≫ b).hom := Space.isSmooth_comp B S hS V'.property
    V.property Y.property c.hom b.hom hcsmooth hb
  obtain ⟨e', he', h₁, h₂⟩ := exists_etale_to_fiberProduct B S hS f (c ≫ b) _ _ outer (a ≫ d)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom] using Space.isEtale_comp B S hS ha hd)
  refine ⟨T, A, c ≫ b, e', u'', hcb, he', ?_, ?_⟩
  · have hcomp : (a ≫ d) ≫ s ≫ p = (a ≫ j) ≫ e ≫ p := by
      simp only [Category.assoc]
      rw [← Category.assoc d s, ← sqU.w, Category.assoc]
    rw [h₁, hcomp]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Space.pointsMap_comp,
      Function.comp_apply]
    change Space.pointsMap B S hS (yoneda.obj A) a.hom u'' = u' at hua
    change Space.pointsMap B S hS U'.obj j.hom u' = u at huj
    rw [hua, huj]
    simpa only [ObjectProperty.FullSubcategory.comp_hom, Space.pointsMap_comp,
      Function.comp_apply] using hu
  · rw [h₂, Category.assoc]
    exact Space.comp_isEtale (P := P) a (d ≫ r) ha hP

/-- A property local at the target for the smooth topology descends along a single smooth morphism
which is surjective on points. -/
theorem of_isPullback_surjective_smooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, w} .smooth B S hS)]
    {X' X Y' Y : AlgebraicSpaces B S hS}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    (sq : IsPullback a f' f b)
    (hb : Space.IsSmooth B S hS b.hom)
    (hsurj : Function.Surjective (Space.pointsMap B S hS Y'.obj b.hom))
    (hf' : P f') : P f := by
  let R := Presieve.ofArrows (fun _ : PUnit.{w + 1} => Y') (fun _ => b)
  have hR : R ∈ Space.Topology.precoverage.{u, w} .smooth B S hS Y := by
    refine ⟨PUnit.{w + 1}, (fun _ => Y'), (fun _ => b), rfl,
      Y.property, (fun _ => Y'.property), Y.property, (fun _ => Y'.property),
      (fun _ => hb), ?_⟩
    simpa only [Set.iUnion_const] using hsurj.range_eq
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hR
  rintro Z g _ ⟨i⟩
  apply (P.cancel_left_of_respectsIso sq.isoPullback.hom _).mp
  simpa only [sq.isoPullback_hom_snd] using hf'

/-- A property local at the target for the smooth topology holds for a morphism as soon as every
base change of it along an étale morphism from a represented algebraic space has it. -/
private theorem of_forall_etale_scheme_target
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, w} .smooth B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : ∀ (V : BigFppfOver B S hS)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ :
        AlgebraicSpaces B S hS) ⟶ Y),
      Space.IsEtale B S hS b.hom →
        P (ObjectProperty.homMk (Limits.pullback.snd f.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS f b ⟶ _)) : P f := by
  obtain ⟨V, b, hb, hsurj⟩ := exists_surjective_etale_atlas B S hS Y
  exact of_isPullback_surjective_smooth B S hS P _ _ f b
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
    (Space.isSmooth_of_isEtale B S hS Y.property hb) hsurj
    (hf V b hb)

/-- A morphism satisfying the locality condition has the property, provided every morphism of
represented algebraic spaces satisfying the represented locality condition has it. -/
theorem property_of_scheme_neighborhood_descent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, v} .etale B S hS)]
    [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, w} .smooth B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hlocal : HasEtaleSmoothNeighborhoods B S hS P f)
    (hdesc : ∀ (U V : BigFppfOver B S hS) (g : U ⟶ V),
      HasEtaleSmoothSchemeNeighborhoods B S hS P
        (ObjectProperty.homMk (yoneda.map g) :
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
            AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) →
      P (ObjectProperty.homMk (yoneda.map g) :
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
            AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) : P f := by
  apply of_forall_etale_scheme_target B S hS P f
  intro V b hb
  apply of_forall_etale_scheme_source B S hS P
  intro U a ha
  let Q := AlgebraicSpaces.fiberProduct B S hS f b
  let p : Q ⟶ X := ObjectProperty.homMk (Limits.pullback.fst _ _)
  let q : Q ⟶ _ := ObjectProperty.homMk (Limits.pullback.snd f.hom b.hom)
  let sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  have hp : Space.IsEtale B S hS p.hom :=
    Space.isEtale_of_isPullback B S hS q p b f sq.flip hb
  have hap : Space.IsEtale B S hS (a ≫ p).hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using Space.isEtale_comp B S hS ha hp
  have hcomp : (a ≫ q) ≫ b = (a ≫ p) ≫ f := by
    rw [Category.assoc, ← sq.w, Category.assoc]
  have hN : HasEtaleSmoothNeighborhoods B S hS P (a ≫ q) := by
    apply neighborhoods_of_postcomp_etale B S hS P (a ≫ q) b hb
    rw [hcomp]
    exact neighborhoods_precomp_etale B S hS P (a ≫ p) f hap hlocal
  have hSchemes := scheme_neighborhoods_of_neighborhoods B S hS P (a ≫ q) hN
  let g : U ⟶ V := yoneda.preimage (a ≫ q).hom
  have hg : (ObjectProperty.homMk (yoneda.map g) :
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) = a ≫ q :=
    ObjectProperty.hom_ext _ (yoneda.map_preimage _)
  rw [← hg] at hSchemes ⊢
  exact hdesc U V g hSchemes

/-- The morphism of represented algebraic spaces induced by a morphism of the big fppf site. -/
abbrev schemeMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    Space.representedAlgebraicSpace B S hS U ⟶ Space.representedAlgebraicSpace B S hS V :=
  ObjectProperty.homMk (yoneda.map g)

/-- A morphism of the site whose induced morphism of represented algebraic spaces is étale is
étale on underlying schemes. -/
private theorem etale_of_yoneda_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Space.IsEtale B S hS (yoneda.map g)) :
    Etale ((BigFppfOver.toScheme B S hS).map g) := by
  apply MorphismProperty.of_relative_map (F := yoneda)
    (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  simpa using hg U (𝟙 _) (AlgebraicGeometry.Space.presheaf_etale_id B S hS U)

end AlgebraicGeometry

end
