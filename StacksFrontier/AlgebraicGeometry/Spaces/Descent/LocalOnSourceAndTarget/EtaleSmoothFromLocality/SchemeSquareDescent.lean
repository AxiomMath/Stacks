module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.SmoothLocus

/-!
# Étale-smooth locality from locality hypotheses: the descent along scheme squares

The commutative squares of schemes of the site produced by the represented locality condition,
Stacks 0CF1 for the induced property of morphisms of schemes over `S`, and Stacks 0CG2:
`AlgebraicGeometry.Space.isEtaleSmoothLocalOnSourceAndTarget_of_local`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is deep (see the docstring)
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf_bigFppfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Limits.HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_bigFppfOver
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.HasLimit (Limits.cospan f g) :=
  Limits.HasLimitsOfShape.has_limit _

/-- A morphism of the site whose induced morphism of represented algebraic spaces is smooth is
smooth on underlying schemes. -/
private theorem smooth_of_yoneda_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Space.IsSmooth B S hS (yoneda.map g)) :
    Smooth ((BigFppfOver.toScheme B S hS).map g) :=
  hg U V (𝟙 _) (𝟙 _) g (AlgebraicGeometry.Space.presheaf_etale_id B S hS U)
    (AlgebraicGeometry.Space.presheaf_etale_id B S hS V) (by simp)

/-- A functor preserving pullbacks sends the lift into a pullback to the lift of the images, up to
the canonical isomorphism with the pullback of the images. -/
private theorem map_pullback_lift_comp_isoPullback_hom
    {C D : Type*} [Category* C] [Category* D] [Limits.HasPullbacks C] [Limits.HasPullbacks D]
    (F : C ⥤ D) [Limits.PreservesLimitsOfShape Limits.WalkingCospan F] {A X T Y : C}
    (a : A ⟶ X) (h : A ⟶ T) (f : X ⟶ Y) (b : T ⟶ Y) (comm : a ≫ f = h ≫ b) :
    F.map (Limits.pullback.lift a h comm) ≫
        ((IsPullback.of_hasPullback f b).map F).isoPullback.hom =
      Limits.pullback.lift (F.map a) (F.map h)
        (by simpa only [Functor.map_comp] using congrArg F.map comm) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp,
      Limits.pullback.lift_fst, Limits.pullback.lift_fst]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp,
      Limits.pullback.lift_snd, Limits.pullback.lift_snd]

/-- A morphism into a fibre product has a property as soon as the comparison morphism of the
represented fibre product is relatively representable by that property. -/
private theorem property_pullback_lift_of_presheaf
    {C : Type*} [Category* C] [Limits.HasPullbacks C]
    (Q : MorphismProperty C) {A X T Y : C}
    (a : A ⟶ X) (h : A ⟶ T) (f : X ⟶ Y) (b : T ⟶ Y)
    (comm : a ≫ f = h ≫ b)
    (he : Q.presheaf (Limits.pullback.lift (yoneda.map a) (yoneda.map h)
      (by simpa only [Functor.map_comp] using congrArg yoneda.map comm))) :
    Q (Limits.pullback.lift a h comm) := by
  let sq := (IsPullback.of_hasPullback f b).map yoneda
  let i := sq.isoPullback
  let k := Limits.pullback.lift a h comm
  have hk : yoneda.map k ≫ i.hom =
      Limits.pullback.lift (yoneda.map a) (yoneda.map h)
        (by simpa only [Functor.map_comp] using congrArg yoneda.map comm) :=
    map_pullback_lift_comp_isoPullback_hom yoneda a h f b comm
  exact he.property i.hom (𝟙 _) k
    (IsPullback.of_horiz_isIso ⟨by simpa only [Category.id_comp] using hk.symm⟩)

/-- If the comparison morphism to the fibre product of represented algebraic spaces is étale, then
the comparison morphism of the underlying schemes is étale. -/
private theorem etale_pullback_lift_of_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A X T Y : BigFppfOver B S hS}
    (a : A ⟶ X) (h : A ⟶ T) (f : X ⟶ Y) (b : T ⟶ Y)
    (comm : a ≫ f = h ≫ b)
    (he : Space.IsEtale B S hS
      (Limits.pullback.lift (yoneda.map a) (yoneda.map h)
        (by simpa only [Functor.map_comp] using congrArg yoneda.map comm))) :
    Etale (Limits.pullback.lift
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map h)
      (by simpa only [Functor.map_comp] using
        congrArg (BigFppfOver.toScheme B S hS).map comm)) := by
  let F := BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F
  have hrel : Q.presheaf
      (Limits.pullback.lift (yoneda.map a) (yoneda.map h)
        (by simpa only [Functor.map_comp] using congrArg yoneda.map comm)) := by
    simpa using he A (𝟙 _) (AlgebraicGeometry.Space.presheaf_etale_id B S hS A)
  let k := Limits.pullback.lift a h comm
  have hkEtale : Etale (F.map k) :=
    property_pullback_lift_of_presheaf Q a h f b comm hrel
  have : Limits.PreservesLimitsOfShape Limits.WalkingCospan F :=
    Limits.comp_preservesLimitsOfShape _ _
  let sq := (IsPullback.of_hasPullback f b).map F
  have hk : F.map k ≫ sq.isoPullback.hom = Limits.pullback.lift (F.map a) (F.map h)
      (by simpa only [Functor.map_comp] using congrArg F.map comm) :=
    map_pullback_lift_comp_isoPullback_hom F a h f b comm
  rw [← hk]
  exact Etale.etale_comp _ _

/-- The represented locality condition for a morphism of the site produces, above every point, a
commutative square of the site with smooth right arrow and étale comparison morphism. -/
private theorem exists_scheme_square_of_neighborhoods
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : HasEtaleSmoothSchemeNeighborhoods B S hS P (schemeMap B S hS g))
    (x : Space.points B S hS (yoneda.obj U)) :
    ∃ (U' V' : BigFppfOver B S hS)
      (a : U' ⟶ U) (b : V' ⟶ V) (g' : U' ⟶ V')
      (hcomm : a ≫ g = g' ≫ b)
      (x' : Space.points B S hS (yoneda.obj U')),
      Space.IsSmooth B S hS (yoneda.map b) ∧
      Space.IsEtale B S hS
        (Limits.pullback.lift (yoneda.map a) (yoneda.map g')
          (by simpa only [Functor.map_comp] using congrArg yoneda.map hcomm)) ∧
      Space.pointsMap B S hS (yoneda.obj U') (yoneda.map a) x' = x ∧
      P (schemeMap B S hS g') := by
  obtain ⟨V', U', b, e, x', hb, he, hx, hP⟩ := hg x
  obtain ⟨b', hbmap⟩ := yoneda.map_surjective b.hom
  have hb' : b = schemeMap B S hS b' := ObjectProperty.hom_ext _ hbmap.symm
  clear hbmap
  subst b
  let p : AlgebraicSpaces.fiberProduct B S hS (schemeMap B S hS g)
      (schemeMap B S hS b') ⟶ Space.representedAlgebraicSpace B S hS U :=
    ObjectProperty.homMk (Limits.pullback.fst _ _)
  let q : AlgebraicSpaces.fiberProduct B S hS (schemeMap B S hS g)
      (schemeMap B S hS b') ⟶ Space.representedAlgebraicSpace B S hS V' :=
    ObjectProperty.homMk (Limits.pullback.snd _ _)
  let a := yoneda.preimage (e ≫ p).hom
  let g' := yoneda.preimage (e ≫ q).hom
  have haCat : yoneda.map a = (e ≫ p).hom := yoneda.map_preimage _
  have hgCat : yoneda.map g' = (e ≫ q).hom := yoneda.map_preimage _
  have ha : yoneda.map a =
      e.hom ≫ Limits.pullback.fst (schemeMap B S hS g).hom
        (schemeMap B S hS b').hom := haCat
  have hg' : yoneda.map g' =
      e.hom ≫ Limits.pullback.snd (schemeMap B S hS g).hom
        (schemeMap B S hS b').hom := hgCat
  have hcomm : a ≫ g = g' ≫ b' := by
    apply yoneda.map_injective
    have hsq := congrArg (fun k => e ≫ k)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (schemeMap B S hS g) (schemeMap B S hS b')).w
    have hsq' := congrArg (fun k => k.hom) hsq
    simpa only [Functor.map_comp, haCat, hgCat, schemeMap,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Category.assoc, p, q] using hsq'
  have heq : Limits.pullback.lift (f := (schemeMap B S hS g).hom)
      (g := (schemeMap B S hS b').hom)
      (yoneda.map a) (yoneda.map g')
      (by simpa only [Functor.map_comp, schemeMap, ObjectProperty.homMk_hom]
        using congrArg yoneda.map hcomm) =
      e.hom :=
    Limits.pullback.hom_ext ((Limits.pullback.lift_fst _ _ _).trans ha)
      ((Limits.pullback.lift_snd _ _ _).trans hg')
  refine ⟨U', V', a, b', g', hcomm, x', hb, ?_, ?_, ?_⟩
  · simpa only [schemeMap] using heq ▸ he
  · simpa only [schemeMap] using ha ▸ hx
  · have hmap : schemeMap B S hS g' = e ≫
        (ObjectProperty.homMk (Limits.pullback.snd (schemeMap B S hS g).hom
          (schemeMap B S hS b').hom) :
          AlgebraicSpaces.fiberProduct B S hS (schemeMap B S hS g)
            (schemeMap B S hS b') ⟶ Space.representedAlgebraicSpace B S hS V') :=
      ObjectProperty.hom_ext _ hg'
    rwa [hmap]

/-- The square produced by the represented locality condition, read on underlying schemes and above
a point of the underlying scheme of the source. -/
private theorem exists_underlying_scheme_square_of_neighborhoods
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : HasEtaleSmoothSchemeNeighborhoods B S hS P (schemeMap B S hS g))
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ (U' V' : BigFppfOver B S hS)
      (a : U' ⟶ U) (b : V' ⟶ V) (g' : U' ⟶ V')
      (hcomm : a ≫ g = g' ≫ b)
      (x' : (BigFppfOver.toScheme B S hS).obj U'),
      Smooth ((BigFppfOver.toScheme B S hS).map b) ∧
      Etale (Limits.pullback.lift
        ((BigFppfOver.toScheme B S hS).map a)
        ((BigFppfOver.toScheme B S hS).map g')
        (by simpa only [Functor.map_comp] using
          congrArg (BigFppfOver.toScheme B S hS).map hcomm)) ∧
      (BigFppfOver.toScheme B S hS).map a x' = x ∧
      P (schemeMap B S hS g') := by
  obtain ⟨z, hz⟩ := Space.surjective_pointsToScheme B S hS U x
  obtain ⟨U', V', a, b, g', hcomm, z', hb, he, ha, hP⟩ :=
    exists_scheme_square_of_neighborhoods B S hS P g hg z
  refine ⟨U', V', a, b, g', hcomm, Space.pointsToScheme B S hS U' z',
    smooth_of_yoneda_map B S hS b hb,
    etale_pullback_lift_of_yoneda B S hS a g' g b hcomm he, ?_, hP⟩
  rw [← Space.pointsToScheme_pointsMap, ha, hz]

attribute [local instance] bounded_open
attribute [local instance] bounded_pullback
attribute [local instance] bounded_affineSpace
attribute [local instance] pullbackCanonicallyOverRight
attribute [local instance] pullbackSnd_isOver
attribute [local instance] pullbackFst_isOver
attribute [local instance] pullbackLift_isOver
attribute [local instance] affineCoverCanonicallyOver
attribute [local instance] affineCoverMap_isOver
attribute [local instance] bounded_affineCover
attribute [local instance] bounded_openCover
attribute [local instance] coordinateShear_isOver
attribute [local instance] subPow_isOver
attribute [local instance] reindex_isOver

section RelativeConclusion

open CategoryTheory.Limits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS))
  [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, u + 1} .etale B S hS)]
  [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
  [hopen : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄
    (f : X ⟶ Y) => Space.IsOpenImmersion B S hS f.hom)]

/-- **Stacks 0CF1** for the induced property of morphisms of schemes over `S`: in a commutative
square with right vertical arrow smooth and comparison arrow étale at the chosen point, the two
source points lie in their largest open loci simultaneously. -/
private theorem mem_relativeLargestOpen_smooth_etale
    {X' X Y' Y : Scheme.{u}} [Y'.Over S] [Y.Over S]
    [Fact (B.Contains X')] [Fact (B.Contains X)]
    [Fact (B.Contains Y')] [Fact (B.Contains Y)]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    [g.IsOver S] (hcomm : g' ≫ f = f' ≫ g) (x' : X')
    (hg : InfinitesimalLifting.SmoothAt g (f'.base x'))
    (hg' : EtaleAt (pullback.lift g' f' hcomm) x') :
    g'.base x' ∈ relativeLargestOpen B S hS P f ↔
      x' ∈ relativeLargestOpen B S hS P f' := by
  let c := pullback.lift g' f' hcomm
  have hc : (pullback.fst f g).base (c.base x') = g'.base x' :=
    congrArg (fun k : X' ⟶ X => k.base x') (pullback.lift_fst g' f' hcomm)
  have hs : (pullback.snd f g).base (c.base x') = f'.base x' :=
    congrArg (fun k : X' ⟶ Y' => k.base x') (pullback.lift_snd g' f' hcomm)
  have h := mem_largestOpen_iff_of_smooth_pullback B S hS P f g (c.base x')
    (by rwa [hs])
  simpa only [hc] using h.trans
    (mem_largestOpen_iff_of_comparison_etaleAt B S hS P f f' g g' hcomm x' hg')

/-- A morphism of represented algebraic spaces satisfying the represented locality condition has
the property. -/
private theorem scheme_property_of_neighborhoods
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : HasEtaleSmoothSchemeNeighborhoods B S hS P (schemeMap B S hS g)) :
    P (schemeMap B S hS g) := by
  let F := BigFppfOver.toScheme B S hS
  let : (F.obj U).Over S := ⟨U.hom.hom⟩
  let : (F.obj V).Over S := ⟨V.hom.hom⟩
  have : Fact (B.Contains (F.obj U)) := ⟨U.left.property⟩
  have : Fact (B.Contains (F.obj V)) := ⟨V.left.property⟩
  let : (F.map g).IsOver S := ⟨congrArg (fun a => a.hom) (Over.w g)⟩
  apply (relativeProperty_iff B S hS P (F.map g)).mp
  apply (relativeLargestOpen_eq_top_iff B S hS P (F.map g)).mp
  apply top_unique
  intro x hx
  obtain ⟨U', V', a, b, g', hcomm, x', hb, he, hx', hP⟩ :=
    exists_underlying_scheme_square_of_neighborhoods B S hS P g hg x
  let : (F.obj U').Over S := ⟨U'.hom.hom⟩
  let : (F.obj V').Over S := ⟨V'.hom.hom⟩
  let : Fact (B.Contains (F.obj U')) := ⟨U'.left.property⟩
  let : Fact (B.Contains (F.obj V')) := ⟨V'.left.property⟩
  let : (F.map g').IsOver S := ⟨congrArg (fun a => a.hom) (Over.w g')⟩
  let : (F.map b).IsOver S := ⟨congrArg (fun a => a.hom) (Over.w b)⟩
  have hg' : relativeProperty B S hS P (F.map g') :=
    (relativeProperty_iff B S hS P (F.map g')).mpr hP
  have htop := (relativeLargestOpen_eq_top_iff B S hS P (F.map g')).mpr hg'
  have hmem : x' ∈ relativeLargestOpen B S hS P (F.map g') := by
    rw [htop]
    trivial
  have hb' : InfinitesimalLifting.SmoothAt (F.map b) ((F.map g').base x') := by
    refine ⟨⊤, by simp, ?_⟩
    let : Smooth (F.map b) := hb
    exact instSmoothResLE (F.map b) ⊤ ⊤ _
  have he' : EtaleAt _ x' :=
    (etale_iff_forall_etaleAt _).mp he x'
  rw [← hx']
  exact (mem_relativeLargestOpen_smooth_etale B S hS P
    (F.map g) (F.map g') (F.map b) (F.map a)
    (by simpa only [Functor.map_comp] using congrArg F.map hcomm)
    x' hb' he').mpr hmem

end RelativeConclusion

namespace Space

/-- **Stacks 0CG2.** A property of morphisms of algebraic spaces over `S` which is étale local
on the source, smooth local on the target and stable under postcomposition with open immersions
is étale-smooth local on the source-and-target. -/
@[stacks 0CG2]
theorem isEtaleSmoothLocalOnSourceAndTarget_of_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtSource (Space.Topology.precoverage.{u, u + 1} .etale B S hS)]
    [P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
    [P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄
      (f : X ⟶ Y) => Space.IsOpenImmersion B S hS f.hom)] :
    Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z f g hg hf
    exact Space.comp_isEtale (P := P) f g hg hf
  · intro X Y Y' f hf b hb
    exact prop_pullbackSnd_of_smooth B S hS P f hf b hb
  · intro X Y f
    exact ⟨fun hf x => Space.exists_etale_smooth_neighborhood_of_prop f hf x,
      fun hlocal => property_of_scheme_neighborhood_descent B S hS P f hlocal
        fun U V g hg => scheme_property_of_neighborhoods B S hS P g hg⟩

end Space

end AlgebraicGeometry

end
