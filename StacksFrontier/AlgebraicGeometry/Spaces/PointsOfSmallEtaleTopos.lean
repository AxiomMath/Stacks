module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.SitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.Point.FiberComparison
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint
public import StacksFrontier.CategoryTheory.Sites.Point.Topos

/-!
# Points of the small étale topos of an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Every point
of the small étale topos of `F` has the stalk functor of a geometric point of `F`: there is a
geometric point `x` and an isomorphism of functors on sheaves between the inverse image of the
topos point and the set-valued geometric stalk `AlgebraicGeometry.Space.stalkSetFunctor x` of
Stacks 04JY.  This is Stacks 04K6.

The proof follows the source.  A point of the topos comes from a point of the site
(Stacks 00YA), and its fibre functor is nonempty at some étale chart `X` of `F`; localizing the
site point there (Stacks 04H2) and using that the small étale site of `F` over `X` is the small
étale site of the scheme `X` (Stacks 04M0 together with
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`) reduces the statement to the
classification of the points of the small étale site of a *scheme*, Stacks 04HU.  The geometric
point of the scheme `X` so obtained is enlarged to one whose spectrum lies in the site and then
pushed forward to a geometric point of `F`; its lifts into the charts of `F` over `X` are the
lifts of the scheme geometric point into the small étale site of `X`, which identifies the two
stalks.

## Main results

* `AlgebraicGeometry.Space.exists_geometricPoint_stalkFunctor_iso` is Stacks 04K6.
* `AlgebraicGeometry.Space.exists_chart_geometric_stalk`: the reduction to a chart, giving a
  geometric point of the scheme underlying some étale chart whose neighbourhood colimit
  computes the stalks of the topos point.
* `AlgebraicGeometry.exists_bounded_geometricPoint_extension`: every geometric point of a
  scheme in the site is dominated by one whose spectrum is again an object of the site.
* `AlgebraicGeometry.geometricPointFiberIsoOfExtension`: a morphism of geometric points of a
  scheme over the same image induces an isomorphism of their fibre functors on the small étale
  site.

## Main definitions

* `CategoryTheory.elementColimit` is the functor sending a presheaf to the colimit of its
  sections over the elements of a given covariant functor to sets — the shape in which a point
  of a site computes its stalk — with `CategoryTheory.elementColimitEquivalence` and
  `CategoryTheory.elementColimitIso` its invariance under an equivalence of the index category
  and under an isomorphism of the functor.
* `CategoryTheory.pointOfToposAlongEquivalence` and
  `CategoryTheory.restrictAlongEquivalence` transport a point of a topos, and restrict
  sheaves, along an equivalence of sites for an induced topology.
* `AlgebraicGeometry.Space.geometricPointOfSchemeAtlas` is the geometric point of `F`
  determined by a geometric point of the scheme underlying a chart of `F`.

## Implementation notes

The three isomorphisms of fibre functors that make up the proof are isomorphisms of
*functors*, so the final statement is an isomorphism of stalk functors on sheaves rather than
a family of bijections of stalks, which is what the source asserts.

Enlarging the geometric point is necessary because Stacks 04HU produces a geometric point whose
field is an algebraic closure of a residue field, with no size bound, while a geometric point of
an algebraic space must have its spectrum among the objects of the big fppf site.  The
enlargement does not change the fibre functor, by
`AlgebraicGeometry.geometricPointFiberIsoOfExtension`: a lift of a geometric point through an
étale morphism is determined by its restriction along any field extension, because an étale
scheme over an algebraically closed field is a disjoint union of copies of its base.

## References

* [Stacks Project, Tag 04K6](https://stacks.math.columbia.edu/tag/04K6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v u' v' w a b

namespace CategoryTheory

/-! ### Colimits over the category of elements -/

/-- Precomposition with an equivalence of categories is an equivalence of the categories of
elements. -/
theorem elementsPrecomp_isEquivalence {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (e : C ≌ D) (H : D ⥤ Type w) :
    (Functor.Elements.precomp e.functor H).IsEquivalence := by
  let T := Functor.Elements.precomp e.functor H
  let : T.Faithful := ⟨fun h => Functor.Elements.hom_ext (e.functor.map_injective
    (congrArg (fun f => f.hom) h))⟩
  let : T.Full := ⟨fun {X Y} f => ⟨Functor.Elements.homMk (e.functor.preimage f.hom) (by
    change H.map (e.functor.map (e.functor.preimage f.hom)) X.val = Y.val
    exact (congrArg (fun g => H.map g X.val) (e.functor.map_preimage f.hom)).trans
      (show H.map f.hom X.val = Y.val from f.map_val)),
      by apply Functor.Elements.hom_ext; exact e.functor.map_preimage _⟩⟩
  let : T.EssSurj := ⟨fun Y => ⟨(e.functor ⋙ H).elementsMk (e.inverse.obj Y.obj)
      (H.map (e.counitInv.app Y.obj) Y.val),
    ⟨Functor.Elements.isoMk (e.counitIso.app Y.obj) (by
      change H.map (e.counit.app Y.obj) (H.map (e.counitInv.app Y.obj) Y.val) = Y.val
      simp [← Functor.map_comp_apply])⟩⟩⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- An equivalence of the index category identifies the colimits over the categories of
elements of a functor and of its restriction. -/
noncomputable def elementColimitEquivalence {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (e : C ≌ D) (H : D ⥤ Type w) (A : Type a) [Category.{b} A]
    [HasColimitsOfShape H.Elementsᵒᵖ A]
    [HasColimitsOfShape (e.functor ⋙ H).Elementsᵒᵖ A] :
    (Functor.whiskeringLeft _ _ A).obj e.functor.op ⋙ elementColimit (e.functor ⋙ H) A ≅
      elementColimit H A :=
  letI : (Functor.Elements.precomp e.functor H).IsEquivalence :=
    elementsPrecomp_isEquivalence e H
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π H).op)
    (Functor.Final.colimIso (Functor.Elements.precomp e.functor H).op)

/-- An isomorphism of functors to sets induces an equivalence of their categories of
elements. -/
noncomputable def elementsEquivalenceOfIso {C : Type u} [Category.{v} C] {H G : C ⥤ Type w}
    (α : H ≅ G) : H.Elements ≌ G.Elements where
  functor := NatTrans.mapElements α.hom
  inverse := NatTrans.mapElements α.inv
  unitIso := NatIso.ofComponents (fun X =>
    Functor.Elements.isoMk (Iso.refl _) (by
      change H.map (𝟙 X.obj) X.val = α.inv.app X.obj (α.hom.app X.obj X.val)
      simp)) (by intro X Y f; apply Functor.Elements.hom_ext; simp)
  counitIso := NatIso.ofComponents (fun X =>
    Functor.Elements.isoMk (Iso.refl _) (by
      change G.map (𝟙 X.obj) (α.hom.app X.obj (α.inv.app X.obj X.val)) = X.val
      simp)) (by intro X Y f; apply Functor.Elements.hom_ext; simp)
  functor_unitIso_comp X := by apply Functor.Elements.hom_ext; simp

/-- An isomorphism of functors to sets identifies the colimits over their categories of
elements. -/
noncomputable def elementColimitIso {C : Type u} [Category.{v} C] {H G : C ⥤ Type w}
    (α : H ≅ G) (A : Type a) [Category.{b} A] [HasColimitsOfShape H.Elementsᵒᵖ A]
    [HasColimitsOfShape G.Elementsᵒᵖ A] : elementColimit H A ≅ elementColimit G A :=
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π G).op)
    (Functor.Final.colimIso (elementsEquivalenceOfIso α).functor.op)

/-! ### Transporting points and sheaves along an equivalence of sites -/

/-- Restriction of sheaves along an equivalence of categories which carries one Grothendieck
topology to the other. -/
noncomputable def restrictAlongEquivalence {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (e : C ≌ D) (K : GrothendieckTopology D) (J : GrothendieckTopology C)
    (hJ : e.functor.inducedTopology K = J) (A : Type w) [Category A] :
    Sheaf K A ⥤ Sheaf J A := by
  letI : e.inverse.IsDenseSubsite K J := by
    rw [← hJ]
    change e.symm.functor.IsDenseSubsite K (e.symm.inverse.inducedTopology K)
    infer_instance
  exact (e.sheafCongr J K A).inverse

/-- A point of the topos of sheaves on `D` is a point of the topos of sheaves on `C`, for an
equivalence `C ≌ D` carrying one topology to the other. -/
noncomputable def pointOfToposAlongEquivalence {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (e : C ≌ D) (K : GrothendieckTopology D) (J : GrothendieckTopology C)
    (hJ : e.functor.inducedTopology K = J) (q : PointOfTopos.{w, v', u'} K) :
    PointOfTopos.{w, v, u} J := by
  letI : e.inverse.IsDenseSubsite K J := by
    rw [← hJ]
    change e.symm.functor.IsDenseSubsite K (e.symm.inverse.inducedTopology K)
    infer_instance
  let E := e.sheafCongr J K (Type w)
  let m : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w)) :=
    { pushforward := E.inverse
      inverseImage := E.functor
      adj := E.toAdjunction
      preservesFiniteLimits := by
        let : E.functor.IsEquivalence := E.isEquivalence_functor
        exact ⟨fun _ _ _ => inferInstance⟩ }
  exact m.comp q

/-- The inverse image of the transported point, read through restriction of sheaves, is the
inverse image of the original point. -/
noncomputable def restrictAlongEquivalence_pointIso {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (e : C ≌ D) (K : GrothendieckTopology D) (J : GrothendieckTopology C)
    (hJ : e.functor.inducedTopology K = J) (q : PointOfTopos.{w, v', u'} K) :
    restrictAlongEquivalence e K J hJ (Type w) ⋙
      (pointOfToposAlongEquivalence e K J hJ q).inverseImage ≅ q.inverseImage := by
  letI : e.inverse.IsDenseSubsite K J := by
    rw [← hJ]
    change e.symm.functor.IsDenseSubsite K (e.symm.inverse.inducedTopology K)
    infer_instance
  exact Functor.isoWhiskerRight (e.sheafCongr J K (Type w)).counitIso q.inverseImage

/-- An object of the site together with an element of the fibre of a point over it: the
category of elements of a point's fibre functor is cofiltered, hence nonempty. -/
noncomputable def someSitePointElement {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J) :
    Σ X : C, Φ.fiber.obj X :=
  letI := Φ.isCofiltered
  let e : Φ.fiber.Elements := (IsCofiltered.nonempty (C := Φ.fiber.Elements)).some
  ⟨e.1, e.2⟩

end CategoryTheory

namespace AlgebraicGeometry

/-! ### Enlarging a geometric point of a scheme -/

/-- A geometric point of a scheme contained in a big fppf site is dominated by one whose
spectrum is again an object of that site: the algebraic closure of the residue field at the
image point is no larger than the bound the site's cutoff is closed under. -/
theorem exists_bounded_geometricPoint_extension (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (s : GeometricPoint X) :
    ∃ t : GeometricPoint X, B.Contains t.source ∧ ∃ f : s.source ⟶ t.source,
      f ≫ t.hom = s.hom := by
  obtain ⟨⟨x, a⟩, ha⟩ := (X.SpecToEquivOfField s.residueField).symm.surjective s.hom
  let K := AlgebraicClosure (X.residueField x)
  let : Algebra (X.residueField x) s.residueField := a.hom.toAlgebra
  let φ : K →ₐ[X.residueField x] s.residueField := IsAlgClosed.lift
  let t : GeometricPoint X :=
    { residueField := K
      hom := Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
        X.fromSpecResidueField x }
  have hK : Cardinal.mk K ≤ X.size ^ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max (X.residueField x) K).trans <|
      (max_le (Space.residueField_size_le X x) (Scheme.aleph0_le_size X)).trans
        (Cardinal.self_le_power _ Cardinal.one_le_aleph0)
  refine ⟨t, Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (.of K) hX hK, Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x) = s.hom
  rw [← Category.assoc, ← Spec.map_comp]
  have hφ : CommRingCat.ofHom (algebraMap (X.residueField x) K) ≫
      CommRingCat.ofHom φ.toRingHom = a := by
    ext z
    exact φ.commutes z
  rwa [hφ]

/-- Composing with a field extension is a bijection from the sections of an étale morphism
over a geometric point to the sections over its restriction: an étale scheme over an
algebraically closed field is a disjoint union of copies of that field's spectrum, so a
field-valued point of it factors through a section. -/
theorem geometric_lift_bijective_of_extension {k L : Type u} [Field k] [IsAlgClosed k]
    [Field L] {X V : Scheme.{u}} (v : V ⟶ X) [Etale v] (s : Spec (.of k) ⟶ X)
    (f : Spec (.of L) ⟶ Spec (.of k)) :
    Function.Bijective (fun p : {p : Spec (.of k) ⟶ V // p ≫ v = s} =>
      (⟨f ≫ p.1, by rw [Category.assoc, p.2]⟩ :
        {q : Spec (.of L) ⟶ V // q ≫ v = f ≫ s})) := by
  have : Surjective f := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi f := Flat.epi_of_flat_of_surjective f
  constructor
  · exact fun p q h => Subtype.ext ((cancel_epi f).mp (congrArg Subtype.val h))
  · intro q
    let g : pullback v s ⟶ Spec (.of k) := pullback.snd v s
    let q' : Spec (.of L) ⟶ pullback v s := pullback.lift q.1 f q.2
    obtain ⟨l, hl, hq⟩ := etale_field_map_factors k g inferInstance L q'
    refine ⟨⟨l ≫ pullback.fst v s, ?_⟩, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hl, Category.id_comp]
    · apply Subtype.ext
      change f ≫ (l ≫ pullback.fst v s) = q.1
      calc
        _ = ((q' ≫ g) ≫ l) ≫ pullback.fst v s := by
          rw [show q' ≫ g = f from pullback.lift_snd _ _ _]
          exact (Category.assoc _ _ _).symm
        _ = q' ≫ pullback.fst v s := congrArg (· ≫ pullback.fst v s) hq.symm
        _ = q.1 := pullback.lift_fst _ _ _

/-- A morphism of geometric points of a scheme over the same morphism to the scheme induces an
isomorphism of their fibre functors on the small étale site: restriction along the field
extension is bijective on lifts through each étale object. -/
noncomputable def geometricPointFiberIsoOfExtension (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (s t : GeometricPoint X) (f : s.source ⟶ t.source)
    (hf : f ≫ t.hom = s.hom) :
    geometricPointFiber B X hX t ≅ geometricPointFiber B X hX s := by
  let α : geometricPointFiber B X hX t ⟶ geometricPointFiber B X hX s :=
    { app U := ↾(fun p => ⟨f ≫ p.1, by rw [Category.assoc, p.2, hf]⟩)
      naturality U V g := by
        apply ConcreteCategory.hom_ext
        intro p
        apply Subtype.ext
        change f ≫ (p.1 ≫ (SmallEtale.toScheme B X hX).map g) =
          (f ≫ p.1) ≫ (SmallEtale.toScheme B X hX).map g
        exact (Category.assoc _ _ _).symm }
  have hiso : ∀ U, IsIso (α.app U) := by
    intro U
    apply (isIso_iff_bijective _).2
    have : Etale (B.inclusion.map U.obj.hom) := U.property
    change Function.Bijective (fun p :
      {q : t.source ⟶ B.inclusion.obj U.obj.left // q ≫ B.inclusion.map U.obj.hom = t.hom} =>
      (⟨f ≫ p.1, _⟩ :
        {q : s.source ⟶ B.inclusion.obj U.obj.left //
          q ≫ B.inclusion.map U.obj.hom = s.hom}))
    have hb := geometric_lift_bijective_of_extension (B.inclusion.map U.obj.hom) t.hom f
    constructor
    · intro p q h
      apply hb.injective
      have hval := congrArg Subtype.val h
      exact Subtype.ext hval
    · intro p
      obtain ⟨q, hq⟩ := hb.surjective ⟨p.val, p.property.trans hf.symm⟩
      have hval := congrArg Subtype.val hq
      exact ⟨q, Subtype.ext hval⟩
  letI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The geometric point of `F` determined by a scheme chart `a : yoneda.obj U ⟶ F` and a
geometric point of the scheme underlying `U` whose spectrum lies in the site. -/
noncomputable def geometricPointOfSchemeAtlas (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ F)
    (s : {t : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj U) //
      B.Contains (Spec (.of t.residueField))}) : GeometricPoint B S hS F :=
  let f : B.obj s.2 ⟶ U.left := B.inclusion.preimage s.1.hom
  ⟨{ carrier := s.1.residueField
     field := inferInstance
     contained := s.2
     toBase := B.inclusion.map (f ≫ U.hom)
     value := a.app (Opposite.op (Over.mk (f ≫ U.hom)))
       (yonedaEquiv (yoneda.map (Over.homMk f))) }, s.1.isAlgClosed_residueField⟩

/-- The chart equivalence of Stacks 04M0, read as an isomorphism of functors into the big fppf
site over `S` rather than into presheaves: the equivalence identifies an étale chart of the
representing object with its image chart of `F` over `X`. -/
noncomputable def chartEquivalenceOverIso (X : SmallEtale B S hS F)
    (e : SmallEtale B S hS (yoneda.obj X.obj.left) ≌ Over X)
    (he : e.functor ⋙ Over.post (SmallEtale.toOver B S hS F ⋙ yoneda) =
      SmallEtale.inclusion B S hS (yoneda.obj X.obj.left) ⋙
        CostructuredArrow.toOver yoneda (yoneda.obj X.obj.left)) :
    e.functor ⋙ Over.post (SmallEtale.toOver B S hS F) ≅
      SmallEtale.inclusion B S hS (yoneda.obj X.obj.left) ⋙
        (yonedaCostructuredArrowOverEquiv X.obj.left).functor := by
  let Q := Over.post (X := X.obj.left) yoneda
  let I := SmallEtale.inclusion B S hS (yoneda.obj X.obj.left)
  let d := yonedaCostructuredArrowOverEquiv X.obj.left
  let ε : (I ⋙ d.functor) ⋙ Q ≅
      I ⋙ CostructuredArrow.toOver yoneda (yoneda.obj X.obj.left) :=
    NatIso.ofComponents (fun V => Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ V.obj.hom = yoneda.map (yonedaEquiv V.obj.hom)
      rw [Category.id_comp]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_yoneda_map])) (by
        intro V W f
        apply Over.OverMorphism.ext
        change yoneda.map f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ yoneda.map f.hom.left
        simp)
  exact ((Functor.whiskeringRight (SmallEtale B S hS (yoneda.obj X.obj.left)) _ _).obj
    Q).preimageIso (eqToIso he ≪≫ ε.symm)

/-- The fibre functor of the point of the site determined by a geometric point, localized at a
lift of that point into an étale chart `X`, is corepresented over the slice at `X` by the
lift: a lift of the geometric point into a chart over `X` is exactly a morphism over `X` out of
the point's site object. -/
noncomputable def geometricFiberOverIsoCoyoneda (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) (X : SmallEtale B S hS F)
    (z : (etaleSitePoint B S hS F x hF).fiber.obj X) :
    ((etaleSitePoint B S hS F x hF).over z).fiber ≅
      Over.post (SmallEtale.toOver B S hS F) ⋙
        coyoneda.obj (Opposite.op (Over.mk z.1)) := by
  let Φ := etaleSitePoint B S hS F x hF
  let T := SmallEtale.toOver B S hS F
  let eqv (V : Over X) : (Φ.over z).fiber.obj V ≃ (Over.mk z.1 ⟶ (Over.post T).obj V) :=
    { toFun p := Over.homMk p.1.1 (congrArg Subtype.val
        ((FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).mp p.2))
      invFun p := ⟨⟨p.left, by
        have hv := congrArg (fun α => α.app (Opposite.op x.val.siteObject) p.left)
          (CostructuredArrow.w V.hom.hom)
        change X.obj.hom.app _ (p.left ≫ T.map V.hom) =
          V.left.obj.hom.app _ p.left at hv
        rw [show p.left ≫ T.map V.hom = z.1 from p.w] at hv
        exact hv.symm.trans z.2⟩,
        (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).mpr (Subtype.ext p.w)⟩
      left_inv p := Subtype.ext rfl
      right_inv p := Over.OverMorphism.ext rfl }
  exact NatIso.ofComponents (fun V => Equiv.toIso (eqv V)) (by
    intro V W f
    apply ConcreteCategory.hom_ext
    intro p
    apply Over.OverMorphism.ext
    rfl)

/-- Every point of the small étale topos of `F` is, after localizing at a suitable étale chart
`X` of `F`, computed by the neighbourhood colimit of a geometric point of the scheme underlying
`X`.  This is the reduction of Stacks 04K6 to the scheme case, Stacks 04HU. -/
theorem exists_chart_geometric_stalk (hF : IsAlgebraicSpace B S hS F)
    (p : PointOfTopos.{u + 1} (SmallEtale.topology B S hS F)) :
    ∃ (X : SmallEtale B S hS F)
      (e : SmallEtale B S hS (yoneda.obj X.obj.left) ≌ Over X),
      (e.functor ⋙ Over.post (SmallEtale.toOver B S hS F ⋙ yoneda) =
        SmallEtale.inclusion B S hS (yoneda.obj X.obj.left) ⋙
          CostructuredArrow.toOver yoneda (yoneda.obj X.obj.left)) ∧
      ∃ s : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj X.obj.left),
      Nonempty (p.inverseImage ≅
        sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          ((representedSmallEtaleEquivalence B S hS X.obj.left).inverse ⋙
            e.functor ⋙ Over.forget X).op ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (Functor.Elements.π (geometricPointFiber (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj X.obj.left)
            X.obj.left.left.property s)).op ⋙ colim) := by
  obtain ⟨Φ, ⟨ι⟩⟩ := PointOfTopos.exists_sitePoint p
  obtain ⟨X, z⟩ := someSitePointElement Φ
  obtain ⟨e, he, _, hcanonical⟩ := smallEtaleEquivalenceOverChart B S hS F hF X
  let J := SmallEtale.topology B S hS F
  let K := SmallEtale.topology B S hS (yoneda.obj X.obj.left)
  let L := _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj X.obj.left) X.obj.left.left.property
  let d := representedSmallEtaleEquivalence B S hS X.obj.left
  have hd : d.symm.functor.inducedTopology K = L :=
    inducedTopology_symm_of_equivalence d L K
      (representedSmallEtaleEquivalence_topology B S hS X.obj.left)
  let q₀ := (Φ.over z).pointOfTopos
  let q₁ := pointOfToposAlongEquivalence e (J.over X) K he q₀
  let q₂ := pointOfToposAlongEquivalence d.symm K L hd q₁
  let R₀ := restrictAlongEquivalence e (J.over X) K he (Type (u + 1))
  let R₁ := restrictAlongEquivalence d.symm K L hd (Type (u + 1))
  obtain ⟨s, ⟨hs⟩⟩ := exists_geometricPoint_inverseImage_iso (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj X.obj.left) X.obj.left.left.property q₂
  refine ⟨X, e, hcanonical, s, ⟨?_⟩⟩
  let α : p.inverseImage ≅ J.overPullback (Type (u + 1)) X ⋙ q₀.inverseImage :=
    ι ≪≫ (Φ.sheafFiberOverIso z (Type (u + 1))).symm
  let β : R₀ ⋙ q₁.inverseImage ≅ q₀.inverseImage :=
    restrictAlongEquivalence_pointIso e (J.over X) K he q₀
  let γ : R₁ ⋙ q₂.inverseImage ≅ q₁.inverseImage :=
    restrictAlongEquivalence_pointIso d.symm K L hd q₁
  exact α ≪≫ Functor.isoWhiskerLeft (J.overPullback (Type (u + 1)) X)
    (β.symm ≪≫ Functor.isoWhiskerLeft R₀ (γ.symm ≪≫ Functor.isoWhiskerLeft R₁ hs))

/-- The lift into the chart `X` of a geometric point of the scheme underlying `X`, as a
morphism out of the site object of the geometric point of `F` it induces. -/
noncomputable def geometricPointChartLift (X : SmallEtale B S hS F)
    (t : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj X.obj.left))
    (ht : B.Contains t.source) :
    (geometricPointOfSchemeAtlas B S hS F X.obj.left X.obj.hom ⟨t, ht⟩).val.siteObject ⟶
      X.obj.left :=
  Over.homMk (B.inclusion.preimage (X := B.obj ht) (Y := X.obj.left.left) t.hom) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- At an étale object `V` of the scheme underlying the chart `X`, morphisms over `X` out of
the chart lift of a geometric point `t` into `V` are the lifts of `t` through `V`. -/
noncomputable def chartCoyonedaEquivGeometricPointFiber (X : SmallEtale B S hS F)
    (t : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj X.obj.left))
    (ht : B.Contains t.source)
    (V : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj X.obj.left) X.obj.left.left.property) :
    ((representedSmallEtaleEquivalence B S hS X.obj.left).inverse ⋙
      SmallEtale.inclusion B S hS (yoneda.obj X.obj.left) ⋙
      (yonedaCostructuredArrowOverEquiv X.obj.left).functor ⋙
      coyoneda.obj (Opposite.op (Over.mk (geometricPointChartLift B S hS F X t ht)))).obj V ≃
    (geometricPointFiber (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj X.obj.left) X.obj.left.left.property t).obj V := by
  let d := representedSmallEtaleEquivalence B S hS X.obj.left
  let I := SmallEtale.inclusion B S hS (yoneda.obj X.obj.left)
  let Y := yonedaCostructuredArrowOverEquiv X.obj.left
  have hV : (Y.functor.obj (I.obj (d.inverse.obj V))).hom =
      Over.homMk (U := Over.mk (V.obj.hom ≫ X.obj.left.hom)) (V := X.obj.left)
        V.obj.hom (by rfl) :=
    yonedaEquiv_yoneda_map _
  exact
    { toFun p := ⟨B.inclusion.map p.left.left, by
        have hp := congrArg (fun g => B.inclusion.map g.left) p.w
        rw [hV] at hp
        change B.inclusion.map (p.left.left ≫ V.obj.hom) =
          B.inclusion.map (B.inclusion.preimage (X := B.obj ht)
            (Y := X.obj.left.left) t.hom) at hp
        change B.inclusion.map p.left.left ≫ B.inclusion.map V.obj.hom = t.hom
        exact (B.inclusion.map_comp p.left.left V.obj.hom).symm.trans
          (hp.trans (B.inclusion.map_preimage
            (X := B.obj ht) (Y := X.obj.left.left) t.hom))⟩
      invFun p := Over.homMk
        (Over.homMk (ObjectProperty.homMk p.1) (by
          apply ObjectProperty.hom_ext
          change p.1 ≫ B.inclusion.map (V.obj.hom ≫ X.obj.left.hom) =
            B.inclusion.map (B.inclusion.preimage (X := B.obj ht)
              (Y := X.obj.left.left) t.hom ≫ X.obj.left.hom)
          calc
            _ = (p.1 ≫ B.inclusion.map V.obj.hom) ≫
                B.inclusion.map X.obj.left.hom :=
                  (congrArg (p.1 ≫ ·)
                    (B.inclusion.map_comp V.obj.hom X.obj.left.hom)).trans
                    (Category.assoc _ _ _).symm
            _ = t.hom ≫ B.inclusion.map X.obj.left.hom :=
              congrArg (· ≫ B.inclusion.map X.obj.left.hom)
                (p.2 : p.1 ≫ B.inclusion.map V.obj.hom = t.hom)
            _ = _ := by simp only [Functor.map_comp, B.inclusion.map_preimage])) (by
          rw [hV]
          apply Over.OverMorphism.ext
          apply ObjectProperty.hom_ext
          change p.1 ≫ B.inclusion.map V.obj.hom =
            B.inclusion.map (B.inclusion.preimage (X := B.obj ht)
              (Y := X.obj.left.left) t.hom)
          rw [B.inclusion.map_preimage]
          exact p.2)
      left_inv p := by
        apply Over.OverMorphism.ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        rfl
      right_inv p := Subtype.ext rfl }

/-- On the small étale site of the scheme underlying the chart `X`, the functor corepresented
over `X` by the chart lift of a geometric point `t` is the fibre functor of `t`. -/
noncomputable def chartCoyonedaIsoGeometricPointFiber (X : SmallEtale B S hS F)
    (t : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj X.obj.left))
    (ht : B.Contains t.source) :
    (representedSmallEtaleEquivalence B S hS X.obj.left).inverse ⋙
      SmallEtale.inclusion B S hS (yoneda.obj X.obj.left) ⋙
      (yonedaCostructuredArrowOverEquiv X.obj.left).functor ⋙
      coyoneda.obj (Opposite.op (Over.mk (geometricPointChartLift B S hS F X t ht))) ≅
    geometricPointFiber (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj X.obj.left) X.obj.left.left.property t :=
  NatIso.ofComponents
    (fun V => (chartCoyonedaEquivGeometricPointFiber B S hS F X t ht V).toIso) (by
      intro V W f
      apply ConcreteCategory.hom_ext
      intro p
      apply Subtype.ext
      rfl)

/-- A geometric point of the scheme underlying an étale chart `X` of `F`, with spectrum in the
site, comes from a geometric point of `F` together with a lift of it into `X`, in such a way
that the two fibre functors over `X` agree. -/
theorem exists_geometricPoint_chart_fiber_iso (hF : IsAlgebraicSpace B S hS F)
    (X : SmallEtale B S hS F)
    (e : SmallEtale B S hS (yoneda.obj X.obj.left) ≌ Over X)
    (he : e.functor ⋙ Over.post (SmallEtale.toOver B S hS F ⋙ yoneda) =
      SmallEtale.inclusion B S hS (yoneda.obj X.obj.left) ⋙
        CostructuredArrow.toOver yoneda (yoneda.obj X.obj.left))
    (t : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj X.obj.left))
    (ht : B.Contains t.source) :
    ∃ (x : GeometricPoint B S hS F) (z : (etaleSitePoint B S hS F x hF).fiber.obj X),
      Nonempty (((representedSmallEtaleEquivalence B S hS X.obj.left).inverse ⋙ e.functor) ⋙
        ((etaleSitePoint B S hS F x hF).over z).fiber ≅
        geometricPointFiber (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj X.obj.left) X.obj.left.left.property t) := by
  let x := geometricPointOfSchemeAtlas B S hS F X.obj.left X.obj.hom ⟨t, ht⟩
  let z : (etaleSitePoint B S hS F x hF).fiber.obj X :=
    ⟨geometricPointChartLift B S hS F X t ht, rfl⟩
  exact ⟨x, z, ⟨Functor.isoWhiskerLeft (representedSmallEtaleEquivalence B S hS X.obj.left).inverse
    (Functor.isoWhiskerLeft e.functor (geometricFiberOverIsoCoyoneda B S hS F hF x X z) ≪≫
      Functor.isoWhiskerRight (chartEquivalenceOverIso B S hS F X e he)
        (coyoneda.obj (Opposite.op (Over.mk (geometricPointChartLift B S hS F X t ht))))) ≪≫
    chartCoyonedaIsoGeometricPointFiber B S hS F X t ht⟩⟩

/-- **Stacks 04K6.** Every point of the small étale topos of an algebraic space is
represented, at the level of stalk functors, by a geometric point of the space. -/
@[stacks 04K6, sga "4 VIII 7.9" "essential surjectivity"]
theorem exists_geometricPoint_stalkFunctor_iso (hF : IsAlgebraicSpace B S hS F)
    (p : PointOfTopos.{u + 1} (SmallEtale.topology B S hS F)) :
    ∃ x : GeometricPoint B S hS F,
      Nonempty (p.inverseImage ≅
        sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙
          stalkSetFunctor x) := by
  obtain ⟨X, e, he, s, ⟨hs⟩⟩ := exists_chart_geometric_stalk B S hS F hF p
  obtain ⟨t, ht, f, hf⟩ :=
    exists_bounded_geometricPoint_extension B X.obj.left.left.property s
  obtain ⟨x, z, ⟨σ⟩⟩ := exists_geometricPoint_chart_fiber_iso B S hS F hF X e he t ht
  let Ψ := etaleSitePoint B S hS F x hF
  let d := representedSmallEtaleEquivalence B S hS X.obj.left
  let D := d.symm.trans e
  let A := Type (u + 1)
  let P := sheafToPresheaf (SmallEtale.topology B S hS F) A
  let R := (Functor.whiskeringLeft _ _ A).obj (Over.forget X).op
  let L := (Functor.whiskeringLeft _ _ A).obj (D.functor ⋙ Over.forget X).op
  let τ := geometricPointFiberIsoOfExtension (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj X.obj.left) X.obj.left.left.property s t f hf
  refine ⟨x, ⟨?_⟩⟩
  exact hs ≪≫ Functor.isoWhiskerLeft (P ⋙ L)
      (elementColimitIso τ.symm A ≪≫ elementColimitIso σ.symm A) ≪≫
    Functor.isoWhiskerLeft (P ⋙ R) (elementColimitEquivalence D (Ψ.over z).fiber A) ≪≫
    Functor.isoWhiskerLeft P
      (Ψ.presheafFiberOverIso z A ≪≫ etaleSitePointStalkIso B S hS F x hF)

end Space

end AlgebraicGeometry

end
