module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Comp

/-!
# Unramified and étale transformations are formally unramified

An unramified representable transformation of set-valued functors on the big fppf site over
a scheme has at most one lift in every affine square-zero infinitesimal lifting problem.
Consequently a formally unramified transformation stays formally unramified after
precomposition with an étale one.

## Main definitions

* `AlgebraicGeometry.Space.RepresentableSurjectiveEtaleSituation` packages the standing
  situation of a pair of composable transformations whose first member is representable,
  surjective and étale.

## Main results

* `AlgebraicGeometry.Space.exists_representing_scheme_lift_equiv` identifies a lifting
  problem for a representable transformation with a lifting problem for the scheme
  representing its base change along a point of the target.
* `AlgebraicGeometry.Space.formallyUnramified_of_unramified` gives formal unramifiedness of
  an unramified representable transformation.
* `AlgebraicGeometry.Space.formallyUnramified_comp_of_etale` gives formal unramifiedness of
  the composite of an étale transformation with a formally unramified one.

## Implementation notes

Representability is relative to the Yoneda embedding of the big fppf site over the base, and
`CategoryTheory.MorphismProperty.presheaf` incorporates representability and tests the
scheme-morphism property on every represented base change; the scheme-morphism property is
pulled back from schemes along `AlgebraicGeometry.BigFppfOver.toScheme`.

The representing object of a base change is taken in the big fppf slice over the base
scheme, and the pullback square specifies its maps to the functor and to the larger test
object. The lift correspondence is characterized by evaluation of the map to the functor, so
it is canonical. The affine and square-zero hypotheses of the source play no role in that
identification, which therefore holds for every morphism of test objects.

The standing situation of Tag 04CY also assumes representability and surjectivity of the
first transformation; neither is needed for the conclusion drawn here.

## References

* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Precomposition by the Yoneda image of a morphism evaluates a transformation from a
representable functor at that morphism. -/
private theorem yoneda_map_comp_eq_yonedaEquiv_symm.{v, w} {C : Type w} [Category.{v} C] {X Y : C}
    {F : Cᵒᵖ ⥤ Type v} (f : X ⟶ Y) (q : yoneda.obj Y ⟶ F) :
    yoneda.map f ≫ q = yonedaEquiv.symm (q.app (op X) f) :=
  yonedaEquiv.injective <| by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]

/-- A compatibility `a x = G.map i y` of sections becomes a commutative square of
transformations from representable functors. -/
private theorem yonedaEquiv_symm_comp_eq_of_app_eq.{v, w} {C : Type w} [Category.{v} C]
    {F G : Cᵒᵖ ⥤ Type v} (a : F ⟶ G) {T T' : C} (i : T ⟶ T') {x : F.obj (op T)}
    {y : G.obj (op T')} (h : a.app (op T) x = G.map i.op y) :
    yonedaEquiv.symm x ≫ a = yoneda.map i ≫ yonedaEquiv.symm y :=
  (yonedaEquiv_symm_naturality_right T a x).trans
    ((congrArg yonedaEquiv.symm h).trans (yonedaEquiv_symm_naturality_left i G y).symm)

/-- For a pullback of `a` along a point `y`, there is a section `t` over `T` of the projection to
`T'` lifting `x`, and the lifts of the square for `a` correspond to the sections through `t` of
the projection, by evaluation of the map to the functor. -/
private theorem exists_lift_equiv_of_isPullback
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    {T T' P : BigFppfOver B S hS} (i : T ⟶ T') (x : F.obj (op T)) (y : G.obj (op T'))
    (hxy : a.app (op T) x = G.map i.op y)
    {p : P ⟶ T'} {q : yoneda.obj P ⟶ F}
    (hP : IsPullback q (yoneda.map p) a (yonedaEquiv.symm y)) :
    ∃ (t : T ⟶ P), (t ≫ p = i) ∧ (q.app (op T) t = x) ∧
      ∃ e : {z : F.obj (op T') // IsLift a i x y z} ≃
        {s : T' ⟶ P // (s ≫ p = 𝟙 T') ∧ (i ≫ s = t)},
        ∀ s, (e.symm s).val = q.app (op T') s.val := by
  have hex {X : BigFppfOver B S hS} (v : X ⟶ T') (z : F.obj (op X))
      (h : a.app (op X) z = G.map v.op y) : ∃ s : X ⟶ P, s ≫ p = v ∧ q.app (op X) s = z := by
    let L := hP.lift (yonedaEquiv.symm z) (yoneda.map v) (yonedaEquiv_symm_comp_eq_of_app_eq a v h)
    have hL : yoneda.map (yoneda.preimage L) = L := yoneda.map_preimage L
    refine ⟨yoneda.preimage L, yoneda.map_injective ?_, yonedaEquiv.symm.injective ?_⟩
    · rw [yoneda.map_comp, hL]
      exact hP.lift_snd _ _ _
    · rw [← yoneda_map_comp_eq_yonedaEquiv_symm, hL]
      exact hP.lift_fst _ _ _
  have huniq {X : BigFppfOver B S hS} {s s' : X ⟶ P} (hp : s ≫ p = s' ≫ p)
      (hq : q.app (op X) s = q.app (op X) s') : s = s' := by
    apply yoneda.map_injective
    apply hP.hom_ext
    · rw [yoneda_map_comp_eq_yonedaEquiv_symm, yoneda_map_comp_eq_yonedaEquiv_symm, hq]
    · rw [← yoneda.map_comp, ← yoneda.map_comp, hp]
  obtain ⟨t, htp, hqx⟩ := hex i x hxy
  have hsec {z : F.obj (op T')} (h : a.app (op T') z = y) :
      ∃ s : T' ⟶ P, s ≫ p = 𝟙 T' ∧ q.app (op T') s = z := hex (𝟙 T') z (by simpa using h)
  choose sec hsp hleft using @hsec
  have hnat (s : T' ⟶ P) : q.app (op T) (i ≫ s) = F.map i.op (q.app (op T') s) :=
    ConcreteCategory.congr_hom (q.naturality i.op) s
  have hit {z} (h : IsLift a i x y z) : i ≫ sec h.2 = t :=
    huniq (by rw [Category.assoc, hsp h.2, Category.comp_id, htp])
      (by rw [hnat, hleft h.2, h.1, hqx])
  have hsnd (s : T' ⟶ P) (hs : s ≫ p = 𝟙 T') : a.app (op T') (q.app (op T') s) = y := by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality_right, ← yoneda_map_comp_eq_yonedaEquiv_symm,
      Category.assoc, hP.w, ← Category.assoc, ← yoneda.map_comp, hs, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hright (s : {s : T' ⟶ P // (s ≫ p = 𝟙 T') ∧ (i ≫ s = t)}) :
      sec (hsnd s.1 s.2.1) = s.1 := huniq ((hsp _).trans s.2.1.symm) (hleft _)
  exact ⟨t, htp, hqx, { toFun z := ⟨sec z.2.2, hsp z.2.2, hit z.2⟩
                        invFun s := ⟨q.app (op T') s.1, by rw [← hnat, s.2.2, hqx], hsnd s.1 s.2.1⟩
                        left_inv z := Subtype.ext (hleft z.2.2)
                        right_inv s := Subtype.ext (hright s) }, fun _ => rfl⟩

/-- The base change of a representable transformation by a point of its target is a scheme,
and lifts of a compatible square correspond to lifts to that scheme over the larger test
object. -/
public theorem exists_representing_scheme_lift_equiv
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a)
    (T T' : BigFppfOver B S hS)
    (i : T ⟶ T')
    (x : F.obj (op T)) (y : G.obj (op T'))
    (hxy : a.app (op T) x = G.map i.op y) :
    ∃ (P : BigFppfOver B S hS) (p : P ⟶ T')
      (q : yoneda.obj P ⟶ F),
      IsPullback q (yoneda.map p) a (yonedaEquiv.symm y) ∧
      ∃ (t : T ⟶ P),
        (t ≫ p = i) ∧ (q.app (op T) t = x) ∧
          ∃ e : {z : F.obj (op T') // IsLift a i x y z} ≃
            {s : T' ⟶ P // (s ≫ p = 𝟙 T') ∧ (i ≫ s = t)},
            ∀ s, (e.symm s).val = q.app (op T') s.val := by
  obtain ⟨P, p, q, hP⟩ := ha (yonedaEquiv.symm y)
  exact ⟨P, p, q, hP, exists_lift_equiv_of_isPullback a i x y hxy hP⟩

/-- The standing situation of composable transformations of presheaves on the
big fppf site over a scheme, with the first transformation representable,
surjective, and étale. -/
public structure RepresentableSurjectiveEtaleSituation where
  /-- A chosen big fppf site. -/
  B : BigFppfSite.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The base scheme belongs to the chosen site. -/
  hS : B.Contains S
  /-- The source presheaf. -/
  F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The intermediate presheaf. -/
  G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The target presheaf. -/
  H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The first transformation. -/
  a : F ⟶ G
  /-- The second transformation. -/
  b : G ⟶ H
  /-- The first transformation is representable. -/
  representable_a : yoneda.relativelyRepresentable a
  /-- Every represented base change of the first transformation is surjective. -/
  surjective_a :
    (MorphismProperty.inverseImage
      (@Surjective : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a
  /-- Every represented base change of the first transformation is étale. -/
  etale_a :
    (MorphismProperty.inverseImage
      (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a

/-- **Stacks Project, Tag 04AL.** An unramified representable transformation is
formally unramified. -/
@[stacks 04AL "unramified_implies_formally_unramified"]
public theorem formallyUnramified_of_unramified
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : (MorphismProperty.inverseImage
      (@Unramified.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    FormallyUnramified a := by
  intro T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂
  obtain ⟨P, p, q, hpb, t, htp, htx, e, he⟩ :=
    exists_representing_scheme_lift_equiv B S hS a ha.1 T T' i x y hxy
  have : Unramified ((BigFppfOver.toScheme B S hS).map p) :=
    ha.2 (g := yonedaEquiv.symm y) (fst := q) (snd := p) hpb
  let s₁ := e ⟨z₁, hz₁⟩
  let s₂ := e ⟨z₂, hz₂⟩
  suffices s₁ = s₂ from congrArg Subtype.val (e.injective this)
  apply Subtype.ext
  apply Functor.map_injective (F := BigFppfOver.toScheme B S hS)
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hi.1
  have : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map p) :=
    ((unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mp ‹_›).2
  apply _root_.AlgebraicGeometry.FormallyUnramified.hom_ext
    ((BigFppfOver.toScheme B S hS).map i) ⟨2, by simpa using hi.2⟩
    ((BigFppfOver.toScheme B S hS).map p)
  · simp only [← Functor.map_comp, s₁.property.2, s₂.property.2]
  · simp only [← Functor.map_comp, s₁.property.1, s₂.property.1]

/-- A formally unramified transformation remains formally unramified after
precomposition with an étale transformation. -/
@[stacks 04CY "compose_formally_unramified"]
public theorem formallyUnramified_comp_of_etale
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : (MorphismProperty.inverseImage (@Etale :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : FormallyUnramified b) :
    FormallyUnramified (a ≫ b) :=
  formallyUnramified_comp a b (formallyUnramified_of_unramified B S hS a
    (MorphismProperty.relative_monotone (F := CategoryTheory.yoneda)
      (MorphismProperty.monotone_inverseImage _
        (fun _ _ _ hf => @unramified_of_etale _ _ _ hf)) a ha)) hb

end AlgebraicGeometry.Space

end
