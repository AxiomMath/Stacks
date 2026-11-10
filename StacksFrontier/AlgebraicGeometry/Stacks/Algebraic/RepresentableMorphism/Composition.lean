module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of representable 1-morphisms of fibred categories

The composite of two representable 1-morphisms of categories fibred in groupoids over a base
category is again representable.

The proof is the one in the source. Fix a 1-morphism `H : 𝒞/U ⥤ 𝒵` over the base.
Representability of `G` gives an object `V` of `𝒞/U` representing the 2-fibre product
`(𝒞/U) ×_𝒵 𝒴`; representability of `F` applied to the resulting 1-morphism `𝒞/V ⥤ 𝒴` gives an
object `W` of `𝒞/V` representing `(𝒞/V) ×_𝒴 𝒳`. Composing the two comparisons identifies
`(𝒞/U) ×_𝒵 𝒳` with the slice of `𝒞/U` at the composite `W ⟶ V ⟶ U`, which is therefore a
representable category fibred in groupoids over `𝒞/U`.

## Main results

* `Stacks.RepresentableMorphism.isRepresentableMorphism_comp`: representability of 1-morphisms is
  stable under
  composition.

## Implementation notes

The statement is made over an arbitrary base category rather than only over the big fppf site
of a scheme: the composition argument uses neither the topology nor the base scheme. The
equations expressing that the functors lie over the base are explicit arguments because
`Stacks.RepresentableMorphism.IsRepresentableMorphism` takes the underlying functors rather than
  bundled
1-morphisms.

## References

* [Stacks Project, Tag 02ZS](https://stacks.math.columbia.edu/tag/02ZS)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] TwoFibreProductOver.fst TwoFibreProductOver.snd
  TwoFibreProductOver.structureFunctor

namespace Stacks.RepresentableMorphism

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
  {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  {𝒵 : Type u₄} [Category.{v₄} 𝒵]

private def homOfLifts
    {C A B D : Type*} [Category C] [Category A] [Category B] [Category D]
    {pA : A ⥤ C} {pB : B ⥤ C} {pD : D ⥤ C} {F : A ⥤ D} {G : B ⥤ D}
    {x y : TwoFibreProductOver pA pB pD F G}
    {U V : C} (f : U ⟶ V) (a : x.x ⟶ y.x) (b : x.y ⟶ y.y)
    [pA.IsHomLift f a] [pB.IsHomLift f b]
    (w : F.map a ≫ y.iso.hom = x.iso.hom ≫ G.map b) : x ⟶ y :=
  TwoFibreProductOver.Hom.mk' a b (by
    rw [IsHomLift.fac' pA f a, IsHomLift.fac' pB f b]
    simp) w

private lemma homOfLifts_isHomLift
    {C A B D : Type*} [Category C] [Category A] [Category B] [Category D]
    {pA : A ⥤ C} {pB : B ⥤ C} {pD : D ⥤ C} {F : A ⥤ D} {G : B ⥤ D}
    {x y : TwoFibreProductOver pA pB pD F G}
    {U V : C} (f : U ⟶ V) (a : x.x ⟶ y.x) (b : x.y ⟶ y.y)
    [pA.IsHomLift f a] [pB.IsHomLift f b]
    (w : F.map a ≫ y.iso.hom = x.iso.hom ≫ G.map b) :
    (TwoFibreProductOver.structureFunctor pA pB pD F G).IsHomLift f
      (homOfLifts f a b w) := by
  apply IsHomLift.of_fac' _ f _
    (x.hx.symm.trans (IsHomLift.domain_eq pA f a))
    (y.hx.symm.trans (IsHomLift.codomain_eq pA f a))
  change eqToHom _ ≫ pA.map a ≫ eqToHom _ = _
  rw [IsHomLift.fac' pA f a]
  simp

private lemma cartesianFunctor_of_comp_eq
    {C A B : Type*} [Category C] [Category A] [Category B]
    (p : A ⥤ C) (q : B ⥤ C) (hq : q.IsFiberedInGroupoids)
    (F : A ⥤ B) (hF : F ⋙ q = p) : IsCartesianFunctorStrict p q F := by
  refine ⟨hF, ?_⟩
  intro _ _ _ _ f φ _ _
  have := Functor.isHomLift_map_of_comp_eq hF f φ
  have := hq.isStronglyCartesian_homLift f (F.map φ)
  infer_instance

private lemma isFibredEquivalence_of_isEquivalence
    {C A B : Type*} [Category C] [Category A] [Category B]
    (p : A ⥤ C) (q : B ⥤ C) (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (F : A ⥤ B) (hF : F ⋙ q = p)
    (he : F.IsEquivalence) : IsFibredEquivalence p q F := by
  obtain ⟨G, hG, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over p q hp hq F hF he
  refine ⟨cartesianFunctor_of_comp_eq p q hq F hF, G,
    cartesianFunctor_of_comp_eq q p hp G hG, ⟨ε, ?_⟩, ⟨η, ?_⟩⟩
  · intro x
    have := hε x
    exact ⟨_, by simpa using IsHomLift.fac' q (𝟙 (q.obj x)) (ε.hom.app x)⟩
  · intro x
    have := hη x
    exact ⟨_, by simpa using IsHomLift.fac' p (𝟙 (p.obj x)) (η.hom.app x)⟩

-- A morphism lying over `f` for `p` lies over `q(f)` for `p ⋙ q`:
-- `CategoryTheory.Functor.isHomLift_comp_functor`, public in
-- `StacksFrontier.CategoryTheory.FiberedCategory.HomLift` (closure 1; already in this file's
-- closure). A `private` re-declaration under the same bare name, taking `p` explicitly
-- where the canonical leaves it implicit, stood here.

/-- Replacing the intermediate pullback by an equivalent category and composing the
comparison isomorphisms gives an equivalence with the pullback of the composite. -/
private lemma exists_pullbackComparison
    {C A X Y Z D : Type*}
    [Category C] [Category A] [Category X] [Category Y] [Category Z] [Category D]
    (a : A ⥤ C) (p : X ⥤ C) (q : Y ⥤ C) (r : Z ⥤ C)
    (H : A ⥤ Z) (F : X ⥤ Y) (G : Y ⥤ Z) (hF : F ⋙ q = p) (hG : G ⋙ r = q)
    (d : D ⥤ C) (L : D ⥤ TwoFibreProductOver a q r H G)
    (hL : L ⋙ TwoFibreProductOver.structureFunctor a q r H G = d)
    [L.IsEquivalence]
    (hsurj : ∀ z : TwoFibreProductOver a q r H G,
      ∃ (w : D) (e : L.obj w ≅ z),
        (TwoFibreProductOver.structureFunctor a q r H G).IsHomLift (𝟙 z.base) e.hom) :
    ∃ K : TwoFibreProductOver d p q (L ⋙ TwoFibreProductOver.snd a q r H G) F ⥤
        TwoFibreProductOver a p r H (F ⋙ G),
      K.IsEquivalence ∧
        K ⋙ TwoFibreProductOver.fst a p r H (F ⋙ G) =
          TwoFibreProductOver.fst d p q (L ⋙ TwoFibreProductOver.snd a q r H G) F ⋙
            L ⋙ TwoFibreProductOver.fst a q r H G := by
  let P := TwoFibreProductOver a q r H G
  let Q := TwoFibreProductOver d p q (L ⋙ TwoFibreProductOver.snd a q r H G) F
  let R := TwoFibreProductOver a p r H (F ⋙ G)
  let ps := TwoFibreProductOver.structureFunctor a q r H G
  have hbase (x : Q) : (L.obj x.x).base = x.base :=
    (Functor.congr_obj hL x.x).trans x.hx
  have ha {x y : Q} (f : x ⟶ y) : a.IsHomLift f.hbase (L.map f.a).a := by
    have := f.ha
    have hh := Functor.isHomLift_map_of_comp_eq hL f.hbase f.a
    exact Functor.isHomLift_map_of_comp_eq
      (TwoFibreProductOver.fst_comp_eq (p𝒳 := a) (p𝒴 := q) (p𝒮 := r))
      f.hbase (L.map f.a)
  let K : Q ⥤ R :=
    { obj x :=
        { base := x.base
          x := (L.obj x.x).x
          y := x.y
          hx := (L.obj x.x).hx.trans (hbase x)
          hy := x.hy
          iso := (L.obj x.x).iso ≪≫ G.mapIso x.iso
          vertical := by
            have hv : r.IsHomLift (𝟙 x.base) (L.obj x.x).iso.hom := by
              rw [← hbase x]
              exact (L.obj x.x).vertical
            have := x.vertical
            have := Functor.isHomLift_map_of_comp_eq hG (𝟙 x.base) x.iso.hom
            exact IsHomLift.comp_lift_id_right r (𝟙 x.base)
              (L.obj x.x).iso.hom (G.map x.iso.hom) }
      map {x y} f :=
        { hbase := f.hbase
          a := (L.map f.a).a
          b := f.b
          ha := ha f
          hb := f.hb
          w := by
            change H.map (L.map f.a).a ≫ ((L.obj y.x).iso.hom ≫ G.map y.iso.hom) =
              ((L.obj x.x).iso.hom ≫ G.map x.iso.hom) ≫ G.map (F.map f.b)
            rw [← Category.assoc, (L.map f.a).w, Category.assoc, ← G.map_comp,
              show (L.map f.a).b ≫ y.iso.hom = x.iso.hom ≫ F.map f.b from f.w]
            simp }
      map_id x := by
        apply TwoFibreProductOver.Hom.ext'
        · change (L.map (𝟙 x.x)).a = 𝟙 _
          rw [L.map_id]
          rfl
        · rfl
      map_comp f g := by
        apply TwoFibreProductOver.Hom.ext'
        · change (L.map (f.a ≫ g.a)).a = (L.map f.a).a ≫ (L.map g.a).a
          rw [L.map_comp]
          rfl
        · rfl }
  refine ⟨K, ?_, rfl⟩
  have faithful : K.Faithful := by
    constructor
    intro x y f g h
    have hb : f.b = g.b := congrArg (fun k : K.obj x ⟶ K.obj y => k.b) h
    have hax : (L.map f.a).a = (L.map g.a).a :=
      congrArg (fun k : K.obj x ⟶ K.obj y => k.a) h
    have hay : (L.map f.a).b = (L.map g.a).b :=
      (cancel_mono y.iso.hom).1 (f.w.trans (by rw [hb]; exact g.w.symm))
    exact TwoFibreProductOver.Hom.ext' (L.map_injective
      (TwoFibreProductOver.Hom.ext' hax hay)) hb
  have full : K.Full := by
    constructor
    intro x y f
    have := f.ha
    have := f.hb
    have := x.vertical
    have := y.vertical
    have := Functor.isHomLift_map_of_comp_eq hF f.hbase f.b
    have hv : q.IsHomLift f.hbase (x.iso.hom ≫ F.map f.b ≫ y.iso.inv) := by
      have := IsHomLift.comp_lift_id_right q f.hbase (F.map f.b) y.iso.inv
      exact IsHomLift.comp_lift_id_left q f.hbase _ x.iso.hom
    let m : L.obj x.x ⟶ L.obj y.x := homOfLifts f.hbase f.a
      (x.iso.hom ≫ F.map f.b ≫ y.iso.inv) (by
        apply (cancel_mono (G.map y.iso.hom)).1
        simpa [K, Functor.map_comp, Category.assoc] using f.w)
    have hm : ps.IsHomLift f.hbase m := homOfLifts_isHomLift _ _ _ _
    let b := L.preimage m
    have hb : d.IsHomLift f.hbase b := by
      apply (Functor.isHomLift_map_iff_of_comp_eq d ps L hL f.hbase b).1
      simpa [b] using hm
    refine ⟨homOfLifts f.hbase b f.b ?_, ?_⟩
    · have hh := congrArg TwoFibreProductOver.Hom.b (L.map_preimage m)
      change (L.map b).b ≫ y.iso.hom = x.iso.hom ≫ F.map f.b
      rw [hh]
      simp [m, homOfLifts]
    · apply TwoFibreProductOver.Hom.ext'
      · change (L.map b).a = f.a
        rw [show L.map b = m from L.map_preimage m]
        rfl
      · rfl
  have essSurj : K.EssSurj := by
    constructor
    intro z
    let z' : P :=
      { base := z.base
        x := z.x
        y := F.obj z.y
        hx := z.hx
        hy := (Functor.congr_obj hF z.y).trans z.hy
        iso := z.iso
        vertical := z.vertical }
    obtain ⟨w, e, he⟩ := hsurj z'
    have hea : a.IsHomLift (𝟙 z.base) e.hom.a :=
      Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq _ e.hom
    have heb : q.IsHomLift (𝟙 z.base) e.hom.b :=
      Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.snd_comp_eq _ e.hom
    let y : Q :=
      { base := z.base
        x := w
        y := z.y
        hx := (Functor.congr_obj hL w).symm.trans
          (IsHomLift.domain_eq ps (𝟙 z.base) e.hom)
        hy := z.hy
        iso := (TwoFibreProductOver.snd a q r H G).mapIso e
        vertical := heb }
    have hid : p.IsHomLift (𝟙 z.base) (𝟙 z.y) := IsHomLift.id z.hy
    let m : K.obj y ⟶ z := homOfLifts (𝟙 z.base) e.hom.a (𝟙 z.y) (by
      simpa [K, y, z'] using e.hom.w)
    have : IsIso m := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m
      (by change IsIso e.hom.a; exact inferInstanceAs (IsIso
        ((TwoFibreProductOver.fst a q r H G).map e.hom)))
      (by change IsIso (𝟙 z.y); infer_instance)
    exact ⟨y, ⟨asIso m⟩⟩
  exact { faithful, full, essSurj }

/-- The inverse of a fibred equivalence is an equivalence of categories. -/
private lemma exists_inverse_isEquivalence
    {C A B : Type*} [Category C] [Category A] [Category B]
    {p : A ⥤ C} {q : B ⥤ C} {E : A ⥤ B} (hE : IsFibredEquivalence p q E) :
    ∃ J : B ⥤ A, IsCartesianFunctorStrict q p J ∧ J.IsEquivalence ∧
      ∃ ε : E ⋙ J ≅ 𝟭 A, NatTrans.IsOver p ε.hom := by
  obtain ⟨J, hJ, ⟨η, -⟩, ⟨ε, hε⟩⟩ := hE.exists_inverse
  exact ⟨J, hJ, (CategoryTheory.Equivalence.mk J E η.symm ε).isEquivalence_functor, ε,
    hε⟩

/-- **Stacks 02ZS.** A composite of representable 1-morphisms of categories fibred in
groupoids over a base category is representable. -/
@[stacks 02ZS]
public lemma isRepresentableMorphism_comp
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (r : 𝒵 ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ 𝒴) (G : 𝒴 ⥤ 𝒵)
    (hF : F ⋙ q = p) (hG : G ⋙ r = q)
    (hrepF : Stacks.RepresentableMorphism.IsRepresentableMorphism p q F)
    (hrepG : Stacks.RepresentableMorphism.IsRepresentableMorphism q r G) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism p r (F ⋙ G) := by
  have : q.IsFiberedInGroupoids := hq
  intro U H hH
  obtain ⟨V, E, hE⟩ := hrepG U H hH
  obtain ⟨J, hJ, _, ε, hε⟩ := exists_inverse_isEquivalence hE
  let L := Over.iteratedSliceBackward V ⋙ J
  have : (Over.iteratedSliceBackward V).IsEquivalence :=
    (Over.iteratedSliceEquiv V).isEquivalence_inverse
  have : L.IsEquivalence := inferInstance
  have hLP : L ⋙ TwoFibreProductOver.fst (Over.forget U) q r H G =
      Over.map V.hom := by
    dsimp [L]
    rw [Functor.assoc, hJ.comm]
    rfl
  have hL : L ⋙ TwoFibreProductOver.structureFunctor (Over.forget U) q r H G =
      Over.forget V.left := by
    rw [← TwoFibreProductOver.fst_comp_eq, ← Functor.assoc, hLP]
    rfl
  let T := L ⋙ TwoFibreProductOver.snd (Over.forget U) q r H G
  have hT : T ⋙ q = Over.forget V.left := by
    simpa only [T, Functor.assoc, TwoFibreProductOver.snd_comp_eq] using hL
  obtain ⟨W, E', hE'⟩ := hrepF V.left T hT
  obtain ⟨J', hJ', _, -⟩ := exists_inverse_isEquivalence hE'
  have hsurj (z : TwoFibreProductOver (Over.forget U) q r H G) :
      ∃ (w : Over V.left) (e : L.obj w ≅ z),
        (TwoFibreProductOver.structureFunctor (Over.forget U) q r H G).IsHomLift
          (𝟙 z.base) e.hom := by
    let w := (Over.iteratedSliceForward V).obj (E.obj z)
    let u := (Over.iteratedSliceEquiv V).unitIso.symm.app (E.obj z)
    let e : L.obj w ≅ z := J.mapIso u ≪≫ ε.app z
    refine ⟨w, e, ?_⟩
    let ps := TwoFibreProductOver.structureFunctor (Over.forget U) q r H G
    have hJbase : J ⋙ ps = Over.forget V ⋙ Over.forget U := by
      dsimp [ps]
      rw [← TwoFibreProductOver.fst_comp_eq, ← Functor.assoc, hJ.comm]
    have hεlift : ps.IsHomLift (𝟙 z.base) (ε.hom.app z) := by
      obtain ⟨hb, he⟩ := hε z
      have hh : (TwoFibreProductOver.fst (Over.forget U) q r H G).IsHomLift
          (𝟙 z.x) (ε.hom.app z) :=
        IsHomLift.of_fac' _ _ _ hb rfl (by simpa using he)
      have hh' := Functor.isHomLift_comp_functor (Over.forget U) _ _ hh
      rw [TwoFibreProductOver.fst_comp_eq] at hh'
      change ps.IsHomLift (𝟙 z.x.left) (ε.hom.app z) at hh'
      rwa [show z.x.left = z.base from z.hx] at hh'
    have hunit : (Over.forget V ⋙ Over.forget U).IsHomLift
        (𝟙 ((E.obj z).left.left))
        u.hom := by
      apply IsHomLift.of_fac' _ _ _ rfl rfl
      simp only [Over.iteratedSliceEquiv, NatIso.ofComponents,
        Over.isoMk, CostructuredArrow.isoMk, Comma.isoMk,
        Over.forget, Comma.fst, Functor.comp]
      change 𝟙 ((E.obj z).left.left) =
        eqToHom (rfl : (E.obj z).left.left = (E.obj z).left.left) ≫
          𝟙 ((E.obj z).left.left) ≫ 𝟙 ((E.obj z).left.left)
      simp
    have hunit' := Functor.isHomLift_map_of_comp_eq hJbase
      (𝟙 ((E.obj z).left.left))
      u.hom
    have hb : (E.obj z).left.left = z.base := by
      have hh := Functor.congr_obj hE.isCartesianFunctor.comm z
      exact (congrArg (fun t : Over U => t.left) hh).trans z.hx
    rw [hb] at hunit'
    exact IsHomLift.comp_lift_id_right ps (𝟙 z.base)
      (J.map u.hom) (ε.hom.app z)
  obtain ⟨K, hK, hKP⟩ := exists_pullbackComparison (Over.forget U) p q r H F G hF hG
    (Over.forget V.left) L hL hsurj
  have : K.IsEquivalence := hK
  let M : Over U := Over.mk (W.hom ≫ V.hom)
  have : (Over.iteratedSliceForward M).IsEquivalence :=
    (Over.iteratedSliceEquiv M).isEquivalence_functor
  have : (Over.iteratedSliceBackward W).IsEquivalence :=
    (Over.iteratedSliceEquiv W).isEquivalence_inverse
  let B : Over M ⥤ TwoFibreProductOver (Over.forget U) p r H (F ⋙ G) :=
    Over.iteratedSliceForward M ⋙ Over.iteratedSliceBackward W ⋙ J' ⋙ K
  have : B.IsEquivalence := inferInstance
  have hB : B ⋙ TwoFibreProductOver.fst (Over.forget U) p r H (F ⋙ G) =
      Over.forget M := by
    dsimp [B]
    simp only [Functor.assoc, hKP]
    rw [← Functor.assoc J', hJ'.comm, hLP, ← Functor.assoc (Over.iteratedSliceBackward W),
      Over.iteratedSliceBackward_forget, ← Over.mapComp_eq]
    refine Functor.ext_of_iso
      (Functor.isoWhiskerRight (Over.iteratedSliceEquiv M).unitIso.symm
        (Over.forget M)) ?_ ?_
    · intro z
      change Over.mk (z.hom.left ≫ M.hom) = z.left
      rw [Over.w z.hom]
      rfl
    · intro z
      apply Over.OverMorphism.ext
      simp [Over.iteratedSliceEquiv, Over.eqToHom_left]
      rfl
  have hR := TwoFibreProductOver.fst_isFiberedInGroupoids U p r (F ⋙ G) H hp hr
    (by rw [Functor.assoc, hG, hF]) hH
  have hB' := isFibredEquivalence_of_isEquivalence (Over.forget M) _
    (Functor.IsFiberedInGroupoids.over_forget M) hR B hB inferInstance
  obtain ⟨A, hA, ⟨ηA, hηA⟩, ⟨εA, hεA⟩⟩ := hB'.exists_inverse
  exact ⟨M, A, hA, B, hB'.isCartesianFunctor, ⟨εA, hεA⟩, ⟨ηA, hηA⟩⟩

end Stacks.RepresentableMorphism
