module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces.Basic

/-!
# Base change of groupoids in algebraic spaces: the pointwise construction

The ingredients of the base change of a groupoid in algebraic spaces along a morphism of bases:
the base change `AlgebraicGeometry.Space.pullbackMapOver` of a morphism over the base, the
pointwise base change `AlgebraicGeometry.Space.FiberBaseChange.pointwise` of a pointwise groupoid,
the description `AlgebraicGeometry.Space.fiberProductAtEquiv` of the sections of a fibre product,
the identity law from the composition law (`AlgebraicGeometry.Space.mapIdentityOfMapComp`), the
induced map on composable pairs, and the transport
`AlgebraicGeometry.Space.transportPointwise` of a pointwise groupoid along bijections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### Base change -/


/-- Base change of a morphism over the base: a morphism `g` of algebraic spaces over `B`
induces a morphism between the fibre products of the two structure morphisms with `f`. -/
noncomputable def pullbackMapOver
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' U R : AlgebraicSpaces C S hS}
    (f : B' ⟶ B) (qU : U ⟶ B) (qR : R ⟶ B)
    (g : R ⟶ U) (hg : g ≫ qU = qR) :
    AlgebraicSpaces.fiberProduct C S hS f qR ⟶
      AlgebraicSpaces.fiberProduct C S hS f qU := by
  refine (AlgebraicSpaces.isPullback_fiberProduct C S hS f qU).lift
    (ObjectProperty.homMk (pullback.fst f.hom qR.hom) :
      AlgebraicSpaces.fiberProduct C S hS f qR ⟶ B')
    ((ObjectProperty.homMk (pullback.snd f.hom qR.hom) :
      AlgebraicSpaces.fiberProduct C S hS f qR ⟶ R) ≫ g) ?_
  calc
    (ObjectProperty.homMk (pullback.fst f.hom qR.hom) :
        AlgebraicSpaces.fiberProduct C S hS f qR ⟶ B') ≫ f =
        (ObjectProperty.homMk (pullback.snd f.hom qR.hom) :
          AlgebraicSpaces.fiberProduct C S hS f qR ⟶ R) ≫ qR :=
      (AlgebraicSpaces.isPullback_fiberProduct C S hS f qR).w
    _ = ((ObjectProperty.homMk (pullback.snd f.hom qR.hom) :
          AlgebraicSpaces.fiberProduct C S hS f qR ⟶ R) ≫ g) ≫ qU := by
      rw [← hg]
      simp [Category.assoc]

/-- The base change of a morphism over the base commutes with the projections to the new
base. -/
theorem pullbackMapOver_fst
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' U R : AlgebraicSpaces C S hS}
    (f : B' ⟶ B) (qU : U ⟶ B) (qR : R ⟶ B)
    (g : R ⟶ U) (hg : g ≫ qU = qR) :
    pullbackMapOver f qU qR g hg ≫
      (ObjectProperty.homMk (pullback.fst f.hom qU.hom) :
        AlgebraicSpaces.fiberProduct C S hS f qU ⟶ B') =
      (ObjectProperty.homMk (pullback.fst f.hom qR.hom) :
        AlgebraicSpaces.fiberProduct C S hS f qR ⟶ B') :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS f qU).lift_fst _ _ _

/-- The base change of a morphism over the base covers that morphism. -/
theorem pullbackMapOver_snd
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' U R : AlgebraicSpaces C S hS}
    (f : B' ⟶ B) (qU : U ⟶ B) (qR : R ⟶ B)
    (g : R ⟶ U) (hg : g ≫ qU = qR) :
    pullbackMapOver f qU qR g hg ≫
      (ObjectProperty.homMk (pullback.snd f.hom qU.hom) :
        AlgebraicSpaces.fiberProduct C S hS f qU ⟶ U) =
      (ObjectProperty.homMk (pullback.snd f.hom qR.hom) :
        AlgebraicSpaces.fiberProduct C S hS f qR ⟶ R) ≫ g :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS f qU).lift_snd _ _ _

/-- **The base change of a morphism over the base, read on presheaves, composed with the first
projection.** `AlgebraicGeometry.Space.pullbackMapOver_fst` with both sides mapped into the
category of presheaves, where the chosen fibre product of algebraic spaces is the presheaf
pullback. -/
theorem pullbackMapOver_hom_comp_fst
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' U R : AlgebraicSpaces C S hS}
    (f : B' ⟶ B) (qU : U ⟶ B) (qR : R ⟶ B)
    (g : R ⟶ U) (hg : g ≫ qU = qR) :
    (pullbackMapOver f qU qR g hg).hom ≫ pullback.fst f.hom qU.hom =
      pullback.fst f.hom qR.hom :=
  congrArg (fun k => k.hom) (pullbackMapOver_fst f qU qR g hg)

/-- **The base change of a morphism over the base, read on presheaves, composed with the second
projection.** `AlgebraicGeometry.Space.pullbackMapOver_snd` with both sides mapped into the
category of presheaves. -/
theorem pullbackMapOver_hom_comp_snd
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' U R : AlgebraicSpaces C S hS}
    (f : B' ⟶ B) (qU : U ⟶ B) (qR : R ⟶ B)
    (g : R ⟶ U) (hg : g ≫ qU = qR) :
    (pullbackMapOver f qU qR g hg).hom ≫ pullback.snd f.hom qU.hom =
      pullback.snd f.hom qR.hom ≫ g.hom :=
  congrArg (fun k => k.hom) (pullbackMapOver_snd f qU qR g hg)

/-- **Two constructions of the same base change agree.** A morphism of presheaves into the chosen
fibre product which has the same two components as
`AlgebraicGeometry.Space.pullbackMapOver` *is* that base change.

Base changes are built in this library in two ways: as
`AlgebraicGeometry.Space.pullbackMapOver`, from the cartesian square of
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`, and directly as a
`CategoryTheory.Limits.pullback.lift` out of the two chosen fibre products — the latter is how
`AlgebraicGeometry.Space.MorphismDescentSystem.mapAt` writes the base change of the morphism it
descends. This lemma identifies the two, so a property of morphisms proved for either form holds
of the other with no comparison isomorphism to transport along. -/
theorem pullbackMapOver_hom_eq
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' U R : AlgebraicSpaces C S hS}
    (f : B' ⟶ B) (qU : U ⟶ B) (qR : R ⟶ B)
    (g : R ⟶ U) (hg : g ≫ qU = qR)
    (m : pullback f.hom qR.hom ⟶ pullback f.hom qU.hom)
    (hfst : m ≫ pullback.fst f.hom qU.hom = pullback.fst f.hom qR.hom)
    (hsnd : m ≫ pullback.snd f.hom qU.hom = pullback.snd f.hom qR.hom ≫ g.hom) :
    m = (pullbackMapOver f qU qR g hg).hom :=
  pullback.hom_ext
    (hfst.trans (pullbackMapOver_hom_comp_fst f qU qR g hg).symm)
    (hsnd.trans (pullbackMapOver_hom_comp_snd f qU qR g hg).symm)

namespace FiberBaseChange

/-- The set of objects of a base-changed groupoid at a test object: pairs of a point of the
new base and a point of the old object set with the same image in the old base. -/
abbrev Obj {X U Z : Type u} (f : X → Z) (q : U → Z) :=
  {p : X × U // f p.1 = q p.2}

/-- The set of arrows of a base-changed groupoid at a test object: pairs of a point of the new
base and an arrow of the old groupoid with the same image in the old base. -/
abbrev Arr {X R Z : Type u} (f : X → Z) (r : R → Z) :=
  {p : X × R // f p.1 = r p.2}

/-- The source of a base-changed arrow: the source of its old arrow, over the same point of
the new base. -/
def src {X U R Z : Type u} {f : X → Z} {q : U → Z} {r : R → Z}
    (s : R → U) (hs : ∀ a, q (s a) = r a) (a : Arr f r) : Obj f q :=
  ⟨(a.1.1, s a.1.2), by rw [a.2, hs]⟩

/-- The target of a base-changed arrow: the target of its old arrow, over the same point of
the new base. -/
def tgt {X U R Z : Type u} {f : X → Z} {q : U → Z} {r : R → Z}
    (t : R → U) (ht : ∀ a, q (t a) = r a) (a : Arr f r) : Obj f q :=
  ⟨(a.1.1, t a.1.2), by rw [a.2, ht]⟩

/-- Composition of base-changed arrows: the old arrows compose, and the point of the new base
is the common one. -/
def comp {X U R Z : Type u} {f : X → Z} {q : U → Z} {r : R → Z}
    (s t : R → U) (c : {p : R × R // s p.1 = t p.2} → R)
    (hc : ∀ p, r (c p) = r p.1.1)
    (s' : Arr f r → Obj f q) (t' : Arr f r → Obj f q)
    (hsrc : ∀ a, (s' a).val.2 = s a.val.2)
    (htgt : ∀ a, (t' a).val.2 = t a.val.2)
    (p : {xy : Arr f r × Arr f r // s' xy.1 = t' xy.2}) : Arr f r := by
  let old : {p : R × R // s p.1 = t p.2} := ⟨(p.val.1.val.2, p.val.2.val.2), by
    calc
      s p.val.1.val.2 = (s' p.val.1).val.2 := (hsrc p.val.1).symm
      _ = (t' p.val.2).val.2 := congrArg (fun z : Obj f q => z.val.2) p.property
      _ = t p.val.2.val.2 := htgt p.val.2⟩
  exact ⟨(p.val.1.val.1, c old), p.val.1.property.trans (hc old).symm⟩

/-- The base change of a pointwise groupoid: the objects and arrows over a fixed point of the
new base form the old groupoid, so the whole base change is again a pointwise groupoid. -/
noncomputable def pointwise
    {X U R Z : Type u} {f : X → Z} {q : U → Z} {r : R → Z}
    {s t : R → U} {c : {p : R × R // s p.1 = t p.2} → R}
    (P : Deformation.PointwiseGroupoid s t c)
    (hs : ∀ a, q (s a) = r a) (ht : ∀ a, q (t a) = r a)
    (hc : ∀ p, r (c p) = r p.1.1) :
    Deformation.PointwiseGroupoid (src s hs) (tgt t ht)
      (@comp X U R Z f q r s t c hc (src s hs) (tgt t ht)
        (by intro a; simp [src]) (by intro a; simp [tgt])) := by
  classical
  let V := Obj f q
  let W := Arr f r
  letI : Groupoid.{u} U := P.groupoid
  letI : Category.{u} V := {
    Hom := fun x y => PLift (x.val.1 = y.val.1) × (x.val.2 ⟶ y.val.2)
    id := fun x => ⟨PLift.up rfl, 𝟙 x.val.2⟩
    comp := fun g h => ⟨PLift.up (g.1.down.trans h.1.down), g.2 ≫ h.2⟩
    id_comp := by intros; apply Prod.ext <;> first | exact Subsingleton.elim _ _ | simp
    comp_id := by intros; apply Prod.ext <;> first | exact Subsingleton.elim _ _ | simp
    assoc := by
      intros
      apply Prod.ext <;> first | exact Subsingleton.elim _ _ | simp [Category.assoc]
  }
  letI : Groupoid.{u} V := {
    inv := fun g => ⟨PLift.up g.1.down.symm, Groupoid.inv g.2⟩
    inv_comp := by
      intros
      apply Prod.ext <;> first | exact Subsingleton.elim _ _ | exact Groupoid.inv_comp _
    comp_inv := by
      intros
      apply Prod.ext <;> first | exact Subsingleton.elim _ _ | exact Groupoid.comp_inv _
  }
  let ae : ∀ x y : V, (x ⟶ y) ≃ {a : W // src s hs a = x ∧ tgt t ht a = y} := fun x y => {
    toFun := fun g =>
      let a := P.arrowEquiv x.val.2 y.val.2 g.2
      have hbase : f x.val.1 = r a.val :=
        x.property.trans ((congrArg q a.property.1.symm).trans (hs a.val))
      ⟨⟨(x.val.1, a.val), hbase⟩,
        ⟨Subtype.ext (Prod.ext rfl a.property.1),
          Subtype.ext (Prod.ext g.1.down a.property.2)⟩⟩
    invFun := fun a =>
      let hbase₁ := congrArg (fun z : V => z.val.1) a.property.1
      let hbase₂ := congrArg (fun z : V => z.val.1) a.property.2
      let hsrc := congrArg (fun z : V => z.val.2) a.property.1
      let htgt := congrArg (fun z : V => z.val.2) a.property.2
      ⟨PLift.up (hbase₁.symm.trans hbase₂),
       (P.arrowEquiv x.val.2 y.val.2).symm ⟨a.val.val.2, hsrc, htgt⟩⟩
    left_inv := by
      intro g
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · simp
    right_inv := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg (fun z : V => z.val.1) a.property.1).symm
      · simp
  }
  refine ⟨inferInstance, ae, ?_⟩
  intro x y z g h
  refine Subtype.ext (Prod.ext g.1.down ?_)
  change (P.arrowEquiv x.val.2 z.val.2 (g.2 ≫ h.2)).1 =
      c ⟨((P.arrowEquiv y.val.2 z.val.2 h.2).1,
        (P.arrowEquiv x.val.2 y.val.2 g.2).1), _⟩
  exact P.comp_eq g.2 h.2

end FiberBaseChange

/-- The sections of a fibre product of algebraic spaces over a test object are the pairs of
sections with the same image, limits of presheaves being computed pointwise. -/
noncomputable def fiberProductAtEquiv
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {F G H : AlgebraicSpaces C S hS}
    (f : F ⟶ H) (g : G ⟶ H)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    ((AlgebraicSpaces.fiberProduct C S hS f g).obj.obj T) ≃
      FiberBaseChange.Obj (f.hom.app T) (g.hom.app T) := by
  let e₁ := CategoryTheory.Limits.pullbackObjIso f.hom g.hom T
  let e₂ := CategoryTheory.Limits.Types.pullbackIsoPullback
    (f.hom.app T) (g.hom.app T)
  exact e₁.toEquiv.trans e₂.toEquiv

/-- The first component of a section of a fibre product is its first projection. -/
theorem fiberProductAtEquiv_fst
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {F G H : AlgebraicSpaces C S hS}
    (f : F ⟶ H) (g : G ⟶ H)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (AlgebraicSpaces.fiberProduct C S hS f g).obj.obj T) :
    (fiberProductAtEquiv f g T x).val.1 =
      (pullback.fst f.hom g.hom).app T x := by
  simp only [fiberProductAtEquiv]
  exact congrArg (fun k => k x) (pullbackObjIso_hom_comp_fst f.hom g.hom T)

/-- The second component of a section of a fibre product is its second projection. -/
theorem fiberProductAtEquiv_snd
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {F G H : AlgebraicSpaces C S hS}
    (f : F ⟶ H) (g : G ⟶ H)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (AlgebraicSpaces.fiberProduct C S hS f g).obj.obj T) :
    (fiberProductAtEquiv f g T x).val.2 =
      (pullback.snd f.hom g.hom).app T x := by
  simp only [fiberProductAtEquiv]
  exact congrArg (fun k => k x) (pullbackObjIso_hom_comp_snd f.hom g.hom T)

/-- A pair of maps on objects and arrows which respects source, target and composition also
respects identities, identities being determined by the composition law. -/
theorem mapIdentityOfMapComp
    {D : Type u} [Category D]
    {G H : Deformation.GroupoidInFunctors D}
    (mapObjects : G.objects ⟶ H.objects) (mapArrows : G.arrows ⟶ H.arrows)
    (map_source : ∀ T a, H.source.app T (mapArrows.app T a) =
      mapObjects.app T (G.source.app T a))
    (map_target : ∀ T a, H.target.app T (mapArrows.app T a) =
      mapObjects.app T (G.target.app T a))
    (map_comp : ∀ T a b h, H.compose T (mapArrows.app T a) (mapArrows.app T b)
      ((map_source T a).trans ((congrArg (mapObjects.app T) h).trans
        (map_target T b).symm)) = mapArrows.app T (G.compose T a b h))
    (T : D) (x : G.Evaluation T) :
      mapArrows.app T (G.identity T x) = H.identity T (mapObjects.app T x) := by
  let a := G.identity T x
  have ha₁ : G.source.app T a = x := (G.evaluationArrowEquiv T x x (𝟙 x)).2.1
  have ha₂ : G.target.app T a = x := (G.evaluationArrowEquiv T x x (𝟙 x)).2.2
  let y := mapObjects.app T x
  let _inst : Groupoid (H.objects.obj T) := H.evaluationGroupoid T
  have hy₁ : H.source.app T (mapArrows.app T a) = y :=
    (map_source T a).trans (congrArg (mapObjects.app T) ha₁)
  have hy₂ : H.target.app T (mapArrows.app T a) = y :=
    (map_target T a).trans (congrArg (mapObjects.app T) ha₂)
  let v : y ⟶ y := (H.evaluationArrowEquiv T y y).symm
    ⟨mapArrows.app T a, hy₁, hy₂⟩
  have hA : G.source.app T a = G.target.app T a := ha₁.trans ha₂.symm
  have hF : H.source.app T (mapArrows.app T a) =
      H.target.app T (mapArrows.app T a) := hy₁.trans hy₂.symm
  have hCompA : G.compose T a a hA = a := by
    have h := G.evaluationArrowEquiv_comp T (𝟙 x) (𝟙 x)
    rw [Category.comp_id] at h
    exact h.symm
  have hMapComp : H.compose T (mapArrows.app T a) (mapArrows.app T a) hF =
      mapArrows.app T a := by
    rw [map_comp T a a hA, hCompA]
  have hval : (H.evaluationArrowEquiv T y y v).1 = mapArrows.app T a := by
    have h := Equiv.apply_symm_apply (H.evaluationArrowEquiv T y y)
      (⟨mapArrows.app T a, hy₁, hy₂⟩ : {z : H.arrows.obj T //
        H.source.app T z = y ∧ H.target.app T z = y})
    exact congrArg Subtype.val h
  have hF' : H.source.app T (H.evaluationArrowEquiv T y y v).1 =
      H.target.app T (H.evaluationArrowEquiv T y y v).1 := by
    rwa [hval]
  have hvComp : v ≫ v = v := by
    apply (H.evaluationArrowEquiv T y y).injective
    apply Subtype.ext
    calc
      (H.evaluationArrowEquiv T y y (v ≫ v)).1 =
          H.compose T (H.evaluationArrowEquiv T y y v).1
            (H.evaluationArrowEquiv T y y v).1 hF' :=
        H.evaluationArrowEquiv_comp T v v
      _ = H.compose T (mapArrows.app T a) (mapArrows.app T a) hF := by congr 1
      _ = mapArrows.app T a := hMapComp
      _ = (H.evaluationArrowEquiv T y y v).1 := hval.symm
  have hvId : v = 𝟙 y := by rw [← cancel_epi v, hvComp, Category.comp_id]
  exact hval.symm.trans (congrArg (fun z => (H.evaluationArrowEquiv T y y z).1) hvId)

/-- The map from the composable pairs of a base-changed groupoid to the composable pairs of
the original one, induced by the projections. -/
noncomputable def mapComposableToOld
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {U R : AlgebraicSpaces C S hS}
    {U' R' : AlgebraicSpaces C S hS}
    (s t : R ⟶ U)
    (s' t' : R' ⟶ U') (mapU : U' ⟶ U) (mapR : R' ⟶ R)
    (hs : s' ≫ mapU = mapR ≫ s) (ht : t' ≫ mapU = mapR ≫ t) :
    AlgebraicSpaces.fiberProduct C S hS s' t' ⟶
      AlgebraicSpaces.fiberProduct C S hS s t := by
  let p₁ : AlgebraicSpaces.fiberProduct C S hS s' t' ⟶ R' :=
    ObjectProperty.homMk (pullback.fst s'.hom t'.hom)
  let p₂ : AlgebraicSpaces.fiberProduct C S hS s' t' ⟶ R' :=
    ObjectProperty.homMk (pullback.snd s'.hom t'.hom)
  refine (AlgebraicSpaces.isPullback_fiberProduct C S hS s t).lift
    (p₁ ≫ mapR) (p₂ ≫ mapR) ?_
  calc
    (p₁ ≫ mapR) ≫ s = (p₁ ≫ s') ≫ mapU := by
      rw [Category.assoc, ← hs, ← Category.assoc]
    _ = (p₂ ≫ t') ≫ mapU := by
      simpa [Category.assoc] using congrArg (fun k => k ≫ mapU)
        (AlgebraicSpaces.isPullback_fiberProduct C S hS s' t').w
    _ = (p₂ ≫ mapR) ≫ t := by
      simpa [Category.assoc] using congrArg (fun k => p₂ ≫ k) ht

/-- Transport a pointwise groupoid along bijections of the object and arrow sets which match
the source, target and composition maps. -/
noncomputable def transportPointwise
    {U₀ R₀ U R : Type u}
    {s₀ t₀ : R₀ → U₀}
    {c₀ : {p : R₀ × R₀ // s₀ p.1 = t₀ p.2} → R₀}
    {s t : R → U} {c : {p : R × R // s p.1 = t p.2} → R}
    (eU : U₀ ≃ U) (eR : R₀ ≃ R)
    (hs : ∀ a, eU (s₀ a) = s (eR a))
    (ht : ∀ a, eU (t₀ a) = t (eR a))
    (hc : ∀ p, eR (c₀ p) = c ⟨(eR p.1.1, eR p.1.2), by
      calc
        s (eR p.1.1) = eU (s₀ p.1.1) := (hs p.1.1).symm
        _ = eU (t₀ p.1.2) := congrArg eU p.2
        _ = t (eR p.1.2) := ht p.1.2⟩)
    (P : Deformation.PointwiseGroupoid s t c) :
    Deformation.PointwiseGroupoid s₀ t₀ c₀ := by
  classical
  letI : Groupoid.{u} U := P.groupoid
  letI : Category.{u} U₀ := {
    Hom := fun x y => (eU x ⟶ eU y)
    id := fun x => 𝟙 (eU x)
    comp := fun f g => f ≫ g
    id_comp := by intros; simp
    comp_id := by intros; simp
    assoc := by intros; simp [Category.assoc]
  }
  letI : Groupoid.{u} U₀ := {
    inv := fun f => Groupoid.inv f
    inv_comp := by intros; exact Groupoid.inv_comp _
    comp_inv := by intros; exact Groupoid.comp_inv _
  }
  let oldToNew (x y : U₀) :
      {a : R // s a = eU x ∧ t a = eU y} ≃
        {a : R₀ // s₀ a = x ∧ t₀ a = y} := {
    toFun := fun a => ⟨eR.symm a.1, ⟨by
      apply eU.injective
      calc
        eU (s₀ (eR.symm a.1)) = s (eR (eR.symm a.1)) := hs _
        _ = s a.1 := by simp
        _ = eU x := a.2.1,
      by
      apply eU.injective
      calc
        eU (t₀ (eR.symm a.1)) = t (eR (eR.symm a.1)) := ht _
        _ = t a.1 := by simp
        _ = eU y := a.2.2⟩⟩
    invFun := fun a => ⟨eR a.1, ⟨by
      calc
        s (eR a.1) = eU (s₀ a.1) := (hs a.1).symm
        _ = eU x := congrArg eU a.2.1,
      by
      calc
        t (eR a.1) = eU (t₀ a.1) := (ht a.1).symm
        _ = eU y := congrArg eU a.2.2⟩⟩
    left_inv := by intro a; apply Subtype.ext; simp
    right_inv := by intro a; apply Subtype.ext; simp
  }
  refine ⟨inferInstance, fun x y => (P.arrowEquiv (eU x) (eU y)).trans (oldToNew x y), ?_⟩
  intro x y z g h
  apply eR.injective
  rw [hc]
  dsimp [oldToNew]
  simp only [Equiv.apply_symm_apply]
  exact (P.comp_eq g h).trans (congrArg c (by apply Subtype.ext; rfl))

end Space

end AlgebraicGeometry

end
