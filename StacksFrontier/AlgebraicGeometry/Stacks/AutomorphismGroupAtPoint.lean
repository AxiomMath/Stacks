module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# Automorphism groups at a point of an algebraic stack (Stacks 0DTV, 0DTW)

Let `p : X ⥤ C` be a category over a base. The *automorphism group* of an object `a` of `X`
is the subgroup `CategoryTheory.Functor.verticalAut p a` of `Aut a` consisting of the
automorphisms that `p` sends to an identity; these are exactly the automorphisms appearing in
the relative inertia `CategoryTheory.RelativeInertia p` at `a`. A functor `F : X ⥤ Y` over `C`
carries them to automorphisms of `F a` of the same kind, giving a group homomorphism
`CategoryTheory.Functor.verticalAutMap`.

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over a scheme `S` of a big fppf site and a
point `q` of `|𝒳|` (`AlgebraicGeometry.Stack.points`, Stacks 04XG), Stacks 0DTW says that `f`
*induces an isomorphism between automorphism groups at `q` and `f(q)`* when the map
`G_x ⟶ G_{f ∘ x}` of automorphism group algebraic spaces is an isomorphism for a — equivalently,
by Stacks 0DTV, for any — field-valued representative `x` of `q`. The automorphism group
algebraic space itself is `AlgebraicGeometry.Stack.pointAutomorphismSpace` and the map between
two of them is `AlgebraicGeometry.Stack.pointAutomorphismSpaceMap`, both in
`StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension`, which is where
Stacks 0DTV is proved; this module is upstream of it and reads the condition on the sections of
that group space instead. A `T`-section of `G_x` over `t : T ⟶ Spec κ` is an automorphism of
the pullback of `x` along `t` lying over the identity of `T`, so `G_x ⟶ G_y` being an
isomorphism of sheaves says exactly that `verticalAutMap` is bijective at every object of `𝒳`
lying above the representative. That is
`AlgebraicGeometry.Stack.InducesIsomorphismAtObject`, and
`AlgebraicGeometry.Stack.InducesIsomorphismAt` asks for it at every representative.

## Main definitions

* `CategoryTheory.Functor.verticalAut`: the automorphism group of an object of a category over
  a base, i.e. its automorphisms lying over an identity.
* `CategoryTheory.Functor.verticalAutMap`: the group homomorphism induced by a functor over the
  base.
* `AlgebraicGeometry.Stack.InducesIsomorphismAtObject`: `f` induces an isomorphism between the
  automorphism groups at an object and at every object above it.
* `AlgebraicGeometry.Stack.InducesIsomorphismAt`: **Stacks 0DTW**, `f` induces an isomorphism
  between automorphism groups at a point of `|𝒳|`.

## Main results

* `CategoryTheory.Functor.bijective_verticalAutMap_of_iso`: the condition only depends on the
  object up to isomorphism over an identity, so in a category fibred in groupoids it only
  depends on the morphism of the base that the object is pulled back along.
* `CategoryTheory.Functor.bijective_verticalAutMap`: a full and essentially surjective inertia
  comparison (Stacks 06R5) induces isomorphisms between all automorphism groups.
* `AlgebraicGeometry.Stack.inducesIsomorphismAt_iff_forall_representatives`: it suffices to
  exhibit *one* pullback of a representative above each object of the site; the condition then
  holds at *every* object above *every* representative.

## Implementation notes

`Aut.autMulEquivOfIso` conjugates automorphism groups along an isomorphism, and restricts to
the automorphism groups of this file exactly when the isomorphism lies over an identity
(`CategoryTheory.Functor.verticalAutCongr`). This is what makes the condition insensitive to
the choice of pullback: in a category fibred in groupoids any two lifts of the same morphism of
the base are identified by such an isomorphism, by `Functor.IsCartesian.domainUniqueUpToIso`.

Only `𝒳.val.val.p` and `CategoryTheory.CatFiberedInGroupoids.homFunctor` are used of an
algebraic stack, never a projection of
`AlgebraicGeometry.Stack.AlgebraicStacks.toCatFiberedInGroupoids`, whose semireducibility hides
the ambient 2-category from instance search.

`AlgebraicGeometry.Stack.InducesIsomorphismAt` quantifies over every field-valued
representative of the point, which is condition (2) of Stacks 0DTV, so it cannot weaken the
notion of Stacks 0DTW. Condition (1) of Stacks 0DTV, that one representative suffices, agrees
with condition (2) among the lifts of a single representative, which is
`AlgebraicGeometry.Stack.inducesIsomorphismAt_iff_forall_representatives`. Passing between two
representatives of one point is a descent statement about a field extension: the map of
automorphism group algebraic spaces over an extension field is a base change, and being an
isomorphism is fpqc local on the target (Stacks 041Y). That is
`AlgebraicGeometry.Stack.exists_isIso_pointAutomorphismSpaceMap_iff_forall`, proved for the
automorphism group algebraic spaces themselves in
`StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension`.

## References

* [Stacks Project, Tag 0DTV](https://stacks.math.columbia.edu/tag/0DTV)
* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe uC vC uX vX uY vY

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y]

/-- The automorphism group of an object `a` of a category over `C`: the automorphisms of `a`
that the structure functor `p` sends to the identity. These are the automorphisms carried by
the objects of the relative inertia `CategoryTheory.RelativeInertia p` lying at `a`. -/
def verticalAut (p : X ⥤ C) (a : X) : Subgroup (Aut a) := (p.mapAut a).ker

/-- An automorphism `α` of `a` lies in the automorphism group `p.verticalAut a` if and only if
`p` sends it to the identity of `p.obj a`. -/
@[simp]
lemma mem_verticalAut_iff (p : X ⥤ C) {a : X} (α : Aut a) :
    α ∈ p.verticalAut a ↔ p.map α.asIso.hom = 𝟙 (p.obj a) := by
  rw [verticalAut, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg (fun x => x.asIso.hom) h, fun h => Aut.ext (Iso.ext h)⟩

/-- The defining equation of the automorphism group: its elements lie over an identity. -/
lemma verticalAut.cond {p : X ⥤ C} {a : X} (α : p.verticalAut a) :
    p.map (α : Aut a).asIso.hom = 𝟙 (p.obj a) := (mem_verticalAut_iff p _).mp α.2

/-- The object of the relative inertia determined by an element of an automorphism group. -/
def verticalAut.toRelativeInertia {p : X ⥤ C} {a : X} (α : p.verticalAut a) :
    RelativeInertia p where
  obj := a
  auto := α
  cond := verticalAut.cond α

variable {pX : X ⥤ C} {pY : Y ⥤ C}

private lemma map_map_eq (F : X ⥤ Y) (hF : F ⋙ pY = pX) {a b : X} (m : a ⟶ b) :
    pY.map (F.map m) = eqToHom (Functor.congr_obj hF a) ≫ pX.map m ≫
      eqToHom (Functor.congr_obj hF b).symm := by
  simpa using Functor.congr_hom hF m

/-- A functor over `C` carries automorphisms lying over an identity to automorphisms lying over
an identity, hence induces a homomorphism of automorphism groups. -/
def verticalAutMap (F : X ⥤ Y) (hF : F ⋙ pY = pX) (a : X) :
    pX.verticalAut a →* pY.verticalAut (F.obj a) :=
  ((F.mapAut a).comp (pX.verticalAut a).subtype).codRestrict _ <| by
    intro α
    simp only [mem_verticalAut_iff]
    change pY.map (F.map (α : Aut a).asIso.hom) = _
    rw [map_map_eq F hF, verticalAut.cond α]
    simp

/-- The homomorphism `verticalAutMap F hF a` sends an automorphism `α` of `a` to `F.map α`. -/
@[simp]
lemma verticalAutMap_coe_hom (F : X ⥤ Y) (hF : F ⋙ pY = pX) (a : X) (α : pX.verticalAut a) :
    ((verticalAutMap F hF a α : Aut (F.obj a))).asIso.hom = F.map (α : Aut a).asIso.hom := rfl

private lemma map_inv_eq_eqToHom (p : X ⥤ C) {a b : X} (e : a ≅ b) {hab : p.obj a = p.obj b}
    (he : p.map e.hom = eqToHom hab) : p.map e.inv = eqToHom hab.symm := by
  rw [← cancel_epi (p.map e.hom), ← p.map_comp, e.hom_inv_id, p.map_id, he]
  simp

/-- Conjugation by an isomorphism lying over an identity identifies the automorphism groups of
its source and target. -/
def verticalAutCongr (p : X ⥤ C) {a b : X} (e : a ≅ b) {hab : p.obj a = p.obj b}
    (he : p.map e.hom = eqToHom hab) : p.verticalAut a ≃* p.verticalAut b where
  toFun α := ⟨Aut.autMulEquivOfIso e α, by
    simp only [mem_verticalAut_iff]
    change p.map (e.inv ≫ (α : Aut a).asIso.hom ≫ e.hom) = _
    rw [p.map_comp, p.map_comp, map_inv_eq_eqToHom p e he, he, verticalAut.cond α]
    simp⟩
  invFun β := ⟨(Aut.autMulEquivOfIso e).symm β, by
    simp only [mem_verticalAut_iff]
    change p.map (e.hom ≫ (β : Aut b).asIso.hom ≫ e.inv) = _
    rw [p.map_comp, p.map_comp, map_inv_eq_eqToHom p e he, he, verticalAut.cond β]
    simp⟩
  left_inv α := Subtype.ext ((Aut.autMulEquivOfIso e).symm_apply_apply _)
  right_inv β := Subtype.ext ((Aut.autMulEquivOfIso e).apply_symm_apply _)
  map_mul' α β := Subtype.ext (map_mul (Aut.autMulEquivOfIso e) _ _)

private lemma map_map_eq_eqToHom (F : X ⥤ Y) (hF : F ⋙ pY = pX) {a b : X} (e : a ≅ b)
    {hab : pX.obj a = pX.obj b} (he : pX.map e.hom = eqToHom hab) :
    pY.map (F.mapIso e).hom = eqToHom ((Functor.congr_obj hF a).trans
      (hab.trans (Functor.congr_obj hF b).symm)) := by
  show pY.map (F.map e.hom) = _
  rw [map_map_eq F hF, he]
  simp

/-- Whether a functor over `C` induces an isomorphism between the automorphism groups at an
object only depends on that object up to isomorphism over an identity. -/
theorem bijective_verticalAutMap_of_iso (F : X ⥤ Y) (hF : F ⋙ pY = pX) {a b : X} (e : a ≅ b)
    {hab : pX.obj a = pX.obj b} (he : pX.map e.hom = eqToHom hab)
    (hb : Function.Bijective (verticalAutMap F hF b)) :
    Function.Bijective (verticalAutMap F hF a) := by
  have heY := map_map_eq_eqToHom F hF e he
  have key : (verticalAutMap F hF a : pX.verticalAut a → _) =
      (verticalAutCongr pY (F.mapIso e) heY).symm ∘ (verticalAutMap F hF b) ∘
        (verticalAutCongr pX e he) := by
    funext α
    apply (verticalAutCongr pY (F.mapIso e) heY).injective
    simp only [Function.comp_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Aut.ext
    apply Iso.ext
    show F.map e.inv ≫ F.map (α : Aut a).asIso.hom ≫ F.map e.hom =
      F.map (e.inv ≫ (α : Aut a).asIso.hom ≫ e.hom)
    simp
  rw [key]
  exact (verticalAutCongr pY (F.mapIso e) heY).symm.bijective.comp
    (hb.comp (verticalAutCongr pX e he).bijective)

section Inertia

variable (pX pY) (F : X ⥤ Y) (hF : F ⋙ pY = pX)

/-- A **full** inertia comparison (Stacks 06R5) induces injections between automorphism
groups: an automorphism lying over an identity is determined by its image. -/
theorem injective_verticalAutMap_of_full
    [(inertiaPullbackComparison pX pY F hF).Full] (a : X) :
    Function.Injective (verticalAutMap F hF a) := by
  intro α β h
  apply Subtype.ext
  apply Aut.ext
  apply Iso.ext
  have hh : F.map (β : Aut a).asIso.hom = F.map (α : Aut a).asIso.hom := by
    simpa using (congrArg (fun z : pY.verticalAut (F.obj a) => (z : Aut (F.obj a)).asIso.hom) h).symm
  simpa using (inertiaPullbackComparison_reflects_comm pX pY F hF
    ⟨a, α, verticalAut.cond α⟩ ⟨a, β, verticalAut.cond β⟩ (𝟙 a) (by simpa using hh)).symm

/-- An **essentially surjective** inertia comparison (Stacks 06R5) induces surjections between
automorphism groups: every automorphism of `F a` lying over an identity is the image of one of
`a`. -/
theorem surjective_verticalAutMap_of_essSurj
    [(inertiaPullbackComparison pX pY F hF).EssSurj] (a : X) :
    Function.Surjective (verticalAutMap F hF a) := by
  intro β
  obtain ⟨α, hα, hmap⟩ := inertiaPullbackComparison_exists_aut pX pY F hF a β (verticalAut.cond β)
  exact ⟨⟨α, (mem_verticalAut_iff pX α).mpr hα⟩, Subtype.ext (Aut.ext (Iso.ext hmap))⟩

/-- A full and essentially surjective inertia comparison (Stacks 06R5) induces isomorphisms
between all automorphism groups. -/
theorem bijective_verticalAutMap
    [(inertiaPullbackComparison pX pY F hF).Full]
    [(inertiaPullbackComparison pX pY F hF).EssSurj] (a : X) :
    Function.Bijective (verticalAutMap F hF a) :=
  ⟨injective_verticalAutMap_of_full pX pY F hF a,
    surjective_verticalAutMap_of_essSurj pX pY F hF a⟩

end Inertia

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

open CategoryTheory

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The homomorphism from the automorphism group of an object of `𝒳` to the automorphism group
of its image under a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks. For an object lying over `T`
this is the map on `T`-sections of the automorphism group algebraic spaces. -/
def automorphismGroupMap (f : 𝒳 ⟶ 𝒴) (a : 𝒳.val.val.obj) :
    𝒳.val.val.p.verticalAut a →*
      𝒴.val.val.p.verticalAut ((CatFiberedInGroupoids.homFunctor f.hom).obj a) :=
  Functor.verticalAutMap (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) a

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks *induces an isomorphism between automorphism
groups at an object* `a` of `𝒳` when it does so at every object of `𝒳` lying above `a`. For `a`
lying over `T`, the objects above `a` are the pullbacks of `a`, and their automorphism groups
are the sections of the automorphism group algebraic space of `a`; so this says that the
morphism of automorphism group algebraic spaces at `a` is an isomorphism. -/
def InducesIsomorphismAtObject (f : 𝒳 ⟶ 𝒴) (a : 𝒳.val.val.obj) : Prop :=
  ∀ (b : 𝒳.val.val.obj) (_ : b ⟶ a), Function.Bijective (automorphismGroupMap B S hS f b)

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks *induces an isomorphism between automorphism
groups at a point* `q` of `|𝒳|` and at `f(q)` — in the literature, `f` is *stabilizer
preserving*, or *fixed-point reflecting*, at `q` — when for every field-valued representative `p`
of `q` and every object of the big site the morphism of automorphism group algebraic spaces of
`p` has a pullback of `p` at which it is bijective on sections.

By `AlgebraicGeometry.Stack.inducesIsomorphismAt_iff_forall_representatives` one such pullback
per object of the site is enough: the condition then holds at every object lying above every
representative of `q`, which is the content of Stacks 0DTV for the representatives of a fixed
field-valued point. -/
@[stacks 0DTW "f induces an isomorphism between automorphism groups at a point"]
def InducesIsomorphismAt (f : 𝒳 ⟶ 𝒴)
    (q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids) : Prop :=
  ∀ p : FieldValuedPoint B S hS 𝒳.val.val,
    pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q →
      ∀ (V : BigFppfOver B S hS) (t : V ⟶ p.base),
        ∃ (b : 𝒳.val.val.obj) (m : b ⟶ p.obj), 𝒳.val.val.p.IsHomLift t m ∧
          Function.Bijective (automorphismGroupMap B S hS f b)

/-- Two lifts of the same morphism of the big site along the same object of an algebraic stack
induce isomorphisms between the same automorphism groups. -/
theorem bijective_automorphismGroupMap_of_isHomLift (f : 𝒳 ⟶ 𝒴)
    {V : BigFppfOver B S hS} {U : BigFppfOver B S hS} {t : V ⟶ U} {a b b' : 𝒳.val.val.obj}
    (m : b ⟶ a) (m' : b' ⟶ a) (hm : 𝒳.val.val.p.IsHomLift t m)
    (hm' : 𝒳.val.val.p.IsHomLift t m')
    (h : Function.Bijective (automorphismGroupMap B S hS f b')) :
    Function.Bijective (automorphismGroupMap B S hS f b) := by
  have := hm
  have := hm'
  have hc : 𝒳.val.val.p.IsStronglyCartesian t m :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift t m
  have hc' : 𝒳.val.val.p.IsStronglyCartesian t m' :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift t m'
  let e : b ≅ b' := Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p t m' m
  have he : 𝒳.val.val.p.IsHomLift (𝟙 V) e.hom := inferInstance
  refine Functor.bijective_verticalAutMap_of_iso _
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) e (hab := ?_) ?_ h
  · exact (IsHomLift.domain_eq 𝒳.val.val.p (𝟙 V) e.hom).trans
      (IsHomLift.codomain_eq 𝒳.val.val.p (𝟙 V) e.hom).symm
  · simpa using IsHomLift.fac' 𝒳.val.val.p (𝟙 V) e.hom

/-- A 1-morphism of algebraic stacks induces an isomorphism between automorphism groups at a
point of `|𝒳|` exactly when it does so at *every* object lying above *every* field-valued
representative of that point: one pullback of one representative above each object of the big
site already decides it, because in a category fibred in groupoids any two lifts of the same
morphism of the base are isomorphic over an identity.

This is Stacks 0DTV for the lifts of one field-valued representative. Passing between two
representatives of the same point is a descent statement, proved for the automorphism group
algebraic spaces in
`AlgebraicGeometry.Stack.exists_isIso_pointAutomorphismSpaceMap_iff_forall`: the map of
automorphism group algebraic spaces over a field extension is a base change, and being an
isomorphism is fpqc local on the target (Stacks 041Y).
`AlgebraicGeometry.Stack.InducesIsomorphismAt` quantifies over *all* field-valued
representatives, which is condition (2) of Stacks 0DTV and so never weaker than the notion of
Stacks 0DTW. -/
@[stacks 0DTV "for the lifts of one field-valued representative: some lift, hence any lift"]
theorem inducesIsomorphismAt_iff_forall_representatives (f : 𝒳 ⟶ 𝒴)
    (q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids) :
    InducesIsomorphismAt B S hS f q ↔
      ∀ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q →
          InducesIsomorphismAtObject B S hS f p.obj := by
  refine ⟨fun h p hp b m => ?_, fun h p hp V t => ?_⟩
  · have hm : 𝒳.val.val.p.IsHomLift
        (𝒳.val.val.p.map m ≫ eqToHom p.over) m :=
      IsHomLift.of_fac' 𝒳.val.val.p _ m rfl p.over (by simp)
    obtain ⟨b', m', hm', hbij⟩ := h p hp (𝒳.val.val.p.obj b) (𝒳.val.val.p.map m ≫ eqToHom p.over)
    exact bijective_automorphismGroupMap_of_isHomLift B S hS f m m' hm hm' hbij
  · obtain ⟨b, m, hm⟩ := 𝒳.val.isFiberedInGroupoids.exists_lift t p.obj p.over
    exact ⟨b, m, hm, h p hp b m⟩

end AlgebraicGeometry.Stack

end
