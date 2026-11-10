module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidTarget

/-!
# Membership in the arrow space of the finite part of a groupoid

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces whose source morphism is separated
and locally of finite type, and let `(U', Z_univ)` be the object space and the arrow space of its
finite part, Stacks 04RT. A point of `Z_univ` over a test space is a triple `(u, Z, z)`, and the
clause which is not visible in the ambient fibre product `U' ×_{g, U, s} R` is that `z` lies in
`Z`. This file isolates that clause as a membership predicate and proves the dictionary between
the two readings of it, which is what the remaining structure morphisms of Stacks 04RT are built
out of.

## Main definitions

* `AlgebraicGeometry.Space.MemSubspace`: the condition that a point `(k, w)` of the ambient fibre
  product of a pair of Stacks 04PC lies in the pair's open subspace.

## Main results

* `AlgebraicGeometry.Space.memSubspace_of_pointwise` and
  `AlgebraicGeometry.Space.memSubspace_sections`: the two directions of the dictionary. A point of
  the ambient fibre product over `U'` lies in `Z_univ` exactly when, at every scheme-valued point,
  the arrow lies in the collection which that point of `U'` names.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.memSubspace_translatePair_iff`: the subfunctor-level
  form of the pointwise computation that an arrow lies in a translated collection `c(Z, i ∘ z)`
  exactly when its composite with `z` lies in `Z`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.containsSection_named`: every collection
  named by a point of `U'` contains the unit, which is what makes `U'` the finite part containing
  the unit.

## Implementation notes

`MemSubspace` is phrased as containment of the range of the point in the open subspace, rather
than as the existence of a factorization through it. The two are equivalent, which is
`AlgebraicGeometry.Space.memSubspace_iff`, but only the first produces the factorization as a
*definition*, by `CategoryTheory.Subfunctor.lift`; the structure morphisms of Stacks 04RT are
data, and may not be extracted from an existence statement.

The two directions of the dictionary both go through the cartesian squares of Stacks 04PE,
part (2), which identify the collection named by a scheme-valued point of `U'` with the base
change of `Z_univ`. Transport of membership across such a square, in both directions, is
`AlgebraicGeometry.Space.memSubspace_of_isPullback` and
`AlgebraicGeometry.Space.memSubspace_of_isPullback'`.

The translation statement is an equality of subfunctors read through the ambient isomorphism
`c(-, i ∘ z)` of Stacks 04RT: the open subspace of the translated pair is by construction the
preimage of the original one, so membership in it is membership of the translated point, and the
translated point is computed by `translateBwd`, whose arrow component is composition with `z`.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RS](https://stacks.math.columbia.edu/tag/04RS)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) AlgebraicGeometry.Space.hasPullbacks_presheaf_groupoidCompose
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) AlgebraicGeometry.Space.hasPullback_presheaf_groupoidCompose
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (AlgebraicGeometry.Space.hasPullbacks_presheaf_groupoidCompose B S hS).has_limit _

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A point of the ambient fibre product of a pair of Stacks 04PC lies in the pair's open
subspace: the point with base component `k` and fibre component `w` has its range inside the
subfunctor.

In the reading of Stacks 04RT, where a pair over `T` is a `T`-valued family of finite collections
of arrows with source `a`, this is the condition that the arrow `w` lies in the collection at the
point `k`. -/
def MemSubspace {X Y T : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (p : FiniteOpenSubspace B S hS f T) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ T.obj) (w : F ⟶ X.obj) (h : k ≫ p.toBase.hom = w ≫ f.hom) : Prop :=
  Subfunctor.range (pullback.lift k w h) ≤ p.subspace

variable {B S hS}

/-- Membership depends only on the two components of the point. -/
theorem memSubspace_congr {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {k k' : F ⟶ T.obj} {w w' : F ⟶ X.obj} (hk : k = k') (hw : w = w')
    {h : k ≫ p.toBase.hom = w ≫ f.hom} {h' : k' ≫ p.toBase.hom = w' ≫ f.hom}
    (hm : MemSubspace B S hS f p k w h) : MemSubspace B S hS f p k' w' h' := by
  subst hk hw
  exact hm

/-- A map into the open subspace followed by the inclusion is the point `(k, w)` of the ambient
fibre product exactly when its two components are `k` and `w`. -/
private theorem comp_ι_eq_lift_iff {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (l : F ⟶ p.subspace.toFunctor) (k : F ⟶ T.obj) (w : F ⟶ X.obj)
    (h : k ≫ p.toBase.hom = w ≫ f.hom) :
    l ≫ p.subspace.ι = pullback.lift k w h ↔
      l ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom = k ∧
        l ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom = w := by
  rw [pullback.hom_ext_iff]
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

/-- Membership of a point in the open subspace of a pair of Stacks 04PC is the existence of a
factorization of the point through the open subspace, read through the two projections of the
ambient fibre product. -/
theorem memSubspace_iff {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ T.obj) (w : F ⟶ X.obj) (h : k ≫ p.toBase.hom = w ≫ f.hom) :
    MemSubspace B S hS f p k w h ↔
      ∃ l : F ⟶ p.subspace.toFunctor,
        l ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom = k ∧
          l ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom = w := by
  constructor
  · exact fun hm => ⟨_, (comp_ι_eq_lift_iff p _ k w h).1 (Subfunctor.lift_ι _ hm)⟩
  · rintro ⟨l, hl⟩
    change Subfunctor.range (pullback.lift k w h) ≤ p.subspace
    rw [← (comp_ι_eq_lift_iff p l k w h).2 hl]
    rintro V _ ⟨x, rfl⟩
    exact (l.app V x).2

/-- Membership of a point passes to any reparametrization of it. -/
theorem memSubspace_comp {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : F' ⟶ F)
    {k : F ⟶ T.obj} {w : F ⟶ X.obj} {h : k ≫ p.toBase.hom = w ≫ f.hom}
    (h' : (φ ≫ k) ≫ p.toBase.hom = (φ ≫ w) ≫ f.hom)
    (hm : MemSubspace B S hS f p k w h) : MemSubspace B S hS f p (φ ≫ k) (φ ≫ w) h' := by
  obtain ⟨l, hfst, hsnd⟩ := (memSubspace_iff p k w h).1 hm
  exact (memSubspace_iff p (φ ≫ k) (φ ≫ w) h').2
    ⟨φ ≫ l, by rw [Category.assoc, hfst], by rw [Category.assoc, hsnd]⟩

/-- Membership of a point whose base component is the identity is the existence of a
factorization of the section it determines. -/
theorem memSubspace_id_iff {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) (w : T.obj ⟶ X.obj)
    (h : 𝟙 T.obj ≫ p.toBase.hom = w ≫ f.hom) :
    MemSubspace B S hS f p (𝟙 T.obj) w h ↔
      ∃ l : T.obj ⟶ p.subspace.toFunctor,
        l ≫ p.subspace.ι = pullback.lift (𝟙 T.obj) w h := by
  rw [memSubspace_iff]
  exact exists_congr fun l => (comp_ι_eq_lift_iff p l _ _ h).symm

/-- The condition that an arrow lies in a pair of Stacks 04PC is membership of the point it
determines. -/
theorem memSubspace_of_containsArrow {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) (z : T ⟶ X) (hz : z.hom ≫ f.hom = p.toBase.hom)
    (h : 𝟙 T.obj ≫ p.toBase.hom = z.hom ≫ f.hom)
    (hc : ContainsArrow B S hS f p z hz) : MemSubspace B S hS f p (𝟙 T.obj) z.hom h :=
  (memSubspace_id_iff p z.hom h).2 hc

/-- Membership of the point determined by an arrow is the condition that the arrow lies in the
pair. -/
theorem containsArrow_of_memSubspace {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) (z : T ⟶ X) (hz : z.hom ≫ f.hom = p.toBase.hom)
    (h : 𝟙 T.obj ≫ p.toBase.hom = z.hom ≫ f.hom)
    (hm : MemSubspace B S hS f p (𝟙 T.obj) z.hom h) : ContainsArrow B S hS f p z hz :=
  (memSubspace_id_iff p z.hom h).1 hm

/-- The condition that a pair of Stacks 04PC contains the section induced by `σ` is membership of
the point that section determines. -/
theorem memSubspace_of_containsSection {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y} {σ : Y ⟶ X}
    {hσ : σ.hom ≫ f.hom = 𝟙 Y.obj} (p : FiniteOpenSubspace B S hS f T)
    (h : 𝟙 T.obj ≫ p.toBase.hom = (p.toBase.hom ≫ σ.hom) ≫ f.hom)
    (hc : ContainsSection B S hS f σ hσ p) :
    MemSubspace B S hS f p (𝟙 T.obj) (p.toBase.hom ≫ σ.hom) h :=
  (memSubspace_id_iff p (p.toBase.hom ≫ σ.hom) h).2 hc

/-- Membership of the point induced by `σ` is the condition that the pair contains that
section. -/
theorem containsSection_of_memSubspace {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y} {σ : Y ⟶ X}
    {hσ : σ.hom ≫ f.hom = 𝟙 Y.obj} (p : FiniteOpenSubspace B S hS f T)
    (h : 𝟙 T.obj ≫ p.toBase.hom = (p.toBase.hom ≫ σ.hom) ≫ f.hom)
    (hm : MemSubspace B S hS f p (𝟙 T.obj) (p.toBase.hom ≫ σ.hom) h) :
    ContainsSection B S hS f σ hσ p :=
  (memSubspace_id_iff p (p.toBase.hom ≫ σ.hom) h).1 hm

/-- Membership descends along a cartesian square of pairs of Stacks 04PC: a point of the ambient
fibre product over the base which lies in the given pair, and whose base component factors
through the square, lies in the base-changed pair. -/
theorem memSubspace_of_isPullback {X Y T T' : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) (q : FiniteOpenSubspace B S hS f T')
    (g : T'.obj ⟶ T.obj) (j : q.subspace.toFunctor ⟶ p.subspace.toFunctor)
    (hpb : IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g
      (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom))
    (hsnd : j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
      q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ T'.obj) (w : F ⟶ X.obj)
    (hq : k ≫ q.toBase.hom = w ≫ f.hom)
    (hp : (k ≫ g) ≫ p.toBase.hom = w ≫ f.hom)
    (hm : MemSubspace B S hS f p (k ≫ g) w hp) : MemSubspace B S hS f q k w hq := by
  obtain ⟨n, hfst, hsnd'⟩ := (memSubspace_iff p (k ≫ g) w hp).1 hm
  refine (memSubspace_iff q k w hq).2 ⟨hpb.lift k n hfst.symm, ?_, ?_⟩
  · simpa only [Category.assoc] using hpb.lift_fst k n hfst.symm
  · rw [← hsnd, hpb.lift_snd_assoc, hsnd']

/-- Membership ascends along a cartesian square of pairs of Stacks 04PC: a point lying in the
base-changed pair lies, after composing its base component with the morphism of the square, in
the given pair. -/
theorem memSubspace_of_isPullback' {X Y T T' : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) (q : FiniteOpenSubspace B S hS f T')
    (g : T'.obj ⟶ T.obj) (j : q.subspace.toFunctor ⟶ p.subspace.toFunctor)
    (hpb : IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g
      (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom))
    (hsnd : j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
      q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ T'.obj) (w : F ⟶ X.obj)
    (hq : k ≫ q.toBase.hom = w ≫ f.hom)
    (hp : (k ≫ g) ≫ p.toBase.hom = w ≫ f.hom)
    (hm : MemSubspace B S hS f q k w hq) : MemSubspace B S hS f p (k ≫ g) w hp := by
  obtain ⟨l, hfst, hsnd'⟩ := (memSubspace_iff q k w hq).1 hm
  refine (memSubspace_iff p (k ≫ g) w hp).2 ⟨l ≫ j, ?_, ?_⟩
  · calc (l ≫ j) ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom
        = l ≫ (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) ≫ g := by
          simpa only [Category.assoc] using
            congrArg (fun m => l ≫ m) hpb.w.symm
      _ = (l ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) ≫ g := by
          simp only [Category.assoc]
      _ = k ≫ g := by rw [hfst]
  · rw [Category.assoc, hsnd, hsnd']

/-- Membership transports across a pair whose open subspace is the preimage of another one: the
point lies in the pair exactly when the point it is carried to lies in the other pair. -/
theorem memSubspace_preimage_iff {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p q : FiniteOpenSubspace B S hS f T)
    (φ : pullback q.toBase.hom f.hom ⟶ pullback p.toBase.hom f.hom)
    (hq : q.subspace = p.subspace.preimage φ)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ T.obj) (w : F ⟶ X.obj)
    (h : k ≫ q.toBase.hom = w ≫ f.hom) (k' : F ⟶ T.obj) (w' : F ⟶ X.obj)
    (h' : k' ≫ p.toBase.hom = w' ≫ f.hom)
    (hpt : pullback.lift k w h ≫ φ = pullback.lift k' w' h') :
    MemSubspace B S hS f q k w h ↔ MemSubspace B S hS f p k' w' h' := by
  change Subfunctor.range (pullback.lift k w h) ≤ q.subspace ↔
    Subfunctor.range (pullback.lift k' w' h') ≤ p.subspace
  rw [hq, ← Subfunctor.image_le_iff, ← Subfunctor.range_comp, hpt]

/-- The factorization, through the open subspace of a pair of Stacks 04PC, of a point that lies
in it. -/
noncomputable def memSubspaceLift {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ T.obj) (w : F ⟶ X.obj) (h : k ≫ p.toBase.hom = w ≫ f.hom)
    (hm : MemSubspace B S hS f p k w h) : F ⟶ p.subspace.toFunctor :=
  Subfunctor.lift (pullback.lift k w h) hm

/-- The factorization followed by the inclusion of the open subspace is the point itself. -/
theorem memSubspaceLift_ι {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ T.obj) (w : F ⟶ X.obj) (h : k ≫ p.toBase.hom = w ≫ f.hom)
    (hm : MemSubspace B S hS f p k w h) :
    memSubspaceLift p k w h hm ≫ p.subspace.ι = pullback.lift k w h :=
  Subfunctor.lift_ι _ _

/-- The base component of the factorization is the base component of the point. -/
theorem memSubspaceLift_fst {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ T.obj) (w : F ⟶ X.obj) (h : k ≫ p.toBase.hom = w ≫ f.hom)
    (hm : MemSubspace B S hS f p k w h) :
    memSubspaceLift p k w h hm ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom = k := by
  rw [← Category.assoc, memSubspaceLift_ι, pullback.lift_fst]

/-- The fibre component of the factorization is the fibre component of the point. -/
theorem memSubspaceLift_snd {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (p : FiniteOpenSubspace B S hS f T) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ T.obj) (w : F ⟶ X.obj) (h : k ≫ p.toBase.hom = w ≫ f.hom)
    (hm : MemSubspace B S hS f p k w h) :
    memSubspaceLift p k w h hm ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom = w := by
  rw [← Category.assoc, memSubspaceLift_ι, pullback.lift_snd]

/-- A point of the ambient fibre product over an algebraic space naming pairs of Stacks 04PC lies
in the named pair as soon as it does at every scheme-valued point.

This is the direction of the dictionary that produces a point of `Z_univ`: the hypothesis is that
at every scheme-valued point the arrow lies in the collection which that point names, and the
conclusion is membership in the universal open subspace. The collection and the arrow are taken
as parameters together with equations naming them, so that a consumer may present them in
whatever form is convenient. -/
theorem memSubspace_of_pointwise {X Y T : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (incl : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (p : FiniteOpenSubspace B S hS f T)
    (hp : p = (finiteOpenSubspaceEquiv B S hS f T).1 incl)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ T.obj) (w : F ⟶ X.obj)
    (h : k ≫ p.toBase.hom = w ≫ f.hom)
    (hmem : ∀ (V : BigFppfOver B S hS) (y : (schemeSpace V).obj ⟶ F)
      (x : (finiteOpenSubspacePresheaf B S hS f).toFunctor.obj (op V))
      (_ : x = incl.app (op V) (yonedaEquiv (y ≫ k)))
      (w' : (schemeSpace V).obj ⟶ X.obj) (_ : w' = y ≫ w)
      (hy : 𝟙 (schemeSpace V).obj ≫
        ((finiteOpenSubspacePresheaf B S hS f).sections V x).toBase.hom = w' ≫ f.hom),
      MemSubspace B S hS f ((finiteOpenSubspacePresheaf B S hS f).sections V x)
        (𝟙 _) w' hy) :
    MemSubspace B S hS f p k w h := by
  subst hp
  intro V x hx
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨hb, j, hpb, hjsnd⟩ :=
    (finiteOpenSubspaceEquiv B S hS f T).2 incl V.unop (yonedaEquiv.symm a ≫ k)
  have hassoc : (yonedaEquiv.symm a ≫ k) ≫
      ((finiteOpenSubspaceEquiv B S hS f T).1 incl).toBase.hom =
      (yonedaEquiv.symm a ≫ w) ≫ f.hom := by
    simp only [Category.assoc, h]
  have hid : (𝟙 _ ≫ (yonedaEquiv.symm a ≫ k)) ≫
      ((finiteOpenSubspaceEquiv B S hS f T).1 incl).toBase.hom =
      (yonedaEquiv.symm a ≫ w) ≫ f.hom := by
    rwa [Category.id_comp]
  have hy := (Category.id_comp _).trans (hb.trans hassoc)
  have hstep := memSubspace_of_isPullback' ((finiteOpenSubspaceEquiv B S hS f T).1 incl) _
    (yonedaEquiv.symm a ≫ k) j hpb hjsnd (𝟙 _) (yonedaEquiv.symm a ≫ w) hy hid
    (hmem V.unop (yonedaEquiv.symm a) _ rfl _ rfl hy)
  obtain ⟨l, hfst, hsnd⟩ :=
    (memSubspace_iff ((finiteOpenSubspaceEquiv B S hS f T).1 incl) _
      (yonedaEquiv.symm a ≫ w) hid).1 hstep
  have hl : l ≫ ((finiteOpenSubspaceEquiv B S hS f T).1 incl).subspace.ι =
      yonedaEquiv.symm a ≫ pullback.lift k w h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfst, Category.id_comp, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, hsnd, Category.assoc, pullback.lift_snd]
  rw [show (pullback.lift k w h).app V a =
      yonedaEquiv (yonedaEquiv.symm a ≫ pullback.lift k w h) by
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply], ← hl]
  exact (yonedaEquiv l).2

/-- A point of the ambient fibre product over an algebraic space naming pairs of Stacks 04PC
which lies in the named pair lies, at every scheme-valued point, in the pair named there.

This is the direction of the dictionary that reads clause (3) of Stacks 04RT off a point of
`Z_univ`. -/
theorem memSubspace_sections {X Y T : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (incl : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (p : FiniteOpenSubspace B S hS f T)
    (hp : p = (finiteOpenSubspaceEquiv B S hS f T).1 incl)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ T.obj) (w : F ⟶ X.obj)
    (h : k ≫ p.toBase.hom = w ≫ f.hom) (hm : MemSubspace B S hS f p k w h)
    (V : BigFppfOver B S hS) (y : (schemeSpace V).obj ⟶ F)
    (x : (finiteOpenSubspacePresheaf B S hS f).toFunctor.obj (op V))
    (hx : x = incl.app (op V) (yonedaEquiv (y ≫ k)))
    (w' : (schemeSpace V).obj ⟶ X.obj) (hw' : w' = y ≫ w)
    (hy : 𝟙 (schemeSpace V).obj ≫
      ((finiteOpenSubspacePresheaf B S hS f).sections V x).toBase.hom = w' ≫ f.hom) :
    MemSubspace B S hS f ((finiteOpenSubspacePresheaf B S hS f).sections V x) (𝟙 _) w' hy := by
  subst hp hx hw'
  obtain ⟨hb, j, hpb, hjsnd⟩ := (finiteOpenSubspaceEquiv B S hS f T).2 incl V (y ≫ k)
  have hassoc : (y ≫ k) ≫ ((finiteOpenSubspaceEquiv B S hS f T).1 incl).toBase.hom =
      (y ≫ w) ≫ f.hom := by
    simp only [Category.assoc, h]
  have hid : (𝟙 _ ≫ (y ≫ k)) ≫
      ((finiteOpenSubspaceEquiv B S hS f T).1 incl).toBase.hom = (y ≫ w) ≫ f.hom := by
    rwa [Category.id_comp]
  exact memSubspace_of_isPullback ((finiteOpenSubspaceEquiv B S hS f T).1 incl) _
    (y ≫ k) j hpb hjsnd (𝟙 _) (y ≫ w) hy hid <|
    memSubspace_congr _ (Category.id_comp (y ≫ k)).symm rfl
      (memSubspace_comp _ y hassoc hm)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

/-- A family of arrows composed with its own inverse on the left is the unit at its source. -/
theorem composeHom_self_inverse {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (β : F ⟶ G.arrows.obj)
    (h : (β ≫ (inverseHom G).hom) ≫ G.source.hom = β ≫ G.target.hom) :
    composeHom (β ≫ (inverseHom G).hom) β h = β ≫ G.source.hom ≫ (identityHom G).hom := by
  ext V x
  exact (G.toGroupoidInFunctors.pointwiseData V).comp_inverseArrow_fst (β.app V x) _

variable {T : AlgebraicSpaces C S hS} {a b : T ⟶ G.objects}

/-- The point `(k, w)` of the translated ambient fibre product is carried by `c(-, z)` to the
point whose arrow component is the composite `w ∘ z`. -/
theorem translateBwd_lift_point (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = a.hom)
    (hzt : z.hom ≫ G.target.hom = b.hom) {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ T.obj) (w : F ⟶ G.arrows.obj) (h : k ≫ b.hom = w ≫ G.source.hom)
    (hc : w ≫ G.source.hom = (k ≫ z.hom) ≫ G.target.hom)
    (h' : k ≫ a.hom = composeHom w (k ≫ z.hom) hc ≫ G.source.hom) :
    pullback.lift k w h ≫ translateBwd z hzs hzt =
      pullback.lift k (composeHom w (k ≫ z.hom) hc) h' := by
  apply pullback.hom_ext
  · rw [Category.assoc, translateBwd_fst, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, translateBwd_snd, pullback.lift_snd]
    exact composeHom_comp_left (pullback.lift k w h) (translateBwd_condition z hzt)
      (pullback.lift_snd _ _ _)
      (by rw [← Category.assoc, pullback.lift_fst]) hc

/-- **The subfunctor-level form of the membership criterion of Stacks 04RS.** An arrow lies in
the translated collection `c(Z, i ∘ z)` exactly when its composite with `z` lies in `Z`.

Pointwise this is the computation that `w = z' ∘ z⁻¹` for some `z'` of the collection exactly
when `w ∘ z` is in the collection; here it is the equality of the open subspace of the translated
pair with the preimage of the original one, together with the computation of the translated point
by the inverse of the ambient isomorphism `c(-, i ∘ z)`. -/
theorem memSubspace_translatePair_iff (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hz : z.hom ≫ G.source.hom = p.toBase.hom)
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ T.obj) (w : F ⟶ G.arrows.obj)
    (h : k ≫ (z ≫ G.target).hom = w ≫ G.source.hom)
    (hc : w ≫ G.source.hom = (k ≫ z.hom) ≫ G.target.hom)
    (h' : k ≫ p.toBase.hom = composeHom w (k ≫ z.hom) hc ≫ G.source.hom) :
    Space.MemSubspace C S hS G.source (translatePair p z hz) k w h ↔
      Space.MemSubspace C S hS G.source p k (composeHom w (k ≫ z.hom) hc) h' :=
  Space.memSubspace_preimage_iff p (translatePair p z hz)
    (translateAmbientIso (b := z ≫ G.target) z hz rfl).inv
    (translatePair_subspace p z hz) k w h k (composeHom w (k ≫ z.hom) hc) h'
    (translateBwd_lift_point (b := z ≫ G.target) z hz rfl k w h hc h')

namespace FinitePart

variable (fp : FinitePart G)

/-- **Stacks 04RT, clause (1b), for every point of `U'`.** The collection named by a point of the
object space of the finite part contains the unit at its base point.

This is what the identification of `U'` with the subfunctor of Stacks 04RR says: a point of `U'`
is a pair whose open subspace contains the base change of the unit, and the pair it names over an
algebraic space is determined by the pairs it names over the schemes of the site. -/
theorem containsSection_named (W : AlgebraicSpaces C S hS) (v : W.obj ⟶ fp.objects.obj) :
    Space.ContainsSection C S hS G.source (identityHom G) (identityHom_comp_source G)
      ((Space.finiteOpenSubspaceEquiv C S hS G.source W).1 (v ≫ fp.inclusion)) := by
  refine Space.containsSection_of_pointwise C S hS G.source (identityHom G)
    (identityHom_comp_source G) W _
    (fun V y => (Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
      ((v ≫ fp.inclusion).app (op V) (yonedaEquiv y)))
    (fun V y => ((Space.finiteOpenSubspaceEquiv C S hS G.source W).2
      (v ≫ fp.inclusion) V y).1)
    (fun V y => ((Space.finiteOpenSubspaceEquiv C S hS G.source W).2
      (v ≫ fp.inclusion) V y).2)
    (fun V y => ?_)
  have hx : (v ≫ fp.inclusion).app (op V) (yonedaEquiv y) =
      fp.inclusion.app (op V) (yonedaEquiv (y ≫ v)) := rfl
  rw [hx]
  refine ((Space.finitePartWithSection C S hS G.source (identityHom G)
    (identityHom_comp_source G)).mem_iff V _).1 ?_
  rw [← fp.range_inclusion]
  exact ⟨yonedaEquiv (y ≫ v), rfl⟩

/-- The base morphism of the collection named at a scheme-valued point of `U'`. -/
theorem toBase_sections (V : BigFppfOver C S hS)
    (m : (schemeSpace V).obj ⟶ fp.objects.obj) :
    ((Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
        (fp.inclusion.app (op V) (yonedaEquiv m))).toBase.hom = m ≫ fp.pair.toBase.hom := by
  have h := ((Space.finiteOpenSubspaceEquiv C S hS G.source fp.objects).2 fp.inclusion V m).1
  rwa [← fp.pair_eq] at h

/-- **Stacks 04RT, clause (3), tautologically.** The tautological point of `Z_univ` lies in
`Z_univ`: the point with components `s'` and the tautological arrow is the inclusion of `Z_univ`
into the ambient fibre product. -/
theorem memSubspace_pair :
    Space.MemSubspace C S hS G.source fp.pair fp.sourceHom fp.arrowHom
      fp.sourceHom_comp_toBase := by
  have hlift : pullback.lift fp.sourceHom fp.arrowHom fp.sourceHom_comp_toBase =
      fp.pair.subspace.ι :=
    pullback.hom_ext ((pullback.lift_fst _ _ _).trans (sourceHom_eq fp))
      ((pullback.lift_snd _ _ _).trans (arrowHom_eq fp))
  rw [Space.MemSubspace, hlift, Subfunctor.range_ι]

/-! ### The unit of the finite part -/

/-- The unit rule lies over the source morphism of the groupoid. -/
theorem unit_condition : 𝟙 fp.objects.obj ≫ fp.pair.toBase.hom =
    (fp.pair.toBase.hom ≫ (identityHom G).hom) ≫ G.source.hom := by
  rw [Category.id_comp, Category.assoc, identityHom_comp_source, Category.comp_id]

/-- **Stacks 04RT, the unit `e'`.** The morphism `e' : U' ⟶ Z_univ` given by the rule
`(u, Z) ↦ (u, Z, e ∘ u)`.

It lands in `Z_univ` because the collection of a point of `U'` contains the unit at its base
point, which is the clause that makes `U'` the finite part containing the unit. -/
noncomputable def unitHom : fp.objects.obj ⟶ fp.pair.subspace.toFunctor :=
  Space.memSubspaceLift fp.pair (𝟙 fp.objects.obj)
    (fp.pair.toBase.hom ≫ (identityHom G).hom) (unit_condition fp)
    (Space.memSubspace_of_containsSection fp.pair (unit_condition fp) fp.containsUnit)

/-- The unit of the finite part is a section of the source morphism of the finite part. -/
theorem unitHom_comp_sourceHom : unitHom fp ≫ fp.sourceHom = 𝟙 fp.objects.obj :=
  Space.memSubspaceLift_fst fp.pair _ _ _ _

/-- The arrow of the unit of the finite part is the unit of the groupoid. -/
theorem unitHom_comp_arrowHom :
    unitHom fp ≫ fp.arrowHom = fp.pair.toBase.hom ≫ (identityHom G).hom :=
  Space.memSubspaceLift_snd fp.pair _ _ _ _

/-! ### The inverse and the composition of the finite part -/

/-- The composability datum of the inverse rule: the inverse of an arrow has the target of the
arrow as its source. -/
theorem inverse_composable :
    (fp.arrowHom ≫ (inverseHom G).hom) ≫ G.source.hom =
      (𝟙 (arrowSpace fp).obj ≫ fp.arrowHom) ≫ G.target.hom := by
  rw [Category.assoc, inverseHom_comp_source, Category.id_comp]

/-- The inverse rule lies over the translated collection. -/
theorem inverse_targetPair_condition :
    𝟙 (arrowSpace fp).obj ≫ (targetPair fp).toBase.hom =
      (fp.arrowHom ≫ (inverseHom G).hom) ≫ G.source.hom := by
  rw [Category.id_comp, Category.assoc, inverseHom_comp_source]
  rfl

/-- The arrow which the inverse rule composes back into the original collection. -/
theorem inverse_sourcePair_condition :
    𝟙 (arrowSpace fp).obj ≫ (sourcePair fp).toBase.hom =
      composeHom (fp.arrowHom ≫ (inverseHom G).hom) (𝟙 (arrowSpace fp).obj ≫ fp.arrowHom)
        (inverse_composable fp) ≫ G.source.hom := by
  rw [composeHom_comp_source]
  simp only [Category.id_comp]
  exact (arrowMap_comp_source fp).symm

/-- **Stacks 04RT, the inverse rule lands in `Z_univ`.** The arrow `i ∘ z` lies in the translated
collection `c(Z, i ∘ z)`, because composing it with `z` gives the unit at the base point of `Z`,
which lies in `Z`. -/
theorem memSubspace_targetPair_inverse :
    Space.MemSubspace C S hS G.source (targetPair fp) (𝟙 (arrowSpace fp).obj)
      (fp.arrowHom ≫ (inverseHom G).hom) (inverse_targetPair_condition fp) := by
  have hiv : (fp.arrowHom ≫ (inverseHom G).hom) ≫ G.source.hom =
      fp.arrowHom ≫ G.target.hom := by
    rw [Category.assoc, inverseHom_comp_source]
  have hcc := (composeHom_congr rfl (Category.id_comp fp.arrowHom)
    (inverse_composable fp) hiv).trans (composeHom_self_inverse fp.arrowHom hiv)
  have hu : 𝟙 (arrowSpace fp).obj ≫ (sourcePair fp).toBase.hom =
      ((sourcePair fp).toBase.hom ≫ (identityHom G).hom) ≫ G.source.hom := by
    rw [Category.id_comp, Category.assoc, identityHom_comp_source, Category.comp_id]
  have hw : (sourcePair fp).toBase.hom ≫ (identityHom G).hom =
      composeHom (fp.arrowHom ≫ (inverseHom G).hom) (𝟙 (arrowSpace fp).obj ≫ fp.arrowHom)
        (inverse_composable fp) :=
    (congrArg (fun m => m ≫ (identityHom G).hom) (arrowMap_comp_source fp).symm).trans
      ((Category.assoc fp.arrowHom G.source.hom (identityHom G).hom).trans hcc.symm)
  refine (memSubspace_translatePair_iff (sourcePair fp) (arrowMap fp) (arrowMap_comp_source fp)
    (𝟙 (arrowSpace fp).obj) (fp.arrowHom ≫ (inverseHom G).hom)
    (inverse_targetPair_condition fp) (inverse_composable fp)
    (inverse_sourcePair_condition fp)).2 ?_
  exact Space.memSubspace_congr (sourcePair fp) rfl hw
    (Space.memSubspace_of_containsSection (sourcePair fp) hu
      (containsSection_named fp (arrowSpace fp) fp.sourceHom))

variable (t' : fp.pair.subspace.toFunctor ⟶ fp.objects.obj)
  (ht' : t' ≫ fp.inclusion = targetSection fp)

include ht'

/-- A morphism of `Z_univ` into `U'` which names the translated collections lies over the target
morphism of the groupoid. -/
theorem comp_toBase_of_targetSection :
    t' ≫ fp.pair.toBase.hom = fp.arrowHom ≫ G.target.hom := by
  calc t' ≫ fp.pair.toBase.hom
      = t' ≫ fp.inclusion ≫ (Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap :=
        congrArg (fun m => t' ≫ m) fp.toBase_pair
    _ = targetSection fp ≫ (Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap := by
        rw [← Category.assoc, ht']
    _ = ((Space.finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)).1
          (targetSection fp)).toBase.hom :=
        (Space.toBase_finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)
          (targetSection fp)).symm
    _ = (targetPair fp).toBase.hom :=
        congrArg (fun q : Space.FiniteOpenSubspace C S hS G.source (arrowSpace fp) =>
          q.toBase.hom) (targetSection_spec fp)
    _ = fp.arrowHom ≫ G.target.hom := rfl

/-- At a scheme-valued point of `Z_univ`, the collection named by that point through `t'` is the
one named by the translated section. -/
theorem sections_targetSection (V : BigFppfOver C S hS)
    (m : (schemeSpace V).obj ⟶ fp.pair.subspace.toFunctor) :
    fp.inclusion.app (op V) (yonedaEquiv (m ≫ t')) =
      (targetSection fp).app (op V) (yonedaEquiv m) :=
  congrArg (fun α : fp.pair.subspace.toFunctor ⟶
      (Space.finiteOpenSubspacePresheaf C S hS G.source).toFunctor =>
    α.app (op V) (yonedaEquiv m)) ht'

/-- The inverse rule lies over the source morphism of the groupoid. -/
theorem inverse_condition :
    t' ≫ fp.pair.toBase.hom = (fp.arrowHom ≫ (inverseHom G).hom) ≫ G.source.hom := by
  rw [comp_toBase_of_targetSection fp t' ht', Category.assoc, inverseHom_comp_source]

/-- **Stacks 04RT, the inverse rule lands in `Z_univ`, over `Z_univ`.** -/
theorem memSubspace_inverse :
    Space.MemSubspace C S hS G.source fp.pair t' (fp.arrowHom ≫ (inverseHom G).hom)
      (inverse_condition fp t' ht') := by
  refine Space.memSubspace_of_pointwise G.source fp.inclusion fp.pair fp.pair_eq
    t' (fp.arrowHom ≫ (inverseHom G).hom) (inverse_condition fp t' ht') ?_
  intro V y x hx w' hw' hy
  refine Space.memSubspace_sections G.source (targetSection fp) (targetPair fp)
    (targetSection_spec fp).symm (𝟙 (arrowSpace fp).obj)
    (fp.arrowHom ≫ (inverseHom G).hom) (inverse_targetPair_condition fp)
    (memSubspace_targetPair_inverse fp) V y x ?_ w' hw' hy
  exact hx.trans <| (sections_targetSection fp t' ht' V y).trans <|
    congrArg (fun m : (schemeSpace V).obj ⟶ fp.pair.subspace.toFunctor =>
      (targetSection fp).app (op V) (yonedaEquiv m)) (Category.comp_id y).symm

/-- **Stacks 04RT, the inverse `i'`.** The morphism `i' : Z_univ ⟶ Z_univ` given by the rule
`(u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z), i ∘ z)`: its first two components are the translation `t'` and
its arrow is the inverse of the tautological arrow. -/
noncomputable def invHom : fp.pair.subspace.toFunctor ⟶ fp.pair.subspace.toFunctor :=
  Space.memSubspaceLift fp.pair t' (fp.arrowHom ≫ (inverseHom G).hom)
    (inverse_condition fp t' ht') (memSubspace_inverse fp t' ht')

/-- The source of the inverse of a point of `Z_univ` is its target. -/
theorem invHom_comp_sourceHom : invHom fp t' ht' ≫ fp.sourceHom = t' :=
  Space.memSubspaceLift_fst fp.pair _ _ _ _

/-- The arrow of the inverse of a point of `Z_univ` is the inverse of its arrow. -/
theorem invHom_comp_arrowHom :
    invHom fp t' ht' ≫ fp.arrowHom = fp.arrowHom ≫ (inverseHom G).hom :=
  Space.memSubspaceLift_snd fp.pair _ _ _ _

/-- The two tautological arrows over the fibre product `Z_univ ×_{s', U', t'} Z_univ` are
composable: the source of the first is the base point of the collection of the second translated
by its arrow, which is the target of the second. -/
theorem composable_compose :
    (pullback.fst fp.sourceHom t' ≫ fp.arrowHom) ≫ G.source.hom =
      (pullback.snd fp.sourceHom t' ≫ fp.arrowHom) ≫ G.target.hom := by
  calc (pullback.fst fp.sourceHom t' ≫ fp.arrowHom) ≫ G.source.hom
      = (pullback.fst fp.sourceHom t' ≫ fp.sourceHom) ≫ fp.pair.toBase.hom := by
        simp only [Category.assoc, fp.sourceHom_comp_toBase]
    _ = (pullback.snd fp.sourceHom t' ≫ t') ≫ fp.pair.toBase.hom := by
        rw [pullback.condition]
    _ = (pullback.snd fp.sourceHom t' ≫ fp.arrowHom) ≫ G.target.hom := by
        simp only [Category.assoc, comp_toBase_of_targetSection fp t' ht']

/-- The composition rule lies over the source morphism of the groupoid. -/
theorem compose_condition :
    (pullback.snd fp.sourceHom t' ≫ fp.sourceHom) ≫ fp.pair.toBase.hom =
      composeHom (pullback.fst fp.sourceHom t' ≫ fp.arrowHom)
        (pullback.snd fp.sourceHom t' ≫ fp.arrowHom) (composable_compose fp t' ht') ≫
        G.source.hom := by
  rw [composeHom_comp_source]
  simp only [Category.assoc, fp.sourceHom_comp_toBase]

/-- **Stacks 04RT, the composition rule lands in `Z_univ`, at a scheme-valued point.**

At a scheme-valued point of the fibre product, the first collection is the translation of the
second by the second arrow, because the first point's source and the second point's target agree
in `U'`. The first arrow lies in the first collection by clause (3), so its composite with the
second arrow lies in the second collection, which is the criterion of Stacks 04RS. -/
theorem memSubspace_sections_compose (V : BigFppfOver C S hS)
    (k₁ k₂ : (schemeSpace V).obj ⟶ fp.pair.subspace.toFunctor)
    (hk : k₂ ≫ t' = k₁ ≫ fp.sourceHom)
    (hc : (k₁ ≫ fp.arrowHom) ≫ G.source.hom = (k₂ ≫ fp.arrowHom) ≫ G.target.hom)
    (x : (Space.finiteOpenSubspacePresheaf C S hS G.source).toFunctor.obj (op V))
    (hx : x = fp.inclusion.app (op V) (yonedaEquiv (k₂ ≫ fp.sourceHom)))
    (w' : (schemeSpace V).obj ⟶ G.arrows.obj)
    (hw' : w' = composeHom (k₁ ≫ fp.arrowHom) (k₂ ≫ fp.arrowHom) hc)
    (hy : 𝟙 (schemeSpace V).obj ≫
      ((Space.finiteOpenSubspacePresheaf C S hS G.source).sections V x).toBase.hom =
        w' ≫ G.source.hom) :
    Space.MemSubspace C S hS G.source
      ((Space.finiteOpenSubspacePresheaf C S hS G.source).sections V x) (𝟙 _) w' hy := by
  subst hx hw'
  have hy1 : 𝟙 (schemeSpace V).obj ≫
      ((Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
        (fp.inclusion.app (op V) (yonedaEquiv (k₂ ≫ t')))).toBase.hom =
      (k₁ ≫ fp.arrowHom) ≫ G.source.hom := by
    refine (Category.id_comp _).trans ((toBase_sections fp V (k₂ ≫ t')).trans ?_)
    rw [hk]
    simp only [Category.assoc, fp.sourceHom_comp_toBase]
  have h1 := Space.memSubspace_sections G.source fp.inclusion fp.pair fp.pair_eq
    fp.sourceHom fp.arrowHom fp.sourceHom_comp_toBase (memSubspace_pair fp) V k₁ _
    (congrArg (fun m => fp.inclusion.app (op V) (yonedaEquiv m)) hk) _ rfl hy1
  have hT : k₂ ≫ (arrowMap fp ≫ G.target).hom = (k₁ ≫ fp.arrowHom) ≫ G.source.hom := by
    rw [hc]
    exact (Category.assoc k₂ fp.arrowHom G.target.hom).symm
  have hid : (𝟙 _ ≫ k₂) ≫ (arrowMap fp ≫ G.target).hom =
      (k₁ ≫ fp.arrowHom) ≫ G.source.hom := by
    rwa [Category.id_comp]
  have hSrc : k₂ ≫ (sourcePair fp).toBase.hom =
      composeHom (k₁ ≫ fp.arrowHom) (k₂ ≫ fp.arrowHom) hc ≫ G.source.hom := by
    rw [composeHom_comp_source, ← arrowMap_comp_source fp]
    exact (Category.assoc k₂ fp.arrowHom G.source.hom).symm
  have hSrc' : (𝟙 _ ≫ k₂) ≫ (sourcePair fp).toBase.hom =
      composeHom (k₁ ≫ fp.arrowHom) (k₂ ≫ fp.arrowHom) hc ≫ G.source.hom := by
    rwa [Category.id_comp]
  have hspec := (Space.finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)).2
    (targetSection fp) V k₂
  rw [targetSection_spec, ← sections_targetSection fp t' ht' V k₂] at hspec
  obtain ⟨hbt, jt, hpbt, hjsndt⟩ := hspec
  have h2 := Space.memSubspace_of_isPullback' (targetPair fp) _ k₂ jt hpbt hjsndt
    (𝟙 _) (k₁ ≫ fp.arrowHom) hy1 hid h1
  have h4 := (memSubspace_translatePair_iff (sourcePair fp) (arrowMap fp)
    (arrowMap_comp_source fp) k₂ (k₁ ≫ fp.arrowHom) hT hc hSrc).1
    (Space.memSubspace_congr (targetPair fp) (Category.id_comp k₂) rfl h2)
  obtain ⟨hbs, js, hpbs, hjsnds⟩ := (Space.finiteOpenSubspaceEquiv C S hS G.source
    (arrowSpace fp)).2 (fp.sourceHom ≫ fp.inclusion) V k₂
  exact Space.memSubspace_of_isPullback (sourcePair fp) _ k₂ js hpbs hjsnds (𝟙 _) _ hy hSrc'
    (Space.memSubspace_congr (sourcePair fp) (Category.id_comp k₂).symm rfl h4)

/-- **Stacks 04RT, the composition rule lands in `Z_univ`.** -/
theorem memSubspace_compose :
    Space.MemSubspace C S hS G.source fp.pair
      (pullback.snd fp.sourceHom t' ≫ fp.sourceHom)
      (composeHom (pullback.fst fp.sourceHom t' ≫ fp.arrowHom)
        (pullback.snd fp.sourceHom t' ≫ fp.arrowHom) (composable_compose fp t' ht'))
      (compose_condition fp t' ht') := by
  refine Space.memSubspace_of_pointwise G.source fp.inclusion fp.pair fp.pair_eq _ _
    (compose_condition fp t' ht') ?_
  intro V y x hx w' hw' hy
  have hk : (y ≫ pullback.snd fp.sourceHom t') ≫ t' =
      (y ≫ pullback.fst fp.sourceHom t') ≫ fp.sourceHom := by
    simp only [Category.assoc, pullback.condition]
  have hcpt : ((y ≫ pullback.fst fp.sourceHom t') ≫ fp.arrowHom) ≫ G.source.hom =
      ((y ≫ pullback.snd fp.sourceHom t') ≫ fp.arrowHom) ≫ G.target.hom := by
    simpa only [Category.assoc] using congrArg (y ≫ ·) (composable_compose fp t' ht')
  refine memSubspace_sections_compose fp t' ht' V (y ≫ pullback.fst fp.sourceHom t')
    (y ≫ pullback.snd fp.sourceHom t') hk hcpt x ?_ w' ?_ hy
  · exact hx.trans (congrArg (fun m : (schemeSpace V).obj ⟶ fp.objects.obj =>
      fp.inclusion.app (op V) (yonedaEquiv m))
      (Category.assoc y (pullback.snd fp.sourceHom t') fp.sourceHom).symm)
  · exact hw'.trans (composeHom_comp_left y (composable_compose fp t' ht')
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm hcpt)

/-- **Stacks 04RT, the composition `c'`.** The morphism
`c' : Z_univ ×_{s', U', t'} Z_univ ⟶ Z_univ` given by the rule
`((u₁, Z₁, z₁), (u₂, Z₂, z₂)) ↦ (u₂, Z₂, z₁ ∘ z₂)`.

The collection that survives is the second one, and the arrow is the composite of the two
arrows; the point lands in `Z_univ` because the composite lies in the second collection. -/
noncomputable def compHom : pullback fp.sourceHom t' ⟶ fp.pair.subspace.toFunctor :=
  Space.memSubspaceLift fp.pair (pullback.snd fp.sourceHom t' ≫ fp.sourceHom)
    (composeHom (pullback.fst fp.sourceHom t' ≫ fp.arrowHom)
      (pullback.snd fp.sourceHom t' ≫ fp.arrowHom) (composable_compose fp t' ht'))
    (compose_condition fp t' ht') (memSubspace_compose fp t' ht')

/-- The source of a composite of two points of `Z_univ` is the source of the second. -/
theorem compHom_comp_sourceHom :
    compHom fp t' ht' ≫ fp.sourceHom = pullback.snd fp.sourceHom t' ≫ fp.sourceHom :=
  Space.memSubspaceLift_fst fp.pair _ _ _ _

/-- The arrow of a composite of two points of `Z_univ` is the composite of the two arrows. -/
theorem compHom_comp_arrowHom :
    compHom fp t' ht' ≫ fp.arrowHom =
      composeHom (pullback.fst fp.sourceHom t' ≫ fp.arrowHom)
        (pullback.snd fp.sourceHom t' ≫ fp.arrowHom) (composable_compose fp t' ht') :=
  Space.memSubspaceLift_snd fp.pair _ _ _ _

end FinitePart

/-! ### The remaining structure morphisms of the constructed finite part -/

variable (hsep : Space.IsSeparated C S hS G.source.hom)
  (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom)

/-- **Stacks 04RT, the unit `e'`.** The morphism `e' : U' ⟶ Z_univ` of the finite part of a
groupoid in algebraic spaces whose source morphism is separated and locally of finite type: the
rule `(u, Z) ↦ (u, Z, e ∘ u)`. -/
noncomputable def unitHom :
    (finitePart G hsep hft).objects.obj ⟶ (finitePart G hsep hft).pair.subspace.toFunctor :=
  FinitePart.unitHom (finitePart G hsep hft)

/-- **Stacks 04RT, the inverse `i'`.** The morphism `i' : Z_univ ⟶ Z_univ` of the finite part of
a groupoid in algebraic spaces whose source morphism is separated and locally of finite type: the
rule `(u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z), i ∘ z)`, whose first two components are the target
morphism `t'`. -/
noncomputable def invHom :
    (finitePart G hsep hft).pair.subspace.toFunctor ⟶
      (finitePart G hsep hft).pair.subspace.toFunctor :=
  FinitePart.invHom (finitePart G hsep hft) (targetHom hsep hft)
    (targetHom_comp_inclusion hsep hft)

/-- **Stacks 04RT, the composition `c'`.** The morphism
`c' : Z_univ ×_{s', U', t'} Z_univ ⟶ Z_univ` of the finite part of a groupoid in algebraic spaces
whose source morphism is separated and locally of finite type: the rule
`((u₁, Z₁, z₁), (u₂, Z₂, z₂)) ↦ (u₂, Z₂, z₁ ∘ z₂)`.

The domain is the fibre product of the source morphism `s'` and the target morphism `t'` of the
finite part, which is the underlying presheaf of the fibre product of algebraic spaces; the
collection that survives is the second one. -/
noncomputable def compHom :
    pullback (FinitePart.sourceHom (finitePart G hsep hft)) (targetHom hsep hft) ⟶
      (finitePart G hsep hft).pair.subspace.toFunctor :=
  FinitePart.compHom (finitePart G hsep hft) (targetHom hsep hft)
    (targetHom_comp_inclusion hsep hft)

/-- The unit of the finite part is a section of its source morphism. -/
theorem unitHom_comp_sourceHom :
    unitHom hsep hft ≫ FinitePart.sourceHom (finitePart G hsep hft) =
      𝟙 (finitePart G hsep hft).objects.obj :=
  FinitePart.unitHom_comp_sourceHom (finitePart G hsep hft)

/-- The arrow of the unit of the finite part is the unit of the groupoid. -/
theorem unitHom_comp_arrowHom :
    unitHom hsep hft ≫ (finitePart G hsep hft).arrowHom =
      (finitePart G hsep hft).pair.toBase.hom ≫ (identityHom G).hom :=
  FinitePart.unitHom_comp_arrowHom (finitePart G hsep hft)

/-- The source of the inverse of a point of `Z_univ` is its target. -/
theorem invHom_comp_sourceHom :
    invHom hsep hft ≫ FinitePart.sourceHom (finitePart G hsep hft) = targetHom hsep hft :=
  FinitePart.invHom_comp_sourceHom (finitePart G hsep hft) (targetHom hsep hft)
    (targetHom_comp_inclusion hsep hft)

/-- The arrow of the inverse of a point of `Z_univ` is the inverse of its arrow. -/
theorem invHom_comp_arrowHom :
    invHom hsep hft ≫ (finitePart G hsep hft).arrowHom =
      (finitePart G hsep hft).arrowHom ≫ (inverseHom G).hom :=
  FinitePart.invHom_comp_arrowHom (finitePart G hsep hft) (targetHom hsep hft)
    (targetHom_comp_inclusion hsep hft)

/-- The source of a composite of two points of `Z_univ` is the source of the second. -/
theorem compHom_comp_sourceHom :
    compHom hsep hft ≫ FinitePart.sourceHom (finitePart G hsep hft) =
      pullback.snd (FinitePart.sourceHom (finitePart G hsep hft)) (targetHom hsep hft) ≫
        FinitePart.sourceHom (finitePart G hsep hft) :=
  FinitePart.compHom_comp_sourceHom (finitePart G hsep hft) (targetHom hsep hft)
    (targetHom_comp_inclusion hsep hft)

/-- The arrow of a composite of two points of `Z_univ` is the composite of the two arrows. -/
theorem compHom_comp_arrowHom :
    compHom hsep hft ≫ (finitePart G hsep hft).arrowHom =
      composeHom
        (pullback.fst (FinitePart.sourceHom (finitePart G hsep hft)) (targetHom hsep hft) ≫
          (finitePart G hsep hft).arrowHom)
        (pullback.snd (FinitePart.sourceHom (finitePart G hsep hft)) (targetHom hsep hft) ≫
          (finitePart G hsep hft).arrowHom)
        (FinitePart.composable_compose (finitePart G hsep hft) (targetHom hsep hft)
          (targetHom_comp_inclusion hsep hft)) :=
  FinitePart.compHom_comp_arrowHom (finitePart G hsep hft) (targetHom hsep hft)
    (targetHom_comp_inclusion hsep hft)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
