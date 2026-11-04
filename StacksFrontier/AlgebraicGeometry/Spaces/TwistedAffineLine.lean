module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Scheme.ClopenIdempotent
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal

/-!
# The affine line twisted along an étale equivalence relation

Let `s, t : R ⟶ W` be an étale equivalence relation on an object `W` of the big fppf site of a
scheme `S`, and let `e` be an idempotent global section of `R` which behaves like a cocycle with
values in `ℤ/2`. That is, `e` vanishes on the diagonal, is invariant under the symmetry of the
relation, and is additive (as an exclusive or) along composition. Twisting the affine line over
`W` by the involution `t ↦ 1 - t` wherever `e = 1` gives an étale equivalence relation on
`𝔸¹_W`. Two points `(w, a)` and `(w', a')` are related exactly when a point `r` of `R` relates
`w'` to `w` and `a' = a + e(r) (1 - 2a)`.

## Main definitions

* `AlgebraicGeometry.TwistedAffineLine.twist`: the involution `t ↦ t + e (1 - 2t)` of the
  affine line over a scheme, for an idempotent global section `e`.
* `AlgebraicGeometry.TwistedAffineLine.twistedSource`,
  `AlgebraicGeometry.TwistedAffineLine.twistedTarget`: the two projections of the twisted
  relation `𝔸¹_R ⇉ 𝔸¹_W`, as morphisms of the site.

## Main results

* `AlgebraicGeometry.TwistedAffineLine.twist_comp_twist`: the twist is an involution.
* `AlgebraicGeometry.TwistedAffineLine.isEtaleEquivalenceRelation_twisted`: the twisted
  relation is an étale equivalence relation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedAffineLine

open _root_.AlgebraicGeometry.AffineSpace

/-- The index type of the coordinate of the affine line. -/
abbrev Idx : Type u := ULift.{u} (Fin 1)

/-- The unique coordinate index of the affine line. -/
abbrev c₀ : Idx.{u} := ⟨0⟩

/-- Every coordinate index of the affine line is `c₀`. -/
theorem idx_eq (i : Idx.{u}) : i = c₀ := by
  rcases i with ⟨i⟩
  rw [Subsingleton.elim i 0]

/-! ### The twist of the affine line by an idempotent -/

section Twist

variable {X : Scheme.{u}}

/-- **The twist of the affine line over `X` by an idempotent global section `e`**: the morphism
`t ↦ t + e (1 - 2t)` over `X`. It is the identity where `e = 0` and `t ↦ 1 - t` where
`e = 1`. -/
noncomputable def twist (e : Γ(X, ⊤)) : 𝔸(Idx; X) ⟶ 𝔸(Idx; X) :=
  homOfVector (𝔸(Idx; X) ↘ X) fun _ ↦
    coord X c₀ + (𝔸(Idx; X) ↘ X).appTop e * (1 - 2 * coord X c₀)

/-- The twist is a morphism over `X`. -/
@[reassoc (attr := simp)]
theorem twist_over (e : Γ(X, ⊤)) : twist e ≫ 𝔸(Idx; X) ↘ X = 𝔸(Idx; X) ↘ X :=
  homOfVector_over _ _

/-- The twist pulls the coordinate `t` back to `t + e (1 - 2t)`. -/
theorem twist_appTop_coord (e : Γ(X, ⊤)) (i : Idx.{u}) :
    (twist e).appTop (coord X i) =
      coord X c₀ + (𝔸(Idx; X) ↘ X).appTop e * (1 - 2 * coord X c₀) :=
  homOfVector_appTop_coord _ _ _

/-- The coordinate of a point of the affine line, read after the twist. -/
theorem comp_twist_appTop_coord {T : Scheme.{u}} (e : Γ(X, ⊤)) (g : T ⟶ 𝔸(Idx; X))
    (i : Idx.{u}) :
    (g ≫ twist e).appTop (coord X i) =
      g.appTop (coord X c₀) + (g ≫ 𝔸(Idx; X) ↘ X).appTop e * (1 - 2 * g.appTop (coord X c₀)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, twist_appTop_coord]
  simp only [map_add, map_mul, map_sub, map_one, map_ofNat, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

/-- The twist by an idempotent is an involution. -/
theorem twist_comp_twist {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    twist e ≫ twist e = 𝟙 _ := by
  ext1
  · simp
  · rename_i i
    rw [comp_twist_appTop_coord, twist_over, twist_appTop_coord, Scheme.Hom.id_appTop, idx_eq i]
    set c := coord X c₀
    set f := (𝔸(Idx; X) ↘ X).appTop e
    have hf : f * f = f := he.map _
    change c + f * (1 - 2 * c) + f * (1 - 2 * (c + f * (1 - 2 * c))) = c
    linear_combination (-2 * (1 - 2 * c)) * hf

/-- The twist by an idempotent is an isomorphism. -/
theorem isIso_twist {e : Γ(X, ⊤)} (he : IsIdempotentElem e) : IsIso (twist e) :=
  ⟨⟨twist e, twist_comp_twist he, twist_comp_twist he⟩⟩

end Twist

/-! ### The twisted relation on the affine line over a site object -/

section Relation

open Stack.AlgebraicStacks (affineSpaceChart)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {W R : BigFppfOver B S hS} (s t : R ⟶ W)
variable (e : Γ((BigFppfOver.toScheme B S hS).obj R, ⊤))

/-- **The source projection of the twisted relation**: the affine line over the source
projection of the relation. -/
noncomputable def twistedSource : affineSpaceChart B S hS R 1 ⟶ affineSpaceChart B S hS W 1 :=
  Over.homMk ⟨AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map s)⟩ (by
    ext1
    change AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map s) ≫
        (𝔸(Idx; ((BigFppfOver.toScheme B S hS).obj W)) ↘ ((BigFppfOver.toScheme B S hS).obj W)) ≫
          B.inclusion.map W.hom =
      (𝔸(Idx; ((BigFppfOver.toScheme B S hS).obj R)) ↘ ((BigFppfOver.toScheme B S hS).obj R)) ≫
        B.inclusion.map R.hom
    rw [AffineSpace.map_over_assoc]
    congr 1
    exact congrArg B.inclusion.map (Over.w s))

/-- **The target projection of the twisted relation**: the affine line over the target
projection of the relation, precomposed with the twist by `e`. -/
noncomputable def twistedTarget : affineSpaceChart B S hS R 1 ⟶ affineSpaceChart B S hS W 1 :=
  Over.homMk ⟨twist e ≫ AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map t)⟩ (by
    ext1
    change (twist e ≫ AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map t)) ≫
        (𝔸(Idx; ((BigFppfOver.toScheme B S hS).obj W)) ↘ ((BigFppfOver.toScheme B S hS).obj W)) ≫
          B.inclusion.map W.hom =
      (𝔸(Idx; ((BigFppfOver.toScheme B S hS).obj R)) ↘ ((BigFppfOver.toScheme B S hS).obj R)) ≫
        B.inclusion.map R.hom
    rw [Category.assoc, AffineSpace.map_over_assoc, twist_over_assoc]
    congr 1
    exact congrArg B.inclusion.map (Over.w t))

end Relation

/-! ### Points of the twisted relation -/

/-- A morphism into the affine line over a scheme is determined by its projection and its
coordinate. -/
theorem eq_homOfVector {Y X : Scheme.{u}} (g : Y ⟶ 𝔸(Idx; X)) :
    g = homOfVector (g ≫ 𝔸(Idx; X) ↘ X) fun _ ↦ g.appTop (coord X c₀) := by
  ext1
  · simp
  · rename_i i
    rw [homOfVector_appTop_coord, idx_eq i]

/-- Two morphisms into the affine line over a scheme agree if and only if their projections and
their coordinates agree. -/
theorem homOfVector_eq_homOfVector_iff {Y X : Scheme.{u}} {f f' : Y ⟶ X}
    {a a' : Γ(Y, ⊤)} :
    (homOfVector f fun (_ : Idx.{u}) ↦ a) = homOfVector f' (fun (_ : Idx.{u}) ↦ a') ↔
      f = f' ∧ a = a' := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ by rw [h.1, h.2]⟩
  · simpa using congrArg (· ≫ 𝔸(Idx; X) ↘ X) h
  · simpa using congrArg (fun g ↦ g.appTop (coord X c₀)) h

/-- The affine line over a morphism `g`, on a point given by a projection `f` and a coordinate
`a`, gives the point with projection `f ≫ g` and coordinate `a`. -/
theorem homOfVector_comp_map {Y X X' : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ X')
    (a : Γ(Y, ⊤)) :
    (homOfVector f fun (_ : Idx.{u}) ↦ a) ≫ AffineSpace.map Idx g =
      homOfVector (f ≫ g) fun _ ↦ a := by
  ext1
  · simp
  · rename_i i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
      homOfVector_appTop_coord, homOfVector_appTop_coord]

/-- The twist, on a point given by a projection and a coordinate. -/
theorem homOfVector_comp_twist {Y X : Scheme.{u}} (f : Y ⟶ X) (e : Γ(X, ⊤))
    (a : Γ(Y, ⊤)) :
    (homOfVector f fun (_ : Idx.{u}) ↦ a) ≫ twist e =
      homOfVector f fun _ ↦ a + f.appTop e * (1 - 2 * a) := by
  ext1
  · simp
  · rename_i i
    rw [comp_twist_appTop_coord, homOfVector_appTop_coord, homOfVector_appTop_coord,
      homOfVector_over]

/-- The twist by an idempotent `e` composed with the twist by an idempotent `e'` is the twist by
their exclusive or, on coordinates. -/
theorem twistCoord_twistCoord {A : Type*} [CommRing A] {e e' : A} (_he : IsIdempotentElem e)
    (_he' : IsIdempotentElem e') (a : A) :
    (a + e' * (1 - 2 * a)) + e * (1 - 2 * (a + e' * (1 - 2 * a))) =
      a + (e + e' - 2 * e * e') * (1 - 2 * a) := by
  ring

/-- Twisting a coordinate twice by the same idempotent `e` returns it unchanged. -/
theorem twistCoord_self {A : Type*} [CommRing A] {e : A} (he : IsIdempotentElem e) (a : A) :
    (a + e * (1 - 2 * a)) + e * (1 - 2 * (a + e * (1 - 2 * a))) = a := by
  unfold IsIdempotentElem at he
  linear_combination (-2 * (1 - 2 * a)) * he

section Points

open Stack.AlgebraicStacks (affineSpaceChart affineSpaceChartHom)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of schemes underlying a point, over an arbitrary scheme over `S`, of a site
object, typed with the underlying scheme of the object as its target. -/
abbrev schemeHom {T : Over (B.inclusion.obj (B.obj hS))} {X : BigFppfOver B S hS}
    (ρ : T ⟶ (Over.post B.inclusion).obj X) : T.left ⟶ (BigFppfOver.toScheme B S hS).obj X :=
  ρ.left

/-- **A point of the affine line over a site object**, over an arbitrary scheme over `S`, from a
point of the object and a coordinate. -/
noncomputable def mkPoint {T : Over (B.inclusion.obj (B.obj hS))} {X : BigFppfOver B S hS}
    (ρ : T ⟶ (Over.post B.inclusion).obj X) (a : Γ(T.left, ⊤)) :
    T ⟶ (Over.post B.inclusion).obj (affineSpaceChart B S hS X 1) :=
  Over.homMk (homOfVector (schemeHom B S hS ρ)
    fun _ ↦ a) (by
    change (homOfVector (schemeHom B S hS ρ) fun _ ↦ a) ≫
        (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj X) ↘ (BigFppfOver.toScheme B S hS).obj X) ≫
          B.inclusion.map X.hom = T.hom
    rw [homOfVector_over_assoc]
    exact Over.w ρ)

/-- The underlying morphism of schemes of `mkPoint B S hS ρ a`. -/
@[simp]
theorem mkPoint_left {T : Over (B.inclusion.obj (B.obj hS))} {X : BigFppfOver B S hS}
    (ρ : T ⟶ (Over.post B.inclusion).obj X) (a : Γ(T.left, ⊤)) :
    (mkPoint B S hS ρ a).left =
      homOfVector (schemeHom B S hS ρ) fun _ ↦ a := rfl

/-- The projection of a point of the affine line over a site object. -/
noncomputable def pointBase {T : Over (B.inclusion.obj (B.obj hS))} {X : BigFppfOver B S hS}
    (x : T ⟶ (Over.post B.inclusion).obj (affineSpaceChart B S hS X 1)) :
    T ⟶ (Over.post B.inclusion).obj X :=
  x ≫ (Over.post B.inclusion).map (affineSpaceChartHom B S hS X 1)

/-- The underlying morphism of schemes of the projection of a point of the affine line. -/
@[simp]
theorem pointBase_left {T : Over (B.inclusion.obj (B.obj hS))} {X : BigFppfOver B S hS}
    (x : T ⟶ (Over.post B.inclusion).obj (affineSpaceChart B S hS X 1)) :
    (pointBase B S hS x).left =
      x.left ≫ (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj X) ↘
        (BigFppfOver.toScheme B S hS).obj X) := rfl

/-- Every point of the affine line over a site object is the point given by its projection and
its coordinate. -/
theorem eq_mkPoint {T : Over (B.inclusion.obj (B.obj hS))} {X : BigFppfOver B S hS}
    (x : T ⟶ (Over.post B.inclusion).obj (affineSpaceChart B S hS X 1)) :
    x = mkPoint B S hS (pointBase B S hS x)
      (x.left.appTop (coord ((BigFppfOver.toScheme B S hS).obj X) c₀)) := by
  ext1
  rw [mkPoint_left]
  exact eq_homOfVector (x.left : T.left ⟶ 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj X))

/-- Two points of the affine line over a site object agree if and only if their points of the
object and their coordinates agree. -/
theorem mkPoint_eq_mkPoint_iff {T : Over (B.inclusion.obj (B.obj hS))}
    {X : BigFppfOver B S hS} {ρ ρ' : T ⟶ (Over.post B.inclusion).obj X} {a a' : Γ(T.left, ⊤)} :
    mkPoint B S hS ρ a = mkPoint B S hS ρ' a' ↔ ρ = ρ' ∧ a = a' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h.1, h.2]⟩
  have h' : (homOfVector (schemeHom B S hS ρ) fun (_ : Idx.{u}) ↦ a) =
      homOfVector (schemeHom B S hS ρ') fun _ ↦ a' :=
    congrArg (fun g ↦ CommaMorphism.left g) h
  rw [homOfVector_eq_homOfVector_iff] at h'
  exact ⟨Over.OverMorphism.ext h'.1, h'.2⟩

variable {W R : BigFppfOver B S hS} (s t : R ⟶ W)
variable (e : Γ((BigFppfOver.toScheme B S hS).obj R, ⊤))

/-- The source projection of the twisted relation sends the point `(ρ, a)` to `(ρ ≫ s, a)`. -/
theorem mkPoint_comp_twistedSource {T : Over (B.inclusion.obj (B.obj hS))}
    (ρ : T ⟶ (Over.post B.inclusion).obj R) (a : Γ(T.left, ⊤)) :
    mkPoint B S hS ρ a ≫ (Over.post B.inclusion).map (twistedSource B S hS s) =
      mkPoint B S hS (ρ ≫ (Over.post B.inclusion).map s) a := by
  ext1
  change (homOfVector (schemeHom B S hS ρ) fun _ ↦ a) ≫
      AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map s) = _
  rw [homOfVector_comp_map]
  rfl

/-- The target projection of the twisted relation sends the point `(ρ, a)` to
`(ρ ≫ t, a + e(ρ) (1 - 2a))`. -/
theorem mkPoint_comp_twistedTarget {T : Over (B.inclusion.obj (B.obj hS))}
    (ρ : T ⟶ (Over.post B.inclusion).obj R) (a : Γ(T.left, ⊤)) :
    mkPoint B S hS ρ a ≫ (Over.post B.inclusion).map (twistedTarget B S hS t e) =
      mkPoint B S hS (ρ ≫ (Over.post B.inclusion).map t)
        (a + (schemeHom B S hS ρ).appTop e * (1 - 2 * a)) := by
  ext1
  change (homOfVector (schemeHom B S hS ρ) fun _ ↦ a) ≫
      twist e ≫ AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map t) = _
  rw [← Category.assoc, homOfVector_comp_twist, homOfVector_comp_map]
  rfl

end Points

/-! ### The twisted relation is an étale equivalence relation -/

section Equivalence

open Stack.AlgebraicStacks (affineSpaceChart affineSpaceChartHom)
open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {W R : BigFppfOver B S hS} (s t : R ⟶ W)
variable (e : Γ((BigFppfOver.toScheme B S hS).obj R, ⊤))

/-- The target of the relation given by `s, t` is the image of `t`. -/
theorem relation_target_eq :
    (Space.relation B S hS s t).target = (Over.post B.inclusion).map t :=
  prod.lift_fst _ _

/-- The source of the relation given by `s, t` is the image of `s`. -/
theorem relation_source_eq :
    (Space.relation B S hS s t).source = (Over.post B.inclusion).map s :=
  prod.lift_snd _ _

/-- The source projection of the twisted relation, on a point given by its projection and
coordinate. -/
private theorem comp_twistedSource_eq {T : Over (B.inclusion.obj (B.obj hS))}
    (r : T ⟶ (Over.post B.inclusion).obj (affineSpaceChart B S hS R 1)) :
    r ≫ (Over.post B.inclusion).map (twistedSource B S hS s) =
      mkPoint B S hS (pointBase B S hS r ≫ (Over.post B.inclusion).map s)
        (r.left.appTop (coord ((BigFppfOver.toScheme B S hS).obj R) c₀)) := by
  conv_lhs => rw [eq_mkPoint B S hS r]
  rw [mkPoint_comp_twistedSource]

/-- The target projection of the twisted relation, on a point given by its projection and
coordinate. -/
private theorem comp_twistedTarget_eq {T : Over (B.inclusion.obj (B.obj hS))}
    (r : T ⟶ (Over.post B.inclusion).obj (affineSpaceChart B S hS R 1)) :
    r ≫ (Over.post B.inclusion).map (twistedTarget B S hS t e) =
      mkPoint B S hS (pointBase B S hS r ≫ (Over.post B.inclusion).map t)
        (r.left.appTop (coord ((BigFppfOver.toScheme B S hS).obj R) c₀) +
          (schemeHom B S hS (pointBase B S hS r)).appTop e *
            (1 - 2 * r.left.appTop (coord ((BigFppfOver.toScheme B S hS).obj R) c₀))) := by
  conv_lhs => rw [eq_mkPoint B S hS r]
  rw [mkPoint_comp_twistedTarget]

/-- **The twisted relation is an étale equivalence relation.** Let `s, t : R ⟶ W` be an étale
equivalence relation, and let `e` be an idempotent global section of `R` which vanishes on the
diagonal, is invariant under the symmetry of the relation, and is additive along composition,
additivity being the exclusive or `e₁ + e₂ - 2 e₁ e₂` of idempotents. Then the affine line over
`R`, mapped to the affine line over `W` by the source projection and by the target projection
composed with the twist by `e`, is an étale equivalence relation. -/
theorem isEtaleEquivalenceRelation_twisted
    [hrel : IsEtaleEquivalenceRelation (Space.relation B S hS s t)]
    (he : IsIdempotentElem e)
    (he₀ : ∀ (T : Over (B.inclusion.obj (B.obj hS))) (r : T ⟶ (Over.post B.inclusion).obj R),
      r ≫ (Over.post B.inclusion).map s = r ≫ (Over.post B.inclusion).map t →
        (schemeHom B S hS r).appTop e = 0)
    (he₁ : ∀ (T : Over (B.inclusion.obj (B.obj hS)))
      (r r' : T ⟶ (Over.post B.inclusion).obj R),
      r' ≫ (Over.post B.inclusion).map s = r ≫ (Over.post B.inclusion).map t →
      r' ≫ (Over.post B.inclusion).map t = r ≫ (Over.post B.inclusion).map s →
        (schemeHom B S hS r').appTop e = (schemeHom B S hS r).appTop e)
    (he₂ : ∀ (T : Over (B.inclusion.obj (B.obj hS)))
      (r₁ r₂ r₃ : T ⟶ (Over.post B.inclusion).obj R),
      r₁ ≫ (Over.post B.inclusion).map s = r₂ ≫ (Over.post B.inclusion).map t →
      r₃ ≫ (Over.post B.inclusion).map t = r₁ ≫ (Over.post B.inclusion).map t →
      r₃ ≫ (Over.post B.inclusion).map s = r₂ ≫ (Over.post B.inclusion).map s →
        (schemeHom B S hS r₃).appTop e =
          (schemeHom B S hS r₁).appTop e + (schemeHom B S hS r₂).appTop e -
            2 * (schemeHom B S hS r₁).appTop e * (schemeHom B S hS r₂).appTop e) :
    IsEtaleEquivalenceRelation
      (Space.relation B S hS (twistedSource B S hS s) (twistedTarget B S hS t e)) := by
  obtain ⟨hmono, hpre⟩ := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (Space.relation B S hS s t)).1 hrel.isEquivalenceRelation
  have hetS : Etale ((Over.post B.inclusion).map s).left := by
    have := hrel.etale_source
    rwa [relation_source_eq] at this
  have hetT : Etale ((Over.post B.inclusion).map t).left := by
    have := hrel.etale_target
    rwa [relation_target_eq] at this
  have hidem : ∀ {T : Over (B.inclusion.obj (B.obj hS))}
      (r : T ⟶ (Over.post B.inclusion).obj R), IsIdempotentElem ((schemeHom B S hS r).appTop e) :=
    fun r ↦ he.map _
  have hpre' : IsPreEquivalenceRelation
      (Space.relation B S hS (twistedSource B S hS s) (twistedTarget B S hS t e)) := by
    intro T
    have hT := hpre T
    have hrefl : ∀ w : T ⟶ (Over.post B.inclusion).obj W, ∃ ρ : T ⟶ (Over.post B.inclusion).obj R,
        ρ ≫ (Over.post B.inclusion).map t = w ∧ ρ ≫ (Over.post B.inclusion).map s = w := by
      intro w
      obtain ⟨ρ, h₁, h₂⟩ := hT.refl w
      rw [relation_target_eq] at h₁
      rw [relation_source_eq] at h₂
      exact ⟨ρ, h₁, h₂⟩
    have hsymm : ∀ ρ : T ⟶ (Over.post B.inclusion).obj R, ∃ ρ' : T ⟶ (Over.post B.inclusion).obj R,
        ρ' ≫ (Over.post B.inclusion).map t = ρ ≫ (Over.post B.inclusion).map s ∧
          ρ' ≫ (Over.post B.inclusion).map s = ρ ≫ (Over.post B.inclusion).map t := by
      intro ρ
      obtain ⟨ρ', h₁, h₂⟩ := hT.symm ⟨ρ, rfl, rfl⟩
      rw [relation_target_eq, relation_source_eq] at h₁ h₂
      exact ⟨ρ', h₁, h₂⟩
    have htrans : ∀ ρ₁ ρ₂ : T ⟶ (Over.post B.inclusion).obj R,
        ρ₁ ≫ (Over.post B.inclusion).map s = ρ₂ ≫ (Over.post B.inclusion).map t →
        ∃ ρ₃ : T ⟶ (Over.post B.inclusion).obj R,
          ρ₃ ≫ (Over.post B.inclusion).map t = ρ₁ ≫ (Over.post B.inclusion).map t ∧
            ρ₃ ≫ (Over.post B.inclusion).map s = ρ₂ ≫ (Over.post B.inclusion).map s := by
      intro ρ₁ ρ₂ h
      obtain ⟨ρ₃, h₁, h₂⟩ := hT.trans (y := ρ₁ ≫ (Space.relation B S hS s t).source)
        ⟨ρ₁, rfl, rfl⟩ ⟨ρ₂, by rw [relation_target_eq, relation_source_eq, h], rfl⟩
      rw [relation_target_eq] at h₁
      rw [relation_source_eq] at h₂
      exact ⟨ρ₃, h₁, h₂⟩
    refine ⟨fun x ↦ ?_, fun {x y} hxy ↦ ?_, fun {x y z} hxy hyz ↦ ?_⟩
    · obtain ⟨ρ, hρt, hρs⟩ := hrefl (pointBase B S hS x)
      refine ⟨mkPoint B S hS ρ (x.left.appTop
        (coord ((BigFppfOver.toScheme B S hS).obj W) c₀)), ?_, ?_⟩
      · rw [relation_target_eq, mkPoint_comp_twistedTarget, he₀ T ρ (hρs.trans hρt.symm),
          zero_mul, add_zero, hρt, ← eq_mkPoint]
      · rw [relation_source_eq, mkPoint_comp_twistedSource, hρs, ← eq_mkPoint]
    · obtain ⟨r, hrt, hrs⟩ := hxy
      rw [relation_target_eq, comp_twistedTarget_eq] at hrt
      rw [relation_source_eq, comp_twistedSource_eq] at hrs
      set ρ := pointBase B S hS r
      set a := r.left.appTop (coord ((BigFppfOver.toScheme B S hS).obj R) c₀)
      obtain ⟨ρ', hρ't, hρ's⟩ := hsymm ρ
      have he' := he₁ T ρ ρ' hρ's hρ't
      refine ⟨mkPoint B S hS ρ' (a + (schemeHom B S hS ρ).appTop e * (1 - 2 * a)), ?_, ?_⟩
      · rw [relation_target_eq, mkPoint_comp_twistedTarget, ← hrs, hρ't, he',
          twistCoord_self (hidem ρ)]
      · rw [relation_source_eq, mkPoint_comp_twistedSource, ← hrt, hρ's]
    · obtain ⟨r₁, h₁t, h₁s⟩ := hxy
      obtain ⟨r₂, h₂t, h₂s⟩ := hyz
      rw [relation_target_eq, comp_twistedTarget_eq] at h₁t
      rw [relation_source_eq, comp_twistedSource_eq] at h₁s
      rw [relation_target_eq, comp_twistedTarget_eq] at h₂t
      rw [relation_source_eq, comp_twistedSource_eq] at h₂s
      set ρ₁ := pointBase B S hS r₁
      set a₁ := r₁.left.appTop (coord ((BigFppfOver.toScheme B S hS).obj R) c₀)
      set ρ₂ := pointBase B S hS r₂
      set a₂ := r₂.left.appTop (coord ((BigFppfOver.toScheme B S hS).obj R) c₀)
      obtain ⟨hρ, ha⟩ := (mkPoint_eq_mkPoint_iff B S hS).1 (h₁s.trans h₂t.symm)
      obtain ⟨ρ₃, hρ₃t, hρ₃s⟩ := htrans ρ₁ ρ₂ hρ
      have he₃ := he₂ T ρ₁ ρ₂ ρ₃ hρ hρ₃t hρ₃s
      refine ⟨mkPoint B S hS ρ₃ a₂, ?_, ?_⟩
      · rw [relation_target_eq, mkPoint_comp_twistedTarget, ← h₁t, hρ₃t, he₃, ha,
          twistCoord_twistCoord (hidem ρ₁) (hidem ρ₂)]
      · rw [relation_source_eq, mkPoint_comp_twistedSource, ← h₂s, hρ₃s]
  have hmono' : Mono
      (Space.relation B S hS (twistedSource B S hS s) (twistedTarget B S hS t e)) := by
    refine ⟨fun {T} f g hfg ↦ ?_⟩
    have hft := congrArg (· ≫ prod.fst) hfg
    have hfs := congrArg (· ≫ prod.snd) hfg
    simp only [Category.assoc, Space.relation, prod.lift_fst, prod.lift_snd] at hft hfs
    rw [comp_twistedTarget_eq, comp_twistedTarget_eq] at hft
    rw [comp_twistedSource_eq, comp_twistedSource_eq] at hfs
    rw [eq_mkPoint B S hS f, eq_mkPoint B S hS g]
    obtain ⟨hρt, -⟩ := (mkPoint_eq_mkPoint_iff B S hS).1 hft
    obtain ⟨hρs, ha⟩ := (mkPoint_eq_mkPoint_iff B S hS).1 hfs
    have hρ : pointBase B S hS f = pointBase B S hS g := by
      apply hmono.right_cancellation
      apply prod.hom_ext
      · simpa only [Category.assoc, Space.relation, prod.lift_fst] using hρt
      · simpa only [Category.assoc, Space.relation, prod.lift_snd] using hρs
    rw [hρ, ha]
  have hiso := isIso_twist he
  have hequiv := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation _).2
    ⟨hmono', hpre'⟩
  have hs' : Etale (Space.relation B S hS (twistedSource B S hS s)
      (twistedTarget B S hS t e)).source.left := by
    rw [relation_source_eq]
    change Etale (AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map s))
    exact MorphismProperty.of_isPullback (AffineSpace.isPullback_map _).flip hetS
  have ht' : Etale (Space.relation B S hS (twistedSource B S hS s)
      (twistedTarget B S hS t e)).target.left := by
    rw [relation_target_eq]
    change Etale (twist e ≫ AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map t))
    have : Etale (AffineSpace.map Idx ((BigFppfOver.toScheme B S hS).map t)) :=
      MorphismProperty.of_isPullback (AffineSpace.isPullback_map _).flip hetT
    infer_instance
  exact @IsEtaleEquivalenceRelation.mk _ _ _ _ hequiv hs' ht'

end Equivalence

end AlgebraicGeometry.TwistedAffineLine

end
