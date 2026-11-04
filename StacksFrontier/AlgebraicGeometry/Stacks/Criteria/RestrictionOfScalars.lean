module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism

/-!
# Restriction of scalars

Let `S` be a scheme contained in a big fppf site and let `x : X ⟶ Z` and `z : Z ⟶ Q` be morphisms
of algebraic spaces over `S`. The *restriction of scalars* of `X` along `z` is the functor of
points

```text
Res_{Z/Q}(X) : (Sch/S)ᵒᵖ ⥤ Set,   T ↦ {(a, b)},
```

where `a : T ⟶ Q` is a morphism and `b : T ×_{a, Q} Z ⟶ X` is a morphism **over `Z`**, that is
one whose composite with `x` is the projection to `Z`. Such a pair is
`AlgebraicGeometry.Space.RestrictionPair`. It is a value of the relative morphism functor
`Mor_Q(Z, X)` of `AlgebraicGeometry.Space.RelativeMorphism` whose second component lies over `Z`
rather than merely over `Q`, and restriction of scalars is the subpresheaf of the relative morphism
functor cut out by this condition, which is stable under base change.

## Main definitions

* `AlgebraicGeometry.Space.RestrictionPair`: a pair `(a, b)` with `b` over `Z`.
* `AlgebraicGeometry.Space.RestrictionPair.restrict`: base change of a pair along a morphism of
  test presheaves.
* `AlgebraicGeometry.Space.RestrictionPair.IsPullbackAlong`: the relation "`p'` is the base
  change of `p` along `f`", stated by an explicit comparison of the two fibre products.
* `AlgebraicGeometry.Space.RestrictionPair.postcomp`: postcomposition of the second component of
  a pair with a morphism `X' ⟶ X` over `Z`.
* `AlgebraicGeometry.Space.restrictionPairEquivSubtype`: restriction pairs are the pairs of the
  relative morphism functor whose second component lies over `Z`.
* `AlgebraicGeometry.Space.restrictionOfScalarsPresheaf`: the restriction-of-scalars presheaf.
* `AlgebraicGeometry.Space.RestrictionOfScalarsConstruction`: the restriction-of-scalars
  presheaf together with its projection to `Q`, the identification of its sections over a
  scheme with pairs, and the description of its restriction maps.
* `AlgebraicGeometry.Space.restrictionOfScalars`: that construction.

## Main results

* `AlgebraicGeometry.Space.RestrictionPair.isPullbackAlong_restrict` and
  `AlgebraicGeometry.Space.RestrictionPair.eq_restrict_of_isPullbackAlong`: being a base change
  along `f` characterizes `AlgebraicGeometry.Space.RestrictionPair.restrict` up to equality.
* `AlgebraicGeometry.Space.RestrictionPair.eq_of_isPullbackAlong` and
  `AlgebraicGeometry.Space.RestrictionPair.IsPullbackAlong.comp`: base changes are unique and
  compose.

## References

* [Stacks Project, Tag 05Y9](https://stacks.math.columbia.edu/tag/05Y9)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Pairs -/

/-- A pair `(a, b)` for the restriction of scalars of `x : X ⟶ Z` along
`z : Z ⟶ Q` at a test presheaf `T`: a morphism `a : T ⟶ Q` together with a morphism
`b : T ×_{a, Q} Z ⟶ X` lying over `Z`.

This is a pair of `AlgebraicGeometry.Space.RelativeMorphism` for `z` and `x ≫ z` subject to the
stronger requirement that `b` lie over `Z` and not merely over `Q`; see
`AlgebraicGeometry.Space.restrictionPairEquivSubtype`. -/
@[stacks_fixed 05Y9 "the pair (a, b) displayed by the diagram"]
structure RestrictionPair {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The morphism `a : T ⟶ Q` to the base. -/
  base : T ⟶ Q.obj
  /-- The morphism `b : T ×_{a, Q} Z ⟶ X` from the base change of `Z`. -/
  lift : pullback base z.hom ⟶ X.obj
  /-- The morphism `b` lies over `Z`. -/
  over : lift ≫ x.hom = pullback.snd base z.hom

variable {B S hS}

/-- Two pairs with the same first component are equal as soon as their second components agree
after the canonical identification of the two base changes. -/
theorem RestrictionPair.ext_of_base_eq {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z} {z : Z ⟶ Q}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p q : RestrictionPair B S hS x z T}
    (hbase : p.base = q.base)
    (hlift : p.lift = (pullback.congrHom hbase rfl).hom ≫ q.lift) : p = q := by
  obtain ⟨pb, pl, po⟩ := p
  obtain ⟨qb, ql, qo⟩ := q
  cases hbase
  have hid : (pullback.congrHom (rfl : pb = pb) (rfl : z.hom = z.hom)).hom =
      𝟙 (pullback pb z.hom) := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  rw [hid, Category.id_comp] at hlift
  cases hlift
  rfl

/-- Base change of a pair `(a, b)` along a morphism `f : T' ⟶ T` of test presheaves: compose `a`
with `f` and base change `b`. -/
noncomputable def RestrictionPair.restrict {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T)
    (p : RestrictionPair B S hS x z T) : RestrictionPair B S hS x z T' where
  base := f ≫ p.base
  lift :=
    pullback.map (f ≫ p.base) z.hom p.base z.hom f (𝟙 Z.obj) (𝟙 Q.obj) (by simp) (by simp) ≫
      p.lift
  over := by simp [p.over]

/-- The first component of a base-changed pair. -/
@[simp] theorem RestrictionPair.restrict_base {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T)
    (p : RestrictionPair B S hS x z T) :
    (RestrictionPair.restrict f p).base = f ≫ p.base := rfl

/-- The second component of a base-changed pair. -/
@[simp] theorem RestrictionPair.restrict_lift {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T)
    (p : RestrictionPair B S hS x z T) :
    (RestrictionPair.restrict f p).lift =
      pullback.map (f ≫ p.base) z.hom p.base z.hom f (𝟙 Z.obj) (𝟙 Q.obj) (by simp) (by simp) ≫
        p.lift :=
  rfl

/-- Base change along an identity does nothing. -/
@[simp] theorem RestrictionPair.restrict_id {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : RestrictionPair B S hS x z T) :
    RestrictionPair.restrict (𝟙 T) p = p :=
  RestrictionPair.ext_of_base_eq (Category.id_comp p.base) rfl

/-- Base change along a composite is the composite of the base changes. -/
theorem RestrictionPair.restrict_comp {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z} {z : Z ⟶ Q}
    {T T' T'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T) (f' : T'' ⟶ T')
    (p : RestrictionPair B S hS x z T) :
    RestrictionPair.restrict f' (RestrictionPair.restrict f p) =
      RestrictionPair.restrict (f' ≫ f) p := by
  have key :
      pullback.map (f' ≫ f ≫ p.base) z.hom (f ≫ p.base) z.hom f' (𝟙 Z.obj) (𝟙 Q.obj)
          (by simp) (by simp) ≫
        pullback.map (f ≫ p.base) z.hom p.base z.hom f (𝟙 Z.obj) (𝟙 Q.obj) (by simp) (by simp) =
      (pullback.congrHom (Category.assoc f' f p.base).symm (rfl : z.hom = z.hom)).hom ≫
        pullback.map ((f' ≫ f) ≫ p.base) z.hom p.base z.hom (f' ≫ f) (𝟙 Z.obj) (𝟙 Q.obj)
          (by simp) (by simp) := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  exact RestrictionPair.ext_of_base_eq (Category.assoc f' f p.base).symm
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ p.lift) key).trans (Category.assoc _ _ _)))

/-- Postcomposition of a pair in its second component with a morphism `g : X' ⟶ X` over `Z`. -/
noncomputable def RestrictionPair.postcomp {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Z}
    {x : X ⟶ Z} (g : X' ⟶ X) (hg : g ≫ x = x') {z : Z ⟶ Q}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : RestrictionPair B S hS x' z T) :
    RestrictionPair B S hS x z T where
  base := p.base
  lift := p.lift ≫ g.hom
  over := by
    have hh : g.hom ≫ x.hom = x'.hom := congrArg (fun k : X' ⟶ Z => k.hom) hg
    simpa only [Category.assoc, hh] using p.over

/-! ### Being a base change -/

/-- `p'` is the base change of `p` along `f`: the first component of `p'` is that of `p`
composed with `f`, and there is a comparison of the two fibre products, over `T` and over `Z`,
carrying the second component of `p` to that of `p'`. -/
def RestrictionPair.IsPullbackAlong {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z} {z : Z ⟶ Q}
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T)
    (p : RestrictionPair B S hS x z T) (p' : RestrictionPair B S hS x z T') : Prop :=
  (p'.base = f ≫ p.base) ∧
    ∃ q : pullback p'.base z.hom ⟶ pullback p.base z.hom,
      (q ≫ pullback.fst p.base z.hom = pullback.fst p'.base z.hom ≫ f) ∧
      (q ≫ pullback.snd p.base z.hom = pullback.snd p'.base z.hom) ∧
      (p'.lift = q ≫ p.lift)

/-- A base change is a base change. -/
theorem RestrictionPair.isPullbackAlong_restrict {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T)
    (p : RestrictionPair B S hS x z T) :
    RestrictionPair.IsPullbackAlong f p (RestrictionPair.restrict f p) :=
  ⟨rfl, pullback.map (f ≫ p.base) z.hom p.base z.hom f (𝟙 Z.obj) (𝟙 Q.obj) (by simp) (by simp),
    by simp, by simp, rfl⟩

/-- Anything that is a base change of `p` along `f` equals
`AlgebraicGeometry.Space.RestrictionPair.restrict f p`. -/
theorem RestrictionPair.eq_restrict_of_isPullbackAlong {X Z Q : AlgebraicSpaces B S hS}
    {x : X ⟶ Z} {z : Z ⟶ Q} {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : T' ⟶ T}
    {p : RestrictionPair B S hS x z T} {p' : RestrictionPair B S hS x z T'}
    (h : RestrictionPair.IsPullbackAlong f p p') : p' = RestrictionPair.restrict f p := by
  obtain ⟨hbase, q, hfst, hsnd, hlift⟩ := h
  refine RestrictionPair.ext_of_base_eq hbase ?_
  have hq : q = (pullback.congrHom hbase (rfl : z.hom = z.hom)).hom ≫
      pullback.map (f ≫ p.base) z.hom p.base z.hom f (𝟙 Z.obj) (𝟙 Q.obj) (by simp) (by simp) := by
    exact pullback.hom_ext (by simpa using hfst) (by simpa using hsnd)
  rw [hlift, hq, RestrictionPair.restrict_lift, Category.assoc]
  rfl

/-- Two pairs that are both base changes of `p` along `f` are equal. -/
theorem RestrictionPair.eq_of_isPullbackAlong {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : T' ⟶ T}
    {p : RestrictionPair B S hS x z T} {p₁ p₂ : RestrictionPair B S hS x z T'}
    (h₁ : RestrictionPair.IsPullbackAlong f p p₁)
    (h₂ : RestrictionPair.IsPullbackAlong f p p₂) : p₁ = p₂ :=
  (RestrictionPair.eq_restrict_of_isPullbackAlong h₁).trans
    (RestrictionPair.eq_restrict_of_isPullbackAlong h₂).symm

/-- Base changes compose. -/
theorem RestrictionPair.IsPullbackAlong.comp {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T₀ T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : T₁ ⟶ T₀} {g : T₂ ⟶ T₁}
    {p₀ : RestrictionPair B S hS x z T₀} {p₁ : RestrictionPair B S hS x z T₁}
    {p₂ : RestrictionPair B S hS x z T₂}
    (h₁ : RestrictionPair.IsPullbackAlong f p₀ p₁)
    (h₂ : RestrictionPair.IsPullbackAlong g p₁ p₂) :
    RestrictionPair.IsPullbackAlong (g ≫ f) p₀ p₂ := by
  cases RestrictionPair.eq_restrict_of_isPullbackAlong h₁
  cases RestrictionPair.eq_restrict_of_isPullbackAlong h₂
  rw [RestrictionPair.restrict_comp]
  exact RestrictionPair.isPullbackAlong_restrict _ _

/-! ### Pairs as relative morphisms over `Z` -/

/-- The pair `(a, b)` of Stacks 05Y1 underlying a restriction pair: forget that `b` lies over
`Z` and remember only that it lies over `Q`. -/
noncomputable def RestrictionPair.toRelativeMorphism {X Z Q : AlgebraicSpaces B S hS}
    {x : X ⟶ Z} {z : Z ⟶ Q} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RestrictionPair B S hS x z T) :
    RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) T where
  base := p.base
  morphism := p.lift
  commutes := by simpa only [Category.assoc] using congrArg (fun k => k ≫ z.hom) p.over

/-- The condition on a pair of Stacks 05Y1 that cuts out the restriction pairs: its second
component lies over `Z`, not merely over `Q`. -/
def RelativeMorphism.LiesOverZ {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) T) : Prop :=
  p.morphism ≫ x.hom = pullback.snd p.base z.hom

/-- Restriction pairs are the pairs of Stacks 05Y1 whose second component lies over `Z`. -/
noncomputable def restrictionPairEquivSubtype {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z)
    (z : Z ⟶ Q) (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    {p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) T //
        RelativeMorphism.LiesOverZ x z p} ≃
      RestrictionPair B S hS x z T where
  toFun p := ⟨p.1.base, p.1.morphism, p.2⟩
  invFun p := ⟨p.toRelativeMorphism, p.over⟩
  left_inv := by
    rintro ⟨⟨base, morphism, commutes⟩, hp⟩
    rfl
  right_inv := by
    rintro ⟨base, lift, over⟩
    rfl

/-! ### The presheaf -/

variable (B S hS)

/-- The restriction-of-scalars presheaf: the subpresheaf of the relative morphism functor of
Stacks 05Y2 on those pairs whose second component lies over `Z`. -/
noncomputable def restrictionOfScalarsPresheaf {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z)
    (z : Z ⟶ Q) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  let H := relativeHomData B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom)
    Z.property X.property Q.property
  { obj := fun T => {v : H.functor.obj T // RelativeMorphism.LiesOverZ x z (H.sections T.unop v)}
    map := fun {T U} f => ↾fun v => ⟨H.functor.map f.unop.op v.1, by
      obtain ⟨-, q, -, hsnd, hmor⟩ := H.sections_map f.unop v.1
      change (H.sections U.unop (H.functor.map f.unop.op v.1)).morphism ≫ x.hom = _
      rw [hmor, Category.assoc, v.2, hsnd]⟩
    map_id := fun T => by
      ext v
      exact Functor.map_id_apply H.functor T v.1
    map_comp := fun {T U V} f g => by
      ext v
      exact Functor.map_comp_apply H.functor f g v.1 }

/-- The data the restriction-of-scalars functor of Stacks 05YA is specified by: a presheaf on
the big fppf site of `S`, the identification of its sections over a scheme `T` with the pairs of
Stacks 05Y9 at `T`, the description of its restriction maps as base change of pairs, its
projection to `Q`, and the compatibility of the identification with that projection. -/
structure RestrictionOfScalarsConstruction {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z)
    (z : Z ⟶ Q) where
  /-- The restriction-of-scalars functor `Res_{Z/Q}(X)`. -/
  presheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Its sections over a scheme are the pairs of Stacks 05Y9. -/
  pairEquiv : ∀ T : BigFppfOver B S hS,
    presheaf.obj (op T) ≃ RestrictionPair B S hS x z (yoneda.obj T)
  /-- Its restriction maps are base change of pairs. -/
  natural : ∀ {T U : BigFppfOver B S hS} (f : U ⟶ T) (v : presheaf.obj (op T)),
    RestrictionPair.IsPullbackAlong (yoneda.map f) (pairEquiv T v)
      (pairEquiv U (presheaf.map f.op v))
  /-- Its projection to the base, remembering the first component of a pair. -/
  projection : presheaf ⟶ Q.obj
  /-- The projection reads off the first component of a pair. -/
  projection_pairEquiv : ∀ (T : BigFppfOver B S hS) (v : presheaf.obj (op T)),
    projection.app (op T) v = yonedaEquiv ((pairEquiv T v).base)

/-- The restriction of scalars `Res_{Z/Q}(X)` of `x : X ⟶ Z` along `z : Z ⟶ Q`: the functor of
points on the big fppf site of `S` whose sections over a scheme `T` are the pairs `(a, b)` of
Stacks 05Y9, with its projection to `Q` and with restriction given by base change. -/
@[stacks 05YA]
noncomputable def restrictionOfScalars {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z)
    (z : Z ⟶ Q) : RestrictionOfScalarsConstruction B S hS x z :=
  let H := relativeHomData B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom)
    Z.property X.property Q.property
  { presheaf := restrictionOfScalarsPresheaf B S hS x z
    pairEquiv := fun T =>
      (Equiv.subtypeEquiv (H.sections T) fun _ => Iff.rfl).trans
        (restrictionPairEquivSubtype x z (yoneda.obj T))
    natural := fun f v => H.sections_map f v.1
    projection :=
      { app := fun T => ↾fun v => yonedaEquiv ((H.sections T.unop v.1).base)
        naturality := fun T U f => by
          ext v
          obtain ⟨hbase, -⟩ := H.sections_map f.unop v.1
          change yonedaEquiv ((H.sections U.unop (H.functor.map f.unop.op v.1)).base) = _
          rw [hbase]
          exact (yonedaEquiv_naturality ((H.sections T.unop v.1).base) f.unop).symm }
    projection_pairEquiv := fun _T _v => rfl }

end AlgebraicGeometry.Space

end
