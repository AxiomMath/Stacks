module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic

/-!
# Base change of the dependent product of fppf sheaves

Let `S` be a scheme contained in a big fppf site `B` and let `i : I ⟶ X`, `p : W ⟶ I` be
morphisms of fppf sheaves, with dependent product `Π_i W`
(`AlgebraicGeometry.FormalSpace.DependentProduct.liftAlong`). This file proves that the
construction commutes with base change: for a cartesian square whose sides are
`i' : I' ⟶ X'`, `g : I' ⟶ I`, `f : X' ⟶ X` and `i : I ⟶ X`, and for `p : W ⟶ I` with its base
change `p' : W' ⟶ I'`, the square whose sides are the comparison morphism
`Π_{i'} W' ⟶ Π_i W`, the two structure morphisms to `X'` and `X`, and `f`, is cartesian. This is
the Beck–Chevalley isomorphism for the dependent product.

## Main definitions

* `AlgebraicGeometry.FormalSpace.DependentProduct.IsSectionwisePullback`: a commuting square of
  fppf sheaves is cartesian on sections over every object of the site.
* `AlgebraicGeometry.FormalSpace.DependentProduct.liftAlongBaseChange`: the comparison morphism
  `Π_{i'} W' ⟶ Π_i W` attached to a cartesian change of base.

## Main results

* `AlgebraicGeometry.FormalSpace.DependentProduct.isPullback_liftAlongMap`: the comparison
  square is cartesian over an arbitrary point of a dependent product.
* `AlgebraicGeometry.FormalSpace.DependentProduct.isPullback_liftAlongBaseChange`: the
  comparison square is cartesian, `Π_{i'} W' = X' ×_X Π_i W`.

## Implementation notes

Everything is a chase on sections. Pushing a section of `Π_{i'} W'` forward replaces the section
`a'` of `X'` by `f(a')` and transports the rule by sending a pair over `X` to the unique pair
above it over `X'`, which the cartesianness of the square of `I'` provides; pulling a section
back reverses this, using the cartesianness of the square of `W'`. The general square is stated
over a point `σ : X' ⟶ Π_i Wt` of a dependent product; base change along `f : X' ⟶ X` is the
case `Wt = I`, the dependent product of the identity being `X` itself.

## References

* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cartesian squares, read on sections -/

/-- A commuting square of fppf sheaves on the big fppf site of `S` is *cartesian on sections*
when, over every object of the site, every compatible pair of sections of the two sides comes
from a unique section of the apex. A cartesian square is one, by
`AlgebraicGeometry.FormalSpace.DependentProduct.isSectionwisePullback_of_isPullback`. -/
abbrev IsSectionwisePullback {A C D E : FppfSheaf B S hS} (t : A ⟶ C) (l : A ⟶ D)
    (r : C ⟶ E) (b : D ⟶ E) : Prop :=
  ∀ (T : BigFppfOver B S hS) (c : C.obj.obj (Opposite.op T)) (d : D.obj.obj (Opposite.op T)),
    r.hom.app (Opposite.op T) c = b.hom.app (Opposite.op T) d →
      ∃! a : A.obj.obj (Opposite.op T),
        t.hom.app (Opposite.op T) a = c ∧ l.hom.app (Opposite.op T) a = d

/-- A square of fppf sheaves is cartesian on sections as soon as its square of sections over
every object of the site is cartesian. -/
private theorem isSectionwisePullback_of_forall_isPullback {A C D E : FppfSheaf B S hS}
    {t : A ⟶ C} {l : A ⟶ D} {r : C ⟶ E} {b : D ⟶ E}
    (h : ∀ T : BigFppfOver B S hS, IsPullback (t.hom.app (Opposite.op T))
      (l.hom.app (Opposite.op T)) (r.hom.app (Opposite.op T)) (b.hom.app (Opposite.op T))) :
    IsSectionwisePullback B S hS t l r b := by
  intro T c d hcd
  obtain ⟨a, ha₁, ha₂⟩ := Types.exists_of_isPullback (h T) c d hcd
  exact ⟨a, ⟨ha₁, ha₂⟩, fun a' ⟨ha'₁, ha'₂⟩ ↦
    Types.ext_of_isPullback (h T) (ha'₁.trans ha₁.symm) (ha'₂.trans ha₂.symm)⟩

/-- A cartesian square of fppf sheaves is cartesian on sections: the forgetful functor to
presheaves preserves fibre products, as does evaluation at an object of the site, and a
cartesian square of types is a fibre product of sets. -/
theorem isSectionwisePullback_of_isPullback {A C D E : FppfSheaf B S hS} {t : A ⟶ C}
    {l : A ⟶ D} {r : C ⟶ E} {b : D ⟶ E} (h : IsPullback t l r b) :
    IsSectionwisePullback B S hS t l r b :=
  isSectionwisePullback_of_forall_isPullback B S hS fun T ↦
    (h.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).map
      ((evaluation ((BigFppfOver B S hS)ᵒᵖ) (Type (u + 1))).obj (Opposite.op T))

/-- A square of fppf sheaves whose underlying square of presheaves is cartesian is cartesian on
sections: evaluation at an object of the site preserves fibre products, and a cartesian square
of types is a fibre product of sets. -/
theorem isSectionwisePullback_of_isPullback_hom {A C D E : FppfSheaf B S hS} {t : A ⟶ C}
    {l : A ⟶ D} {r : C ⟶ E} {b : D ⟶ E} (h : IsPullback t.hom l.hom r.hom b.hom) :
    IsSectionwisePullback B S hS t l r b :=
  isSectionwisePullback_of_forall_isPullback B S hS fun T ↦
    h.map ((evaluation ((BigFppfOver B S hS)ᵒᵖ) (Type (u + 1))).obj (Opposite.op T))

/-! ### The comparison morphism -/

section BaseChange

variable {B S hS} {X X' I I' W W' : FppfSheaf B S hS}
  {i : I ⟶ X} {i' : I' ⟶ X'} {f : X' ⟶ X} {g : I' ⟶ I}
  {p : W ⟶ I} {p' : W' ⟶ I'} (q : W' ⟶ W)

/-- Two equal composites of morphisms of fppf sheaves act equally on sections. -/
private theorem comp_app_congr {A₁ A₂ A₃ A₄ : FppfSheaf B S hS} {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₄}
    {c : A₁ ⟶ A₃} {d : A₃ ⟶ A₄} (h : a ≫ b = c ≫ d) (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : A₁.obj.obj T) : b.hom.app T (a.hom.app T x) = d.hom.app T (c.hom.app T x) :=
  congrArg (fun m : A₁ ⟶ A₄ ↦ m.hom.app T x) h

/-- The unique section of `I'` above a compatible pair of sections of `X'` and `I`. -/
def bcPoint (hIex : IsSectionwisePullback B S hS i' g f i) {T : BigFppfOver B S hS}
    (a : X'.obj.obj (Opposite.op T)) (w : I.obj.obj (Opposite.op T))
    (h : f.hom.app (Opposite.op T) a = i.hom.app (Opposite.op T) w) :
    I'.obj.obj (Opposite.op T) :=
  (hIex T a w h).choose

/-- The section `bcPoint hIex a w h` of `I'` maps to `a` under `i'`. -/
theorem bcPoint_fst (hIex : IsSectionwisePullback B S hS i' g f i) {T : BigFppfOver B S hS}
    (a : X'.obj.obj (Opposite.op T)) (w : I.obj.obj (Opposite.op T))
    (h : f.hom.app (Opposite.op T) a = i.hom.app (Opposite.op T) w) :
    i'.hom.app (Opposite.op T) (bcPoint hIex a w h) = a :=
  (hIex T a w h).choose_spec.1.1

/-- The section `bcPoint hIex a w h` of `I'` maps to `w` under `g`. -/
theorem bcPoint_snd (hIex : IsSectionwisePullback B S hS i' g f i) {T : BigFppfOver B S hS}
    (a : X'.obj.obj (Opposite.op T)) (w : I.obj.obj (Opposite.op T))
    (h : f.hom.app (Opposite.op T) a = i.hom.app (Opposite.op T) w) :
    g.hom.app (Opposite.op T) (bcPoint hIex a w h) = w :=
  (hIex T a w h).choose_spec.1.2

/-- A section of `I'` mapping to `a` under `i'` and to `w` under `g` is `bcPoint hIex a w h`. -/
theorem bcPoint_eq (hIex : IsSectionwisePullback B S hS i' g f i) {T : BigFppfOver B S hS}
    (a : X'.obj.obj (Opposite.op T)) (w : I.obj.obj (Opposite.op T))
    (h : f.hom.app (Opposite.op T) a = i.hom.app (Opposite.op T) w)
    (v : I'.obj.obj (Opposite.op T)) (hv₁ : i'.hom.app (Opposite.op T) v = a)
    (hv₂ : g.hom.app (Opposite.op T) v = w) :
    v = bcPoint hIex a w h :=
  (hIex T a w h).choose_spec.2 v ⟨hv₁, hv₂⟩

/-- The transpose of a square cartesian on sections is cartesian on sections. -/
theorem isSectionwisePullback_flip {A C D E : FppfSheaf B S hS} {t : A ⟶ C} {l : A ⟶ D}
    {r : C ⟶ E} {b : D ⟶ E} (h : IsSectionwisePullback B S hS t l r b) :
    IsSectionwisePullback B S hS l t b r := fun T d c hdc ↦ by
  obtain ⟨a, ⟨ha₁, ha₂⟩, hu⟩ := h T c d hdc.symm
  exact ⟨a, ⟨ha₂, ha₁⟩, fun a' ⟨h₁, h₂⟩ ↦ hu a' ⟨h₂, h₁⟩⟩

/-! #### Pushing a section forward -/

variable (hIex : IsSectionwisePullback B S hS i' g f i)

/-- The point of `I'` at which the lifting rule of a section of `Π_{i'} W'` is evaluated in
order to push that section forward. -/
def bcAux {T : BigFppfOver B S hS} (ζ : LiftAlong B S hS i' p' T)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (f.hom.app (Opposite.op T) ζ.base)) :
    I'.obj.obj (Opposite.op T') :=
  bcPoint hIex (X'.obj.map s.op ζ.base) w ((app_map_op B S hS f s ζ.base).trans h.symm)

/-- The point `bcAux hIex ζ T' s w h` of `I'` maps under `i'` to the restriction along `s` of
the base of `ζ`. -/
theorem bcAux_fst {T : BigFppfOver B S hS} (ζ : LiftAlong B S hS i' p' T)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (f.hom.app (Opposite.op T) ζ.base)) :
    i'.hom.app (Opposite.op T') (bcAux hIex ζ T' s w h) = X'.obj.map s.op ζ.base :=
  bcPoint_fst hIex _ _ _

/-- The point `bcAux hIex ζ T' s w h` of `I'` maps to `w` under `g`. -/
theorem bcAux_snd {T : BigFppfOver B S hS} (ζ : LiftAlong B S hS i' p' T)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (f.hom.app (Opposite.op T) ζ.base)) :
    g.hom.app (Opposite.op T') (bcAux hIex ζ T' s w h) = w :=
  bcPoint_snd hIex _ _ _

/-- The lifting rule of the pushforward of a section of `Π_{i'} W'`. -/
def bcRule {T : BigFppfOver B S hS} (ζ : LiftAlong B S hS i' p' T)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (f.hom.app (Opposite.op T) ζ.base)) :
    W.obj.obj (Opposite.op T') :=
  q.hom.app (Opposite.op T')
    (ζ.lift T' s (bcAux hIex ζ T' s w h) (bcAux_fst hIex ζ T' s w h))

/-- The value of the pushed-forward lifting rule at `w` lies over `w` under `p`. -/
theorem bcRule_proj (hcomm' : q ≫ p = p' ≫ g) {T : BigFppfOver B S hS}
    (ζ : LiftAlong B S hS i' p' T)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (f.hom.app (Opposite.op T) ζ.base)) :
    p.hom.app (Opposite.op T') (bcRule q hIex ζ T' s w h) = w := by
  rw [bcRule, comp_app_congr hcomm' (Opposite.op T'),
    ζ.lift_proj T' s (bcAux hIex ζ T' s w h) (bcAux_fst hIex ζ T' s w h), bcAux_snd]

/-- The pushed-forward lifting rule is compatible with restriction along `r : T'' ⟶ T'`. -/
theorem bcRule_map {T : BigFppfOver B S hS} (ζ : LiftAlong B S hS i' p' T)
    (T' T'' : BigFppfOver B S hS) (r : T'' ⟶ T') (s : T' ⟶ T)
    (w : I.obj.obj (Opposite.op T'))
    (h : i.hom.app (Opposite.op T') w = X.obj.map s.op (f.hom.app (Opposite.op T) ζ.base))
    (h' : i.hom.app (Opposite.op T'') (I.obj.map r.op w)
      = X.obj.map (r ≫ s).op (f.hom.app (Opposite.op T) ζ.base)) :
    W.obj.map r.op (bcRule q hIex ζ T' s w h)
      = bcRule q hIex ζ T'' (r ≫ s) (I.obj.map r.op w) h' := by
  have hcompat : i'.hom.app (Opposite.op T'') (I'.obj.map r.op (bcAux hIex ζ T' s w h))
      = X'.obj.map (r ≫ s).op ζ.base := by
    rw [app_map_op, bcAux_fst, LiftAlong.map_comp_op_apply]
  have hpt : I'.obj.map r.op (bcAux hIex ζ T' s w h)
      = bcAux hIex ζ T'' (r ≫ s) (I.obj.map r.op w) h' := by
    refine bcPoint_eq hIex _ _ _ _ hcompat ?_
    rw [app_map_op, bcAux_snd]
  have hlm := ζ.lift_map T' T'' r s (bcAux hIex ζ T' s w h) (bcAux_fst hIex ζ T' s w h) hcompat
  rw [bcRule, bcRule, ← app_map_op, hlm]
  refine congrArg _ ?_
  exact LiftAlong.lift_congr rfl rfl hpt _ _

/-- The pushforward of a section of `Π_{i'} W'` along a cartesian change of base. -/
def bcApp (hcomm' : q ≫ p = p' ≫ g) (T : BigFppfOver B S hS)
    (ζ : LiftAlong B S hS i' p' T) : LiftAlong B S hS i p T where
  base := f.hom.app (Opposite.op T) ζ.base
  lift := bcRule q hIex ζ
  lift_proj := bcRule_proj q hIex hcomm' ζ
  lift_map := fun T' T'' r s w h h' ↦ bcRule_map q hIex ζ T' T'' r s w h h'

/-- Pushing a section of `Π_{i'} W'` forward commutes with restriction along `r : T₀ ⟶ T`. -/
theorem bcApp_restrict (hcomm' : q ≫ p = p' ≫ g) {T T₀ : BigFppfOver B S hS} (r : T₀ ⟶ T)
    (ζ : LiftAlong B S hS i' p' T) :
    (bcApp q hIex hcomm' T ζ).restrict r = bcApp q hIex hcomm' T₀ (ζ.restrict r) := by
  refine LiftAlong.ext _ _ (app_map_op B S hS f r ζ.base).symm fun T' t w h h' ↦ ?_
  have hb : i.hom.app (Opposite.op T') w
      = X.obj.map (t ≫ r).op (f.hom.app (Opposite.op T) ζ.base) :=
    h.trans (LiftAlong.map_comp_op_apply X.obj r t (f.hom.app (Opposite.op T) ζ.base)).symm
  have hL : i.hom.app (Opposite.op T') w
      = X.obj.map t.op (f.hom.app (Opposite.op T₀) (ζ.restrict r).base) := h'
  have hv₁ : i'.hom.app (Opposite.op T') (bcAux hIex (ζ.restrict r) T' t w hL)
      = X'.obj.map (t ≫ r).op ζ.base :=
    (bcAux_fst hIex (ζ.restrict r) T' t w hL).trans
      (LiftAlong.map_comp_op_apply X'.obj r t ζ.base).symm
  have hpt : bcAux hIex ζ T' (t ≫ r) w hb = bcAux hIex (ζ.restrict r) T' t w hL :=
    (bcPoint_eq hIex _ _ _ _ hv₁ (bcAux_snd hIex (ζ.restrict r) T' t w hL)).symm
  refine Eq.trans (LiftAlong.restrict_lift r (bcApp q hIex hcomm' T ζ) rfl h hb) ?_
  refine Eq.trans (congrArg (q.hom.app (Opposite.op T'))
    (LiftAlong.lift_congr (ξ := ζ) rfl (rfl : t ≫ r = t ≫ r) hpt
      (bcAux_fst hIex ζ T' (t ≫ r) w hb) hv₁)) ?_
  exact congrArg (q.hom.app (Opposite.op T'))
    (LiftAlong.restrict_lift r ζ rfl (bcAux_fst hIex (ζ.restrict r) T' t w hL) hv₁).symm

/-- The comparison morphism `Π_{i'} W' ⟶ Π_i W` attached to a cartesian change of base,
over `f : X' ⟶ X`. -/
def liftAlongBaseChange (hcomm' : q ≫ p = p' ≫ g) :
    liftAlong B S hS i' p' ⟶ liftAlong B S hS i p :=
  ⟨{ app := fun T ↦ TypeCat.ofHom (bcApp q hIex hcomm' T.unop)
     naturality := fun _ _ r ↦ ConcreteCategory.hom_ext _ _ fun ζ ↦
       (bcApp_restrict q hIex hcomm' r.unop ζ).symm }⟩

/-- On sections over `T`, the comparison morphism is the pushforward `bcApp`. -/
@[simp]
theorem liftAlongBaseChange_app_apply (hcomm' : q ≫ p = p' ≫ g) (T : BigFppfOver B S hS)
    (ζ : LiftAlong B S hS i' p' T) :
    (liftAlongBaseChange q hIex hcomm').hom.app (Opposite.op T) ζ
      = bcApp q hIex hcomm' T ζ :=
  rfl

/-- The comparison morphism `Π_{i'} W' ⟶ Π_i W` lies over `f : X' ⟶ X`. -/
theorem liftAlongBaseChange_comp_liftAlongBase (hcomm' : q ≫ p = p' ≫ g) :
    liftAlongBaseChange q hIex hcomm' ≫ liftAlongBase B S hS i p
      = liftAlongBase B S hS i' p' ≫ f :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

/-! #### The compatibility a section of `I'` provides -/

/-- A section of `I'` lying over a section of `X'` lies, after `g`, over its image in `X`. -/
theorem bcCompat (hcomm : i' ≫ f = g ≫ i) {T : BigFppfOver B S hS}
    (b : X'.obj.obj (Opposite.op T)) {T' : BigFppfOver B S hS} (s : T' ⟶ T)
    (v : I'.obj.obj (Opposite.op T'))
    (hv : i'.hom.app (Opposite.op T') v = X'.obj.map s.op b) :
    i.hom.app (Opposite.op T') (g.hom.app (Opposite.op T') v)
      = X.obj.map s.op (f.hom.app (Opposite.op T) b) := by
  rw [← comp_app_congr hcomm (Opposite.op T') v, hv, app_map_op]

/-! #### The point of `Wt` over `I'` determined by a point of the dependent product -/

section Point

variable {Wt : FppfSheaf B S hS} {pt : Wt ⟶ I} {σ : X' ⟶ liftAlong B S hS i pt}
  (hσ : σ ≫ liftAlongBase B S hS i pt = f) (hcomm : i' ≫ f = g ≫ i)

include hσ hcomm in
/-- The compatibility under which a point of the dependent product over `X'` restricts to a
point of it over `I'`. -/
theorem bcPointSection_cond : (i' ≫ σ) ≫ liftAlongBase B S hS i pt = g ≫ i :=
  (Category.assoc i' σ (liftAlongBase B S hS i pt)).trans
    ((congrArg (fun m : X' ⟶ X ↦ i' ≫ m) hσ).trans hcomm)

include hσ hcomm in
/-- **The morphism `I' ⟶ Wt` over `I` that a point `σ : X' ⟶ Π_i Wt` determines.** The
fibre product `X' ×_X I` is `I'`, and `Wt` is the fibre product `Π_i Wt ×_X I` by
`AlgebraicGeometry.FormalSpace.DependentProduct.isPullback_liftAlongSection`, so restricting
the point along `i' : I' ⟶ X'` and evaluating its lifting rule at the identity gives a morphism
`I' ⟶ Wt` over `I`. -/
def bcPointSection : I' ⟶ Wt :=
  liftAlongCone B S hS (i' ≫ σ) g (bcPointSection_cond hσ hcomm)

/-- The morphism `bcPointSection hσ hcomm : I' ⟶ Wt` lies over `g : I' ⟶ I`. -/
theorem bcPointSection_comp_proj : bcPointSection hσ hcomm ≫ pt = g :=
  liftAlongCone_comp_proj B S hS (i' ≫ σ) g (bcPointSection_cond hσ hcomm)

/-- On a section `v` of `I'`, `bcPointSection hσ hcomm` is the lifting rule of `σ (i' v)`
evaluated at the identity on `g v`. -/
theorem bcPointSection_app {T : BigFppfOver B S hS} (v : I'.obj.obj (Opposite.op T))
    (h : i.hom.app (Opposite.op T) (g.hom.app (Opposite.op T) v)
      = X.obj.map (𝟙 T).op
        (σ.hom.app (Opposite.op T) (i'.hom.app (Opposite.op T) v)).base) :
    (bcPointSection hσ hcomm).hom.app (Opposite.op T) v
      = (σ.hom.app (Opposite.op T) (i'.hom.app (Opposite.op T) v)).lift T (𝟙 T)
        (g.hom.app (Opposite.op T) v) h :=
  LiftAlong.lift_congr rfl rfl rfl _ h

/-- For a section `v` of `I'` over the restriction of `b` along `t` and `w = g v`, the
section of `Wt` attached to `v` is the lifting rule of `σ b` evaluated at `w`. -/
private theorem bcPointSection_app_eq_lift {T T' : BigFppfOver B S hS}
    (b : X'.obj.obj (Opposite.op T)) (t : T' ⟶ T) (v : I'.obj.obj (Opposite.op T'))
    (hv : i'.hom.app (Opposite.op T') v = X'.obj.map t.op b)
    {w : I.obj.obj (Opposite.op T')} (hw : g.hom.app (Opposite.op T') v = w)
    (h : i.hom.app (Opposite.op T') w
      = X.obj.map t.op (σ.hom.app (Opposite.op T) b).base) :
    (bcPointSection hσ hcomm).hom.app (Opposite.op T') v
      = (σ.hom.app (Opposite.op T) b).lift T' t w h := by
  have hη : σ.hom.app (Opposite.op T') (i'.hom.app (Opposite.op T') v)
      = (σ.hom.app (Opposite.op T) b).restrict t := by
    rw [hv]
    exact app_map_op B S hS σ t b
  have hgoal : i.hom.app (Opposite.op T') (g.hom.app (Opposite.op T') v)
      = X.obj.map (𝟙 T').op
        (σ.hom.app (Opposite.op T') (i'.hom.app (Opposite.op T') v)).base := by
    rw [op_id, FunctorToTypes.map_id_apply, congrArg LiftAlong.base hη, hw]
    exact h
  exact (bcPointSection_app hσ hcomm v hgoal).trans
    (LiftAlong.lift_eq_of_eq_restrict (σ.hom.app (Opposite.op T) b) t _ hη
      (Category.id_comp t) hw hgoal h)

end Point

/-! #### Pulling a section back -/

section Cone

variable {Wt : FppfSheaf B S hS} {pt : Wt ⟶ I} {k : W ⟶ Wt} (hk : k ≫ pt = p)
  {σ : X' ⟶ liftAlong B S hS i pt} (hσ : σ ≫ liftAlongBase B S hS i pt = f)
  (hcomm : i' ≫ f = g ≫ i)
  (hWex : IsSectionwisePullback B S hS q p' k (bcPointSection hσ hcomm))
  (hcommW : q ≫ k = p' ≫ bcPointSection hσ hcomm)
  {Z : FppfSheaf B S hS} (α : Z ⟶ liftAlong B S hS i p) (β : Z ⟶ X')
  (hαβ : α ≫ liftAlongMap B S hS i k hk = β ≫ σ)

include hσ hαβ in
/-- The morphism `α : Z ⟶ Π_i W` of a cone over the comparison square lies over `β ≫ f`. -/
theorem bcCone_comp_base : α ≫ liftAlongBase B S hS i p = β ≫ f := by
  rw [← liftAlongMap_comp_base B S hS i k hk, ← hσ, ← Category.assoc, ← Category.assoc, hαβ]

include hσ hαβ in
/-- For a section `z` of `Z`, the base of `α z` is the image of `β z` under `f`. -/
theorem bcCone_base {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T)) :
    f.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)
      = (α.hom.app (Opposite.op T) z).base := by
  exact (comp_app_congr (bcCone_comp_base hk hσ α β hαβ) (Opposite.op T) z).symm

include hcomm in
/-- The compatibility with which the lifting rule of a section of `Π_i W` is fed when a
section of `Π_{i'} W'` is pulled back out of it. -/
theorem bcCone_cond {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (hbase : f.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)
      = (α.hom.app (Opposite.op T) z).base)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (v : I'.obj.obj (Opposite.op T'))
    (hv : i'.hom.app (Opposite.op T') v = X'.obj.map s.op (β.hom.app (Opposite.op T) z)) :
    i.hom.app (Opposite.op T') (g.hom.app (Opposite.op T') v)
      = X.obj.map s.op (α.hom.app (Opposite.op T) z).base :=
  (bcCompat hcomm (β.hom.app (Opposite.op T) z) s v hv).trans
    (congrArg (X.obj.map s.op) hbase)

include hk hσ hcomm hαβ in
/-- The value of the cone's lifting rule and the point of `I'` carry the same section of `Wt`,
which is what makes them a section of the fibre product `W' = W ×_{Wt} I'`. -/
theorem bcCone_compat {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (hbase : f.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)
      = (α.hom.app (Opposite.op T) z).base)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (v : I'.obj.obj (Opposite.op T'))
    (hv : i'.hom.app (Opposite.op T') v = X'.obj.map s.op (β.hom.app (Opposite.op T) z)) :
    k.hom.app (Opposite.op T')
        ((α.hom.app (Opposite.op T) z).lift T' s (g.hom.app (Opposite.op T') v)
          (bcCone_cond hcomm α β z hbase T' s v hv))
      = (bcPointSection hσ hcomm).hom.app (Opposite.op T') v := by
  have hpush : LiftAlong.pushforward B S hS i k hk T (α.hom.app (Opposite.op T) z)
      = σ.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z) :=
    congrArg (fun m : Z ⟶ liftAlong B S hS i pt ↦ m.hom.app (Opposite.op T) z) hαβ
  have hb : (σ.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)).base
      = (α.hom.app (Opposite.op T) z).base :=
    (congrArg (fun m : X' ⟶ X ↦ m.hom.app (Opposite.op T)
      (β.hom.app (Opposite.op T) z)) hσ).trans hbase
  have h' : i.hom.app (Opposite.op T') (g.hom.app (Opposite.op T') v)
      = X.obj.map s.op
        (σ.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)).base := by
    rw [hb]
    exact bcCone_cond hcomm α β z hbase T' s v hv
  refine Eq.trans ?_ (bcPointSection_app_eq_lift hσ hcomm _ s v hv rfl h').symm
  exact LiftAlong.lift_congr hpush rfl rfl (bcCone_cond hcomm α β z hbase T' s v hv) h'

include hk hσ hcomm hWex hαβ in
/-- The lifting rule of the section of `Π_{i'} W'` attached to a cone over the comparison
square. -/
def bcConeRule {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (hbase : f.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)
      = (α.hom.app (Opposite.op T) z).base)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (v : I'.obj.obj (Opposite.op T'))
    (hv : i'.hom.app (Opposite.op T') v = X'.obj.map s.op (β.hom.app (Opposite.op T) z)) :
    W'.obj.obj (Opposite.op T') :=
  bcPoint hWex
    ((α.hom.app (Opposite.op T) z).lift T' s (g.hom.app (Opposite.op T') v)
      (bcCone_cond hcomm α β z hbase T' s v hv))
    v (bcCone_compat hk hσ hcomm α β hαβ z hbase T' s v hv)

/-- The value of the cone's lifting rule at `v` lies over `v` under `p'`. -/
theorem bcConeRule_proj {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (hbase : f.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)
      = (α.hom.app (Opposite.op T) z).base)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (v : I'.obj.obj (Opposite.op T'))
    (hv : i'.hom.app (Opposite.op T') v = X'.obj.map s.op (β.hom.app (Opposite.op T) z)) :
    p'.hom.app (Opposite.op T') (bcConeRule q hk hσ hcomm hWex α β hαβ z hbase T' s v hv)
      = v :=
  bcPoint_snd hWex _ _ _

/-- The value of the cone's lifting rule at `v` maps under `q` to the lifting rule of `α z`
evaluated at `g v`. -/
theorem bcConeRule_snd {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (hbase : f.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)
      = (α.hom.app (Opposite.op T) z).base)
    (T' : BigFppfOver B S hS) (s : T' ⟶ T) (v : I'.obj.obj (Opposite.op T'))
    (hv : i'.hom.app (Opposite.op T') v = X'.obj.map s.op (β.hom.app (Opposite.op T) z)) :
    q.hom.app (Opposite.op T') (bcConeRule q hk hσ hcomm hWex α β hαβ z hbase T' s v hv)
      = (α.hom.app (Opposite.op T) z).lift T' s (g.hom.app (Opposite.op T') v)
          (bcCone_cond hcomm α β z hbase T' s v hv) :=
  bcPoint_fst hWex _ _ _

/-- The cone's lifting rule is compatible with restriction along `r : T'' ⟶ T'`. -/
theorem bcConeRule_map {T : BigFppfOver B S hS} (z : Z.obj.obj (Opposite.op T))
    (hbase : f.hom.app (Opposite.op T) (β.hom.app (Opposite.op T) z)
      = (α.hom.app (Opposite.op T) z).base)
    (T' T'' : BigFppfOver B S hS) (r : T'' ⟶ T') (s : T' ⟶ T)
    (v : I'.obj.obj (Opposite.op T'))
    (hv : i'.hom.app (Opposite.op T') v = X'.obj.map s.op (β.hom.app (Opposite.op T) z))
    (hv' : i'.hom.app (Opposite.op T'') (I'.obj.map r.op v)
      = X'.obj.map (r ≫ s).op (β.hom.app (Opposite.op T) z)) :
    W'.obj.map r.op (bcConeRule q hk hσ hcomm hWex α β hαβ z hbase T' s v hv)
      = bcConeRule q hk hσ hcomm hWex α β hαβ z hbase T'' (r ≫ s) (I'.obj.map r.op v) hv' := by
  have hcond : i.hom.app (Opposite.op T'') (I.obj.map r.op (g.hom.app (Opposite.op T') v))
      = X.obj.map (r ≫ s).op (α.hom.app (Opposite.op T) z).base :=
    (app_map_op B S hS i r (g.hom.app (Opposite.op T') v)).trans
      ((congrArg (X.obj.map r.op) (bcCone_cond hcomm α β z hbase T' s v hv)).trans
        (LiftAlong.map_comp_op_apply X.obj s r (α.hom.app (Opposite.op T) z).base).symm)
  refine bcPoint_eq hWex _ _ _ _ ?_ ?_
  · refine Eq.trans
      (app_map_op B S hS q r (bcConeRule q hk hσ hcomm hWex α β hαβ z hbase T' s v hv)) ?_
    refine Eq.trans (congrArg (W.obj.map r.op)
      (bcConeRule_snd q hk hσ hcomm hWex α β hαβ z hbase T' s v hv)) ?_
    refine Eq.trans ((α.hom.app (Opposite.op T) z).lift_map T' T'' r s
      (g.hom.app (Opposite.op T') v) (bcCone_cond hcomm α β z hbase T' s v hv) hcond) ?_
    exact LiftAlong.lift_congr rfl rfl (app_map_op B S hS g r v).symm _ _
  · exact (app_map_op B S hS p' r
      (bcConeRule q hk hσ hcomm hWex α β hαβ z hbase T' s v hv)).trans
      (congrArg (I'.obj.map r.op)
        (bcConeRule_proj q hk hσ hcomm hWex α β hαβ z hbase T' s v hv))

include hαβ in
/-- The section of `Π_{i'} W'` attached to a cone over the comparison square. -/
def bcConeApp (T : BigFppfOver B S hS) (z : Z.obj.obj (Opposite.op T)) :
    LiftAlong B S hS i' p' T where
  base := β.hom.app (Opposite.op T) z
  lift := bcConeRule q hk hσ hcomm hWex α β hαβ z (bcCone_base hk hσ α β hαβ z)
  lift_proj := bcConeRule_proj q hk hσ hcomm hWex α β hαβ z (bcCone_base hk hσ α β hαβ z)
  lift_map := fun T' T'' r s v hv hv' ↦
    bcConeRule_map q hk hσ hcomm hWex α β hαβ z (bcCone_base hk hσ α β hαβ z)
      T' T'' r s v hv hv'

/-- The section of `Π_{i'} W'` attached to a cone commutes with restriction along
`r : T₀ ⟶ T`. -/
theorem bcConeApp_restrict {T T₀ : BigFppfOver B S hS} (r : T₀ ⟶ T)
    (z : Z.obj.obj (Opposite.op T)) :
    (bcConeApp q hk hσ hcomm hWex α β hαβ T z).restrict r
      = bcConeApp q hk hσ hcomm hWex α β hαβ T₀ (Z.obj.map r.op z) := by
  refine LiftAlong.ext _ _ (app_map_op B S hS β r z).symm fun T' t v h h' ↦ ?_
  have hb : i'.hom.app (Opposite.op T') v
      = X'.obj.map (t ≫ r).op (β.hom.app (Opposite.op T) z) :=
    h.trans (LiftAlong.map_comp_op_apply X'.obj r t (β.hom.app (Opposite.op T) z)).symm
  refine Eq.trans
    (LiftAlong.restrict_lift r (bcConeApp q hk hσ hcomm hWex α β hαβ T z) rfl h hb) ?_
  refine bcPoint_eq hWex _ _
    (bcCone_compat hk hσ hcomm α β hαβ (Z.obj.map r.op z)
      (bcCone_base hk hσ α β hαβ (Z.obj.map r.op z)) T' t v h') _ ?_
    (bcConeRule_proj q hk hσ hcomm hWex α β hαβ z (bcCone_base hk hσ α β hαβ z)
      T' (t ≫ r) v hb)
  refine Eq.trans (bcConeRule_snd q hk hσ hcomm hWex α β hαβ z
    (bcCone_base hk hσ α β hαβ z) T' (t ≫ r) v hb) ?_
  exact (LiftAlong.lift_eq_of_eq_restrict (α.hom.app (Opposite.op T) z) r
    (α.hom.app (Opposite.op T₀) (Z.obj.map r.op z))
    (NatTrans.naturality_apply α.hom r.op z) (rfl : t ≫ r = t ≫ r) rfl _ _).symm

include hαβ in
/-- The morphism to `Π_{i'} W'` induced by a cone over the comparison square. -/
def bcCone : Z ⟶ liftAlong B S hS i' p' :=
  ⟨{ app := fun T ↦ TypeCat.ofHom (bcConeApp q hk hσ hcomm hWex α β hαβ T.unop)
     naturality := fun _ _ r ↦ ConcreteCategory.hom_ext _ _ fun z ↦
       (bcConeApp_restrict q hk hσ hcomm hWex α β hαβ r.unop z).symm }⟩

/-- The morphism induced by a cone, followed by the structure morphism to `X'`, is `β`. -/
theorem bcCone_comp_liftAlongBase :
    bcCone q hk hσ hcomm hWex α β hαβ ≫ liftAlongBase B S hS i' p' = β :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

/-- The morphism induced by a cone, followed by the comparison morphism, is `α`. -/
theorem bcCone_comp_liftAlongBaseChange (hcomm' : q ≫ p = p' ≫ g) :
    bcCone q hk hσ hcomm hWex α β hαβ ≫ liftAlongBaseChange q hIex hcomm' = α := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦
    ConcreteCategory.hom_ext _ _ fun z ↦ ?_))
  show bcApp q hIex hcomm' T.unop (bcConeApp q hk hσ hcomm hWex α β hαβ T.unop z)
    = α.hom.app T z
  refine LiftAlong.ext _ _ (bcCone_base hk hσ α β hαβ z) fun T' s w h h' ↦ ?_
  refine Eq.trans (bcConeRule_snd q hk hσ hcomm hWex α β hαβ z
    (bcCone_base hk hσ α β hαβ z) T' s
    (bcAux hIex (bcConeApp q hk hσ hcomm hWex α β hαβ T.unop z) T' s w h)
    (bcAux_fst hIex (bcConeApp q hk hσ hcomm hWex α β hαβ T.unop z) T' s w h)) ?_
  exact LiftAlong.lift_congr rfl rfl
    (bcAux_snd hIex (bcConeApp q hk hσ hcomm hWex α β hαβ T.unop z) T' s w h) _ _

/-- A morphism `Z ⟶ Π_{i'} W'` whose composites with the comparison morphism and the structure
morphism are `α` and `β` is the morphism induced by the cone. -/
theorem bcCone_uniq (hcomm' : q ≫ p = p' ≫ g) (m : Z ⟶ liftAlong B S hS i' p')
    (hm₁ : m ≫ liftAlongBaseChange q hIex hcomm' = α)
    (hm₂ : m ≫ liftAlongBase B S hS i' p' = β) :
    m = bcCone q hk hσ hcomm hWex α β hαβ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦
    ConcreteCategory.hom_ext _ _ fun z ↦ ?_))
  have hbase : (m.hom.app T z).base = β.hom.app T z :=
    congrArg (fun n : Z ⟶ X' ↦ n.hom.app T z) hm₂
  have hpush : bcApp q hIex hcomm' T.unop (m.hom.app T z) = α.hom.app T z :=
    congrArg (fun n : Z ⟶ liftAlong B S hS i p ↦ n.hom.app T z) hm₁
  show m.hom.app T z = bcConeApp q hk hσ hcomm hWex α β hαβ T.unop z
  refine LiftAlong.ext _ _ hbase fun T' s v hv hv' ↦ ?_
  have hA : i.hom.app (Opposite.op T') (g.hom.app (Opposite.op T') v)
      = X.obj.map s.op (f.hom.app T (m.hom.app T z).base) :=
    bcCompat hcomm (m.hom.app T z).base s v hv
  have hvv : v = bcAux hIex (m.hom.app T z) T' s (g.hom.app (Opposite.op T') v) hA :=
    bcPoint_eq hIex (X'.obj.map s.op (m.hom.app T z).base)
      (g.hom.app (Opposite.op T') v)
      ((app_map_op B S hS f s (m.hom.app T z).base).trans hA.symm) v hv rfl
  refine bcPoint_eq hWex _ _
    (bcCone_compat hk hσ hcomm α β hαβ z (bcCone_base hk hσ α β hαβ z) T' s v hv') _ ?_
    ((m.hom.app T z).lift_proj T' s v hv)
  refine Eq.trans (congrArg (q.hom.app (Opposite.op T'))
    (LiftAlong.lift_congr (ξ := m.hom.app T z) rfl (rfl : s = s) hvv hv
      (bcAux_fst hIex (m.hom.app T z) T' s (g.hom.app (Opposite.op T') v) hA))) ?_
  exact LiftAlong.lift_congr hpush rfl rfl hA
    (bcCone_cond hcomm α β z (bcCone_base hk hσ α β hαβ z) T' s v hv')

end Cone

section Square

variable {Wt : FppfSheaf B S hS} {pt : Wt ⟶ I} {k : W ⟶ Wt} (hk : k ≫ pt = p)
  {σ : X' ⟶ liftAlong B S hS i pt} (hσ : σ ≫ liftAlongBase B S hS i pt = f)
  (hcomm : i' ≫ f = g ≫ i)
  (hWex : IsSectionwisePullback B S hS q p' k (bcPointSection hσ hcomm))
  (hcommW : q ≫ k = p' ≫ bcPointSection hσ hcomm)

include hk hσ hcomm hcommW in
/-- The comparison square commutes: the comparison morphism followed by
`liftAlongMap B S hS i k hk` equals the structure morphism to `X'` followed by `σ`. -/
theorem liftAlongBaseChange_comp_liftAlongMap (hcomm' : q ≫ p = p' ≫ g) :
    liftAlongBaseChange q hIex hcomm' ≫ liftAlongMap B S hS i k hk
      = liftAlongBase B S hS i' p' ≫ σ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦
    ConcreteCategory.hom_ext _ _ fun ξ ↦ ?_))
  show LiftAlong.pushforward B S hS i k hk T.unop (bcApp q hIex hcomm' T.unop ξ)
    = σ.hom.app T ξ.base
  refine LiftAlong.ext _ _
    ((congrArg (fun m : X' ⟶ X ↦ m.hom.app T ξ.base) hσ).symm) fun T' t w h h' ↦ ?_
  have hy := ξ.lift_proj T' t (bcAux hIex ξ T' t w h) (bcAux_fst hIex ξ T' t w h)
  have hkq := comp_app_congr hcommW (Opposite.op T')
    (ξ.lift T' t (bcAux hIex ξ T' t w h) (bcAux_fst hIex ξ T' t w h))
  show k.hom.app (Opposite.op T')
      (q.hom.app (Opposite.op T') (ξ.lift T' t (bcAux hIex ξ T' t w h)
        (bcAux_fst hIex ξ T' t w h)))
    = (σ.hom.app T ξ.base).lift T' t w h'
  refine Eq.trans hkq ?_
  refine Eq.trans (congrArg ((bcPointSection hσ hcomm).hom.app (Opposite.op T')) hy) ?_
  exact bcPointSection_app_eq_lift hσ hcomm ξ.base t _ (bcAux_fst hIex ξ T' t w h)
    (bcAux_snd hIex ξ T' t w h) h'

include hσ hcomm hWex hcommW in
/-- The dependent product `Π_i W` commutes with base change and the dependent
product preserves fibre products, in one square. Let `i : I ⟶ X` and `p : W ⟶ I` be morphisms
of fppf sheaves, let `k : W ⟶ Wt` be a morphism over `I` and let `σ : X' ⟶ Π_i Wt` be a
point of the dependent product of `pt : Wt ⟶ I`, lying over `f : X' ⟶ X`. Form the fibre
product `I' = X' ×_X I` and let `W'` be the fibre product of `W` with `I'` over `Wt`, taken
along `k` and along the morphism `I' ⟶ Wt` that `σ` determines. Then the square whose sides are
the comparison morphism `Π_{i'} W' ⟶ Π_i W`, the two structure morphisms, and `σ` is
cartesian.

This is the Beck–Chevalley isomorphism for the dependent product together with the fact that a
dependent product, being a right adjoint, preserves fibre products. The case `pt = 𝟙 I` is
`AlgebraicGeometry.FormalSpace.DependentProduct.isPullback_liftAlongBaseChange`. -/
theorem isPullback_liftAlongMap (hcomm' : q ≫ p = p' ≫ g) :
    IsPullback (liftAlongBaseChange q hIex hcomm') (liftAlongBase B S hS i' p')
      (liftAlongMap B S hS i k hk) σ :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (liftAlongBaseChange_comp_liftAlongMap q hIex hk hσ hcomm hcommW hcomm')
    (fun c ↦ bcCone q hk hσ hcomm hWex c.fst c.snd c.condition)
    (fun c ↦ bcCone_comp_liftAlongBaseChange q hIex hk hσ hcomm hWex c.fst c.snd c.condition
      hcomm')
    (fun c ↦ bcCone_comp_liftAlongBase q hk hσ hcomm hWex c.fst c.snd c.condition)
    (fun c m hm₁ hm₂ ↦ bcCone_uniq q hIex hk hσ hcomm hWex c.fst c.snd c.condition hcomm'
      m hm₁ hm₂))

end Square

/-- The dependent product `Π_i W` commutes with base change: for a cartesian
square whose sides are `i' : I' ⟶ X'`, `g : I' ⟶ I`, `f : X' ⟶ X` and `i : I ⟶ X`, and for
`p : W ⟶ I` with base change `p' : W' ⟶ I'`, the square whose sides are the comparison
morphism `Π_{i'} W' ⟶ Π_i W`, the two structure morphisms and `f` is cartesian.

This is the case `pt = 𝟙 I` of
`AlgebraicGeometry.FormalSpace.DependentProduct.isPullback_liftAlongMap`: the dependent product
of the identity of `I` is `X` itself, so a point of it over `X'` is a morphism `X' ⟶ X` and the
morphism `I' ⟶ I` it determines is `g`. -/
theorem isPullback_liftAlongBaseChange
    (hWex : IsSectionwisePullback B S hS p' q g p) (hcomm : i' ≫ f = g ≫ i)
    (hcomm' : q ≫ p = p' ≫ g) :
    IsPullback (liftAlongBaseChange q hIex hcomm') (liftAlongBase B S hS i' p')
      (liftAlongBase B S hS i p) f := by
  have hk : p ≫ 𝟙 I = p := Category.comp_id p
  have hσ : (f ≫ inv (liftAlongBase B S hS i (𝟙 I))) ≫ liftAlongBase B S hS i (𝟙 I) = f := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hs : bcPointSection hσ hcomm = g :=
    (Category.comp_id _).symm.trans (bcPointSection_comp_proj hσ hcomm)
  have hWex' : IsSectionwisePullback B S hS q p' p (bcPointSection hσ hcomm) := by
    rw [hs]
    exact isSectionwisePullback_flip hWex
  have hcommW : q ≫ p = p' ≫ bcPointSection hσ hcomm := by
    rw [hs]
    exact hcomm'
  have H := isPullback_liftAlongMap q hIex hk hσ hcomm hWex' hcommW hcomm'
  refine H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (asIso (liftAlongBase B S hS i (𝟙 I))) (by simp) (by simp) ?_ (by simp)
  show liftAlongMap B S hS i p hk ≫ liftAlongBase B S hS i (𝟙 I)
    = (Iso.refl (liftAlong B S hS i p)).hom ≫ liftAlongBase B S hS i p
  rw [Iso.refl_hom, Category.id_comp]
  exact liftAlongMap_comp_base B S hS i p hk

end BaseChange

end AlgebraicGeometry.FormalSpace.DependentProduct

end

