module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteOfPresheaf

/-!
# The presheaf of abelian groups of a descent datum on the site of the members

The restriction map of the presheaf of abelian groups of a descent datum on the site of the
members of an étale covering, carried behind names for its two factors, together with the bridge
that identifies it with the restriction map of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbMap_laws` and with both of its
functorial laws as equations of morphisms of `AddCommGrpCat`.  The sections, the written-out
restriction map and its two additive laws are those of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteOfPresheaf.lean`; what is
added here are the identifications between the named spelling and that one.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbFn_apply_of_eq`: **the bridge** --
  the additive map built out of `.memberDatumAbFn_laws` is the one built out of
  `.memberDatumAbMap_laws`, read on a section carried as a variable.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbFnHom_id` and
  `.memberDatumAbFnHom_comp`: **the two functorial laws of that restriction map, as equations of
  morphisms of `AddCommGrpCat`** -- the `map_id` and `map_comp` a presheaf on
  `.MemberSite` valued in `AddCommGrpCat` asks for.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctorOfLaws`: the builder those two laws
  are to be fed to.

## Implementation notes

The mathematics is upstream; every declaration here exists to keep one identification of two
spellings of the same term in a declaration of its own.  The restriction map of this presheaf is
a term so large that comparing two independent elaborations of it is a deterministic exhaustion
of the recursion depth, and all three of the walls the compiler can report -- `maxRecDepth` in
the elaborator, the heartbeat budget at `whnf` or `isDefEq`, and a deterministic timeout of the
**kernel** -- occur on this one restriction map.  What follows is the record of which
shape avoids each of them.

**The functor is assembled through `.memberFunctorOfLaws`, which takes no instance argument
and does its own bundling.**
A generic builder `{C} [Category C]` defers that instance: `?instC` is still a metavariable while
the `map` field -- the giant term -- is elaborated, and solving it afterwards forces a traversal
of that term which reports maximum recursion depth.  Here the category is `AddCommGrpCat.{u}`
and the instance is resolved before any field is seen.

**The restriction map of the functor is the named constant `.memberDatumAbFn` and not the
written-out restriction map of `.memberDatumAbMap_laws`.**  The `map` field of the structure
instance has to be instantiated at `𝟙 p` for `map_id` and at `g ≫ h` for `map_comp`, and the
instantiation of a written-out copy of that text is not the term a law stated at `𝟙 p` carries --
reconciling the two is a deterministic timeout of the kernel.  Behind the named
constant each instantiation is an application of one constant to arguments, and the field carries
no proof at all, so the nested-proof abstraction a `def` body is subjected to has nothing to
lift and the kernel has nothing of this size to check.

**The bridge from the named restriction map to the written-out one is split into one
identification per declaration**, which is the discipline `.memberDatumAb_comp_apply'` and
`.val_app_apply_of_eq_id` upstream were introduced for.  The three are
`.memberDatumAbFn_eq_app` (a delta and nothing else),
`.memberDatumAbTransHom_val_app_apply` (the transition factor, on an opaque section),
`.memberDatumAbRestrFn_val_app_congr` (the restriction factor, under a fixed transition) and
`.memberDatumAbMap_laws_apply` upstream (the written-out reading as the bundled law), joined two
at a time by `.memberDatumAbFn_apply_trans`, `.memberDatumAbFn_apply_written` and
`.memberDatumAbFn_apply_of_eq`.  Each middle term is spelled the same way in the two statements
it joins, so no `Eq.trans` has anything to identify.  Three links in one declaration, or two
links of which one is the delta, each exhaust the recursion depth; two links
with the delta already paid is what fits.

The restriction factor is rewritten **under the written-out transition morphism and not under the
named one**.  The two modules the congruence quantifies over are read off the transition
morphism's type; off `transitionEtaleForm` that type is a `Quiver.Hom` application and the
reading is one assignment, while off the named constant it is whatever was inferred for a `def`
with no type ascription, and recovering `?M ⟶ ?N` from it exhausts the heartbeat budget at
`whnf`.  Crossing to the written-out morphism first, on a section carried as a variable, costs
nothing: that is `.memberDatumAbTransHom_val_app_apply`.

Both factors are named constants (`.memberDatumAbTransHom`, `.memberDatumAbRestrFn`) for the
same reason the restriction map is: each is written out exactly once, in its own `def`, and the
single identification it owes is paid once, in its own theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### A functor out of the opposite of the site of the members, from its data -/

/-- **A functor from the opposite of the site of the members to `AddCommGrpCat` out of its
objects, the underlying functions of its restriction maps, their two additive laws and the two
functorial laws on sections.**

The bundling -- `.AddMonoidHomLaws.toAddMonoidHom` and `AddCommGrpCat.ofHom` -- happens **here**,
where every object, function and law is a variable, and nowhere in a consumer's `def`.  That is
forced twice over.  `Lean.Meta.abstractNestedProofs` rewrites the body of a `def`, replacing every
nested proof whose arguments are not all local variables by an auxiliary theorem which the
**kernel** type-checks on its own; applied to a bundled restriction map of this size the kernel
reports a deterministic timeout for the restriction map written out and for it carried
behind two named factors alike.  And the target category is fixed, so its `Category` instance is
resolved before any field is elaborated, where a generic builder over `{C} [Category C]` would
leave it a metavariable inside the restriction map and exhaust the recursion depth when solving
it.

The two functorial laws are asked for **on sections and unbundled**: `.map_id` and `.map_comp` of
the structure instance are reached from them by `.addCommGrpCat_ofHom_eq_id` and
`.addCommGrpCat_ofHom_eq_comp` with `.AddMonoidHomLaws.toAddMonoidHom_apply` unfolding the
bundling, all on variables, so a consumer owes only the two laws its own mathematics proves. -/
def memberFunctorOfLaws (obj : (MemberSite B S hS Yi f hf)ᵒᵖ → AddCommGrpCat.{u})
    (Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (↥(obj p) → ↥(obj q)))
    (hlaws : ∀ (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q), AddMonoidHomLaws (Fn p q g))
    (hid : ∀ (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m : ↥(obj p)), Fn p p (𝟙 p) m = m)
    (hcomp : ∀ (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (m : ↥(obj p)),
      Fn q r h (Fn p q g m) = Fn p r (g ≫ h) m) :
    (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj := obj
  map {p q} g := AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom (hlaws p q g))
  map_id p := addCommGrpCat_ofHom_eq_id _ fun m =>
    Eq.trans (AddMonoidHomLaws.toAddMonoidHom_apply (hlaws p p (𝟙 p)) m) (hid p m)
  map_comp {p q r} g h := addCommGrpCat_ofHom_eq_comp _ _ _ fun m =>
    Eq.trans (AddMonoidHomLaws.toAddMonoidHom_apply (hlaws q r h) _)
      (Eq.trans (congrArg (Fn q r h)
          (AddMonoidHomLaws.toAddMonoidHom_apply (hlaws p q g) m))
        (Eq.trans (hcomp p q r g h m)
          (Eq.symm (AddMonoidHomLaws.toAddMonoidHom_apply (hlaws p r (g ≫ h)) m))))

/-! ### Two congruences for a morphism of `𝒪`-modules read on a section -/

/-- **A morphism of `𝒪`-modules equal to another acts the same on a section.**  The companion of
`.val_app_apply_of_eq_id` for an equation between two morphisms, and stated the same way: the two
morphisms are variables, so each is read off a consumer's goal by one assignment even though
`CategoryTheory.SheafOfModules.Hom.val` is a projection.

The chart is **explicit**, unlike there.  A consumer of this one supplies the section from a
hypothesis rather than from the goal, so the chart is not read off a `.val.app` already in the
goal; left implicit it has to be recovered from the type of that section, which is an inversion
of `AlgebraicGeometry.Space.QuasiCoherentDescent.smallEtalePostcomp` under
`CategoryTheory.Functor.obj` and exhausts the recursion depth. -/
theorem val_app_apply_of_eq' (C₀ : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS C₀.1 C₀.2} (A A' : M ⟶ N) (hA : A = A')
    (Z : (smallEtaleRingedSite B S hS C₀.1 C₀.2).Cᵒᵖ) (z : M.val.obj Z) :
    A.val.app Z z = A'.val.app Z z := by
  subst hA
  rfl

/-- **A morphism of `𝒪`-modules equal to another acts the same on a section, with the chart
implicit.**  The companion of `.val_app_apply_of_eq'` for a consumer whose section comes from the
**goal** rather than from a hypothesis: there the chart is read off a `.val.app` the goal already
contains, by one assignment, and supplying it explicitly instead makes its own type be checked
against `(smallEtaleRingedSite …).Cᵒᵖ` and exhausts the recursion depth. -/
theorem val_app_apply_of_eq_goal (C₀ : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS C₀.1 C₀.2} (A A' : M ⟶ N) (hA : A = A')
    {Z : (smallEtaleRingedSite B S hS C₀.1 C₀.2).Cᵒᵖ} (z : M.val.obj Z) :
    A.val.app Z z = A'.val.app Z z := by
  subst hA
  rfl

/-- **A morphism of `𝒪`-modules acts the same on two equal sections.**  The congruence in the
section rather than in the morphism, with the chart explicit for the same reason as at
`.val_app_apply_of_eq'`.

The morphism is one variable and not two, so that a consumer rewrites the section **under a
fixed** morphism: the two identifications a bridge between a named restriction map and a
written-out one owes are the morphism and the section, and performing them together exhausts the
recursion depth. -/
theorem val_app_apply_congr (C₀ : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS C₀.1 C₀.2} (A : M ⟶ N)
    (Z : (smallEtaleRingedSite B S hS C₀.1 C₀.2).Cᵒᵖ) (z z' : M.val.obj Z) (hz : z = z') :
    A.val.app Z z = A.val.app Z z' := by
  subst hz
  rfl

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-! ### The two factors of the restriction map, named -/

/-- **The restriction factor of the restriction map, at the type its own body carries**: the
restriction of a section of the component module at the source along the chart the morphism of the
site induces.  Written out here and nowhere else. -/
def memberDatumAbRestrFnW (D : DescentDatum B S hS Yi f) (p q : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (g : p ⟶ q) : ↥(memberDatumObj B S hS Yi f hf D p) →
      ↥((D.F p.unop.1).val.obj (Opposite.op (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f
      hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf
      p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi
      q.unop.1) q.unop.2))))) :=
  fun m => (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S
  hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
  (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))).obj
  (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y := (((smallEtalePostcomp B S hS
  (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
  (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
  p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi
  f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)))) m)

/-- **The restriction factor, read on a section carried as a variable.**  One delta and one
`subst`, at the type the body carries, so nothing is crossed here. -/
theorem memberDatumAbRestrFnW_apply_of_eq (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (z w : ↥(memberDatumObj B S hS Yi f hf D p)) (hzw : z = w) :
    memberDatumAbRestrFnW B S hS Yi f hf D p q g z =
      (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS
      (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y := (((smallEtalePostcomp
      B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
      p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2)))) (memberTransitionHom B S
      hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)))) w) := by
  subst hzw
  rfl

/-- **The restriction factor retyped onto the sections of the étale restriction.**  The sections
of the component module over the induced chart and the sections of the étale restriction over the
identity chart are one type definitionally and not syntactically; the crossing is performed here,
in a declaration whose body is a bare constant, so that the transition factor can be applied to
this one with nothing left to identify. -/
def memberDatumAbRestrFn (D : DescentDatum B S hS Yi f) (p q : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (g : p ⟶ q) : ↥(memberDatumObj B S hS Yi f hf D p) →
      ↥(((etaleModulePullback.{u, u} B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop))).obj (D.F p.unop.1)).val.obj (Opposite.op
      (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))) :=
  memberDatumAbRestrFnW B S hS Yi f hf D p q g

/-- **The retyped restriction factor, read on a section carried as a variable.**
`.memberDatumAbRestrFnW_apply_of_eq` across the retyping, which is one delta of a constant. -/
theorem memberDatumAbRestrFn_apply_of_eq (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (z w : ↥(memberDatumObj B S hS Yi f hf D p)) (hzw : z = w) :
    memberDatumAbRestrFn B S hS Yi f hf D p q g z =
      (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS
      (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y := (((smallEtalePostcomp
      B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
      p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2)))) (memberTransitionHom B S
      hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)))) w) :=
  memberDatumAbRestrFnW_apply_of_eq B S hS Yi f hf D p q g z w hzw

/-- **The transition factor of the restriction map**: the bundled reading of the transition of the
datum at the pair of charts the morphism of the site induces.  Written out here and nowhere else,
and **type-ascribed**: the two modules a congruence in the section quantifies over are read off
this type, and off a `def` with no ascription recovering them exhausts the heartbeat budget at
`whnf`. -/
def memberDatumAbTransHom (D : DescentDatum B S hS Yi f) (p q : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (g : p ⟶ q) :
    ((etaleModulePullback.{u, u} B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom
    B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
    hS Yi f hf g.unop))).obj (D.F p.unop.1) ⟶ (etaleModulePullback.{u, u} B S hS (memberChartMap B S
    hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S
    hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop))).obj (D.F q.unop.1)) :=
  (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
  q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
  (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S
  hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
  Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f
  hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
  g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)
  (memberHom B S hS Yi f hf (𝟙 q).unop) rfl))

omit [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.obj)] in
/-- **The named transition factor is the written-out one.**  A delta step and nothing else. -/
theorem memberDatumAbTransHom_eq (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) :
    memberDatumAbTransHom B S hS Yi f hf D p q g =
      (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
      (memberHom B S hS Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)) := rfl

/-! ### The bridge to the restriction map of `.memberDatumAbMap_laws`, one link at a time -/

omit [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.obj)] in
/-- **Link 1: the transition factor, named to written-out, on an opaque section.** -/
theorem memberDatumAbTransHom_val_app_apply (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (y :
      ↥(((etaleModulePullback.{u, u} B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop))).obj (D.F p.unop.1)).val.obj (Opposite.op
      (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) :
    (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) y =
      (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
      (memberHom B S hS Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) y :=
  val_app_apply_of_eq' B S hS (chartSpace B S hS (Yi q.unop.1) q.unop.2) _ _
    (memberDatumAbTransHom_eq B S hS Yi f hf D p q g)
    (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) y

/-- **Link 2: the restriction factor, named to written-out, under the written-out
transition.** -/
theorem memberDatumAbRestrFn_val_app_congr (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (z w : ↥(memberDatumObj B S hS Yi f hf D p)) (hzw : z = w) :
    (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
    q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
    (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B
    S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B
    S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS
    Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi
    f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
    g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart B S
    hS (Yi q.unop.1) q.unop.2)) (memberDatumAbRestrFn B S hS Yi f hf D p q g z) =
      (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
      (memberHom B S hS Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) (ModuleCat.Hom.hom ((D.F
      p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi
      f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi
      q.unop.1) q.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf g.unop)))) w) :=
  val_app_apply_congr B S hS (chartSpace B S hS (Yi q.unop.1) q.unop.2)
    (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
    q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
    (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B
    S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B
    S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS
    Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi
    f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
    g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl))
    (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) _ _
    (memberDatumAbRestrFn_apply_of_eq B S hS Yi f hf D p q g z w hzw)

/-- **Link 3: the written-out reading is the bundled law.**  `.memberDatumAbMap_laws_apply`
reversed. -/
theorem memberDatumAbMap_laws_apply_symm (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (w : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
    q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
    (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B
    S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B
    S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS
    Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi
    f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
    g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart B S
    hS (Yi q.unop.1) q.unop.2)) (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X :=
    (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
    Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f
    hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y :=
    (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS
    Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS
    Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
    (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)))) w) =
      (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbMap_laws B S hS Yi f hf D p q g)).toZeroHom.toFun w :=
  Eq.symm (memberDatumAbMap_laws_apply B S hS Yi f hf D p q g w)

/-- **Links 2 and 3 joined.** -/
theorem memberDatumAbRestrFn_val_app_eq_laws (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (z w : ↥(memberDatumObj B S hS Yi f hf D p)) (hzw : z = w) :
    (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
    q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
    (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B
    S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B
    S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS
    Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi
    f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
    g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart B S
    hS (Yi q.unop.1) q.unop.2)) (memberDatumAbRestrFn B S hS Yi f hf D p q g z) =
      (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbMap_laws B S hS Yi f hf D p q g)).toZeroHom.toFun w :=
  Eq.trans (memberDatumAbRestrFn_val_app_congr B S hS Yi f hf D p q g z w hzw)
    (memberDatumAbMap_laws_apply_symm B S hS Yi f hf D p q g w)

/-- **The named reading is the bundled law, with the section carried as a variable.**  Link 1 at
the named restriction factor, then links 2 and 3.  This is the only declaration that crosses
between the sections of the étale restriction and the sections of the presheaf while doing
anything else, and what it does besides is two applications of named constants. -/
theorem memberDatumAbNamedRead_eq_laws (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (z w : ↥(memberDatumObj B S hS Yi f hf D p)) (hzw : z = w) :
    (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app (Opposite.op (chartSpaceIdChart B S hS
    (Yi q.unop.1) q.unop.2)) (memberDatumAbRestrFn B S hS Yi f hf D p q g z) =
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf D p q
      g)).toZeroHom.toFun w :=
  Eq.trans (memberDatumAbTransHom_val_app_apply B S hS Yi f hf D p q g
      (memberDatumAbRestrFn B S hS Yi f hf D p q g z))
    (memberDatumAbRestrFn_val_app_eq_laws B S hS Yi f hf D p q g z w hzw)

/-! ### The restriction map of the presheaf of abelian groups -/

/-- **The two additive laws of the restriction map of the presheaf of abelian groups**, at the
reading through the two **named** factors.

The function is carried as a lambda over those two constants and not behind a name of its own.
A name would have to be unfolded to reach either factor, and that one delta -- in every
spelling and at every type -- exhausts the recursion depth; as a lambda over two constants it is
beta, which is free, and it carries no nested proof for `Lean.Meta.abstractNestedProofs` to hand
the kernel separately.  Both laws read every argument off the goal. -/
theorem memberDatumAbFn_laws (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) :
    AddMonoidHomLaws (M := ↥(memberDatumObj B S hS Yi f hf D p))
      (N := ↥(memberDatumObj B S hS Yi f hf D q))
      (fun m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app (Opposite.op
      (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) (memberDatumAbRestrFn B S hS Yi f hf D p q
      g m)) :=
  ⟨val_app_apply_zero _ _ (moduleCat_hom_apply_zero _),
      fun x y => val_app_apply_add _ _ _ _ (moduleCat_hom_apply_add _ x y)⟩

/-- **THE BRIDGE: the additive map `.AddMonoidHomLaws.toAddMonoidHom` builds out of
`.memberDatumAbFn_laws` is the one it builds out of `.memberDatumAbMap_laws`, read on a section
carried as a variable.**

`.AddMonoidHomLaws.toAddMonoidHom_apply` unfolds the bundling -- a beta step, because the function
is a lambda -- and `.memberDatumAbNamedRead_eq_laws` is the identification of the named reading
with the law.

With the section a variable this is usable twice over, exactly as
`.memberDatumAbMap_laws_apply_of_eq` upstream is: at `z := w` it is `.memberDatumAbFn_apply`, and
at `z` the value of another such reading it unfolds the outer of two nested readings while
respelling the inner one. -/
theorem memberDatumAbFn_apply_of_eq (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (z w : ↥(memberDatumObj B S hS Yi f hf D p)) (hzw : z = w) :
    (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbFn_laws B S hS Yi f hf D p q g)).toZeroHom.toFun
    z =
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf D p q
      g)).toZeroHom.toFun w :=
  Eq.trans (AddMonoidHomLaws.toAddMonoidHom_apply _ z)
    (memberDatumAbNamedRead_eq_laws B S hS Yi f hf D p q g z w hzw)

/-- **The bridge at one section**: `.memberDatumAbFn_apply_of_eq` at `z := w := m`. -/
theorem memberDatumAbFn_apply (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbFn_laws B S hS Yi f hf D p q g)).toZeroHom.toFun
    m =
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf D p q
      g)).toZeroHom.toFun m :=
  memberDatumAbFn_apply_of_eq B S hS Yi f hf D p q g m m rfl

/-! ### The two functorial laws of the restriction map -/

/-- **The identity law of the restriction map on a section.**  The bridge, then
`.memberDatumAbMap_laws_id_apply`. -/
theorem memberDatumAbFn_id_apply (D : DescentDatum B S hS Yi f)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbFn_laws B S hS Yi f hf D p p (𝟙
    p))).toZeroHom.toFun m = m :=
  Eq.trans (memberDatumAbFn_apply B S hS Yi f hf D p p (𝟙 p) m)
    (memberDatumAbMap_laws_id_apply B S hS Yi f hf D p m)

/-- **The composition law of the restriction map on a section.**  The bridge with its section a
variable unfolds the outer of the two nested readings while the inner one is respelled by the
bridge at a section; `.memberDatumAbMap_laws_comp_apply` is the law in the middle. -/
theorem memberDatumAbFn_comp_apply (D : DescentDatum B S hS Yi f)
    (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbFn_laws B S hS Yi f hf D q r h)).toZeroHom.toFun
    ((AddMonoidHomLaws.toAddMonoidHom (memberDatumAbFn_laws B S hS Yi f hf D p q g)).toZeroHom.toFun
    m) =
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbFn_laws B S hS Yi f hf D p r (g ≫
      h))).toZeroHom.toFun m :=
  Eq.trans (memberDatumAbFn_apply_of_eq B S hS Yi f hf D q r h _ _
      (memberDatumAbFn_apply B S hS Yi f hf D p q g m))
    (Eq.trans (memberDatumAbMap_laws_comp_apply B S hS Yi f hf D p q r g h m)
      (Eq.symm (memberDatumAbFn_apply B S hS Yi f hf D p r (g ≫ h) m)))

/-! ### The two laws as equations of morphisms of `AddCommGrpCat` -/

/-- **`map_id` of the presheaf of abelian groups**, at the named reading. -/
theorem memberDatumAbFnHom_id (D : DescentDatum B S hS Yi f)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbFn_laws B S hS Yi f hf D p p (𝟙 p))) =
      𝟙 (AddCommGrpCat.of (memberDatumObj B S hS Yi f hf D p)) :=
  addCommGrpCat_ofHom_eq_id _ fun m => memberDatumAbFn_id_apply B S hS Yi f hf D p m

/-- **`map_comp` of the presheaf of abelian groups**, at the named reading. -/
theorem memberDatumAbFnHom_comp (D : DescentDatum B S hS Yi f)
    (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) :
    AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbFn_laws B S hS Yi f hf D p r (g ≫ h))) =
      AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbFn_laws B S hS Yi f hf D p q g)) ≫
      AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbFn_laws B S hS Yi f hf D q r h)) :=
  addCommGrpCat_ofHom_eq_comp _ _ _ fun m =>
    memberDatumAbFn_comp_apply B S hS Yi f hf D p q r g h m

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
