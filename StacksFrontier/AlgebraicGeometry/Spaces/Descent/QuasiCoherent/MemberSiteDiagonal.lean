module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteAbFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteCompatibleFamily

/-!
# The restriction map of the presheaf of a descent datum along a diagonal arrow

Let `D` be a descent datum for quasi-coherent modules relative to a family `(f i : Y i ⟶ X)` of
algebraic spaces étale over an algebraic space `X`.
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteAbFunctor.lean` assembles the
presheaf of abelian groups of `D` on the site of the charts of the members, and
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteCompatibleFamily.lean`
reduces its sheaf condition to unique gluing along the arrows of that site which come from
morphisms of charts of one member — the *diagonal* arrows
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDiagHom`.

**This file proves the one thing that reduction leaves owed: along a diagonal arrow the restriction
map of that presheaf is plain restriction inside the component module `D.F i`.**  The transition
factor of the restriction map collapses, because the two legs of the test space of a diagonal arrow
are one and the same morphism
(`AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartMap_memberDiagHom`), so the transition is
a transition from a member to itself along one leg and hence the identity; and the restriction
factor is restriction along the given morphism of charts, because the chart a diagonal arrow
induces is the source chart of that arrow.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberTransitionChart_memberDiagHom` and
  `.heq_memberTransitionHom_memberDiagHom`: **the chart a diagonal arrow induces is the source
  chart of that arrow, and the morphism of charts it induces is that arrow's own morphism of
  charts.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.heq_transitionEtaleForm_id`: **the bundled reading
  of a transition whose two legs agree is the identity**, with both members, both legs and all the
  data depending on them carried as variables.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.heq_memberDatumAbFunctor_map_of_leg_eq`: **the
  restriction map of the presheaf of abelian groups of a descent datum along an arrow whose two
  legs agree is plain restriction inside the component module**, for an arbitrary arrow of the site
  and with the agreement of the legs a hypothesis.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbFunctor_map_memberDiagHom`: **that at
  a diagonal arrow**, which is the statement the sheaf condition of the presheaf is owed.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctorOfLawsV_obj_memberPair`,
  `.memberDatumAbFunctor_map_memberDiagHom_eq` and
  `.memberDatumAbFunctor_coyoneda_map_memberDiagHom`: the same collapse as an **equality of the
  objects** of the two presheaves over a chart, as an **equation of morphisms of `AddCommGrpCat`**,
  and read through `CategoryTheory.coyoneda`; the last is the form the sheaf condition consumes,
  and `.memberDatumAbFunctor_coyoneda_map_memberDiagHom'` is it with the charts spelled as objects
  of the small étale **ringed** site of the member.

## What is not proved here

The sheaf condition of the presheaf itself.  Feeding the collapse to
`AlgebraicGeometry.Space.QuasiCoherentDescent.isSheaf_memberTopology_of_memberDiagHom` needs the
compatibility of a family on a covering sieve of the charts of the members to be read as the
compatibility of the family of sections of the component module it restricts to, and the one step
of that passage which is still owed is the identification of
`.memberDatumAbFunctor_coyoneda_map_memberDiagHom'` with the right-hand side of
`CategoryTheory.Presieve.FamilyOfElements.SieveCompatible` at a diagonal arrow.  Neither of two
routes closes: `exact` on it exhausts the recursion depth, in every shape of the
arguments tried (the arrow and the section supplied, read off the goal, or supplied in the ringed
spelling of the charts), and `CategoryTheory.Presieve.compatible_iff_sieveCompatible` beta-reduced
first; and `rw`, which does find the rewrite, builds a motive the **kernel** then times out on,
in the compatibility statement on its own as well as inside the sheaf condition.

## Implementation notes

The restriction map of this presheaf is the term whose two readings may not meet in a unification,
and the discipline the upstream files record applies here unchanged: see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteAbPresheaf.lean`.  Two
points are specific to this file.

**Every statement about the restriction map is made with the arrow of the site a variable, and
specialized to a diagonal arrow only in a declaration which does nothing else.**  Instantiating one
of those statements at a concrete arrow is substitution and costs nothing; *matching* an
instantiated one against a goal spelled with the concrete member and chart in place of `p.unop.1`
and `p.unop.2` is a deterministic timeout of `whnf`, because the term being traversed is
the restriction map.  So `.heq_memberDatumAbFunctor_map_of_leg_eq` carries the arrow as a variable
and takes the collapse data as hypotheses, and those hypotheses mention only the legs, the members
and the restriction factor — never the transition — so a consumer discharges them at terms small
enough to compare.

**The crossing between the sections of the étale restriction and the sections of the presheaf is
paid in `.heq_memberDatumAbFunctor_map_apply`, and nowhere else.**  The two sides of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbFunctor_map_apply` are sections of two
spellings of one type, and that identification is affordable only with the objects, the arrow and
the section all variables; so the equation is restated there as a **heterogeneous** equation, whose
two types are independent, and every later step is heterogeneous too.  The final homogeneous form
`.memberDatumAbFunctor_map_memberDiagHom` is `eq_of_heq` and nothing else.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transports along an equal leg -/

/-- Two morphisms of charts with equal sources and the same underlying map are equal, as a
heterogeneous equation.  The source charts are variables, so that the equation between them can
be substituted. -/
theorem heq_hom_of_heq_left {Z : AlgebraicSpaces B S hS} {V : SmallEtale B S hS Z.1}
    (W₁ W₂ : SmallEtale B S hS Z.1) (hW : W₁ = W₂) (b₁ : W₁ ⟶ V) (b₂ : W₂ ⟶ V)
    (hb : HEq b₁.hom.left b₂.hom.left) : HEq b₁ b₂ := by
  subst hW
  exact heq_of_eq (ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (eq_of_heq hb)))

/-- Restriction of a section along two heterogeneously equal morphisms of charts agrees. -/
theorem val_map_heq_of_heq {Z : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS Z.1 Z.2) {V : SmallEtale B S hS Z.1}
    (W₁ W₂ : SmallEtale B S hS Z.1) (hW : W₁ = W₂) (b₁ : W₁ ⟶ V) (b₂ : W₂ ⟶ V)
    (hb : HEq b₁ b₂) (m : M.val.obj (Opposite.op V)) :
    HEq (ModuleCat.Hom.hom (M.val.map b₁.op) m)
      (ModuleCat.Hom.hom (M.val.map b₂.op) m) := by
  subst hW
  obtain rfl := eq_of_heq hb
  rfl

/-- **A morphism of `𝒪`-modules heterogeneously equal to an identity carries a section to any
section heterogeneously equal to it.**  The companion of
`AlgebraicGeometry.Space.QuasiCoherentDescent.val_app_apply_of_eq_id` for a morphism whose source
and target are two spellings of one module, with the target carried in a type of its own so that
no identification of the two spellings of the sections is performed here.

The morphism is a **variable**, so that a consumer's own morphism is read off the goal by one
first-order assignment; two applications of `.val` to concrete arguments are the unification the
upstream implementation notes record as a timeout. -/
theorem val_app_apply_heq_of_heq_id (C₀ : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS C₀.1 C₀.2} (A : M ⟶ N) (hMN : M = N) (hA : HEq A (𝟙 N))
    {Z : (smallEtaleRingedSite B S hS C₀.1 C₀.2).Cᵒᵖ} (z : M.val.obj Z) {γ : Type u} (t : γ)
    (hzt : HEq z t) : HEq (A.val.app Z z) t := by
  subst hMN
  exact HEq.trans (heq_of_eq (val_app_apply_of_eq_id B S hS C₀ A (eq_of_heq hA) z)) hzt

variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-- The étale restrictions of two component modules of a descent datum along two heterogeneously
equal étale morphisms are equal.  The two members and the two morphisms are variables, so that the
equations between them can be substituted. -/
theorem etaleModulePullback_obj_congr (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i j : I) (hij : i = j) (L₁ : T ⟶ Yi i) (L₂ : T ⟶ Yi j)
    (e₁ : IsEtale B S hS L₁.hom) (e₂ : IsEtale B S hS L₂.hom) (hL : HEq L₁ L₂) :
    (etaleModulePullback.{u, u} B S hS L₁ e₁).obj (D.F i) =
      (etaleModulePullback.{u, u} B S hS L₂ e₂).obj (D.F j) := by
  subst hij
  obtain rfl := eq_of_heq hL
  rfl

/-- **The bundled reading of a transition of a descent datum whose two legs agree is
heterogeneously the identity.**  Both members, both legs, their étaleness and their
compatibilities are variables, so that the equations between them can be substituted and so that a
consumer's own transition is matched argument by argument, with nothing unfolded. -/
theorem heq_transitionEtaleForm_id (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i j : I) (hij : i = j) (v : T ⟶ pair B S hS Yi f i j)
    (L₁ : T ⟶ Yi i) (L₂ : T ⟶ Yi j) (e₁ : IsEtale B S hS L₁.hom) (e₂ : IsEtale B S hS L₂.hom)
    (c₁ : v ≫ pairFst B S hS Yi f i j = L₁) (c₂ : v ≫ pairSnd B S hS Yi f i j = L₂)
    (hL : HEq L₁ L₂) :
    HEq (transitionEtaleForm B S hS Yi f D i j v L₁ L₂ e₁ e₂ c₁ c₂)
      (𝟙 ((etaleModulePullback.{u, u} B S hS L₂ e₂).obj (D.F j))) := by
  subst hij
  obtain rfl := eq_of_heq hL
  exact heq_of_eq (transitionEtaleForm_id B S hS Yi f D i v L₁ e₁ c₁ c₂)

variable (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### The chart and the morphism of charts a diagonal arrow induces -/

/-- **The chart of a member that a diagonal arrow of the site of the charts of the members
induces is the source chart of that arrow.** -/
theorem memberTransitionChart_memberDiagHom {i : I} {W V : SmallEtale B S hS (Yi i).1}
    (a : W ⟶ V) :
    memberTransitionChart B S hS Yi f hf V W (memberDiagHom B S hS Yi f hf a).hom = W :=
  smallEtalePostcomp_obj_congr B S hS
    (isEtale_memberChartMap B S hS Yi f hf V W (memberDiagHom B S hS Yi f hf a).hom)
    (isEtale_memberChartMap B S hS Yi f hf W W
      (𝟙 ((smallEtalePostcomp B S hS (f i) (hf i)).obj W)))
    (memberChartMap_memberDiagHom B S hS Yi f hf a _ rfl)
    (chartSpaceIdChart B S hS (Yi i) W)

/-- **The morphism of charts that a diagonal arrow induces is that arrow's own morphism of
charts.**  The two have the same underlying morphism of schemes, and their sources are the one
chart by `.memberTransitionChart_memberDiagHom`. -/
theorem heq_memberTransitionHom_memberDiagHom {i : I} {W V : SmallEtale B S hS (Yi i).1}
    (a : W ⟶ V) :
    HEq (memberTransitionHom B S hS Yi f hf V W (memberDiagHom B S hS Yi f hf a).hom) a :=
  heq_hom_of_heq_left B S hS _ _
    (memberTransitionChart_memberDiagHom B S hS Yi f hf a) _ a (heq_of_eq rfl)

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

omit [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)] in
/-- The restriction of a section along the morphism of charts a diagonal arrow induces is its
restriction along that arrow's own morphism of charts. -/
theorem heq_val_map_memberTransitionHom (D : DescentDatum B S hS Yi f) {i : I}
    {W V : SmallEtale B S hS (Yi i).1} (a : W ⟶ V)
    (m : (D.F i).val.obj (Opposite.op V)) :
    HEq (ModuleCat.Hom.hom ((D.F i).val.map
          (memberTransitionHom B S hS Yi f hf V W
            (memberDiagHom B S hS Yi f hf a).hom).op) m)
      (ModuleCat.Hom.hom ((D.F i).val.map a.op) m) :=
  val_map_heq_of_heq B S hS (D.F i) _ _ (memberTransitionChart_memberDiagHom B S hS Yi f hf a)
    _ a (heq_memberTransitionHom_memberDiagHom B S hS Yi f hf a) m

/-! ### The restriction map of the presheaf, read heterogeneously -/

/-- **The reading of the restriction map of the presheaf of abelian groups of a descent datum, as
a heterogeneous equation.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbFunctor_map_apply` with its two sides
carried in their own types, and it is the one declaration that identifies the sections of the
presheaf with the sections of the étale restriction at the self leg over the identity chart of the
chart space: the two are one type definitionally and not syntactically, and with the objects, the
arrow and the section all **variables** the identification is affordable, where in a consumer's
own goal it is not. -/
theorem heq_memberDatumAbFunctor_map_apply (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    HEq ((memberFunctorOfLawsV B S hS Yi f hf hL).map g m)
      ((memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)) :=
  heq_of_eq (memberDatumAbFunctor_map_apply B S hS Yi f hf D hL p q g m)

/-- **The restriction map of the presheaf of abelian groups of a descent datum along an arrow of
the site whose two legs agree is plain restriction inside the component module of the target
member.**

The arrow is a **variable** and the collapse is asked for as two hypotheses: that the two members
agree and that the two legs of the test space agree.  Those hypotheses, and the target of the
conclusion, mention the legs, the members and the restriction factor and never the transition, so
a consumer discharges them at terms small enough to compare -- which the transition is not. -/
theorem heq_memberDatumAbFunctor_map_of_leg_eq (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) {γ : Type u} (t : γ)
    (hi : p.unop.1 = q.unop.1)
    (hleg : HEq (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
          (memberHom B S hS Yi f hf g.unop))
      (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
          (memberHom B S hS Yi f hf (𝟙 q).unop)))
    (ht : HEq (ModuleCat.Hom.hom ((D.F p.unop.1).val.map
        (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2
          (memberHom B S hS Yi f hf g.unop)).op) m) t) :
    HEq ((memberFunctorOfLawsV B S hS Yi f hf hL).map g m) t := by
  refine (heq_memberDatumAbFunctor_map_apply B S hS Yi f hf D hL p q g m).trans ?_
  refine (heq_of_eq ((memberDatumAbTransHom_val_app_apply B S hS Yi f hf D p q g
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)).trans
    (memberDatumAbRestrFn_val_app_congr B S hS Yi f hf D p q g m m rfl))).trans ?_
  refine val_app_apply_heq_of_heq_id B S hS
    (chartSpace B S hS (Yi q.unop.1) q.unop.2) _ ?_ ?_ _ _ ht
  · exact etaleModulePullback_obj_congr B S hS Yi f D _ _ hi _ _ _ _ hleg
  · exact heq_transitionEtaleForm_id B S hS Yi f D _ _ hi _ _ _ _ _ _ _ hleg

/-- **The restriction map of the presheaf of abelian groups of a descent datum along a diagonal
arrow is plain restriction inside the component module of that member**, as a heterogeneous
equation.  `.heq_memberDatumAbFunctor_map_of_leg_eq` at a diagonal arrow, whose two hypotheses
are `.memberChartMap_memberDiagHom` and `.heq_val_map_memberTransitionHom`.

The section is carried at the sections of the **presheaf** and the target of the equation is a
**variable** whose identification is a hypothesis; the arrow is read off the type of the diagonal
arrow rather than supplied.  All three are forced: with the section carried at the sections of the
component module, or the target written out, or the two objects of the site supplied, the
conclusion has to be compared with a copy of itself freshly elaborated, and that comparison --
in each of those three shapes -- is a deterministic timeout. -/
theorem heq_memberDatumAbFunctor_map_memberDiagHom (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    {i : I} {W V : SmallEtale B S hS (Yi i).1} (a : W ⟶ V)
    (m : ↥((memberFunctorOfLawsV B S hS Yi f hf hL).obj
      (Opposite.op (memberPair B S hS Yi f hf i V))))
    {γ : Type u} (t : γ)
    (ht : HEq (ModuleCat.Hom.hom ((D.F i).val.map a.op) m) t) :
    HEq ((memberFunctorOfLawsV B S hS Yi f hf hL).map
        (memberDiagHom B S hS Yi f hf a).op m) t :=
  heq_memberDatumAbFunctor_map_of_leg_eq B S hS Yi f hf D hL _ _
    (memberDiagHom B S hS Yi f hf a).op m t rfl
    (heq_of_eq (memberChartMap_memberDiagHom B S hS Yi f hf a _ rfl))
    (HEq.trans (heq_val_map_memberTransitionHom B S hS Yi f hf D a m) ht)

/-- **THE RESTRICTION MAP OF THE PRESHEAF OF ABELIAN GROUPS OF A DESCENT DATUM ALONG A DIAGONAL
ARROW IS PLAIN RESTRICTION INSIDE THE COMPONENT MODULE OF THAT MEMBER.**  This is
`.heq_memberDatumAbFunctor_map_memberDiagHom` with the two spellings of the sections identified,
and it does nothing else. -/
theorem memberDatumAbFunctor_map_memberDiagHom (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    {i : I} {W V : SmallEtale B S hS (Yi i).1} (a : W ⟶ V)
    (m : ↥((memberFunctorOfLawsV B S hS Yi f hf hL).obj
      (Opposite.op (memberPair B S hS Yi f hf i V)))) :
    @Eq ↥((memberFunctorOfLawsV B S hS Yi f hf hL).obj
        (Opposite.op (memberPair B S hS Yi f hf i W)))
      ((memberFunctorOfLawsV B S hS Yi f hf hL).map
        (memberDiagHom B S hS Yi f hf a).op m)
      (ModuleCat.Hom.hom ((D.F i).val.map a.op) m) :=
  eq_of_heq (heq_memberDatumAbFunctor_map_memberDiagHom B S hS Yi f hf D hL a m _ (HEq.refl _))

/-! ### The diagonal restriction of the presheaf, and its sheaf condition -/

/-- **The sections of the presheaf of abelian groups of a descent datum over a chart of a member
are the sections of the underlying presheaf of abelian groups of the component module over that
chart.** -/
theorem memberFunctorOfLawsV_obj_memberPair (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    {i : I} (V : SmallEtale B S hS (Yi i).1) :
    (memberFunctorOfLawsV B S hS Yi f hf hL).obj
        (Opposite.op (memberPair B S hS Yi f hf i V)) =
      (D.F i).val.presheaf.obj (Opposite.op V) := rfl

/-- **The restriction map of the presheaf of abelian groups of a descent datum along a diagonal
arrow is the restriction map of the underlying presheaf of abelian groups of the component
module.**  `.memberDatumAbFunctor_map_memberDiagHom` read as an equation of morphisms of
`AddCommGrpCat`, which is what the sheaf condition consumes. -/
theorem memberDatumAbFunctor_map_memberDiagHom_eq (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    {i : I} {W V : SmallEtale B S hS (Yi i).1} (a : W ⟶ V) :
    (memberFunctorOfLawsV B S hS Yi f hf hL).map (memberDiagHom B S hS Yi f hf a).op =
      (D.F i).val.presheaf.map a.op :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m =>
    memberDatumAbFunctor_map_memberDiagHom B S hS Yi f hf D hL a m)

/-- **The restriction map of the presheaf of abelian groups of a descent datum along a diagonal
arrow, read through `CategoryTheory.coyoneda`, is the restriction map of the underlying presheaf
of abelian groups of the component module.**  This is
`.memberDatumAbFunctor_map_memberDiagHom_eq` composed on, and it is the form the sheaf condition
consumes: the identification of the two spellings of the sections is paid here, where the arrow
and the section are the only things in sight. -/
theorem memberDatumAbFunctor_coyoneda_map_memberDiagHom (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    (E : AddCommGrpCat.{u}) {i : I} {W V : SmallEtale B S hS (Yi i).1} (a : W ⟶ V)
    (τ : (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).obj
      (Opposite.op (memberPair B S hS Yi f hf i V))) :
    (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).map
        (memberDiagHom B S hS Yi f hf a).op τ =
      ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E)).map a.op τ :=
  congrArg (fun φ => τ ≫ φ)
    (memberDatumAbFunctor_map_memberDiagHom_eq B S hS Yi f hf D hL a)

/-- `.memberDatumAbFunctor_coyoneda_map_memberDiagHom` with the two charts spelled as objects of
the small étale **ringed** site of the member, which is the spelling the compatibility of a family
of sections of the component module binds them in.  The identification of the two spellings is
paid here, in a declaration which does nothing else. -/
theorem memberDatumAbFunctor_coyoneda_map_memberDiagHom' (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    (E : AddCommGrpCat.{u}) (i : I)
    (W V : (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).C) (a : W ⟶ V)
    (τ : (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).obj
      (Opposite.op (memberPair B S hS Yi f hf i V))) :
    (memberFunctorOfLawsV B S hS Yi f hf hL ⋙ coyoneda.obj (Opposite.op E)).map
        (memberDiagHom B S hS Yi f hf (i := i) (W := W) (V := V) a).op τ =
      ((D.F i).val.presheaf ⋙ coyoneda.obj (Opposite.op E)).map a.op τ :=
  memberDatumAbFunctor_coyoneda_map_memberDiagHom B S hS Yi f hf D hL E
    (i := i) (W := W) (V := V) a τ

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
