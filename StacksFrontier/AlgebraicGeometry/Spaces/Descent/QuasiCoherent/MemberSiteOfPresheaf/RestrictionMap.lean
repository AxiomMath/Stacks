module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSitePresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteOfPresheaf.CompositionLaw

/-!
# The restriction map of the presheaf of abelian groups and its two laws

`.memberDatumAbMap_laws`: the restriction map of the presheaf of abelian groups on the charts of
the members has the two laws of an additive map.  The identity and composition laws stated of
the additive maps `.AddMonoidHomLaws.toAddMonoidHom` builds out of it
(`.memberDatumAbMap_laws_id_apply`, `.memberDatumAbMap_laws_comp_apply`), with the composite
carried as a variable on the way, and the two laws as equations of morphisms of `AddCommGrpCat`,
`.memberDatumAbMapId_eq` and `.memberDatumAbMapComp_eq`.

The overview and the implementation notes are in the module docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteOfPresheaf/Coercions.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)


section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-! ### The restriction map of the presheaf of abelian groups -/

/-- **The identity law of the restriction map, retyped onto the sections of the presheaf of
abelian groups.**  `.memberDatumAb_id_apply` states the law at the type its own two sides carry,
which is the sections of an etale restriction over the identity chart of a chart space, while the
sections the presheaf of abelian groups is to have are the sections of the component module over
the chart the identity morphism of the site induces.  This is `.memberDatumAb_comp_apply'` for
the identity law, and it exists for the same reason: the two spellings are one type definitionally
and not syntactically, and the crossing between them has to be performed in a declaration of its
own, because anywhere else it is one identification too many. -/
theorem memberDatumAb_id_apply' (D : DescentDatum B S hS Yi f) (p : (MemberSite B S hS Yi f hf)ᵒᵖ)
      (m : memberDatumObj B S hS Yi f hf D p) :
      @Eq ↥(memberDatumObj B S hS Yi f hf D p) ((transitionEtaleForm B S hS Yi f D p.unop.1
        p.unop.1 (memberChartPair B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
        p).unop)) (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
        p).unop)) (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
        p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf
        (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f
        hf (𝟙 p).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f
        hf (𝟙 p).unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi
        f hf (𝟙 p).unop) (memberHom B S hS Yi f hf (𝟙 p).unop) rfl)).val.app (Opposite.op
        (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2)) (ModuleCat.Hom.hom ((D.F
        p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS
        Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S
        hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart
        B S hS (Yi p.unop.1) p.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS
        Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S
        hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart
        B S hS (Yi p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 p.unop.2
        (memberHom B S hS Yi f hf (𝟙 p).unop)))) m)) m := memberDatumAb_id_apply B S hS Yi f hf D p
        m

/-- **The restriction map of the presheaf of abelian groups attached to a descent datum has the
two laws of an additive map**: a section over an object of the site of the charts of the members,
restricted along the chart a morphism of the site induces and carried across by the transition of
the datum, depends additively on the section.

Each law is the one crossing between the sections of an etale restriction and the sections over a
composite chart, performed in the **argument** of `.val_app_apply_zero` and of
`.val_app_apply_add`, which is a function-argument position and the only place it is affordable.

Both are carried by one `.AddMonoidHomLaws`, and in a **theorem**, and both of those are forced.
Bundled, because the `0` and the `+` of the sections may not appear in a statement written here --
see `.AddMonoidHomLaws`.  In a theorem, because `Lean.Meta.abstractNestedProofs` rewrites the body
of a `def`, replacing each nested proof whose arguments are not all local variables by an
auxiliary constant abstracted over the whole local context, and the kernel then type-checks those
constants on their own: the two additivity obligations lifted out of a `def` that way
are a deterministic timeout of the kernel, twice over.  A theorem's statement and proof are stored
as they were written, so the function this one speaks of is the same term as the one
`.memberDatumAb_comp_apply'` speaks of, and `map_comp` of a `CategoryTheory.Functor` structure
instance whose restriction map is `.AddMonoidHomLaws.toAddMonoidHom` of this closes on it with no
identification at all. -/
theorem memberDatumAbMap_laws (D : DescentDatum B S hS Yi f) (p q : (MemberSite B S hS Yi f hf)ᵒᵖ)
      (g : p ⟶ q) :
      AddMonoidHomLaws (M := ↥(memberDatumObj B S hS Yi f hf D p)) (N := ↥(memberDatumObj B S hS
        Yi f hf D q)) (fun m => (transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1
        (memberChartPair B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
        (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
        (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop))
        (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
        (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙
        q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
        g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
        g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart
        B S hS (Yi q.unop.1) q.unop.2)) (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X
        := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom
        B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom
        B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y :=
        (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
        hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom
        B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
        (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))))
        m)) :=
  ⟨val_app_apply_zero _ _ (moduleCat_hom_apply_zero _),
      fun x y => val_app_apply_add _ _ _ _ (moduleCat_hom_apply_add _ x y)⟩

/-- **A morphism of `𝒪`-modules equal to an identity acts as the identity on a section**, read
through `CategoryTheory.SheafOfModules.Hom.val` and `CategoryTheory.PresheafOfModules.Hom.app`.
Stated with the morphism as a **variable** and its identity law as a hypothesis, and with the
ambient algebraic space given **explicitly**; both are forced.

As a variable, the morphism is read off a consumer's goal by one first-order assignment even
though `.val` is a projection -- `SheafOfModules.Hom.val ?A` against `SheafOfModules.Hom.val A`
is an assignment, where two *applications* of that projection to concrete arguments are the
unification the implementation notes record as a deterministic exhaustion of the recursion depth.
The hypothesis is then an equation of morphisms of sheaves of modules, one projection **above**
`.val`, where the arguments are compared first order and the comparison is free.

The algebraic space is explicit because it occurs in the rest of the signature only through its
two projections, and a metavariable under a projection cannot be inverted: left implicit it is
never determined. -/
theorem val_app_apply_of_eq_id (C₀ : AlgebraicSpaces B S hS)
    {M : Modules.{u, u} B S hS C₀.1 C₀.2} (A : M ⟶ M) (hA : A = 𝟙 M)
    {Z : (smallEtaleRingedSite B S hS C₀.1 C₀.2).Cᵒᵖ} (z : M.val.obj Z) :
    A.val.app Z z = z := by
  subst hA
  rfl

/-- **The identity law of the restriction map of the presheaf of abelian groups, stated of the
additive map `.AddMonoidHomLaws.toAddMonoidHom` builds out of `.memberDatumAbMap_laws`.**  This is
`.memberDatumAb_id_apply'` with its function **not written out**: the function is the one the
*instantiation* of `.memberDatumAbMap_laws` at `q := p` and `g := 𝟙 p` carries, which is the
function a `map_id` goal of a direct `CategoryTheory.Functor` structure instance built from that
law leaves behind.

That distinction is the whole content of the statement, and it is not a matter of spelling.  A
copy of the law's text, freshly elaborated at `𝟙 p`, solves the implicit arguments of its
restriction factor with the morphism of the site **reducible**; the instantiation solved them with
the morphism of the site **opaque** and then substituted.  The two differ, and
identifying them exhausts the recursion depth -- so `.memberDatumAb_id_apply'`, whose text this
statement reproduces verbatim, does not close this goal and this one does not close that.

The proof reads **every** argument off the goal and writes none of them: the bundling is unfolded
by `.AddMonoidHomLaws.toAddMonoidHom_apply`, the transition factor is discharged by
`.val_app_apply_of_eq_id` with its morphism read off the goal and
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm_id` supplying the identity law
of that morphism, and the restriction factor by `.val_map_eq_id_hom_apply` with its morphism of
charts read off the goal.  The three `refine`s are what order those readings: the morphism of
sheaves of modules has to be assigned from the goal **before** its identity law is elaborated, and
a term-mode application elaborates the hypothesis first, when the morphism is still a
metavariable, and then faces the projection unification that cannot be paid. -/
theorem memberDatumAbMap_laws_id_apply (D : DescentDatum B S hS Yi f)
      (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
      (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbMap_laws B S hS Yi f hf D p p (𝟙 p))).toZeroHom.toFun m = m := by
  refine Eq.trans (AddMonoidHomLaws.toAddMonoidHom_apply _ m) ?_
  refine Eq.trans (val_app_apply_of_eq_id B S hS
    (chartSpace B S hS (Yi p.unop.1) p.unop.2) _ ?_ _) ?_
  · exact transitionEtaleForm_id B S hS Yi f D p.unop.1 _ _ _ _ _
  · exact val_map_eq_id_hom_apply B S hS (D.F p.unop.1) _ rfl m


/-! ### The composition law with the composite carried as a variable -/

/-- **The restriction map of the presheaf of abelian groups, read on a section carried as a
variable.**  `.AddMonoidHomLaws.toAddMonoidHom_apply` at `.memberDatumAbMap_laws`, with the
section the reading is applied to carried as a variable `z` identified by a hypothesis with the
section the written-out reading is applied to.

The variable is what makes this usable twice over.  Taken at `z := w := m` it is the reading of
the restriction map on a section, `.memberDatumAbMap_laws_apply`.  Taken at `z` the *value* of
another such reading and `w` that value written out, it unfolds the outer of two **nested**
readings while respelling the inner one in its argument -- which is a rewrite under the outer
function, and cannot be done by the plain reading lemma, because recovering that function from the
goal is a higher-order unification.  Unfolding both at once instead is a deterministic timeout of
the **kernel**: one level of this nesting it checks, two it does not. -/
theorem memberDatumAbMap_laws_apply_of_eq (D : DescentDatum B S hS Yi f) (p q : (MemberSite B S hS
      Yi f hf)ᵒᵖ) (g : p ⟶ q) (z w : memberDatumObj B S hS Yi f hf D p) (hzw : z = w) :
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf D p q
      g)).toZeroHom.toFun z = ((transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1
      (memberChartPair B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙
      q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart
      B S hS (Yi q.unop.1) q.unop.2)) (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X
      := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
      hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom
      B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
      (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))))
      w)) := by
  subst hzw
  exact AddMonoidHomLaws.toAddMonoidHom_apply _ _

/-- **The restriction map of the presheaf of abelian groups, read on a section**: the additive map
`.AddMonoidHomLaws.toAddMonoidHom` builds out of `.memberDatumAbMap_laws` applied to a section is
that law's function written out and applied to it.  `.memberDatumAbMap_laws_apply_of_eq` at
`z := w := m`. -/
theorem memberDatumAbMap_laws_apply (D : DescentDatum B S hS Yi f) (p q : (MemberSite B S hS Yi f
      hf)ᵒᵖ) (g : p ⟶ q) (m : memberDatumObj B S hS Yi f hf D p) :
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf D p q
      g)).toZeroHom.toFun m = ((transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1
      (memberChartPair B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙
      q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart
      B S hS (Yi q.unop.1) q.unop.2)) (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X
      := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
      hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom
      B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
      (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))))
      m)) :=
  memberDatumAbMap_laws_apply_of_eq B S hS Yi f hf D p q g m m rfl

/-- **Two restriction maps of the presheaf of abelian groups, read one after the other on a
section**, as the two written-out readings nested -- the left-hand side of a `map_comp` goal,
written out.  `.memberDatumAbMap_laws_apply_of_eq` at `z` the inner reading and `w` that reading
written out, with `.memberDatumAbMap_laws_apply` supplying the identification of the two.

Nothing here is identified: the statement is an *instantiation* of that lemma's conclusion.  That
is the point of it, and it is a kernel matter -- the same equation proved in one step from a lemma
unfolding both bundlings at once is a deterministic timeout of the kernel. -/
theorem memberDatumAbMap_laws_comp_apply_aux (D : DescentDatum B S hS Yi f) (p q r : (MemberSite B
      S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (m : memberDatumObj B S hS Yi f hf D p) :
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf D q r
      h)).toZeroHom.toFun ((AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf
      D p q g)).toZeroHom.toFun m) = ((transitionEtaleForm B S hS Yi f D q.unop.1 r.unop.1
      (memberChartPair B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))
      (memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))
      (memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙 r).unop))
      (isEtale_memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))
      (isEtale_memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙
      r).unop)) (memberChartPair_fst B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop)) (memberChartPair_snd' B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop) (memberHom B S hS Yi f hf (𝟙 r).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart
      B S hS (Yi r.unop.1) r.unop.2)) (ModuleCat.Hom.hom ((D.F q.unop.1).val.map (Quiver.Hom.op (X
      := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom
      B S hS Yi f hf h.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom
      B S hS Yi f hf h.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf (𝟙 q).unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))))
      (memberTransitionHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))))
      ((transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf
      p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
      (memberHom B S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2
      q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop)
      rfl)).val.app (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS
      (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
      hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom
      B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
      (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))))
      m)))) :=
  memberDatumAbMap_laws_apply_of_eq B S hS Yi f hf D q r h _ _
    (memberDatumAbMap_laws_apply B S hS Yi f hf D p q g m)

/-- **The restriction factor of the composition law, with the composite morphism of the site and
the connecting restriction of charts both carried as variables.**  This is
`.memberDatumRestrict_comp_apply` with `g ≫ h` replaced by a variable `gh` identified with it by a
hypothesis, and with the connecting restriction of charts replaced by a variable `cc` identified
with it by `HEq` -- the shape `.memberTransitionEtaleForm_comp` asks its hypothesis `ht` in.

`cc` has to be a variable for the same reason `ba` is one there: its source chart is the chart the
*composite* morphism of the site induces, so at an opaque `gh` the restriction of charts the two
morphisms of the site induce does not have that type, and cannot be written in the statement at
all.  And `gh` has to be a variable so that the statement is elaborated with the composite
**opaque**, which is what makes an instantiation of it at `g ≫ h` the term
`.memberTransitionEtaleForm_comp` asks for rather than a second, freshly elaborated copy of the
same text -- the distinction `.memberDatumAbMap_laws_id_apply` records for the identity at `𝟙 p`.

The two restrictions are **written out** in the proof, as they are at
`.memberDatumRestrict_comp_apply`, and they have to be: read off the goal instead, the second is
matched through the direct-application coercion of `CategoryTheory.Functor.map` while
`.val_map_comp_hom_apply` states it through `ModuleCat.Hom.hom`, and with the morphism still a
metavariable that match exhausts the heartbeat budget at `whnf`.  Both are free of
`gh`, so writing them out costs nothing. -/
theorem memberDatumRestrict_comp_apply_of_eq (D : DescentDatum B S hS Yi f) (p q r : (MemberSite B
      S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : gh = g ≫ h) (cc :
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S
      hS Yi f hf gh.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S
      hS Yi f hf gh.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)) ⟶
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))) (hcc : HEq cc
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B
      S hS Yi f hf h.unop)))) (m : memberDatumObj B S hS Yi f hf D p) : (ModuleCat.Hom.hom ((D.F
      p.unop.1).val.map (Quiver.Hom.op (X := ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi
      f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop)) (isEtale_memberChartMap B S hS Yi
      f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop))).obj (chartSpaceIdChart B S hS
      (Yi r.unop.1) r.unop.2))) (Y := ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS
      (Yi p.unop.1) p.unop.2))) (memberTransitionHom B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B
      S hS Yi f hf gh.unop))))) m = (D.F p.unop.1).val.map cc.op ((ModuleCat.Hom.hom ((D.F
      p.unop.1).val.map (Quiver.Hom.op (X := ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi
      f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi
      f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi
      q.unop.1) q.unop.2))) (Y := ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS
      (Yi p.unop.1) p.unop.2))) (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B
      S hS Yi f hf g.unop))))) m) := by
  subst hgh
  obtain rfl := eq_of_heq hcc
  exact (val_map_comp_hom_apply B S hS (D.F p.unop.1) (Quiver.Hom.op (X := ((smallEtalePostcomp B S
    hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
    (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
    g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))) (Y := ((smallEtalePostcomp B
    S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
    (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
    p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))) (memberTransitionHom B S hS
    Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))) ((smallEtalePostcomp B S hS
    (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
    (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
    g.unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
    h.unop))).op m).symm

/-- **The composition law of the restriction map of the presheaf of abelian groups, with the
composite morphism of the site carried as a variable.**  This is `.memberDatumAb_comp_apply'` with
`g ≫ h` replaced throughout by a morphism `gh` equal to it, and with the connecting restriction of
charts carried as a morphism `cc` related by `HEq` to the restriction along the morphism of charts
induced by `h`; its two sides are the readings of `.memberDatumAbMap_laws` at `g`, at `h` and at
`gh`. -/
theorem memberDatumAb_comp_apply_of_eq' (D : DescentDatum B S hS Yi f) (p q r : (MemberSite B S hS
      Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : gh = g ≫ h) (cc :
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S
      hS Yi f hf gh.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S
      hS Yi f hf gh.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)) ⟶
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))) (hcc : HEq cc
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B
      S hS Yi f hf h.unop)))) (m : memberDatumObj B S hS Yi f hf D p) : @Eq ↥(memberDatumObj B
      S hS Yi f hf D r) ((transitionEtaleForm B S hS Yi f D q.unop.1 r.unop.1 (memberChartPair B S
      hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop)) (memberChartMap B S hS Yi f
      hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop)) (memberChartMap B S hS Yi f hf
      r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙 r).unop)) (isEtale_memberChartMap B S hS Yi f
      hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop)) (isEtale_memberChartMap B S hS Yi f
      hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙 r).unop)) (memberChartPair_fst B S hS Yi f
      hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop)) (memberChartPair_snd' B S hS Yi f hf
      q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop) (memberHom B S hS Yi f hf (𝟙 r).unop)
      rfl)).val.app (Opposite.op (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))
      (ModuleCat.Hom.hom ((D.F q.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS
      (memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))
      (isEtale_memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf (𝟙 q).unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))))
      (memberTransitionHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))))
      ((transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf
      p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
      (memberHom B S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2
      q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop)
      rfl)).val.app (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS
      (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
      hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom
      B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
      (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))))
      m)))) ((transitionEtaleForm B S hS Yi f D p.unop.1 r.unop.1 (memberChartPair B S hS Yi f hf
      p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop)) (memberChartMap B S hS Yi f hf
      p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop)) (memberChartMap B S hS Yi f hf
      r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙 r).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop)) (isEtale_memberChartMap B S hS Yi f
      hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙 r).unop)) (memberChartPair_fst B S hS Yi f
      hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop)) (memberChartPair_snd' B S hS Yi f
      hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop) (memberHom B S hS Yi f hf (𝟙
      r).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))
      (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS
      (memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      gh.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
      hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom
      B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
      (memberTransitionHom B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop))))
      m)) := by
  have hba : memberHom B S hS Yi f hf gh.unop =
      memberHom B S hS Yi f hf h.unop ≫ memberHom B S hS Yi f hf g.unop := by
    subst hgh
    rfl
  exact memberTransitionEtaleForm_comp B S hS Yi f hf (i := p.unop.1) (j := q.unop.1) (k :=
    r.unop.1) D p.unop.2 q.unop.2 r.unop.2 (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi
    f hf h.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl (memberHom B S hS Yi f hf (𝟙 r).unop)
    rfl (memberHom B S hS Yi f hf gh.unop) hba cc hcc (memberTransitionHom B S hS Yi f hf q.unop.2
    r.unop.2 (memberHom B S hS Yi f hf h.unop)) (heq_memberTransitionHom_postcomp B S hS Yi f hf q
    r h) ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B
    S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom
    B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))
    (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
    (memberTransitionHom B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf gh.unop)) m
    (memberDatumRestrict_comp_apply_of_eq B S hS Yi f hf D p q r g h gh hgh cc hcc m)

/-- **THE COMPOSITION LAW of the restriction map, stated of the additive maps
`.AddMonoidHomLaws.toAddMonoidHom` builds out of `.memberDatumAbMap_laws`, with the composite
morphism of the site still a variable.**  The three readings are *instantiations* of that law --
at `g`, at `h` and at `gh` -- and not copies of its text; the orientation is the one the
hypothesis `hcomp` of `.addCommGrpCat_ofHom_eq_comp` asks for.

The chain goes **out to the written-out readings and back**:
`.memberDatumAbMap_laws_comp_apply_aux` for the two nested ones, `.memberDatumAb_comp_apply_of_eq'`
for the law itself, and `.memberDatumAbMap_laws_apply` at `gh` for the composite.  Both middle
terms of the chain are therefore the written-out law, which is what the law in the middle states on
the nose, and the two `Eq.trans`s have nothing to identify.  With the chain run the other way
round -- the bundled readings as the middle terms, so that the law has to be identified with them
-- the elaborator still accepts the proof and the kernel then reports a deterministic timeout on
it, and no further splitting of the consumer removes it. -/
theorem memberDatumAbMap_laws_comp_apply_of_eq (D : DescentDatum B S hS Yi f) (p q r : (MemberSite
      B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : gh = g ≫ h) (cc :
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S
      hS Yi f hf gh.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S
      hS Yi f hf gh.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)) ⟶
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))) (hcc : HEq cc
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B
      S hS Yi f hf h.unop)))) (m : memberDatumObj B S hS Yi f hf D p) :
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf D q r
      h)).toZeroHom.toFun ((AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf
      D p q g)).toZeroHom.toFun m) = (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S
      hS Yi f hf D p r gh)).toZeroHom.toFun m :=
  Eq.trans (memberDatumAbMap_laws_comp_apply_aux B S hS Yi f hf D p q r g h m)
    (Eq.trans (memberDatumAb_comp_apply_of_eq' B S hS Yi f hf D p q r g h gh hgh cc hcc m)
      (Eq.symm (memberDatumAbMap_laws_apply B S hS Yi f hf D p r gh m)))

/-- **THE COMPOSITION LAW of the restriction map of the presheaf of abelian groups, in the form a
`map_comp` goal carries it**: `.memberDatumAbMap_laws_comp_apply_of_eq` at `gh := g ≫ h`, which is
where the composite stops being a variable.  The companion of `.memberDatumAbMap_laws_id_apply` for
`map_comp`, and the last thing the presheaf of abelian groups needs.

The connecting restriction of charts and its `HEq` are the two arguments that instantiation owes,
and they are exactly what `.memberDatumAb_comp_apply` supplies to
`.memberTransitionEtaleForm_comp` at the same place. -/
theorem memberDatumAbMap_laws_comp_apply (D : DescentDatum B S hS Yi f) (p q r : (MemberSite B S
      hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (m : memberDatumObj B S hS Yi f hf D p) :
      (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf D q r
      h)).toZeroHom.toFun ((AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S hS Yi f hf
      D p q g)).toZeroHom.toFun m) = (AddMonoidHomLaws.toAddMonoidHom (memberDatumAbMap_laws B S
      hS Yi f hf D p r (g ≫ h))).toZeroHom.toFun m :=
  memberDatumAbMap_laws_comp_apply_of_eq B S hS Yi f hf D p q r g h (g ≫ h) rfl _
    (heq_memberChartSpaceHom_postcomp B S hS Yi f hf p q r g h) m

/-! ### The two laws of the presheaf of abelian groups, as equations of morphisms -/

/-- **The identity law of the restriction map of the presheaf of abelian groups, as an equation
of morphisms of `AddCommGrpCat`** -- `map_id` of the presheaf to be assembled, at an object of the
site.  `.addCommGrpCat_ofHom_eq_id` with its additive map read off the goal and
`.memberDatumAbMap_laws_id_apply` supplying the law on sections. -/
theorem memberDatumAbMapId_eq (D : DescentDatum B S hS Yi f)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbMap_laws B S hS Yi f hf D p p (𝟙 p))) =
      𝟙 (AddCommGrpCat.of (memberDatumObj B S hS Yi f hf D p)) :=
  addCommGrpCat_ofHom_eq_id _ fun m => memberDatumAbMap_laws_id_apply B S hS Yi f hf D p m

/-- **The composition law of the restriction map of the presheaf of abelian groups, as an equation
of morphisms of `AddCommGrpCat`** -- `map_comp` of the presheaf to be assembled, at a composable
pair of morphisms of the site.  `.addCommGrpCat_ofHom_eq_comp` with its three additive maps read
off the goal and `.memberDatumAbMap_laws_comp_apply` supplying the law on sections. -/
theorem memberDatumAbMapComp_eq (D : DescentDatum B S hS Yi f)
    (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) :
    AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbMap_laws B S hS Yi f hf D p r (g ≫ h))) =
      AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbMap_laws B S hS Yi f hf D p q g)) ≫
      AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbMap_laws B S hS Yi f hf D q r h)) :=
  addCommGrpCat_ofHom_eq_comp _ _ _ fun m =>
    memberDatumAbMap_laws_comp_apply B S hS Yi f hf D p q r g h m

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
