module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteAbPresheaf

/-!
# The presheaf of abelian groups of a descent datum, assembled

The presheaf of abelian groups of a descent datum on the site of the charts of the members of an
étale covering, as an object of
`(MemberSite … )ᵒᵖ ⥤ AddCommGrpCat`.  Its sections, its restriction map and the three laws of
that restriction map are those of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteAbPresheaf.lean`; what is
added here is the assembly.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.MemberAbLaws`: the three laws a candidate
  presheaf of abelian groups on the site of the charts of the members has to satisfy -- the
  additivity of each restriction map, the identity law and the composition law, the latter with
  the intermediate value carried as a variable.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctorOfLawsV`: the functor those laws
  build, the sections being asked for as a family of types with a family of
  `AddCommGroup` structures rather than as a family of objects of `AddCommGrpCat`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbGrp`: **the sections of the presheaf
  of abelian groups of a descent datum over a chart of a member**, as an object of
  `AddCommGrpCat`, behind a name whose body the kernel accepts.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbMpPt` and `.memberDatumAbMpSpec`:
  the specification a restriction map of that presheaf has to satisfy, at one morphism of the site
  and at all of them.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAb_laws`: the three laws of that
  presheaf, bundled.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbGrp_eq`: the named sections are the
  sections of the component module of the datum.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbBundled_apply`: **the bundled reading
  of the restriction map, read on a section, is the reading through the two named factors.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctorOfLawsV_map_apply`: the restriction
  map of the presheaf the laws build, read on a section, is the function those laws were stated
  of -- everything in sight a variable.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbFunctor_obj` and
  `.memberDatumAbFunctor_map_apply`: **the sections and the restriction map of the presheaf of
  abelian groups of a descent datum**, at the presheaf
  `.memberFunctorOfLawsV` builds from the three laws of the datum **carried as a hypothesis**.
  These two are the whole interface a consumer needs, and the route by which the presheaf is named
  at all; see the implementation notes.

## Implementation notes

The three laws are bundled into one `Prop`-valued structure, and the builder takes that structure
and nothing else.  The reason is the one recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteOfPresheaf.lean`: the
restriction map of this presheaf is a term whose two readings may not meet in a unification, and
with the sections, the restriction map and the laws all read off the **type** of a single
argument every one of them is one first-order assignment, where passing the sections and the
restriction map as separate arguments leaves the restriction map to be recovered from the type of
the law -- a higher-order problem -- and the sections to be compared against the ascription of
`.memberDatumObj`.

`.memberFunctorOfLawsV` asks for the sections as a family of types together with a family of
`AddCommGroup` structures, and not as a family of objects of `AddCommGrpCat`, for the same
reason: at a descent datum the sections are the ascribed `.memberDatumObj`, whose
`AddCommGroup` structure comes from its `Module` structure, and `AddCommGrpCat.of` is applied
**inside** the builder, where the type and the structure are variables.

The composition law is asked for with the intermediate value carried as a variable, in the shape
`Fn p q g m = y → Fn q r h y = Fn p r (g ≫ h) m`.  That is what lets the law at a descent datum
be proved by one `subst`: the two nested readings of the restriction map are then spelled
independently, and the nesting is restored only after the outer one has been rewritten.

**The presheaf may not be assembled by handing the bundled restriction map to a `def`, and the
measurements that say so are these.**  A `theorem` whose statement or proof mentions that map is
checked; a `def` whose *body* mentions it is a deterministic timeout of the **kernel**, in every
shape there is -- `.memberFunctorOfLawsV` applied to `.memberDatumAb_laws`, with the result type
ascribed and without; the same with the sections, their additive structure or the restriction map
carried behind names of their own; the same with the laws carried as a hypothesis, so that the
body has no nested proof at all; the bundled additive map on its own, ascribed and unascribed; and
the bundled morphism of `AddCommGrpCat` likewise.  The direct `CategoryTheory.Functor` structure
instance does not even reach the kernel: it exhausts the recursion depth in the elaborator, at
`map_id`.

What a `def` does accept is a body, and a type, built from named constants: `.memberDatumAbGrp`
is such a `def`, and so are `.memberDatumAbMpPt` and `.memberDatumAbMpSpec`, whose bodies spell
the restriction map through the two named factors `.memberDatumAbTransHom` and
`.memberDatumAbRestrFn` and pay one chart crossing -- the crossing `.memberDatumAbRestrFn` pays
in its own type.  The route this prepares is to obtain the restriction map as `Exists.choose` of
an existential over morphisms of `.memberDatumAbGrp` satisfying `.memberDatumAbMpSpec`, so that
the `def` has a small type and a small body and the bundled reading is seen only by theorems:
`.memberDatumAbBundled_apply` is the step that reads the bundled map on a section, and it is
`rfl`.  What is **not** yet paid is the single delta of `.memberDatumAbMpPt` that turns that step
into the specification at the bundled witness: on its own, in a declaration of its own, in term
mode and in tactic mode, with the pointwise predicate a `def` and an `abbrev`, and with the
section carried once or twice with an equation between the two spellings, it exhausts the
recursion depth.

**How the presheaf is named, and why no `def` and no choice is needed.**  Nothing downstream of
this file needs the presheaf behind a name of its own: every statement about it is a `Prop`, and
so is the effectivity clause of Stacks 04W6 itself.  So the presheaf is carried as
`.memberFunctorOfLawsV` applied to a **hypothesis** of type `.MemberAbLaws` at the written-out
sections, additive structure and restriction map of the datum, which is what
`.memberDatumAbFunctor_obj` and `.memberDatumAbFunctor_map_apply` are stated of.  A consumer
states its own theorem with that hypothesis, and discharges it at the end by applying its theorem
to `.memberDatumAb_laws` -- a plain application of a theorem to a theorem, where the hypothesis
and the conclusion of `.memberDatumAb_laws` are written identically, so the unification is
syntactic.

Three things make that work where a `def` does not.  The sections `obj` and the restriction map
`Fn` are **instantiated** at the datum's, so `.obj p` is `AddCommGrpCat.of` of the sections and
`.map g` read on a section is the named reading, both by `rfl` with no transport; the laws are a
**variable**, so the body of the term the kernel sees carries no nested proof; and the two
readings above are `.memberFunctorOfLawsV_obj` and `.memberFunctorOfLawsV_map_apply`
instantiated, each one first-order assignment.  In particular no `Exists.choose` and no
`Classical.choice` enters: an existential over functors would have to be characterized by an
equation of objects and a transport of its restriction map along that equation, and the
`CategoryTheory.eqToHom` sandwich such a characterization carries itself exhausts the
recursion depth, even with both equations `rfl`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

/-- An additive map takes equal elements to equal values. -/
theorem addMonoidHomFun_congr {M N : Type u} [AddCommGroup M] [AddCommGroup N] (A : M →+ N)
    (z w : M) (h : z = w) : A.toZeroHom.toFun z = A.toZeroHom.toFun w := by
  subst h
  rfl

/-- A morphism of `AddCommGrpCat` acting as the identity on sections is the identity. -/
theorem addCommGrpCat_eq_id_of_apply {M : AddCommGrpCat.{u}} (A : M ⟶ M) (h : ∀ m, A m = m) :
    A = 𝟙 M :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext h)

/-- A morphism of `AddCommGrpCat` acting on sections as a composite does is that composite. -/
theorem addCommGrpCat_eq_comp_of_apply {M N P : AddCommGrpCat.{u}} (A : M ⟶ P) (A₁ : M ⟶ N)
    (A₂ : N ⟶ P) (h : ∀ m, A m = A₂ (A₁ m)) : A = A₁ ≫ A₂ :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext h)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### The laws of a presheaf of abelian groups on the site of the members, bundled -/

/-- **The three laws of a candidate presheaf of abelian groups on the site of the charts of the
members**: the additivity of every restriction map, the identity law on sections, and the
composition law on sections with the intermediate value carried as a variable. -/
structure MemberAbLaws (obj : (MemberSite B S hS Yi f hf)ᵒᵖ → Type u)
    (instA : ∀ p, AddCommGroup (obj p))
    (Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (obj p → obj q)) : Prop where
  /-- Each restriction map is additive. -/
  additive : ∀ (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q),
    @AddMonoidHomLaws (obj p) (obj q) (instA p) (instA q) (Fn p q g)
  /-- The identity law on sections. -/
  id_apply : ∀ (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m : obj p), Fn p p (𝟙 p) m = m
  /-- The composition law on sections, with the intermediate value carried as a variable. -/
  comp_apply : ∀ (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (m : obj p)
    (y : obj q), Fn p q g m = y → Fn q r h y = Fn p r (g ≫ h) m

/-- **A presheaf of abelian groups on the site of the charts of the members out of the three laws
of its restriction map.**  The bundling -- `AddCommGrpCat.of`,
`.AddMonoidHomLaws.toAddMonoidHom` and `AddCommGrpCat.ofHom` -- happens here, where the sections,
their `AddCommGroup` structure, the restriction map and the laws are all variables. -/
def memberFunctorOfLawsV {obj : (MemberSite B S hS Yi f hf)ᵒᵖ → Type u}
    {instA : ∀ p, AddCommGroup (obj p)}
    {Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (obj p → obj q)}
    (hL : MemberAbLaws B S hS Yi f hf obj instA Fn) :
    (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj p := @AddCommGrpCat.of (obj p) (instA p)
  map {p q} g := AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom (hL.additive p q g))
  map_id p := @addCommGrpCat_ofHom_eq_id (obj p) (instA p) _ fun m =>
    Eq.trans (AddMonoidHomLaws.toAddMonoidHom_apply (hL.additive p p (𝟙 p)) m) (hL.id_apply p m)
  map_comp {p q r} g h :=
    @addCommGrpCat_ofHom_eq_comp (obj p) (obj q) (obj r) (instA p) (instA q) (instA r) _ _ _
      fun m => Eq.trans (AddMonoidHomLaws.toAddMonoidHom_apply (hL.additive q r h) _)
        (Eq.trans (hL.comp_apply p q r g h m _
            (Eq.symm (AddMonoidHomLaws.toAddMonoidHom_apply (hL.additive p q g) m)))
          (Eq.symm (AddMonoidHomLaws.toAddMonoidHom_apply (hL.additive p r (g ≫ h)) m)))

/-- The sections of the presheaf of abelian groups built from the three laws. -/
theorem memberFunctorOfLawsV_obj {obj : (MemberSite B S hS Yi f hf)ᵒᵖ → Type u}
    {instA : ∀ p, AddCommGroup (obj p)}
    {Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (obj p → obj q)}
    (hL : MemberAbLaws B S hS Yi f hf obj instA Fn) (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    (memberFunctorOfLawsV B S hS Yi f hf hL).obj p = @AddCommGrpCat.of (obj p) (instA p) :=
  rfl

/-- The restriction map of the presheaf of abelian groups built from the three laws. -/
theorem memberFunctorOfLawsV_map {obj : (MemberSite B S hS Yi f hf)ᵒᵖ → Type u}
    {instA : ∀ p, AddCommGroup (obj p)}
    {Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (obj p → obj q)}
    (hL : MemberAbLaws B S hS Yi f hf obj instA Fn) (p q : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (g : p ⟶ q) :
    (memberFunctorOfLawsV B S hS Yi f hf hL).map g =
      AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom (hL.additive p q g)) :=
  rfl

/-- **The restriction map of the presheaf of abelian groups built from the three laws, read on a
section, is the function those laws were stated of.**  The bundling of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctorOfLawsV` is
`.AddMonoidHomLaws.toAddMonoidHom` of a function and `AddCommGrpCat.ofHom` of that, so on a
section it is that function.

This is the only reading of that presheaf a consumer needs, and it is stated with the sections,
their additive structure and the function all **variables**: a consumer instantiates them at its
own, and the instantiation is one first-order assignment each. -/
theorem memberFunctorOfLawsV_map_apply {obj : (MemberSite B S hS Yi f hf)ᵒᵖ → Type u}
    {instA : ∀ p, AddCommGroup (obj p)}
    {Fn : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) → (obj p → obj q)}
    (hL : MemberAbLaws B S hS Yi f hf obj instA Fn) (p q : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (g : p ⟶ q) (m : obj p) :
    (memberFunctorOfLawsV B S hS Yi f hf hL).map g m = Fn p q g m :=
  rfl

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-! ### The laws at a descent datum, at the reading through the two named factors -/

/-- The restriction map at the two named factors is the bundled additive map built from its
laws, read on a section. -/
theorem memberDatumAbFnRaw_eq_bundled (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m) =
      (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbFn_laws B S hS Yi f hf D p q g)).toZeroHom.toFun m :=
  Eq.symm (AddMonoidHomLaws.toAddMonoidHom_apply _ m)

/-- The identity law at the two named factors. -/
theorem memberDatumAbFnRaw_id_apply (D : DescentDatum B S hS Yi f)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberDatumAbTransHom B S hS Yi f hf D p p (𝟙 p)).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p p (𝟙 p) m) = m :=
  Eq.trans (memberDatumAbFnRaw_eq_bundled B S hS Yi f hf D p p (𝟙 p) m)
    (memberDatumAbFn_id_apply B S hS Yi f hf D p m)

/-- The composition law at the two named factors, up to the bundled reading of the composite. -/
theorem memberDatumAbFnRaw_comp_aux (D : DescentDatum B S hS Yi f)
    (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberDatumAbTransHom B S hS Yi f hf D q r h).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D q r h
          ((memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
            (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
            (memberDatumAbRestrFn B S hS Yi f hf D p q g m))) =
      (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbFn_laws B S hS Yi f hf D p r (g ≫ h))).toZeroHom.toFun m :=
  Eq.trans (memberDatumAbFnRaw_eq_bundled B S hS Yi f hf D q r h _)
    (Eq.trans (addMonoidHomFun_congr _ _ _
        (memberDatumAbFnRaw_eq_bundled B S hS Yi f hf D p q g m))
      (memberDatumAbFn_comp_apply B S hS Yi f hf D p q r g h m))

/-- The composition law at the two named factors. -/
theorem memberDatumAbFnRaw_comp_apply (D : DescentDatum B S hS Yi f)
    (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberDatumAbTransHom B S hS Yi f hf D q r h).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D q r h
          ((memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
            (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
            (memberDatumAbRestrFn B S hS Yi f hf D p q g m))) =
      (memberDatumAbTransHom B S hS Yi f hf D p r (g ≫ h)).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p r (g ≫ h) m) :=
  Eq.trans (memberDatumAbFnRaw_comp_aux B S hS Yi f hf D p q r g h m)
    (Eq.symm (memberDatumAbFnRaw_eq_bundled B S hS Yi f hf D p r (g ≫ h) m))

/-- The composition law at the two named factors, with the intermediate value a variable. -/
theorem memberDatumAbFnRaw_comp_of_eq (D : DescentDatum B S hS Yi f)
    (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) (y : ↥(memberDatumObj B S hS Yi f hf D q))
    (hy : (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m) = y) :
    (memberDatumAbTransHom B S hS Yi f hf D q r h).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D q r h y) =
      (memberDatumAbTransHom B S hS Yi f hf D p r (g ≫ h)).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p r (g ≫ h) m) := by
  subst hy
  exact memberDatumAbFnRaw_comp_apply B S hS Yi f hf D p q r g h m

/-- **The three laws of the presheaf of abelian groups of a descent datum**, bundled. -/
theorem memberDatumAb_laws (D : DescentDatum B S hS Yi f) :
    MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)) where
  additive p q g := memberDatumAbFn_laws B S hS Yi f hf D p q g
  id_apply p m := memberDatumAbFnRaw_id_apply B S hS Yi f hf D p m
  comp_apply p q r g h m y hy := memberDatumAbFnRaw_comp_of_eq B S hS Yi f hf D p q r g h m y hy

/-! ### The sections and the restriction map, behind names the kernel can afford -/

/-- **The sections of the presheaf of abelian groups of a descent datum over a chart of a
member**, as an object of `AddCommGrpCat`: the sections of the component module of the datum at
that member over the chart the identity morphism of the site induces. -/
def memberDatumAbGrp (D : DescentDatum B S hS Yi f) (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of (memberDatumObj B S hS Yi f hf D p)

/-- The named sections are the sections of the component module. -/
theorem memberDatumAbGrp_eq (D : DescentDatum B S hS Yi f)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    memberDatumAbGrp B S hS Yi f hf D p =
      AddCommGrpCat.of (memberDatumObj B S hS Yi f hf D p) :=
  rfl

/-- **The bundled reading of the restriction map, read on a section**, is the reading through the
two named factors.  The bundling is `.AddMonoidHomLaws.toAddMonoidHom` of a function and
`AddCommGrpCat.ofHom` of that, so on a section it is that function: one projection of a structure
literal, one beta, and the `AddCommGrpCat.of` of the sections stripped. -/
theorem memberDatumAbBundled_apply (D : DescentDatum B S hS Yi f)
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (AddCommGrpCat.ofHom (AddMonoidHomLaws.toAddMonoidHom
        (memberDatumAbFn_laws B S hS Yi f hf D p q g))) m =
      (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m) :=
  rfl

/-- **The specification of one restriction map of the presheaf of abelian groups of a descent
datum**: that it reads a section as the transition of the datum applied to the restriction of
that section along the chart the morphism of the site induces.

The morphism is a **variable**, so that a consumer's own morphism is read off the goal rather than
compared with one.  Stated at the reading through the two named factors and not at the bundled
reading: the bundled reading in the body of a `def` is the timeout the implementation notes
record, while the reading through the two factors is two named constants and one crossing, which a
`def` does pay -- it is the crossing `.memberDatumAbRestrFn` pays in its own type. -/
def memberDatumAbMpPt (D : DescentDatum B S hS Yi f) (p q : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (g : p ⟶ q) (A : AddCommGrpCat.of (memberDatumObj B S hS Yi f hf D p) ⟶
      AddCommGrpCat.of (memberDatumObj B S hS Yi f hf D q)) : Prop :=
  ∀ m : ↥(memberDatumObj B S hS Yi f hf D p), A m =
    (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)

/-- **The specification of the restriction map of the presheaf of abelian groups of a descent
datum**: `.memberDatumAbMpPt` at every morphism of the site.

Carried behind a name of its own because it is the **predicate of an existential**, and the
predicate of an existential occurs in the body of any `def` that chooses from it.  Its argument is
typed through `.memberDatumAbGrp`, so that the `def` which chooses from it has a small **type**;
the identification of that with `AddCommGrpCat.of` of the sections is paid here, in the body of a
`def`, where there is room for it. -/
def memberDatumAbMpSpec (D : DescentDatum B S hS Yi f)
    (mp : ∀ p q : (MemberSite B S hS Yi f hf)ᵒᵖ, (p ⟶ q) →
      (memberDatumAbGrp B S hS Yi f hf D p ⟶ memberDatumAbGrp B S hS Yi f hf D q)) : Prop :=
  ∀ (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q),
    memberDatumAbMpPt B S hS Yi f hf D p q g (mp p q g)

/-! ### The presheaf of abelian groups of a descent datum, with its laws a hypothesis -/

/-- **The sections of the presheaf of abelian groups of a descent datum**, where that presheaf is
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctorOfLawsV` at the three laws carried as a
**hypothesis** rather than supplied: the sections of the component module of the datum at that
member over the chart the identity morphism of the site induces, as an object of
`AddCommGrpCat`.

The laws are a hypothesis and the sections, their additive structure and the restriction map are
written out.  That is what makes this -- and `.memberDatumAbFunctor_map_apply` -- affordable, and
it is the route by which the presheaf is named at all; see the implementation notes. -/
theorem memberDatumAbFunctor_obj (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    (memberFunctorOfLawsV B S hS Yi f hf hL).obj p = memberDatumAbGrp B S hS Yi f hf D p :=
  rfl

/-- **The restriction map of the presheaf of abelian groups of a descent datum, read on a
section**: the transition of the datum applied to the restriction of that section along the chart
the morphism of the site induces.

This is `.memberFunctorOfLawsV_map_apply` at the laws of the datum carried as a hypothesis, which
is `rfl` with everything in sight a variable; the instantiation is one first-order assignment
each. -/
theorem memberDatumAbFunctor_map_apply (D : DescentDatum B S hS Yi f)
    (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
      (fun _ => inferInstance)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberFunctorOfLawsV B S hS Yi f hf hL).map g m =
      (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m) :=
  memberFunctorOfLawsV_map_apply B S hS Yi f hf hL p q g m

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
