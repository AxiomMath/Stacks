module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSitePresheaf

/-!
# The transition of a descent datum: bundled legs, naturality and change of test space

The bundled data `.TransitionLegs` a reading of the transition depends on, with its two
readings and their congruences; the identity law of the restriction map of the presheaf on the
charts of the members; the morphism of charts `.memberChartSpaceHom` a morphism of the site
induces on the chart spaces; and the naturality of the transition in the chart and its change of
test space, on variables, joined into the composition law `.transitionEtaleForm_base_comp`.

All names are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`; the overview and
the implementation notes are in the module docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteOfPresheaf/Coercions.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)


/-! ### The data a reading of the transition depends on, bundled -/

/-- **The data on which a reading of the transition of a descent datum depends**: a test space
mapping to the pairwise fibre product, the two legs to the members, their étaleness and the two
compatibilities.

It is bundled because the laws of the presheaf of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSitePresheaf.lean` need to
compare two readings whose data differ only by a respelling, and comparing them *argument by
argument* is unaffordable while comparing them in **one opaque field** is free: see the
implementation notes. -/
structure TransitionLegs (T : AlgebraicSpaces B S hS) (i j : I) where
  /-- The morphism of the test space to the pairwise fibre product. -/
  v : T ⟶ pair B S hS Yi f i j
  /-- The leg to the source member. -/
  vi : T ⟶ Yi i
  /-- The leg to the target member. -/
  vj : T ⟶ Yi j
  /-- The source leg is étale. -/
  hvi : IsEtale B S hS vi.hom
  /-- The target leg is étale. -/
  hvj : IsEtale B S hS vj.hom
  /-- The first projection of the morphism to the fibre product is the source leg. -/
  hi : v ≫ pairFst B S hS Yi f i j = vi
  /-- The second projection of the morphism to the fibre product is the target leg. -/
  hj : v ≫ pairSnd B S hS Yi f i j = vj

/-- **The bundled reading of the transition of a descent datum**:
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm` taking its test space, legs,
étaleness and compatibilities as one `.TransitionLegs`.

For a literal bundle the projections reduce, so this is the written-out reading on the nose and a
consumer may write either. -/
def transitionLegsForm (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i j : I)
    (L : TransitionLegs B S hS Yi f T i j) :
    (etaleModulePullback.{u, u} B S hS L.vi L.hvi).obj (D.F i) ⟶
      (etaleModulePullback.{u, u} B S hS L.vj L.hvj).obj (D.F j) :=
  transitionEtaleForm B S hS Yi f D i j L.v L.vi L.vj L.hvi L.hvj L.hi L.hj

/-- **Two readings of the transition over one chart, whose data are equal, agree on a section.**

This is the way past the wall the laws of the presheaf meet.  `SheafOfModules.Hom.val` is a
projection, so `.val.app (.op U)` of two readings is never compared argument by argument: the
elaborator demands the morphism in constructor form, and for the transition that means reducing
through the comparison of Stacks 03LU, which is an adjunction-uniqueness isomorphism and does not
get there.  Supplying the agreement of the two readings **propositionally**, from the equality of
their bundled data — where it is `rfl` — asks for no such reduction.

The two sections are carried as separate variables related by `HEq`, not as one section and its
transport: with a transport `h ▸ s` in the statement the `rfl` after `subst` has to reduce the
transport *inside* `.val.app`, which is the very thing being avoided, and it times out.  With two
variables, `subst` and `cases` make the two sides literally one term. -/
theorem transitionLegsForm_congr (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS}
    (i j : I) (L L' : TransitionLegs B S hS Yi f T i j) (h : L = L')
    (U : SmallEtale B S hS T.1)
    (s : ((etaleModulePullback.{u, u} B S hS L.vi L.hvi).obj (D.F i)).val.obj (Opposite.op U))
    (s' : ((etaleModulePullback.{u, u} B S hS L'.vi L'.hvi).obj (D.F i)).val.obj (Opposite.op U))
    (hs : HEq s s') :
    HEq ((transitionLegsForm B S hS Yi f D i j L).val.app (Opposite.op U) s)
      ((transitionLegsForm B S hS Yi f D i j L').val.app (Opposite.op U) s') := by
  subst h
  cases hs
  rfl



/-- **The written-out reading of the transition of a descent datum over a chart**, taking the
test space, the legs, their étaleness and the two compatibilities as one `.TransitionLegs`.

For a literal bundle the projections reduce, so this is the written-out reading
`etaleSect … (transitionHom … ).val.app … (etaleSectInv … )` on the nose, and the laws of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartLaws.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartBaseChange.lean` may be read as statements about it. -/
def transitionLegsSect (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i j : I)
    (L : TransitionLegs B S hS Yi f T i j) (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS L.vi L.hvi).obj U))) :
    (D.F j).val.obj (Opposite.op ((smallEtalePostcomp B S hS L.vj L.hvj).obj U)) :=
  etaleSect B S hS L.vj L.hvj (D.F j) U
    ((transitionHom B S hS Yi f D i j L.v L.vi L.vj L.hi L.hj).val.app (Opposite.op U)
      (etaleSectInv B S hS L.vi L.hvi (D.F i) U s))

/-- **Two written-out readings of the transition over one chart, whose data are equal, agree on
a section.**  This is `.transitionLegsForm_congr` for the written-out reading, and it is what
respells a leg: the agreement is supplied propositionally from the equality of the bundles,
where it is `rfl`, so `.app (.op U)` is never asked for a defeq.  The two sections are separate
variables related by `HEq`, for the reason in the implementation notes. -/
theorem transitionLegsSect_congr (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS}
    (i j : I) (L L' : TransitionLegs B S hS Yi f T i j) (h : L = L')
    (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS L.vi L.hvi).obj U)))
    (s' : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS L'.vi L'.hvi).obj U)))
    (hs : HEq s s') :
    HEq (transitionLegsSect B S hS Yi f D i j L U s)
      (transitionLegsSect B S hS Yi f D i j L' U s') := by
  subst h
  cases hs
  rfl



/-- `.transitionLegsSect_congr` with the second section written as the transport of the first.

This is the form a consumer uses.  Its two sides are applications of one *definition* with the
same head, so the elaborator compares them argument by argument and the transport is stripped by
a single iota — it never unfolds the reading, and so never meets the projection
`SheafOfModules.Hom.val`.  The two-section form above cannot be used directly at a consumer's
concrete data: the section types there are written through the bundle's projections,
so passing a `HEq` stated in the consumer's own spelling asks for **two** crossings in one
unification and times out. -/
theorem transitionLegsSect_congr_transport (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i j : I) (L L' : TransitionLegs B S hS Yi f T i j)
    (h : L = L') (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS L.vi L.hvi).obj U))) :
    HEq (transitionLegsSect B S hS Yi f D i j L U s)
      (transitionLegsSect B S hS Yi f D i j L' U (h ▸ s)) := by
  subst h
  rfl


section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- **The restriction factor of the restriction map of the presheaf, at an identity morphism of
the site of the charts of the members, acts as the identity on a section** — with its two charts
spelled explicitly, as the restriction map of the presheaf of abelian groups below carries them.
This is `.memberDatumRestrict_id_apply` in the spelling of `.memberDatumAb_comp_apply`: at an
identity morphism the chart a morphism of the site induces and the chart over which the
transition reads its target are **one and the same** term, so the explicit spelling costs nothing
here. -/
theorem memberDatumRestrict_id_apply' (D : DescentDatum B S hS Yi f) (p : (MemberSite B S hS Yi f
      hf)ᵒᵖ) (m : (D.F p.unop.1).val.obj (Opposite.op (((smallEtalePostcomp B S hS (memberChartMap B
      S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap
      B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj
      (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))) : ModuleCat.Hom.hom ((D.F
      p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi
      f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS
      Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S
      hS (Yi p.unop.1) p.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi
      f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS
      (Yi p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B
      S hS Yi f hf (𝟙 p).unop)))) m = m := val_map_eq_id_hom_apply B S hS (D.F p.unop.1)
      (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2
      p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS
      Yi f hf (𝟙 p).unop))) rfl m

/-- **The identity law of the restriction map of the presheaf attached to a descent datum, with
no restriction of scalars in sight**: the transition attached to an identity morphism of the site
of the charts of the members, applied to the restriction of a section along that morphism, is
that section.

Both factors are written out, in the spelling a direct `CategoryTheory.Functor` structure
instance leaves in the goal of `map_id`.  `.memberDatumRestrict_id_apply` is the restriction
factor and `.transitionEtaleForm_id_hom_apply` the transition factor, joined by `.apply_congr`
— whose argument order is what keeps the restricted section at the type the restriction half
gives it. -/
theorem memberDatumAb_id_apply (D : DescentDatum B S hS Yi f) (p : (MemberSite B S hS Yi f hf)ᵒᵖ) (m
      : (D.F p.unop.1).val.obj (Opposite.op (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi
      f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS
      (Yi p.unop.1) p.unop.2))))) : (transitionEtaleForm B S hS Yi f D p.unop.1 p.unop.1
      (memberChartPair B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
      (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
      (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
      p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf
      (𝟙 p).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf
      (𝟙 p).unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf
      (𝟙 p).unop) (memberHom B S hS Yi f hf (𝟙 p).unop) rfl)).val.app (Opposite.op
      (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2)) (ModuleCat.Hom.hom ((D.F p.unop.1).val.map
      (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2
      p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS
      Yi f hf (𝟙 p).unop)))) m) = m := (apply_congr (memberDatumRestrict_id_apply' B S hS Yi f hf D
      p m) (fun z => (transitionEtaleForm B S hS Yi f D p.unop.1 p.unop.1 (memberChartPair B S hS Yi
      f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi
      f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (memberChartPair_fst B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (memberChartPair_snd' B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop) (memberHom B S hS Yi f hf (𝟙
      p).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))
      z)).trans (transitionEtaleForm_id_hom_apply B S hS Yi f D p.unop.1 (memberChartPair B S hS Yi
      f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (memberChartPair_fst B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (memberChartPair_snd' B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop) (memberHom B S hS Yi f hf (𝟙
      p).unop) rfl) (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2) m)

/-! ### The morphism of charts a morphism of the site induces on the chart spaces -/

/-- **The morphism of charts of the chart space of the source chart of a morphism of the site of
the charts of the members, onto the identity chart of the chart space of the target chart.**  Its
underlying morphism of the big fppf site is the one the morphism of the site carries, and the
triangle over the chart space is the one that morphism commutes.

It is written out rather than taken from the terminality
`AlgebraicGeometry.Space.isTerminalIdEtaleChart` of the identity chart, which would give the same
morphism: see the implementation notes. -/
def memberChartSpaceHom {j k : I} (V' : SmallEtale B S hS (Yi j).1)
    (V'' : SmallEtale B S hS (Yi k).1)
    (b : (smallEtalePostcomp B S hS (f k) (hf k)).obj V'' ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    (smallEtalePostcomp B S hS (chartMap B S hS X b)
          (isEtale_chartMap B S hS X b)).obj (chartSpaceIdChart B S hS (Yi k) V'') ⟶
      chartSpaceIdChart B S hS (Yi j) V' :=
  ObjectProperty.homMk (CostructuredArrow.homMk b.hom.left (by rfl))

/-- **The morphism of charts of the target member induced by a morphism of the site is
`.memberChartSpaceHom` pushed forward along the self leg.**  On the nose; this is what lets the
naturality of the transition in the chart be used at the restriction map of the presheaf. -/
theorem memberChartSpaceHom_postcomp {j k : I} (V' : SmallEtale B S hS (Yi j).1)
    (V'' : SmallEtale B S hS (Yi k).1)
    (b : (smallEtalePostcomp B S hS (f k) (hf k)).obj V'' ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    (smallEtalePostcomp B S hS
        (memberChartMap B S hS Yi f hf V' V'
          (𝟙 ((smallEtalePostcomp B S hS (f j) (hf j)).obj V')))
        (isEtale_memberChartMap B S hS Yi f hf V' V'
          (𝟙 ((smallEtalePostcomp B S hS (f j) (hf j)).obj V')))).map
        (memberChartSpaceHom B S hS Yi f hf V' V'' b) =
      memberTransitionHom B S hS Yi f hf V' V'' b := rfl

/-- **The morphism of charts of a member induced by a composite morphism of the site is the one
induced by the second factor, restricted along `.memberChartSpaceHom` of the first.**  On the
nose, like `.memberChartSpaceHom_postcomp`. -/
theorem memberChartSpaceHom_postcomp_comp {i j k : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1) (V'' : SmallEtale B S hS (Yi k).1)
    (a : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
    (b : (smallEtalePostcomp B S hS (f k) (hf k)).obj V'' ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    (smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V V' a)
          (isEtale_memberChartMap B S hS Yi f hf V V' a)).map
          (memberChartSpaceHom B S hS Yi f hf V' V'' b) ≫
        memberTransitionHom B S hS Yi f hf V V' a =
      memberTransitionHom B S hS Yi f hf V V'' (b ≫ a) := rfl

/-! ### The naturality of the transition in the chart, on variables -/

/-- **The naturality of the transition of a descent datum in the chart, with the restricted
section and the restriction of the target carried as variables.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_restrict` with its two restrictions
replaced by variables identified with them by hypotheses, so that a consumer instantiates it in
**its own** spelling of the two morphisms of charts and the defining equations are discharged by
`rfl` on their own — where they are cheap — rather than inside the unification of two readings of
the transition, where they are not.

At the charts of the members the consumer takes the morphism of charts of the test space to be
`.memberChartSpaceHom` and discharges both hypotheses by `.memberChartSpaceHom_postcomp` and
`.val_map_comp_hom_apply`. -/
theorem memberTransitionSect_restrict (D : DescentDatum B S hS Yi f)
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i)
    (vj : T ⟶ Yi j) (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    {U U' : SmallEtale B S hS T.1} (c : U' ⟶ U)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS vi hvi).obj U)))
    (t : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS vi hvi).obj U')))
    (ht : t = (D.F i).val.map ((smallEtalePostcomp B S hS vi hvi).map c).op s)
    (e : (smallEtalePostcomp B S hS vj hvj).obj U' ⟶ (smallEtalePostcomp B S hS vj hvj).obj U)
    (he : e = (smallEtalePostcomp B S hS vj hvj).map c) :
    etaleSect B S hS vj hvj (D.F j) U'
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (Opposite.op U')
          (etaleSectInv B S hS vi hvi (D.F i) U' t)) =
      ModuleCat.Hom.hom ((D.F j).val.map e.op)
        (etaleSect B S hS vj hvj (D.F j) U
          ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (Opposite.op U)
            (etaleSectInv B S hS vi hvi (D.F i) U s))) := by
  subst ht he
  exact transitionSect_restrict B S hS Yi f D i j v vi vj hvi hvj hi hj c s


/-- **The change of test space composed with the naturality in the chart, as one law on
variables.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_base` followed by
`.transitionSect_restrict`, joined **inside a statement all of whose charts, legs and sections
are variables**, where the middle term of the join is one and the same term on the nose.

Joining the two at a consumer's concrete charts instead is out of reach: both
instantiations elaborate, their middle terms print character-for-character alike, and `Eq.trans`
between them times out at `isDefEq` — the two carry the chart of the smaller test space in the
two spellings `(smallEtalePostcomp (wv ≫ vj) _).obj U` and `(smallEtalePostcomp vj _).obj
((smallEtalePostcomp wv _).obj U)`, and identifying those inside the ambient type of an equation
between two readings of the transition is the operation this material does not support.  Here
they are the same variable.

The restricted section and the restriction of the target are carried as variables identified by
hypotheses, in the shape of `.memberTransitionSect_restrict` and for the same reason. -/
theorem transitionSect_base_restrict (D : DescentDatum B S hS Yi f)
    {T T' : AlgebraicSpaces B S hS} (wv : T' ⟶ T) (hwv : IsEtale B S hS wv.hom) (i j : I)
    (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (hwvi : IsEtale B S hS (wv ≫ vi).hom) (hwvj : IsEtale B S hS (wv ≫ vj).hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : (wv ≫ v) ≫ pairFst B S hS Yi f i j = wv ≫ vi)
    (hj' : (wv ≫ v) ≫ pairSnd B S hS Yi f i j = wv ≫ vj)
    (U : SmallEtale B S hS T'.1) (U₁ : SmallEtale B S hS T.1)
    (c : (smallEtalePostcomp B S hS wv hwv).obj U ⟶ U₁)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS vi hvi).obj U₁)))
    (t : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS vi hvi).obj
      ((smallEtalePostcomp B S hS wv hwv).obj U))))
    (ht : t = (D.F i).val.map ((smallEtalePostcomp B S hS vi hvi).map c).op s)
    (e : (smallEtalePostcomp B S hS vj hvj).obj ((smallEtalePostcomp B S hS wv hwv).obj U) ⟶
      (smallEtalePostcomp B S hS vj hvj).obj U₁)
    (he : e = (smallEtalePostcomp B S hS vj hvj).map c) :
    etaleSect B S hS (wv ≫ vj) hwvj (D.F j) U
        ((transitionHom B S hS Yi f D i j (wv ≫ v) (wv ≫ vi) (wv ≫ vj) hi' hj').val.app
          (Opposite.op U)
          (etaleSectInv B S hS (wv ≫ vi) hwvi (D.F i) U t)) =
      ModuleCat.Hom.hom ((D.F j).val.map e.op)
        (etaleSect B S hS vj hvj (D.F j) U₁
          ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (Opposite.op U₁)
            (etaleSectInv B S hS vi hvi (D.F i) U₁ s))) :=
  by
  subst ht he
  exact (transitionSect_base B S hS Yi f D wv hwv i j v vi vj hvi hvj hwvi hwvj hi hj hi' hj' U
      ((D.F i).val.map ((smallEtalePostcomp B S hS vi hvi).map c).op s)).trans
    (transitionSect_restrict B S hS Yi f D i j v vi vj hvi hvj hi hj c s)


/-! ### The change of test space with the legs of the smaller test space as variables -/

/-- **The change of test space composed with the naturality in the chart, with the two legs of
the smaller test space carried as variables.**  This is `.transitionSect_base_restrict` restated
so that the legs `wvi`, `wvj` over the smaller test space are opaque, identified with the
composites `wv ≫ vi` and `wv ≫ vj` by hypotheses, and so that **every section and every
connecting morphism on the side of the smaller test space is typed through those variables**.

That last point is the whole content.  The implementation notes record a type error for the naive
restatement: with the leg a variable and the connecting morphism of charts still spelled
`(smallEtalePostcomp vi hvi).map c`, the two sides of the hypothesis `ht` have types the
elaborator cannot reconcile, and the statement does not elaborate at all.  Carrying that morphism
as a variable `cc` too, related to `(smallEtalePostcomp vi hvi).map c` by `HEq`, removes the
mismatch: each side of every hypothesis is then written in one spelling only, and the two
spellings meet exactly once, inside this proof, where `subst` has made them one term.

A consumer instantiates it at **its own** spelling of the two legs — at the charts of the members
`memberChartMap V V'' (b ≫ a)` and `memberChartMap V' V'' b` — and discharges `ewi`, `ewj` by
`rfl`.  No leg is ever respelled afterwards, which is what the earlier shapes could not avoid. -/
theorem transitionSect_base_restrict_of_legs (D : DescentDatum B S hS Yi f)
    {T T' : AlgebraicSpaces B S hS} (wv : T' ⟶ T) (hwv : IsEtale B S hS wv.hom) (i j : I)
    (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (wvi : T' ⟶ Yi i) (wvj : T' ⟶ Yi j)
    (hwvi : IsEtale B S hS wvi.hom) (hwvj : IsEtale B S hS wvj.hom)
    (ewi : wvi = wv ≫ vi) (ewj : wvj = wv ≫ vj)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : (wv ≫ v) ≫ pairFst B S hS Yi f i j = wvi)
    (hj' : (wv ≫ v) ≫ pairSnd B S hS Yi f i j = wvj)
    (U : SmallEtale B S hS T'.1) (U₁ : SmallEtale B S hS T.1)
    (c : (smallEtalePostcomp B S hS wv hwv).obj U ⟶ U₁)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS vi hvi).obj U₁)))
    (t : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS wvi hwvi).obj U)))
    (cc : (smallEtalePostcomp B S hS wvi hwvi).obj U ⟶
      (smallEtalePostcomp B S hS vi hvi).obj U₁)
    (hcc : HEq cc ((smallEtalePostcomp B S hS vi hvi).map c))
    (ht : t = (D.F i).val.map cc.op s)
    (e : (smallEtalePostcomp B S hS wvj hwvj).obj U ⟶
      (smallEtalePostcomp B S hS vj hvj).obj U₁)
    (he : HEq e ((smallEtalePostcomp B S hS vj hvj).map c)) :
    etaleSect B S hS wvj hwvj (D.F j) U
        ((transitionHom B S hS Yi f D i j (wv ≫ v) wvi wvj hi' hj').val.app
          (Opposite.op U)
          (etaleSectInv B S hS wvi hwvi (D.F i) U t)) =
      ModuleCat.Hom.hom ((D.F j).val.map e.op)
        (etaleSect B S hS vj hvj (D.F j) U₁
          ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (Opposite.op U₁)
            (etaleSectInv B S hS vi hvi (D.F i) U₁ s))) := by
  subst ewi ewj
  obtain rfl := eq_of_heq hcc
  obtain rfl := eq_of_heq he
  exact transitionSect_base_restrict B S hS Yi f D wv hwv i j v vi vj hvi hvj hwvi hwvj
    hi hj hi' hj' U U₁ c s t ht _ rfl

/-! ### The whole join of the composition law, on variables -/

/-- **THE COMPOSITION LAW OF THE TRANSITION ACROSS A CHANGE OF TEST SPACE, on variables.**  For
a morphism `wv : T' ⟶ T` of test spaces, the transition from `i` to `j` read over `T` and
restricted along `wv`, followed by the transition from `j` to `k` read over `T'`, is the
transition from `i` to `k` read over `T'`.

This is the whole of `map_comp` of the presheaf of abelian groups on the charts of the members,
with the charts, the legs, the sections and the two connecting morphisms all opaque.  It is the
bridge `.transitionEtaleForm_val_app_apply` at each of the three transitions,
`.transitionSect_base_restrict_of_legs` for the change of test space and the naturality in the
chart, and
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_comp` — the cocycle — for the join
of the two transitions over `T'`. -/
theorem transitionEtaleForm_base_comp (D : DescentDatum B S hS Yi f)
    {T T' : AlgebraicSpaces B S hS} (wv : T' ⟶ T) (hwv : IsEtale B S hS wv.hom) (i j k : I)
    (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (wvi : T' ⟶ Yi i) (wvj : T' ⟶ Yi j) (vk : T' ⟶ Yi k)
    (hwvi : IsEtale B S hS wvi.hom) (hwvj : IsEtale B S hS wvj.hom)
    (hvk : IsEtale B S hS vk.hom)
    (ewi : wvi = wv ≫ vi) (ewj : wvj = wv ≫ vj)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : (wv ≫ v) ≫ pairFst B S hS Yi f i j = wvi)
    (hj' : (wv ≫ v) ≫ pairSnd B S hS Yi f i j = wvj)
    (vjk : T' ⟶ pair B S hS Yi f j k) (vik : T' ⟶ pair B S hS Yi f i k)
    (hjk₀ : vjk ≫ pairFst B S hS Yi f j k = wvj)
    (hjk₁ : vjk ≫ pairSnd B S hS Yi f j k = vk)
    (hik₀ : vik ≫ pairFst B S hS Yi f i k = wvi)
    (hik₁ : vik ≫ pairSnd B S hS Yi f i k = vk)
    (U : SmallEtale B S hS T'.1) (U₁ : SmallEtale B S hS T.1)
    (c : (smallEtalePostcomp B S hS wv hwv).obj U ⟶ U₁)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS vi hvi).obj U₁)))
    (t : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS wvi hwvi).obj U)))
    (cc : (smallEtalePostcomp B S hS wvi hwvi).obj U ⟶
      (smallEtalePostcomp B S hS vi hvi).obj U₁)
    (hcc : HEq cc ((smallEtalePostcomp B S hS vi hvi).map c))
    (ht : t = (D.F i).val.map cc.op s)
    (e : (smallEtalePostcomp B S hS wvj hwvj).obj U ⟶
      (smallEtalePostcomp B S hS vj hvj).obj U₁)
    (he : HEq e ((smallEtalePostcomp B S hS vj hvj).map c)) :
    (transitionEtaleForm B S hS Yi f D j k vjk wvj vk hwvj hvk hjk₀ hjk₁).val.app
        (Opposite.op U)
        (ModuleCat.Hom.hom ((D.F j).val.map e.op)
          ((transitionEtaleForm B S hS Yi f D i j v vi vj hvi hvj hi hj).val.app
            (Opposite.op U₁) s)) =
      (transitionEtaleForm B S hS Yi f D i k vik wvi vk hwvi hvk hik₀ hik₁).val.app
        (Opposite.op U) t :=
  (apply_congr (transitionEtaleForm_val_app_apply B S hS Yi f D i j v vi vj hvi hvj hi hj U₁ s)
      (fun z => (transitionEtaleForm B S hS Yi f D j k vjk wvj vk hwvj hvk hjk₀ hjk₁).val.app
        (Opposite.op U) (ModuleCat.Hom.hom ((D.F j).val.map e.op) z))).trans
    ((apply_congr (transitionSect_base_restrict_of_legs B S hS Yi f D wv hwv i j v vi vj hvi hvj
          wvi wvj hwvi hwvj ewi ewj hi hj hi' hj' U U₁ c s t cc hcc ht e he).symm
        (fun z => (transitionEtaleForm B S hS Yi f D j k vjk wvj vk hwvj hvk hjk₀ hjk₁).val.app
          (Opposite.op U) z)).trans
      ((transitionEtaleForm_val_app_apply B S hS Yi f D j k vjk wvj vk hwvj hvk hjk₀ hjk₁ U
            (etaleSect B S hS wvj hwvj (D.F j) U
              ((transitionHom B S hS Yi f D i j (wv ≫ v) wvi wvj hi' hj').val.app
                (Opposite.op U) (etaleSectInv B S hS wvi hwvi (D.F i) U t)))).trans
        ((transitionSect_comp B S hS Yi f D i j k T' wvi wvj vk hwvi hwvj hvk
              (wv ≫ v) vjk vik hi' hj' hjk₀ hjk₁ hik₀ hik₁ U t).trans
          (transitionEtaleForm_val_app_apply B S hS Yi f D i k vik wvi vk hwvi hvk hik₀ hik₁
            U t).symm)))

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
