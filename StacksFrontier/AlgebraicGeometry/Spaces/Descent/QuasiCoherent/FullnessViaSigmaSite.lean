module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardIdentityNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ChartCoversTop
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleCanonicalDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.PairChartNaturality

/-!
# The site of the charts of the members of an étale covering

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be an étale covering of
`X`, for instance a Zariski covering.  The charts of the members of the covering form a site: the
objects are the pairs `(i, V)` of a member and a chart of that member, the morphisms are the
morphisms of the induced charts of `X`, and the topology is the one restricted from the small
étale topology of `X`.  The charts of the members refine every chart of `X`, so the functor to
the small étale site of `X` is cover dense; by the Comparison Lemma for sheaves of modules,
`Stacks.DenseSubsiteModules.moduleRestriction`, restriction of `𝒪_X`-modules along it is
therefore fully faithful.

This is the site on which a morphism of the canonical descent data of Stacks 04W5 becomes a
morphism of modules: the component of such a morphism at a member of the family is, along the
étale morphism `f i`, a map of sections over the charts of `Y i`, and the pairwise condition of
Stacks 04W3 is naturality of those maps across the members, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_naturality`.  A pairwise compatible
family of morphisms of the inverse images is therefore a morphism of the restrictions of the two
modules to this site, hence the restriction of a morphism of `𝒪_X`-modules; and the inverse
images of that morphism are the members of the family.  That is the fullness half of Stacks
04W6, which this file proves for an étale and for a Zariski covering, and combines with the
faithfulness half into full faithfulness of the canonical descent functor.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent` unless said
otherwise.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.MemberSite` is the category of the charts of the
  members of the family, `.memberFunctor` its functor to the small étale site of `X` and
  `.memberTopology` the topology restricted along it.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberRing` and `.memberRestriction` are the
  structure sheaf of `X` and the `𝒪_X`-modules read on that site.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.IsPairwiseCompatible` is the pairwise condition
  of Stacks 04W3 on a family of morphisms of the inverse images of two `𝒪_X`-modules.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFormApp` is the étale form of a member of
  such a family, read on sections over a chart of that member, and
  `.memberForm` is the family itself as a morphism of the restrictions of the two modules to the
  site of the charts of the members.
* `fullyFaithfulEtaleCanonicalDescentFunctorOfIsZariskiCovering` is the full faithfulness of the
  canonical descent functor of a Zariski covering.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.isCoverDense_memberFunctor`: **the charts of the
  members of an étale covering are cover dense in the small étale site of `X`.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_naturality_memberPair`: the pairwise
  condition of a family of morphisms of the inverse images, read as naturality of their étale
  forms across two charts of two members.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberRestriction_map_val_app`: the restriction
  of a morphism of `𝒪_X`-modules to the site of the charts of the members is, at a pair of a
  member and a chart of that member, its étale restriction to that member read on sections over
  the chart.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_naturality`:
  **a family of morphisms of the inverse images along an étale covering whose étale forms are
  natural across the charts of the members is the family of the inverse images of a morphism of
  `𝒪_X`-modules.**  Nothing is carried: this is the fullness half of Stacks 04W6 with its input
  taken on sections, which is the one place the compatibility of Stacks 03LU with étale
  restriction was used.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq`: the same for a
  *pairwise compatible* family, which is the shape of Stacks 04W3; this is where the
  compatibility enters, through
  `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartForm_naturality`.
* `full_etaleCanonicalDescentFunctor_of_isEtaleCovering` and
  `full_etaleCanonicalDescentFunctor_of_isZariskiCovering`: **the canonical descent functor
  of an étale, respectively Zariski, covering of an algebraic space is full**, the fullness half
  of Stacks 04W6.

## Implementation notes

Quasi-coherence enters nowhere: the statements below are about arbitrary sheaves of modules on
the small étale site of `X`, descent of morphisms along an étale covering being the sheaf
condition there.

The compatibility of the comparison of inverse images of Stacks 03LU with iterated étale
restriction is what makes the pairwise condition readable on charts, and it is carried only
where that reading happens.  It is carried as
`AlgebraicGeometry.Space.QuasiCoherentDescent.PairEtaleRestrictionComp`, the compatibility at the
two projections of a pairwise fibre product followed by the two members and at no other pair;
this development does not have the predicate quantified over every pair of algebraic spaces, but
it does have the localized one for a family of relatively representable members, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairEtaleRestrictionComp_of_representable`.  The
statements that do not perform that reading — everything from
`…exists_modulePullback_map_eq_of_naturality` downwards — carry nothing.

The structure ring of a chart `V` of a member `Y i` and the structure ring of the induced chart
`V ≫ f i` of `X` are the ring of regular functions on one and the same scheme, so they agree
definitionally — that is why `AlgebraicGeometry.Space.etaleModulePullback` can be formed with the
identity morphism of sheaves of rings.  They are not syntactically equal, and the elaborator
performs the identification only in the position of a type or of a morphism, not between two
sections: every statement below is arranged so that it is asked for in one of those two
positions.  `AlgebraicGeometry.Space.QuasiCoherentDescent.memberObj` and `.memberPair` are
reducible abbreviations for the same reason; the pairwise condition is turned from an
elementwise statement into an equality of morphisms of the modules of sections by
`PresheafOfModules.naturality_of_apply`, in which the two presheaves, the two objects and the
morphism between them are variables; and it is handed to
`Stacks.DenseSubsiteModules.moduleRestrictionHom`, in which the functor and the two sheaves are
variables, in that form.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 041G](https://stacks.math.columbia.edu/tag/041G)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
* [Stacks Project, Tag 0DF1](https://stacks.math.columbia.edu/tag/0DF1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### The site of the charts of the members -/

/-- The chart of `X` attached to a member of a family of algebraic spaces étale over `X`
together with a chart of that member: the chart postcomposed with the member morphism.

This is `AlgebraicGeometry.Space.memberChart`, repeated as a reducible abbreviation: the sections
of a module over such a chart have to be recognized as the sections of its étale restriction to
the member, and the elaborator does not perform that identification through a semireducible
definition. -/
abbrev memberObj (p : Σ i : I, SmallEtale B S hS (Yi i).1) : SmallEtale B S hS X.1 :=
  (smallEtalePostcomp B S hS (f p.1) (hf p.1)).obj p.2

/-- The site of the charts of the members of a family of algebraic spaces étale over `X`: the
pairs of a member and a chart of it, with the morphisms of the induced charts of `X`. -/
abbrev MemberSite :=
  InducedCategory (SmallEtale B S hS X.1) (memberObj B S hS Yi f hf)

/-- The object of the site of the charts of the members attached to a member of the family and a
chart of that member. -/
abbrev memberPair (i : I) (V : SmallEtale B S hS (Yi i).1) : MemberSite B S hS Yi f hf :=
  ⟨i, V⟩

/-- The functor from the charts of the members to the charts of `X`. -/
abbrev memberFunctor : MemberSite B S hS Yi f hf ⥤ SmallEtale B S hS X.1 :=
  inducedFunctor (memberObj B S hS Yi f hf)

/-- The topology of the charts of the members, restricted from the small étale topology of
`X`. -/
abbrev memberTopology : GrothendieckTopology (MemberSite B S hS Yi f hf) :=
  (memberFunctor B S hS Yi f hf).restrictedTopology (SmallEtale.topology B S hS X.1)

/-- **The charts of the members of an étale covering are cover dense in the small étale site of
`X`.**  Every chart of `X` is refined by charts of the members, so the sieve of the morphisms
into it which factor through a chart of a member is covering. -/
theorem isCoverDense_memberFunctor
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1) where
  is_cover W := by
    obtain ⟨V, q, hcover⟩ := exists_refinement_of_jointlySurjective B S hS Yi f hf
      (fun x => by
        obtain ⟨i, y, hy⟩ :=
          Set.mem_iUnion.1 (hcov.jointly_surjective.symm ▸ Set.mem_univ x)
        exact ⟨i, y, hy⟩) W
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hcover
    rintro Z r ⟨_, b, _, ⟨i⟩, rfl⟩
    exact ⟨⟨⟨i, V i⟩, b, q i, rfl⟩⟩

/-! ### The pairwise condition on a family of morphisms of inverse images -/

/-- The pairwise condition of Stacks 04W3 on a family of morphisms of the inverse images of two
`𝒪_X`-modules along the members of a family: the canonical comparisons of Stacks 04W5 intertwine
the members of the family on every pairwise fibre product. -/
def IsPairwiseCompatible {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N) :
    Prop :=
  ∀ i j, (modulePullback B S hS (pairFst B S hS Yi f i j)).map (w i) ≫
      (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
        (pair_condition B S hS Yi f i j) N).hom =
    (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
        (pair_condition B S hS Yi f i j) M).hom ≫
      (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (w j)

/-- **The pairwise condition of a family of morphisms of the inverse images, read as naturality
of their étale forms across two charts of two members of the family.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_naturality` for a family satisfying the
pairwise condition, which is the form in which a morphism of the canonical descent data of
Stacks 04W5 is natural over the site of the charts of the members. -/
theorem etaleForm_naturality_memberPair
    (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hw : IsPairwiseCompatible B S hS Yi f w) (i j : I) (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
    (m : M.val.obj (.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))) :
    (etaleForm B S hS (f j) (hf j) (w j)).val.app (.op V') (M.val.map k.op m) =
      N.val.map k.op ((etaleForm B S hS (f i) (hf i) (w i)).val.app (.op V) m) :=
  etaleForm_naturality B S hS Yi f hf hcomp (w j) (w i) (hw j i) k m

/-! ### Modules read on the site of the charts of the members -/

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- The structure sheaf of `X`, read on the charts of the members. -/
abbrev memberRing : Sheaf (memberTopology B S hS Yi f hf) RingCat.{u} :=
  Stacks.DenseSubsiteModules.ringRestriction (memberTopology B S hS Yi f hf)
    (SmallEtale.topology B S hS X.1) (memberFunctor B S hS Yi f hf)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- Restriction of `𝒪_X`-modules to the charts of the members.  It is fully faithful by the
Comparison Lemma for sheaves of modules. -/
abbrev memberRestriction :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (memberRing B S hS Yi f hf) :=
  Stacks.DenseSubsiteModules.moduleRestriction (memberTopology B S hS Yi f hf)
    (SmallEtale.topology B S hS X.1) (memberFunctor B S hS Yi f hf)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- The identity, read as the morphism of presheaves of rings along which `𝒪_X`-modules are
restricted to the charts of the members. -/
abbrev memberRingMap :
    (memberRing B S hS Yi f hf).obj ⟶ (memberFunctor B S hS Yi f hf).op ⋙
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj :=
  𝟙 ((memberRing B S hS Yi f hf).obj)

/-- A section of the restriction of an `𝒪_X`-module to the site of the charts of the members,
read as a section of the module itself over the induced chart of `X`.  The result type is
ascribed because the structure ring of a chart of a member is the structure ring of the induced
chart of `X` definitionally but not syntactically. -/
def memberSect {M : Modules.{u, u} B S hS X.1 X.2} (p : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (m : ((memberRestriction B S hS Yi f hf).obj M).val.obj p) :
    M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f p.unop.1) (hf p.unop.1)).obj
      p.unop.2)) :=
  m

/-- Reading a section of the restriction to the site of the charts of the members as a section
over the induced chart of `X` does not change it. -/
theorem memberSect_eq {M : Modules.{u, u} B S hS X.1 X.2}
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (m : ((memberRestriction B S hS Yi f hf).obj M).val.obj p) :
    memberSect B S hS Yi f hf p m = m :=
  rfl

/-- The morphism of the charts of `X` underlying a morphism of the site of the charts of the
members.  The result type is ascribed, so that a consumer matches it without unfolding the
induced category. -/
def memberHom {p q : MemberSite B S hS Yi f hf} (k : p ⟶ q) :
    (smallEtalePostcomp B S hS (f p.1) (hf p.1)).obj p.2 ⟶
      (smallEtalePostcomp B S hS (f q.1) (hf q.1)).obj q.2 :=
  k.hom

/-- The étale form of a member of a family of morphisms of the inverse images, read on sections
over a chart of that member as a map of the sections of the two modules over the induced chart
of `X`. -/
def memberChartForm {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (i : I) (V : SmallEtale B S hS (Yi i).1) :
    M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)) ⟶
      N.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V)) :=
  etaleModulePullbackHomApp B S hS (f i) (hf i) (etaleForm B S hS (f i) (hf i) (w i)) V

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartForm` is the étale form read on
sections over the chart. -/
theorem memberChartForm_eq {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (i : I) (V : SmallEtale B S hS (Yi i).1) :
    memberChartForm B S hS Yi f hf w i V =
      (etaleForm B S hS (f i) (hf i) (w i)).val.app (.op V) :=
  etaleModulePullbackHomApp_eq B S hS (f i) (hf i) (etaleForm B S hS (f i) (hf i) (w i)) V

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartForm` on a section. -/
theorem memberChartForm_apply {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (i : I) (V : SmallEtale B S hS (Yi i).1)
    (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))) :
    memberChartForm B S hS Yi f hf w i V t =
      (etaleForm B S hS (f i) (hf i) (w i)).val.app (.op V) t :=
  etaleModulePullbackHomApp_apply B S hS (f i) (hf i)
    (etaleForm B S hS (f i) (hf i) (w i)) V t

/-- **The pairwise condition of a family of morphisms of the inverse images, read as naturality
of the readings of their étale forms on the charts of the members.** -/
theorem memberChartForm_naturality (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hw : IsPairwiseCompatible B S hS Yi f w) (i j : I) (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
    (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))) :
    memberChartForm B S hS Yi f hf w j V' (M.val.map k.op t) =
      N.val.map k.op (memberChartForm B S hS Yi f hf w i V t) :=
  ((memberChartForm_apply B S hS Yi f hf w j V' (M.val.map k.op t)).trans
      (etaleForm_naturality_memberPair B S hS Yi f hf hcomp w hw i j V V' k t)).trans
    (congrArg (fun z => N.val.map k.op z)
      (memberChartForm_apply B S hS Yi f hf w i V t).symm)

/-- The étale form of a member of a family of morphisms of the inverse images, read on sections
over a chart of that member: a linear map of the sections of the two restrictions of the modules
to the site of the charts of the members. -/
def memberFormApp {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    ((memberRestriction B S hS Yi f hf).obj M).val.obj p ⟶
      ((memberRestriction B S hS Yi f hf).obj N).val.obj p :=
  memberChartForm B S hS Yi f hf w p.unop.1 p.unop.2

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFormApp` on a section. -/
theorem memberFormApp_apply {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ)
    (z : ((memberRestriction B S hS Yi f hf).obj M).val.obj p) :
    memberFormApp B S hS Yi f hf w p z =
      memberChartForm B S hS Yi f hf w p.unop.1 p.unop.2 z :=
  rfl

/-- **The restriction of a morphism of `𝒪_X`-modules to the site of the charts of the members
is, at a pair of a member of the family and a chart of that member, its étale restriction to
that member read on sections over the chart.** -/
theorem memberRestriction_map_val_app {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) (i : I)
    (V : SmallEtale B S hS (Yi i).1) :
    ((memberRestriction B S hS Yi f hf).map φ).val.app
        (.op (memberPair B S hS Yi f hf i V)) =
      ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).map φ).val.app (.op V) :=
  rfl

/-! ### A pairwise compatible family as a morphism of the restrictions -/

/-- **The pairwise condition of a family of morphisms of the inverse images, read as the
commuting naturality square of the readings of their étale forms over two charts of two members
of the family.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartForm_naturality` as an equality of
morphisms of the modules of sections, which is the shape
`Stacks.DenseSubsiteModules.moduleRestrictionHom` consumes. -/
theorem memberChartForm_naturality_hom
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hnat : ∀ (i j : I) (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
        (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
          (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
        (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))),
      memberChartForm B S hS Yi f hf w j V' (M.val.map k.op t) =
        N.val.map k.op (memberChartForm B S hS Yi f hf w i V t))
    (i j : I) (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    M.val.map k.op ≫ (ModuleCat.restrictScalars
          (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.map k.op).hom).map
        (memberChartForm B S hS Yi f hf w j V') =
      memberChartForm B S hS Yi f hf w i V ≫ N.val.map k.op :=
  PresheafOfModules.naturality_of_apply M.val N.val k.op
    (memberChartForm B S hS Yi f hf w i V) (memberChartForm B S hS Yi f hf w j V')
    (hnat i j V V' k)

/-- **A pairwise compatible family of morphisms of the inverse images of two `𝒪_X`-modules, as a
morphism of the restrictions of those modules to the site of the charts of the members.**  The
readings of the étale forms of the members of the family are natural across the charts of the
members by `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartForm_naturality`, which is
the pairwise condition of Stacks 04W3. -/
def memberForm
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hnat : ∀ (i j : I) (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
        (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
          (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
        (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))),
      memberChartForm B S hS Yi f hf w j V' (M.val.map k.op t) =
        N.val.map k.op (memberChartForm B S hS Yi f hf w i V t)) :
    (memberRestriction B S hS Yi f hf).obj M ⟶ (memberRestriction B S hS Yi f hf).obj N :=
  Stacks.DenseSubsiteModules.moduleRestrictionHom (memberTopology B S hS Yi f hf)
    (SmallEtale.topology B S hS X.1) (memberFunctor B S hS Yi f hf)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) M N
    (memberFormApp B S hS Yi f hf w)
    fun p q g => memberChartForm_naturality_hom B S hS Yi f hf w hnat p.unop.1 q.unop.1
      p.unop.2 q.unop.2 ((memberFunctor B S hS Yi f hf).map g.unop)

/-- The morphism of the restrictions attached to a pairwise compatible family is, over a pair of
a member of the family and a chart of that member, the reading of the étale form of that
member. -/
theorem memberForm_val_app
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hnat : ∀ (i j : I) (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
        (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
          (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
        (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))),
      memberChartForm B S hS Yi f hf w j V' (M.val.map k.op t) =
        N.val.map k.op (memberChartForm B S hS Yi f hf w i V t))
    (p : (MemberSite B S hS Yi f hf)ᵒᵖ) :
    (memberForm B S hS Yi f hf w hnat).val.app p = memberFormApp B S hS Yi f hf w p :=
  rfl

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFormApp` at a pair of a member of the
family and a chart of that member is the reading of the étale form of that member over the
chart. -/
theorem memberFormApp_memberPair {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (i : I) (V : SmallEtale B S hS (Yi i).1) :
    memberFormApp B S hS Yi f hf w (.op (memberPair B S hS Yi f hf i V)) =
      memberChartForm B S hS Yi f hf w i V :=
  rfl

/-- **A morphism of `𝒪_X`-modules restricting to the morphism attached to a pairwise compatible
family has the members of that family as its étale forms.** -/
theorem etaleModulePullback_map_eq_etaleForm
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hnat : ∀ (i j : I) (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
        (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
          (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
        (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))),
      memberChartForm B S hS Yi f hf w j V' (M.val.map k.op t) =
        N.val.map k.op (memberChartForm B S hS Yi f hf w i V t))
    (φ : M ⟶ N)
    (hφ : (memberRestriction B S hS Yi f hf).map φ = memberForm B S hS Yi f hf w hnat)
    (i : I) :
    (etaleModulePullback.{u, u} B S hS (f i) (hf i)).map φ =
      etaleForm B S hS (f i) (hf i) (w i) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  obtain ⟨V⟩ := U
  exact (memberRestriction_map_val_app B S hS Yi f hf φ i V).symm.trans
    (((congrArg (fun θ => θ.val.app (.op (memberPair B S hS Yi f hf i V))) hφ).trans
        (memberForm_val_app B S hS Yi f hf w hnat
          (.op (memberPair B S hS Yi f hf i V)))).trans
      ((memberFormApp_memberPair B S hS Yi f hf w i V).trans
        (memberChartForm_eq B S hS Yi f hf w i V)))

/-- **Restriction of `𝒪_X`-modules to the site of the charts of the members is full**, by the
Comparison Lemma for sheaves of modules. -/
theorem full_memberRestriction : (memberRestriction B S hS Yi f hf).Full :=
  Stacks.DenseSubsiteModules.full_moduleRestriction (memberTopology B S hS Yi f hf)
    (SmallEtale.topology B S hS X.1) (memberFunctor B S hS Yi f hf)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

end CoverDense

/-! ### Fullness -/

include hf in
/-- **A pairwise compatible family of morphisms of the inverse images of two `𝒪_X`-modules along
an étale covering of `X` is the family of the inverse images of a morphism of those modules.**
This is the fullness half of Stacks 04W6, read on modules: the charts of the members of the
covering are cover dense in the small étale site of `X`, so the family, being natural across
those charts, is the restriction of a morphism of `𝒪_X`-modules by the Comparison Lemma. -/
theorem exists_modulePullback_map_eq_of_naturality
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hnat : ∀ (i j : I) (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
        (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
          (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
        (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj V))),
      memberChartForm B S hS Yi f hf w j V' (M.val.map k.op t) =
        N.val.map k.op (memberChartForm B S hS Yi f hf w i V t)) :
    ∃ φ : M ⟶ N, ∀ i, (modulePullback B S hS (f i)).map φ = w i := by
  have := isCoverDense_memberFunctor B S hS Yi f hf hcov
  have := full_memberRestriction B S hS Yi f hf
  obtain ⟨φ, hφ⟩ := (memberRestriction B S hS Yi f hf).map_surjective
    (memberForm B S hS Yi f hf w hnat)
  exact ⟨φ, fun i => map_eq_of_etaleForm_eq B S hS (f i) (hf i) φ (w i)
    (etaleModulePullback_map_eq_etaleForm B S hS Yi f hf w hnat φ hφ i)⟩

include hf in
/-- **A pairwise compatible family of morphisms of the inverse images of two `𝒪_X`-modules along
an étale covering of `X` is the family of the inverse images of a morphism of those modules.**
This is the fullness half of Stacks 04W6, read on modules: the pairwise condition of Stacks 04W3
is the naturality above, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartForm_naturality`, which is where the
compatibility of the comparison of Stacks 03LU with étale restriction is used. -/
theorem exists_modulePullback_map_eq (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hw : IsPairwiseCompatible B S hS Yi f w) :
    ∃ φ : M ⟶ N, ∀ i, (modulePullback B S hS (f i)).map φ = w i := by
  have := isCoverDense_memberFunctor B S hS Yi f hf hcov
  exact exists_modulePullback_map_eq_of_naturality B S hS Yi f hf hcov w
    fun i j V V' k t => memberChartForm_naturality B S hS Yi f hf hcomp w hw i j V V' k t

/-- The components of a morphism of two canonical descent data of an étale family satisfy the
pairwise condition of Stacks 04W3. -/
theorem isPairwiseCompatible_of_descentHom {M N : Modules.{u, u} B S hS X.1 X.2}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (θ : etaleCanonicalDescentDatum B S hS Yi f hf M hM ⟶
      etaleCanonicalDescentDatum B S hS Yi f hf N hN) :
    IsPairwiseCompatible B S hS Yi f fun i => θ.app i :=
  fun i j => θ.naturality i j

/-- **A morphism of the canonical descent data of an étale covering of `X` is induced by a
morphism of the two quasi-coherent `𝒪_X`-modules.** -/
theorem exists_modulePullback_map_eq_descentHom
    (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    {M N : Modules.{u, u} B S hS X.1 X.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite)
    (θ : etaleCanonicalDescentDatum B S hS Yi f hf M hM ⟶
      etaleCanonicalDescentDatum B S hS Yi f hf N hN) :
    ∃ φ : M ⟶ N, ∀ i, (modulePullback B S hS (f i)).map φ = θ.app i :=
  exists_modulePullback_map_eq B S hS Yi f hf hcomp hcov (fun i => θ.app i)
    (isPairwiseCompatible_of_descentHom B S hS Yi f hf hM hN θ)

/-- **The canonical descent functor of an étale covering of an algebraic space is full**, the
fullness half of Stacks 04W6. -/
theorem full_etaleCanonicalDescentFunctor_of_isEtaleCovering
    (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).Full where
  map_surjective {M N} θ := by
    obtain ⟨φ, hφ⟩ := exists_modulePullback_map_eq_descentHom B S hS Yi f hf hcomp hcov
      M.property N.property θ
    exact ⟨ObjectProperty.homMk φ, DescentDatum.Hom.ext fun i => hφ i⟩

/-- **The canonical descent functor of a Zariski covering of an algebraic space is full**, a
Zariski covering being an étale covering by Stacks 0DF1. -/
theorem full_etaleCanonicalDescentFunctor_of_isZariskiCovering
    (hcomp : ModulePullbackCompIsoEtaleRestriction B S hS)
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).Full :=
  full_etaleCanonicalDescentFunctor_of_isEtaleCovering B S hS Yi f hf
    (hcomp.toPair B S hS Yi f hf)
    (isEtaleCovering_of_isZariskiCovering B S hS X.2 (fun i => (Yi i).2) hcov)

/-- **The canonical descent functor of a Zariski covering of an algebraic space is fully
faithful.** Faithfulness is `faithful_etaleCanonicalDescentFunctor_of_isZariskiCovering` and
fullness is `full_etaleCanonicalDescentFunctor_of_isZariskiCovering`. -/
def fullyFaithfulEtaleCanonicalDescentFunctorOfIsZariskiCovering
    (hcomp : ModulePullbackCompIsoEtaleRestriction B S hS)
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).FullyFaithful :=
  haveI := faithful_etaleCanonicalDescentFunctor_of_isZariskiCovering B S hS Yi f hf hcov
  haveI := full_etaleCanonicalDescentFunctor_of_isZariskiCovering B S hS Yi f hf hcomp hcov
  .ofFullyFaithful _

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
