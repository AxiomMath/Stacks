module

public import Mathlib.CategoryTheory.Limits.IsConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Local finite presentation over the base and limit preservation of the functor of points

An algebraic space `X` over a scheme `S` is locally of finite presentation over `S` exactly
when `X`, read as a functor on the big fppf site of `S`, is limit preserving: it turns every
cofiltered inverse limit of affine objects of the site into a filtered colimit of sets. It
already suffices that the comparison maps `colim X(T i) ⟶ X(T)` be surjective.

This is the case of Stacks 04AK and of Stacks 0CM6 in which the target is the terminal
presheaf. The terminal presheaf is the Yoneda presheaf of the terminal object of the site,
whose underlying scheme is `S` by `AlgebraicGeometry.Space.toSchemeTerminalIso`, so a
morphism to it is the structure morphism to the base.

## Main definitions

* `AlgebraicGeometry.Space.sectionFiberTerminalIso`: the presheaf of lifts of a section of
  the terminal presheaf over an object `A` of the site is the restriction of the source
  presheaf to the slice over `A`.

## Main results

* `AlgebraicGeometry.Space.relativelyLimitPreserving_terminal_iff_limitPreserving`: the
  structure morphism of a presheaf to the terminal presheaf is relatively limit preserving
  exactly when the presheaf itself is limit preserving.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_terminal_of_affineLimit_surjective`:
  surjectivity of the comparison maps already implies local finite presentation.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving` is
  **Stacks 05N0**.

## Implementation notes

*What "limit preserving" and "locally of finite presentation" mean here.* Both are the
notions already fixed by this repository and no new one is introduced.
`AlgebraicGeometry.LimitPreserving` is Tag 049J, part (1): a presheaf sends each cofiltered
inverse system of affine objects of the site whose underlying cone of schemes is a limit, and
whose limit is again affine, to a filtered colimit of sets. The relative notion
`AlgebraicGeometry.RelativelyLimitPreserving` is Tag 049J, part (2), asking part (1) of the
presheaf `AlgebraicGeometry.sectionFiber` of lifts of each section of the target.
`AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` is Tag 03XP, part (1): every
commuting square of étale scheme charts induces a scheme morphism which is locally of finite
presentation. The functor of points is the presheaf itself; `X` is a presheaf on the big fppf
site of `S` throughout, and its structure morphism to the base is
`CategoryTheory.Limits.terminal.from X`.

*Relation to the scheme-level statement.* For a scheme the same equivalence is
`AlgebraicGeometry.Scheme.locallyOfFinitePresentation_iff_isLimitPreserving_yoneda`, tagged
05LX, and the statement below is its shape one level up. The two limit-preservation notions
are not the same predicate and cannot be: that one,
`AlgebraicGeometry.Scheme.IsLimitPreserving`, is about functors on the slice `Over S` of all
schemes over `S` and asks for Mathlib's `CategoryTheory.Limits.PreservesColimit`, whereas
`AlgebraicGeometry.LimitPreserving` is about presheaves on the size-bounded big fppf site and
asks for the comparison cocone over a *given* limit cone of the site with affine limit point.
The space-level notion is the one Stacks 04AK and Stacks 0CM6 are stated with in this
repository, so it is the one used here; no third notion is introduced.

*The two halves and where they come from.* The implication from local finite presentation is
Stacks 04AK in the form proved here,
`AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation`, followed by
the bridge below. The converse does *not* go through the converse of Stacks 04AK: it goes
through Stacks 0CM6 in the form proved here,
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`, whose
hypothesis is implied by the weaker surjectivity assumption. That is why the surjective
criterion below is proved first and the converse read off from it, matching the order in
which the source states them. The converse of Stacks 04AK is itself available, as
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving`, and is
routed through that same criterion of Stacks 0CM6; appealing to the criterion directly is what
makes the collapse of the fibre product visible.

*The fibre product in the hypothesis of Stacks 0CM6 collapses.* That hypothesis asks for a
section of the source over the limit and a section of the target at a finite stage agreeing
over the limit to have a common antecedent in the colimit of the sections of the source.
When the target is the terminal presheaf, every value of the target has exactly one element
and the colimit of its sections along the system is a singleton, because a filtered colimit
of singletons over a connected index category is one; so only the first component of the
antecedent carries information.

*Index universes.* The hypotheses and conclusions are at index categories `I : Type u` with
`Category.{u} I`, where `u` is the universe of the schemes. This is the size fixed by both
inputs: Stacks 04AK is stated at `AlgebraicGeometry.RelativelyLimitPreserving.{u, u, u, u}`,
inherited from Mathlib's inverse-limit API for schemes with affine transition morphisms, and
the hypothesis of Stacks 0CM6 is stated at the same size. The two restrictions pull in
opposite directions for an equivalence — a smaller index size weakens the conclusion of the
forward implication and strengthens the converse — so neither direction can be moved to a
free index universe while the inputs stay where they are. The bridge
`AlgebraicGeometry.Space.relativelyLimitPreserving_terminal_iff_limitPreserving` is
nevertheless stated at free index universes, since it needs nothing about finite
presentation.

*Where the tag goes, and why only on the equivalence.* Stacks 05N0 says two things: the
equivalence, and that by Stacks 0CM6 surjectivity of the comparison maps already suffices.
Only the first is an assertion of 05N0's own. The second is a forward reference, and the
lemma it points at is proved in this repository in full, with a bare `@[stacks 0CM6]` on
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`; the
surjective criterion below is that lemma read for the structure morphism, so the claim it
makes is already covered and it carries no attribute of its own. The equivalence is
therefore the whole of 05N0 and carries the tag bare.

*What is distinct from Stacks 04AK.* Stacks 04AK is proved in full, on
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_iff_relativelyLimitPreserving`, with
its implication (1) ⇒ (2) suffixed separately on
`AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation` and its
converse on
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving`; the
proof of the converse along the source's own route in
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable` carries no attribute
because it rests on an undischarged scheme-level hypothesis. The equivalence below is
nevertheless a different statement: it is the absolute one — about an algebraic space over its
base rather than about an arbitrary morphism — and it reads the limit-preservation side as
Stacks 05N0 does, as a condition on the functor of points rather than relatively, which is
what 05N0 is a remark about. Its converse is unconditional because it is routed through
Stacks 0CM6 directly.

*Two facts about the terminal presheaf that are not restated.* That it is an algebraic space
over `S` is `AlgebraicGeometry.Space.isAlgebraicSpace_terminal`, which this repository keeps
in `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed`, where it was first
needed; importing that module here would drag its whole closure into a file about finite
presentation, so the two-line term is written out at the point of use instead, exactly as
`StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections` and
`StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuotient` already do, and no
second lemma of that name is declared. That every value of the terminal presheaf is a
singleton is also already in the repository, as
`Stacks.Sites.Localization.terminalPresheaf_subsingleton`, but it is stated under size
hypotheses on the site which the big fppf site does not satisfy — its object type is one
universe above its morphisms — so it does not apply and the step is repeated here as a
private definition rather than a second public copy.

## References

* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w w'

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] IsFiltered.isConnected

/-- Every value of the terminal presheaf on the big fppf site of `S` has exactly one element:
evaluation at an object preserves the terminal object. -/
@[instance_reducible]
private noncomputable def uniqueTerminalObj (A : (BigFppfOver B S hS)ᵒᵖ) :
    Unique ((⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).obj A) :=
  Types.isTerminalEquivUnique _
    (terminalIsTerminal.isTerminalObj ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj A) _)

/-- The presheaf of lifts through the structure morphism `F ⟶ ⊤` of a section of the terminal
presheaf over an object `A` of the site is the restriction of `F` to the slice over `A`: the
lifting condition is vacuous, since every value of the terminal presheaf is a singleton. -/
noncomputable def sectionFiberTerminalIso
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : BigFppfOver B S hS)
    (y : (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).obj (op A)) :
    sectionFiber B S hS (terminal.from F) A y ≅ (Over.forget A).op ⋙ F :=
  NatIso.ofComponents (fun Y => (Equiv.ofBijective (fun x => x.1) (by
    refine ⟨fun x₁ x₂ h => Subtype.ext h, fun x => ⟨⟨x, ?_⟩, rfl⟩⟩
    let _ := uniqueTerminalObj B S hS (op (unop Y).left)
    exact Subsingleton.elim _ _)).toIso) (by intro Y Z f; ext x; rfl)

/-- The structure morphism of a presheaf on the big fppf site of `S` to the terminal presheaf
is relatively limit preserving exactly when the presheaf itself is limit preserving.

Over the terminal object of the site the presheaf of lifts is the presheaf itself, read on the
slice over that object, which is the whole site; over an arbitrary object `A` it is the
restriction of the presheaf to the slice over `A`, and an inverse system in that slice is an
inverse system of the site with a compatible map to `A`. -/
theorem relativelyLimitPreserving_terminal_iff_limitPreserving
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    RelativelyLimitPreserving.{u, u, w, w'} B S hS (terminal.from F) ↔
      LimitPreserving.{u, u, w, w', u + 1, u} (BigFppfOver.toScheme B S hS) F := by
  constructor
  · intro hRel
    exact limitPreserving_whiskerEquivalence
      (Over.equivalenceOfIsTerminal
        (terminalIsTerminal (C := BigFppfOver B S hS))).symm rfl _
      (limitPreserving_of_natIso
        (sectionFiberTerminalIso B S hS (F := F) (⊤_ (BigFppfOver B S hS)) _)
        (hRel (⊤_ (BigFppfOver B S hS))
          (uniqueTerminalObj B S hS (op (⊤_ (BigFppfOver B S hS)))).default))
  · intro hF A y
    refine limitPreserving_of_natIso (sectionFiberTerminalIso B S hS (F := F) A y).symm ?_
    intro I instCat instCof D c hc hAffine hAffineLimit
    obtain ⟨hcol⟩ := hF I (D ⋙ Over.forget A) ((Over.forget A).mapCone c)
      (IsLimit.ofIsoLimit hc (Functor.mapConeMapCone c).symm) hAffine hAffineLimit
    exact ⟨hcol.ofIsoColimit
      (Functor.mapCoconeMapCocone (H := (Over.forget A).op) (H' := F) c.op)⟩

/-- The terminal presheaf on the big fppf site of `S` is an algebraic space. -/
private theorem isAlgebraicSpace_terminal_aux :
    IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  isAlgebraicSpace_of_iso B S hS (yonedaTerminalIso B S hS)
    (isAlgebraicSpace_yoneda B S hS (⊤_ (BigFppfOver B S hS)))

/-- An algebraic space `X` over `S` is locally of finite presentation over `S` as soon as, for
every cofiltered inverse limit `T = lim T i` of affine objects of the big fppf site of `S`,
the comparison map `colim X(T i) ⟶ X(T)` is surjective.

This is **Stacks 0CM6**, in the form
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`, read for
the structure morphism of `X`; it is the sharpening that the last sentence of Stacks 05N0
forward-references. The fibre product appearing in the hypothesis of Stacks 0CM6 collapses,
because the sections of the terminal presheaf along the system form a singleton: the colimit
is a filtered colimit of singletons over a connected index category.

This statement carries no `@[stacks]` attribute. Its content is Stacks 0CM6, whose tag is
already borne in full by the lemma it specialises, and Stacks 05N0 only points at that
lemma rather than asserting the specialisation itself. -/
theorem isLocallyOfFinitePresentation_terminal_of_affineLimit_surjective
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsurj : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ BigFppfOver B S hS) (c : Cone D),
      IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
      ∀ x : X.obj (op c.pt), ∃ z : colimit (D.op ⋙ X),
        colimit.desc (D.op ⋙ X) (X.mapCocone c.op) z = x) :
    IsLocallyOfFinitePresentation B S hS (terminal.from X) := by
  refine isLocallyOfFinitePresentation_of_affineLimit_surjective B S hS hX
    (isAlgebraicSpace_terminal_aux B S hS) (terminal.from X) ?_
  intro I instCat instCof D c hc hAffine hAffineLimit x y _
  obtain ⟨z, hz⟩ := hsurj I D c hc hAffine hAffineLimit x
  refine ⟨z, hz, ?_⟩
  have e : D.op ⋙ (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ≅ Types.constPUnitFunctor Iᵒᵖ :=
    NatIso.ofComponents
      (fun i => Equiv.toIso
        (@Equiv.ofUnique _ PUnit.{u + 1} (uniqueTerminalObj B S hS (D.op.obj i)) _))
      (fun _ => by ext _; exact @Subsingleton.elim PUnit.{u + 1} _ _ _)
  exact @Subsingleton.elim _ (Equiv.subsingleton (HasColimit.isoOfNatIso e).toEquiv) _ _

/-- The functor of points of an algebraic space `X` over `S` which is locally of finite
presentation over `S` is limit preserving.

This is the implication from local finite presentation of Stacks 04AK for the structure
morphism of `X`, followed by
`AlgebraicGeometry.Space.relativelyLimitPreserving_terminal_iff_limitPreserving`. -/
theorem limitPreserving_of_isLocallyOfFinitePresentation
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : IsLocallyOfFinitePresentation B S hS (terminal.from X)) :
    LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X :=
  (relativelyLimitPreserving_terminal_iff_limitPreserving.{u, u, u} B S hS X).mp
    (relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hX
      (isAlgebraicSpace_terminal_aux B S hS) h)

/-- An algebraic space `X` over `S` whose functor of points is limit preserving is locally of
finite presentation over `S`.

A filtered colimit of sets is the union of the images of its legs, so the surjectivity
hypothesis of
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_terminal_of_affineLimit_surjective`
follows from limit preservation. The converse of Stacks 04AK is *not* used. -/
theorem isLocallyOfFinitePresentation_of_limitPreserving
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X) :
    IsLocallyOfFinitePresentation B S hS (terminal.from X) := by
  refine isLocallyOfFinitePresentation_terminal_of_affineLimit_surjective B S hS hX ?_
  intro I instCat instCof D c hc hAffine hAffineLimit x
  obtain ⟨hcol⟩ := h I D c hc hAffine hAffineLimit
  obtain ⟨j, v, hv⟩ := Types.jointly_surjective_of_isColimit hcol x
  refine ⟨colimit.ι (D.op ⋙ X) j v, ?_⟩
  rw [← comp_apply, colimit.ι_desc]
  exact hv

/-- **Stacks 05N0.** An algebraic space `X` over a scheme `S` is locally of finite
presentation over `S` if and only if `X`, read as a functor on the big fppf site of `S`, is
limit preserving.

This is the case of Stacks 04AK in which the target is the terminal presheaf, so that the
morphism is the structure morphism of `X` to `S`. Only the implication (1) ⇒ (2) of Stacks
04AK is used; the converse is obtained from Stacks 0CM6 instead, so no undischarged
hypothesis enters. Compare Stacks 05LX,
`AlgebraicGeometry.Scheme.locallyOfFinitePresentation_iff_isLimitPreserving_yoneda`, which is
this statement for a scheme. -/
@[stacks 05N0]
theorem isLocallyOfFinitePresentation_terminal_iff_limitPreserving
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) :
    IsLocallyOfFinitePresentation B S hS (terminal.from X) ↔
      LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X :=
  ⟨limitPreserving_of_isLocallyOfFinitePresentation B S hS hX,
    isLocallyOfFinitePresentation_of_limitPreserving B S hS hX⟩

end AlgebraicGeometry.Space

end
