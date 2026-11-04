module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinition

/-!
# A quasi-compact formal scheme has a fundamental system of ideals of definition

**Stacks 0AJF** is the translation of Stacks 0AJE into the language of formal schemes à la EGA:

> Every quasi-compact and quasi-separated formal scheme has a fundamental system of ideals of
> definition.

The remark's argument has two halves. The first produces, by the induction principle for
quasi-compact quasi-separated formal schemes and the scheme-theoretic images of the pieces, a
fundamental system of **weak** ideals of definition; that half is the translation of Stacks 0AJE
itself and is not available in this library (see the implementation notes). The second half, which
the remark closes with by appealing to Remark 87.13.4, passes from a fundamental system of weak
ideals of definition to a fundamental system of genuine ideals of definition by shrinking the
system, and that half is proved here.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.exists_subfamily_isFundamentalSystemOfIdealsOfDefinitionOn`:
  on a quasi-compact locally topologically ringed space, a directed fundamental system of weak
  ideals of definition over a class of opens whose rings of sections are pre-admissible contains a
  subfamily which is a fundamental system of **ideals** of definition over a finite covering by
  opens of that class.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.exists_subfamily_isFundamentalSystemOfIdealsOfDefinitionOn_of_isFormalScheme`:
  **Stacks 0AJF**, the same conclusion on a quasi-compact formal scheme à la EGA, where the class
  of opens is the class of affine formal open subschemes and the two geometric inputs are
  discharged.

## Implementation notes

**What is assumed and why.** The fundamental system of weak ideals of definition is a hypothesis.
Producing it is exactly the content of Stacks 0AJE — a presentation of the formal space as a
directed colimit of algebraic spaces along thickenings — together with the dictionary of
Remark 87.13.3 turning such a presentation into a system of weak ideals of definition. Stacks
0AJE is carried by this library,
`AlgebraicGeometry.FormalSpace.exists_colimit_presentation_of_quasiCompact_quasiSeparated`, but
the dictionary of Stacks 0AIV is only present as its two definitions and their locality, not as
a bijection. So what is proved here is the remark's own last step, stated with the system it
consumes as an input, in the same style as the statements of Stacks 0AIW in
`StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinition`.

**Why only quasi-compactness appears.** The source's quasi-separatedness hypothesis is used
exclusively inside the first half, to make the overlaps of the induction quasi-compact so that the
two ideals of definition can be shrunk compatibly. Once a fundamental system of weak ideals of
definition is given, the passage to genuine ideals of definition needs only quasi-compactness of
the underlying space, which is why `CompactSpace` is the only finiteness hypothesis below.

**Why the conclusion is restricted to a finite covering.** The conclusion names a finite covering
by opens of the class and asserts the fundamental-system condition over that covering only. This is
the same restriction that
`AlgebraicGeometry.LocallyTopologicallyRingedSpace`
`.exists_isIdealOfDefinition_of_isFundamentalSystemOfWeakIdealsOfDefinitionOn` carries, and for
the same reason: transferring the ideal-of-definition condition from an affine
formal open to the smaller affine formal opens inside it is not available here, so the covering
produced by quasi-compactness cannot be enlarged to the class of all affine formal opens. A
consumer who has that transfer combines the conclusion with
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isIdealOfDefinitionOn_of_cover` and
`AlgebraicGeometry.LocallyTopologicallyRingedSpace`
`.isFundamentalSystemOfIdealsOfDefinitionOn_of_cover`.

**How the subfamily is chosen.** The subfamily is the set of members of the system lying
sectionwise below the single member `I₀` that
`exists_isIdealOfDefinition_of_isFundamentalSystemOfWeakIdealsOfDefinitionOn` produces. Every such
member is an ideal of definition over the covering, by that statement. That the subfamily is still
a neighbourhood basis of zero is where the directedness hypothesis is used a second time: a
neighbourhood of zero contains the ideal of sections of some member of the full system, and a
common lower bound of that member and `I₀` lies in the subfamily and has a smaller ideal of
sections. Each member of the subfamily has an ideal of sections which is a neighbourhood of zero
because the full system is a basis, so no openness argument is repeated.

## References

* [Stacks Project, Tag 0AJF](https://stacks.math.columbia.edu/tag/0AJF)
* [Stacks Project, Tag 0AJE](https://stacks.math.columbia.edu/tag/0AJE)
* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped Topology

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

universe u

/-- **A fundamental system of weak ideals of definition contains a fundamental system of ideals of
definition.** Let `X` be a quasi-compact locally topologically ringed space and let `𝒮` be a
nonempty, sectionwise directed fundamental system of weak ideals of definition over a class `𝒜` of
opens which cover `X` and over which the rings of sections are pre-admissible. Then there is a
finite covering `𝒰` of `X` by opens of `𝒜` and a subfamily `𝒮' ⊆ 𝒮` which is a fundamental system
of genuine ideals of definition over `𝒰`.

This is the step with which Stacks 0AJF concludes, by way of Remark 87.13.4: the subfamily is cut
out by a single member of `𝒮` below which every member is already an ideal of definition on `𝒰`,
and directedness keeps the subfamily cofinal, hence still a neighbourhood basis of zero. -/
theorem
    exists_subfamily_isFundamentalSystemOfIdealsOfDefinitionOn
    {X : LTRS.{u}} [CompactSpace ↥X] (𝒮 : Set (IdealSheaf X)) (𝒜 : Opens X → Prop)
    (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (hfund : IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 𝒜)
    (hbase : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ 𝒜 U)
    (hadm : ∀ U : Opens X, 𝒜 U →
      TopologicalRing.IsPreAdmissible (X.presheaf.obj (op U)).α) :
    ∃ 𝒰 : Set (Opens X), 𝒰.Finite ∧ (∀ V ∈ 𝒰, 𝒜 V) ∧ sSup 𝒰 = ⊤ ∧
      ∃ 𝒮' : Set (IdealSheaf X), 𝒮' ⊆ 𝒮 ∧ 𝒮'.Nonempty ∧
        IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮' (· ∈ 𝒰) := by
  obtain ⟨𝒰, h𝒰fin, h𝒰mem, h𝒰sup, I₀, hI₀, hI₀def⟩ :=
    exists_isIdealOfDefinition_of_isFundamentalSystemOfWeakIdealsOfDefinitionOn
      𝒮 𝒜 hne hdir hfund hbase hadm
  refine ⟨𝒰, h𝒰fin, h𝒰mem, h𝒰sup,
    {I | I ∈ 𝒮 ∧ ∀ W : Opens X, I.ideal W ≤ I₀.ideal W}, fun _ hI => hI.1,
    ⟨I₀, hI₀, fun _ => le_rfl⟩, fun I hI => ?_, fun V hV => ?_⟩
  · exact fun V hV => hI₀def I hI.1 hI.2 V hV
  · refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
    · obtain ⟨I, hI, hIt⟩ := (hfund.2 V (h𝒰mem V hV)).mem_iff.mp ht
      obtain ⟨K, hK, hKle⟩ := hdir I hI I₀ hI₀
      exact ⟨K, ⟨hK, fun W => (hKle W).2⟩,
        fun _ hx => hIt (SetLike.coe_subset_coe.mpr (hKle V).1 hx)⟩
    · rintro ⟨I, hI, hIt⟩
      exact Filter.mem_of_superset ((hfund.2 V (h𝒰mem V hV)).mem_of_mem hI.1) hIt

/-- **Stacks 0AJF.** A quasi-compact formal scheme à la EGA carrying a fundamental system of weak
ideals of definition carries a fundamental system of genuine ideals of definition, over a finite
covering by affine formal open subschemes.

This is the remark's conclusion. Its hypothesis — the fundamental system of weak ideals of
definition — is what the translation of Stacks 0AJE supplies, and that *translation* is not
carried by this library, although Stacks 0AJE itself is; see the implementation notes of this
file. Here the class of opens is the class of
affine formal open subschemes, so the two geometric inputs of
`exists_subfamily_isFundamentalSystemOfIdealsOfDefinitionOn`
are discharged: the affine formal opens cover `X` because `X` is a formal scheme, and the ring of
sections over one of them is pre-admissible by Stacks 0AHY. -/
@[stacks 0AJF "the shrinking of a fundamental system of WEAK ideals of definition to one of \
ideals of definition; the weak system is a hypothesis, see the implementation notes"]
public theorem exists_subfamily_isFundamentalSystemOfIdealsOfDefinitionOn_of_isFormalScheme
    {X : LTRS.{u}} [CompactSpace ↥X] (hX : IsFormalScheme X) (𝒮 : Set (IdealSheaf X))
    (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (hfund : IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X)) :
    ∃ 𝒰 : Set (Opens X), 𝒰.Finite ∧ (∀ V ∈ 𝒰, IsAffineFormalOpen X V) ∧ sSup 𝒰 = ⊤ ∧
      ∃ 𝒮' : Set (IdealSheaf X), 𝒮' ⊆ 𝒮 ∧ 𝒮'.Nonempty ∧
        IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮' (· ∈ 𝒰) :=
  exists_subfamily_isFundamentalSystemOfIdealsOfDefinitionOn
    𝒮 _ hne hdir hfund ((isFormalScheme_iff_forall_isAffineFormalOpen X).mp hX)
    fun _ hU => isPreAdmissible_of_isAffineFormalOpen hU

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end
