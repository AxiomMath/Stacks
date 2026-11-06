module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Comma
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximationFromPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Relative approximation for morphisms of algebraic spaces

A morphism `f : X ⟶ Y` of quasi-compact and quasi-separated algebraic spaces over `Spec ℤ` is
the inverse limit of a directed inverse system of *morphisms* `f_i : X_i ⟶ Y_i` in which both
families of transition morphisms are affine and every `X_i` and every `Y_i` is quasi-separated
and of finite type over `Spec ℤ`. This is Stacks 0GS3, proved as
`AlgebraicGeometry.Space.hasRelativeApproximation_of_isQuasiCompactSpace`; the system is produced
by aligning an approximation of `X` with an approximation of `Y`, and this file builds that
alignment.

## Main definitions

* `AlgebraicGeometry.Space.RelativeApproximation` is the conclusion of the proposition as data:
  a directed set, an inverse system of *arrows* of algebraic spaces over it whose transition
  morphisms are affine on the source side and on the target side, whose sources and targets are
  all quasi-separated and of finite type over `Spec ℤ`, and a limiting cone whose vertex is the
  given morphism.
* `AlgebraicGeometry.Space.HasRelativeApproximation` is the corresponding proposition,
  `Nonempty` of the above.
* `AlgebraicGeometry.Space.HasSmallNoetherianApproximation` is the conclusion of Stacks 07SU
  with the size of the index set retained: a `AlgebraicGeometry.Space.NoetherianApproximation`
  whose index set is small for the site.
* `AlgebraicGeometry.Space.CLOConstructionOutput` is the hypothesis
  `AlgebraicGeometry.Space.hasSmallNoetherianApproximation_of_cloConstructionOutput` carries,
  verbatim the hypothesis the library's Stacks 07SU carries. See the implementation notes.

## Main results

* `AlgebraicGeometry.Space.hasSmallNoetherianApproximation_of_cloConstructionOutput`: Stacks
  07SU with the size of the index set retained.

## Implementation notes

*The index set of the relative system.* An index is a triple consisting of a stage `a` of the
approximation of `X`, a stage `b` of the approximation of `Y`, and a morphism `X_a ⟶ Y_b`
compatible with `f` and the two projections; one triple refines another when both of its stages
are later and the two morphisms agree over the transition morphisms. Such a triple exists over
every stage `b`, and any two triples are refined by a third, so the triples form a nonempty
directed set; this is where the whole content of the proposition lies. Because a morphism of
presheaves on the big fppf site of `S` lives one universe above the values of the presheaves,
the index set of the relative system lies in `Type (u + 1)` while the index sets of the two
approximations lie in `Type u`.

*Why the two approximations can be aligned.* The existence of the triple over a stage `b`, and
the refinement of two triples by a third, are the two halves of Stacks 0CP4: the structure
morphism `Y_b ⟶ Spec ℤ` is locally of finite presentation, being locally of finite type over
the Noetherian base `Spec ℤ`, so a morphism `X ⟶ Y_b` out of the limit is already defined over
a stage `X_a`, and two morphisms `X_a ⟶ Y_b` which agree over `X` agree after one transition
morphism. These are
`AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving` and
`AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving`.

*The limit.* The projections from the set of triples to the two index sets are initial, so a
limiting cone for either approximation stays limiting after restriction along them; the arrow
category is a comma category of two identity functors, and limits in it are detected by the two
projections to the ambient category, so the restricted cones assemble to a limiting cone with
vertex `f`.

*The hypothesis carried.* Absolute Noetherian approximation for algebraic spaces, Stacks 07SU,
is available in this development only granted the output of the Conrad–Lieblich–Olsson
construction, which is the hypothesis `hCLO` of
`AlgebraicGeometry.Space.hasNoetherianApproximation_of_isomorphicPresentation_limit`; the
construction itself — the stratification of Stacks 07ST, absolute Noetherian approximation for
schemes, and the stagewise approximation of the étale equivalence relations — is not proved
there. That same hypothesis, named `AlgebraicGeometry.Space.CLOConstructionOutput`, is what
`AlgebraicGeometry.Space.hasSmallNoetherianApproximation_of_cloConstructionOutput` carries, and
nothing further is assumed. It is quantified over its own algebraic space, so one instance of it
serves both `X` and `Y`.

*Why the approximation is rebuilt from the construction's output rather than taken from the
library's Stacks 07SU.* Both halves of Stacks 0CP4 used above require the index set of the system
to be small for the site, below the cofinality of `AlgebraicGeometry.BigFppfSite.cutoff`; that
bound is an antecedent of `AlgebraicGeometry.Space.QcqsLimitSquare` and traces back to Stacks
07SF, by which a limit of such a system is recognized as an algebraic space at all. The
construction's output supplies the bound, but
`AlgebraicGeometry.Space.HasNoetherianApproximation`, the conclusion of the library's Stacks 07SU,
does not record it. Since
`AlgebraicGeometry.Space.NoetherianApproximation.ofIso` leaves the index set alone, the bound
survives the passage from the system's limit to the given space, and
`AlgebraicGeometry.Space.hasSmallNoetherianApproximation_of_cloConstructionOutput` records the
conclusion of Stacks 07SU with the bound retained.

*Finite type over `Spec ℤ`.* As in `AlgebraicGeometry.Space.NoetherianApproximation`, a stage is
viewed over the terminal scheme with `AlgebraicGeometry.Space.viewOverIntegers` and the
condition is `AlgebraicGeometry.Space.IsFiniteType` of the resulting structure morphism. Over
the terminal base that view is isomorphic to the identity, since the structure morphism of the
terminal scheme is its own identity; the isomorphism is what turns the finite-type condition on
a stage into local finite presentation of its structure morphism and into quasi-compactness of
the stage itself.

## References

* [Stacks Project, Tag 0GS3](https://stacks.math.columbia.edu/tag/0GS3)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 002R](https://stacks.math.columbia.edu/tag/002R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Relocalization along the identity -/

/-- Restriction of presheaves along the identity of the base is the identity functor: the
functor `CategoryTheory.Over.map` of an identity is isomorphic to the identity. -/
private noncomputable def relocalizeRestrictIdIso {C : Type (u + 1)} [Category.{u} C] (U : C) :
    OverShriek.relocalizeRestrict (𝟙 U) ≅ 𝟭 ((Over U)ᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ (Over U)ᵒᵖ (Type u)).mapIso
    (NatIso.op (Over.mapId U)).symm

/-- Relocalization along the identity of the base is the identity functor: it is left adjoint
to restriction along the identity, which is the identity functor, and a left adjoint of the
identity functor is the identity functor. -/
private noncomputable def relocalizeIdIso {C : Type (u + 1)} [Category.{u} C] (U : C) :
    OverShriek.relocalizePresheafFunctor (𝟙 U) ≅ 𝟭 ((Over U)ᵒᵖ ⥤ Type u) :=
  Adjunction.leftAdjointUniq (OverShriek.relocalizeAdjunction (𝟙 U))
    (Adjunction.id.ofNatIsoRight (relocalizeRestrictIdIso U).symm)

section Terminal

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The structure morphism of the terminal scheme is its identity. -/
private theorem integersMap_terminal_eq_id :
    integersMap B (⊤_ Scheme.{u}) hZ hZ = 𝟙 (B.obj hZ) := by
  ext
  exact terminal.hom_ext _ _

/-- **The view over `Spec ℤ` of a presheaf already over `Spec ℤ` is that presheaf.** The view is
relocalization along the structure morphism of the base, which over the terminal scheme is the
identity. -/
private noncomputable def viewOverIntegersTerminalIso
    (F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :
    viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F ≅ F :=
  eqToIso (congrArg (fun m => (OverShriek.relocalizePresheafFunctor m).obj F)
      (integersMap_terminal_eq_id B hZ)) ≪≫ (relocalizeIdIso (B.obj hZ)).app F

/-! ### The terminal presheaf over `Spec ℤ` -/

/-- The presheaf represented by the identity of the base is terminal: the identity is a terminal
object of the slice category, and the Yoneda embedding preserves terminal objects. -/
private noncomputable def terminalObjIso (S : Scheme.{u}) (hS : B.Contains S) :
    yoneda.obj (Over.mk (𝟙 (B.obj hS))) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal

/-- The terminal scheme is affine: it is isomorphic to the spectrum of the integers. -/
private theorem isAffine_terminalScheme : IsAffine (⊤_ Scheme.{u}) :=
  IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv

/-- The terminal scheme is locally Noetherian: the integers form a Noetherian ring. -/
private theorem isLocallyNoetherian_terminalScheme : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
  have e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).symm
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian e.hom

/-- The terminal presheaf on the big fppf site of `Spec ℤ` is a quasi-compact algebraic space:
it is represented by the identity of the base, whose underlying scheme is affine. -/
private theorem isQuasiCompactSpace_terminalPresheaf :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ
      (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) :=
  isQuasiCompactSpace_of_iso B _ hZ (terminalObjIso B (⊤_ Scheme.{u}) hZ)
    (isQuasiCompactSpace_yoneda_of_isAffine B _ hZ (Over.mk (𝟙 (B.obj hZ)))
      isAffine_terminalScheme)

/-- An isomorphism of presheaves on the big fppf site has every relative morphism property
pulled back from a property of schemes which contains the identities and respects
isomorphisms. -/
private theorem presheaf_inverseImage_of_isIso (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] [P.RespectsIso]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e] :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf e :=
  presheaf_of_isIso B S hS (MorphismProperty.RespectsIso.inverseImage _ _)
    (fun U => by
      simpa using MorphismProperty.id_mem P ((BigFppfOver.toScheme B S hS).obj U)) e

/-- The terminal presheaf on the big fppf site of `Spec ℤ` is locally Noetherian in the
étale-local sense of Stacks 03E6: it is represented by the identity of the base, whose
underlying scheme is the terminal scheme. -/
private theorem hasEtaleLocalProperty_isLocallyNoetherian_terminalPresheaf :
    HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ
      (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  have _ : MorphismProperty.ContainsIdentities
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have _ : MorphismProperty.RespectsIso
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.ContainsIdentities
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have _ : MorphismProperty.RespectsIso
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨Over.mk (𝟙 (B.obj hZ)), (terminalObjIso B (⊤_ Scheme.{u}) hZ).hom,
    presheaf_inverseImage_of_isIso B (⊤_ Scheme.{u}) hZ _ _,
    presheaf_inverseImage_of_isIso B (⊤_ Scheme.{u}) hZ _ _,
    isLocallyNoetherian_terminalScheme⟩

/-! ### Consequences of finite type over `Spec ℤ` -/

variable {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}

/-- An algebraic space of finite type over `Spec ℤ` is quasi-compact: the structure morphism is
quasi-compact, and the base change of it along the identity of the terminal presheaf, which is
quasi-compact, is the space itself. -/
private theorem isQuasiCompactSpace_of_isFiniteTypeOverIntegers
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ F := by
  have hpb := h.2 (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ)
    (isQuasiCompactSpace_terminalPresheaf B hZ) (𝟙 _)
  exact isQuasiCompactSpace_of_iso B _ hZ (viewOverIntegersTerminalIso B hZ F)
    (isQuasiCompactSpace_of_iso B _ hZ (asIso (pullback.snd (𝟙 _) _)) hpb)

/-- The structure morphism of an algebraic space of finite type over `Spec ℤ` is locally of
finite presentation: it is locally of finite type, and the terminal presheaf over `Spec ℤ` is
locally Noetherian, so Stacks 06G4 applies. -/
private theorem isLocallyOfFinitePresentation_terminal_of_isFiniteTypeOverIntegers
    (hF : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ F)
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ (terminal.from F) :=
  isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ hF
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) (terminal.from F)
    (hasEtaleLocalProperty_isLocallyNoetherian_terminalPresheaf B hZ)
    ((isLocallyOfFiniteType_terminal_iff_of_iso B _ hZ
      (viewOverIntegersTerminalIso B hZ F)).mp h.1)

end Terminal

/-! ### The hypothesis of absolute Noetherian approximation -/

/-- **The conclusion of Stacks 07SU, in the form its consumers need.** A presheaf on the big
fppf site of `S` *has a small Noetherian approximation* when it has a
`AlgebraicGeometry.Space.NoetherianApproximation` whose index set is below the cofinality of the
size cutoff of the site.

Stacks 07SU asserts that every quasi-compact quasi-separated algebraic space over `Spec ℤ` has
one; the system it produces is indexed by a set of that size, which is the size the descent
results for such systems are stated for. That assertion is not proved in this development, and
a client carries this proposition as a hypothesis. -/
abbrev HasSmallNoetherianApproximation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ A : NoetherianApproximation B S hS hZ X, #A.I < B.cutoff.ord.cof

/-- **The output of the Conrad–Lieblich–Olsson construction.** For every quasi-compact,
quasi-separated algebraic space `Z` over `S`: a directed index set small for the site, an
inverse system over it of algebraic spaces with affine transition morphisms whose stages are
quasi-separated and of finite type over `Spec ℤ`, and an object `U` of the site carrying a
surjective étale atlas of `Z` and one of the system's limit whose kernel pairs are isomorphic
as relations on `U`.

This is verbatim the hypothesis `hCLO` of
`AlgebraicGeometry.Space.hasNoetherianApproximation_of_isomorphicPresentation_limit`, the library's
form of Stacks 07SU: the construction itself — the stratification of Stacks 07ST, absolute
Noetherian approximation for schemes, and the stagewise approximation of the étale equivalence
relations — is not proved in this development, so Stacks 07SU is available only granted this.
Naming the hypothesis lets results be stated against literally the same assumption. It is
quantified over its own algebraic space, so a
single instance of it serves both the source and the target of a morphism. -/
abbrev CLOConstructionOutput (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) : Prop :=
  ∀ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Z →
    IsQuasiCompactSpace B S hS Z → IsAbsolutelyQuasiSeparated B S hS hZ Z →
      ∃ (I : Type u) (inst : Preorder I),
        let _ := inst
        ∃ (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
          (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
          #I < B.cutoff.ord.cof ∧
          (∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) ∧
          (∀ j, IsAlgebraicSpace B S hS (D.obj j)) ∧
          (∀ {j j' : Iᵒᵖ} (g : j ⟶ j'), IsAffineHom B S hS (D.map g)) ∧
          (∀ j, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj j)) ∧
          (∀ j, IsFiniteType B (⊤_ Scheme.{u}) hZ
            (terminal.from (viewOverIntegers B S hS hZ (D.obj j)))) ∧
          ∃ (R R' U : BigFppfOver B S hS) (s t : R ⟶ U) (s' t' : R' ⟶ U)
            (a : yoneda.obj U ⟶ Z) (a' : yoneda.obj U ⟶ limit D) (e : R ≅ R'),
            IsPullback (yoneda.map s) (yoneda.map t) a a ∧
            IsPullback (yoneda.map s') (yoneda.map t') a' a' ∧
            e.hom ≫ s' = s ∧ e.hom ≫ t' = t ∧
            (MorphismProperty.presheaf (MorphismProperty.inverseImage
              (@Surjective.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS))) a ∧
            (MorphismProperty.presheaf (MorphismProperty.inverseImage
              (@Etale.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS))) a ∧
            (MorphismProperty.presheaf (MorphismProperty.inverseImage
              (@Surjective.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS))) a' ∧
            (MorphismProperty.presheaf (MorphismProperty.inverseImage
              (@Etale.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS))) a'

/-- The opposite of a small index set is small: the two are in bijection. -/
private theorem mk_op_lt (B : BigFppfSite.{u}) {I : Type u} (h : #I < B.cutoff.ord.cof) :
    #Iᵒᵖ < B.cutoff.ord.cof := by
  rw [Cardinal.mk_congr (show Iᵒᵖ ≃ I from ⟨unop, op, fun _ => rfl, fun _ => rfl⟩)]
  exact h

/-- The morphism types of the opposite of a preorder are subsingletons, hence small for the
site. -/
private theorem mk_hom_op_lt (B : BigFppfSite.{u}) {I : Type u} [Preorder I] (a b : Iᵒᵖ) :
    #(a ⟶ b) < B.cutoff.ord.cof :=
  (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

/-- **Stacks 07SU with the index set's size retained.** A quasi-compact quasi-separated
algebraic space over `S` has a small Noetherian approximation, granted the output of the
Conrad–Lieblich–Olsson construction.

The construction supplies the two cardinality conditions on the index set that make the limit
of its system an algebraic space, by Stacks 07SF; the limit is then its own Noetherian
approximation over the very same index set, and the given space is isomorphic to it by Stacks
0262, which `AlgebraicGeometry.Space.NoetherianApproximation.ofIso` transports without changing
the index set. The smallness of that index set is therefore still available at the end, which is
what the descent results of Stacks 0CP4 need and what
`AlgebraicGeometry.Space.HasNoetherianApproximation`, the conclusion of the library's Stacks 07SU,
does not record. -/
theorem hasSmallNoetherianApproximation_of_cloConstructionOutput
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} (hCLO : CLOConstructionOutput B S hS hZ)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZalg : IsAlgebraicSpace B S hS Z)
    (hqc : IsQuasiCompactSpace B S hS Z)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Z) :
    HasSmallNoetherianApproximation B S hS hZ Z := by
  obtain ⟨I, inst, hne, hdir, D, hsize, hhom, hD, hAffine, hqsD, hftD,
    R, R', U, s, t, s', t', a, a', e, hR, hR', hs, ht, hsa, hea, hsa', hea'⟩ :=
    hCLO Z hZalg hqc hqs
  let := inst
  let := hne
  let := hdir
  let : IsCofiltered (Iᵒᵖ) := inferInstance
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit B S hS D (mk_op_lt B hsize) (mk_hom_op_lt B) hD hAffine
  obtain ⟨φ, -⟩ := exists_iso_of_isomorphic_presentations B S hS hR hR' e hs ht hZalg hlim
    hsa hea hsa' hea'
  exact ⟨(noetherianApproximationLimit B S hS hZ D hD hAffine hqsD hftD).ofIso φ.symm, hsize⟩

/-! ### The conclusion of relative approximation -/

/-- A *relative approximation* of a morphism `f : X ⟶ Y` of presheaves on the big fppf site of
`Spec ℤ`: a nonempty directed set `I`, an inverse system of arrows of algebraic spaces indexed
by `I` whose transition morphisms are affine on both sides and whose sources and targets are
quasi-separated and of finite type over `Spec ℤ`, and an identification of `f` with the limit
of that system in the arrow category.

This is the conclusion of Stacks 0GS3. -/
structure RelativeApproximation (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) where
  /-- The directed set indexing the system. -/
  I : Type (u + 1)
  /-- Its order. -/
  [preorder : Preorder I]
  /-- A directed set is nonempty. -/
  [nonempty : Nonempty I]
  /-- A directed set is directed. -/
  [isDirected : IsDirected I (· ≤ ·)]
  /-- The inverse system of morphisms, a functor into the arrow category out of the opposite of
  the index set. -/
  diagram : Iᵒᵖ ⥤ Arrow ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
  /-- The source of every stage is an algebraic space over `Spec ℤ`. -/
  isAlgebraicSpace_left (j : Iᵒᵖ) :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (diagram.obj j).left
  /-- The target of every stage is an algebraic space over `Spec ℤ`. -/
  isAlgebraicSpace_right (j : Iᵒᵖ) :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (diagram.obj j).right
  /-- The transition morphisms of the sources are affine. -/
  isAffineHom_left {j j' : Iᵒᵖ} (g : j ⟶ j') :
    IsAffineHom B (⊤_ Scheme.{u}) hZ (diagram.map g).left
  /-- The transition morphisms of the targets are affine. -/
  isAffineHom_right {j j' : Iᵒᵖ} (g : j ⟶ j') :
    IsAffineHom B (⊤_ Scheme.{u}) hZ (diagram.map g).right
  /-- The source of every stage is quasi-separated. -/
  isAbsolutelyQuasiSeparated_left (j : Iᵒᵖ) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (diagram.obj j).left
  /-- The target of every stage is quasi-separated. -/
  isAbsolutelyQuasiSeparated_right (j : Iᵒᵖ) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (diagram.obj j).right
  /-- The source of every stage is of finite type over `Spec ℤ`. -/
  isFiniteTypeOverIntegers_left (j : Iᵒᵖ) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from
      (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ (diagram.obj j).left))
  /-- The target of every stage is of finite type over `Spec ℤ`. -/
  isFiniteTypeOverIntegers_right (j : Iᵒᵖ) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from
      (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ (diagram.obj j).right))
  /-- The projections from `f` to the stages, a cone in the arrow category. -/
  π : (Functor.const Iᵒᵖ).obj (Arrow.mk f) ⟶ diagram
  /-- They exhibit `f` as the limit of the system. -/
  isLimit : IsLimit (Cone.mk (Arrow.mk f) π)

/-- **The conclusion of Stacks 0GS3.** A morphism of presheaves on the big fppf site of
`Spec ℤ` *has a relative approximation* when it is the limit of a directed inverse system of
morphisms of algebraic spaces with affine transition morphisms on both sides whose sources and
targets are quasi-separated and of finite type over `Spec ℤ`. -/
abbrev HasRelativeApproximation (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  Nonempty (RelativeApproximation B hZ f)


/-! ### Approximations with the index set bundled -/

/-- An approximation of `X` by quasi-separated algebraic spaces of finite type over `Spec ℤ`
with affine transition morphisms, over a directed index set, carrying alongside the two
consequences of the finite-type condition and the limits in the site of its base changes along
affine points, which is what the descent results of Stacks 0CP4 consume. -/
private structure StageSystem (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) where
  /-- The directed set indexing the system. -/
  I : Type u
  /-- Its order. -/
  [preorder : Preorder I]
  /-- A directed set is nonempty. -/
  [nonempty : Nonempty I]
  /-- A directed set is directed. -/
  [isDirected : IsDirected I (· ≤ ·)]
  /-- The inverse system. -/
  diagram : Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u
  /-- Every stage is an algebraic space over `Spec ℤ`. -/
  isAlgebraicSpace (j : Iᵒᵖ) : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (diagram.obj j)
  /-- Every stage is quasi-compact. -/
  isQuasiCompactSpace (j : Iᵒᵖ) : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (diagram.obj j)
  /-- Every stage is quasi-separated. -/
  isAbsolutelyQuasiSeparated (j : Iᵒᵖ) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (diagram.obj j)
  /-- The transition morphisms are affine. -/
  isAffineHom_map {j j' : Iᵒᵖ} (g : j ⟶ j') : IsAffineHom B (⊤_ Scheme.{u}) hZ (diagram.map g)
  /-- Every stage is of finite type over `Spec ℤ`. -/
  isFiniteTypeOverIntegers (j : Iᵒᵖ) : IsFiniteType B (⊤_ Scheme.{u}) hZ
    (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ (diagram.obj j)))
  /-- The structure morphism of every stage is locally of finite presentation. -/
  finitePresentation (j : Iᵒᵖ) :
    IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ (terminal.from (diagram.obj j))
  /-- The projections from `X` to the stages. -/
  π : (Functor.const Iᵒᵖ).obj X ⟶ diagram
  /-- They exhibit `X` as the limit of the system. -/
  isLimit : IsLimit (Cone.mk X π)
  /-- The limits of its base changes along affine points lie in the site, as the descent
  results require. -/
  siteContainsBaseChangeLimits : SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ diagram

attribute [instance] StageSystem.preorder StageSystem.nonempty StageSystem.isDirected

/-- A small Noetherian approximation, repackaged with the two consequences of the finite-type
condition supplied by the lemmas above. -/
private noncomputable def stageSystem (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X)
    (hA : #A.I < B.cutoff.ord.cof) :
    StageSystem B hZ X :=
  letI := A.preorder
  letI := A.nonempty
  letI := A.isDirected
  { I := A.I
    diagram := A.diagram
    isAlgebraicSpace := A.isAlgebraicSpace
    isQuasiCompactSpace := fun j =>
      isQuasiCompactSpace_of_isFiniteTypeOverIntegers B hZ (A.isFiniteTypeOverIntegers j)
    isAbsolutelyQuasiSeparated := A.isAbsolutelyQuasiSeparated
    isAffineHom_map := A.isAffineHom_map
    isFiniteTypeOverIntegers := A.isFiniteTypeOverIntegers
    finitePresentation := fun j =>
      isLocallyOfFinitePresentation_terminal_of_isFiniteTypeOverIntegers B hZ
        (A.isAlgebraicSpace j) (A.isFiniteTypeOverIntegers j)
    π := A.π
    isLimit := A.isLimit
    siteContainsBaseChangeLimits := IsSiteSmall.siteContainsBaseChangeLimits B _ hZ A.diagram
      (IsSiteSmall.of_lt_cof (mk_op_lt B hA) (mk_hom_op_lt B)) }

/-! ### Aligning two approximations -/

section Compatible

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}

/-- The projections of a stage system are compatible with its transition morphisms. -/
private theorem StageSystem.π_app_map {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (S : StageSystem B hZ X)
    {i j : S.Iᵒᵖ} (h : i ⟶ j) : S.π.app i ≫ S.diagram.map h = S.π.app j :=
  (Cone.mk X S.π).w h

/-- **Stacks 0CP4, the surjectivity half, over a stage of the target.** Over every stage `Y_j`
of an approximation of `Y`, the composite of `f` with the projection to `Y_j` factors through
some stage of an approximation of `X`: the structure morphism of `Y_j` is locally of finite
presentation, and the composite lies over the structure morphism of any stage of `X` because
there is only one morphism to the terminal presheaf. -/
private theorem exists_compatible_hom (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y) (j : (SY.I)ᵒᵖ) :
    ∃ (i : (SX.I)ᵒᵖ) (g : SX.diagram.obj i ⟶ SY.diagram.obj j),
      SX.π.app i ≫ g = f ≫ SY.π.app j := by
  classical
  obtain ⟨_, t, k, a, _, h₁, _⟩ :=
    exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B
      (⊤_ Scheme.{u}) hZ hZ SX.diagram (Cone.mk X SX.π) SX.isLimit SX.siteContainsBaseChangeLimits
      SX.isAlgebraicSpace SX.isQuasiCompactSpace SX.isAbsolutelyQuasiSeparated
      SX.isAffineHom_map hX (SY.isAlgebraicSpace j)
      (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ)
      (terminal.from (SY.diagram.obj j)) (SY.finitePresentation j)
      (f ≫ SY.π.app j) (op (Classical.arbitrary SX.I))
      (terminal.from (SX.diagram.obj (op (Classical.arbitrary SX.I))))
      (terminal.hom_ext _ _)
  exact ⟨k, SX.diagram.map a ≫ t, h₁⟩

/-- **Stacks 0CP4, the injectivity half, over a stage of the target.** Two morphisms from a
stage of an approximation of `X` to a stage of an approximation of `Y` which agree over `X`
agree after one transition morphism: they agree over the terminal presheaf for free. -/
private theorem exists_eq_after_transition
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y) {i : (SX.I)ᵒᵖ} {j : (SY.I)ᵒᵖ}
    (r s : SX.diagram.obj i ⟶ SY.diagram.obj j)
    (hlim : SX.π.app i ≫ r = SX.π.app i ≫ s) :
    ∃ (k : (SX.I)ᵒᵖ) (a : k ⟶ i), SX.diagram.map a ≫ r = SX.diagram.map a ≫ s :=
  exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u})
    hZ hZ SX.diagram (Cone.mk X SX.π) SX.isLimit SX.siteContainsBaseChangeLimits
    SX.isAlgebraicSpace SX.isQuasiCompactSpace SX.isAbsolutelyQuasiSeparated
    SX.isAffineHom_map hX (SY.isAlgebraicSpace j)
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ)
    (terminal.from (SY.diagram.obj j)) (SY.finitePresentation j) i r s hlim
    (terminal.hom_ext _ _)

/-- A stage of the relative system: a stage of the approximation of `X`, a stage of the
approximation of `Y`, and a morphism between them compatible with `f` and the two
projections. -/
private structure CompatibleStage {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y) where
  /-- The stage of the approximation of the source. -/
  source : (SX.I)ᵒᵖ
  /-- The stage of the approximation of the target. -/
  target : (SY.I)ᵒᵖ
  /-- The morphism between the two stages. -/
  hom : SX.diagram.obj source ⟶ SY.diagram.obj target
  /-- It is compatible with `f` and the two projections. -/
  compatible : SX.π.app source ≫ hom = f ≫ SY.π.app target

variable {f : X ⟶ Y}

/-- One stage of the relative system refines another when both of its stages are later and the
two morphisms agree over the transition morphisms. -/
private def CompatibleStage.Refines {SX : StageSystem B hZ X} {SY : StageSystem B hZ Y}
    (a b : CompatibleStage f SX SY) : Prop :=
  ∃ (hi : b.source ⟶ a.source) (hj : b.target ⟶ a.target),
    SX.diagram.map hi ≫ a.hom = b.hom ≫ SY.diagram.map hj

private instance {SX : StageSystem B hZ X} {SY : StageSystem B hZ Y} :
    Preorder (CompatibleStage f SX SY) where
  le a b := a.Refines b
  le_refl a := ⟨𝟙 _, 𝟙 _, by simp⟩
  le_trans a b c hab hbc := by
    obtain ⟨hab₁, hab₂, hab⟩ := hab
    obtain ⟨hbc₁, hbc₂, hbc⟩ := hbc
    refine ⟨hbc₁ ≫ hab₁, hbc₂ ≫ hab₂, ?_⟩
    calc SX.diagram.map (hbc₁ ≫ hab₁) ≫ a.hom
        = SX.diagram.map hbc₁ ≫ SX.diagram.map hab₁ ≫ a.hom := by
          simp only [Functor.map_comp, Category.assoc]
      _ = SX.diagram.map hbc₁ ≫ b.hom ≫ SY.diagram.map hab₂ := by rw [hab]
      _ = (SX.diagram.map hbc₁ ≫ b.hom) ≫ SY.diagram.map hab₂ := by
          simp only [Category.assoc]
      _ = (c.hom ≫ SY.diagram.map hbc₂) ≫ SY.diagram.map hab₂ := by rw [hbc]
      _ = c.hom ≫ SY.diagram.map (hbc₂ ≫ hab₂) := by
          simp only [Functor.map_comp, Category.assoc]

/-- Every stage of the approximation of `Y` carries a stage of the relative system, so the
relative system has at least one stage. -/
private theorem compatibleStage_nonempty (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y) :
    Nonempty (CompatibleStage f SX SY) := by
  classical
  obtain ⟨i, g, hg⟩ := exists_compatible_hom f hX SX SY (op (Classical.arbitrary SY.I))
  exact ⟨⟨i, _, g, hg⟩⟩

/-- **Any two stages of the relative system are refined by a third.** Take a stage of the
approximation of `Y` below both targets and a stage of the relative system over it, and refine
its source below both sources. The two resulting morphisms into each of the given targets agree
over `X`, hence after a transition morphism, and a common refinement of the two witnesses
refines both given stages. -/
private theorem compatibleStage_commonRefinement
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    {SX : StageSystem B hZ X} {SY : StageSystem B hZ Y} (a b : CompatibleStage f SX SY) :
    ∃ c : CompatibleStage f SX SY, a ≤ c ∧ b ≤ c := by
  classical
  have _ : IsCofiltered (SX.I)ᵒᵖ := inferInstance
  have _ : IsCofiltered (SY.I)ᵒᵖ := inferInstance
  obtain ⟨i₀, g₀, hg₀⟩ :=
    exists_compatible_hom f hX SX SY (IsCofiltered.min a.target b.target)
  let ja := IsCofiltered.minToLeft a.target b.target
  let jb := IsCofiltered.minToRight a.target b.target
  let im := IsCofiltered.minToRight i₀ (IsCofiltered.min a.source b.source)
  let ii₀ := IsCofiltered.minToLeft i₀ (IsCofiltered.min a.source b.source)
  let iia := im ≫ IsCofiltered.minToLeft a.source b.source
  let iib := im ≫ IsCofiltered.minToRight a.source b.source
  have key (c : CompatibleStage f SX SY)
      (jc : IsCofiltered.min a.target b.target ⟶ c.target)
      (ic : IsCofiltered.min i₀ (IsCofiltered.min a.source b.source) ⟶ c.source) :
      SX.π.app (IsCofiltered.min i₀ (IsCofiltered.min a.source b.source)) ≫
          (SX.diagram.map ii₀ ≫ g₀ ≫ SY.diagram.map jc) =
        SX.π.app (IsCofiltered.min i₀ (IsCofiltered.min a.source b.source)) ≫
          (SX.diagram.map ic ≫ c.hom) := by
    rw [reassoc_of% (SX.π_app_map ii₀), reassoc_of% hg₀, SY.π_app_map jc,
      reassoc_of% (SX.π_app_map ic), c.compatible]
  obtain ⟨ka, hka, eqa⟩ := exists_eq_after_transition hX SX SY
    (SX.diagram.map ii₀ ≫ g₀ ≫ SY.diagram.map ja) (SX.diagram.map iia ≫ a.hom) (key a ja iia)
  obtain ⟨kb, hkb, eqb⟩ := exists_eq_after_transition hX SX SY
    (SX.diagram.map ii₀ ≫ g₀ ≫ SY.diagram.map jb) (SX.diagram.map iib ≫ b.hom) (key b jb iib)
  let hka' := IsCofiltered.minToLeft ka kb
  let hkb' := IsCofiltered.minToRight ka kb
  -- the common refinement refines `c` once its source map is any of the (equal) composites
  have refines (c : CompatibleStage f SX SY) (jc : IsCofiltered.min a.target b.target ⟶ c.target)
      (ic : IsCofiltered.min i₀ (IsCofiltered.min a.source b.source) ⟶ c.source) {k : (SX.I)ᵒᵖ}
      (hk : k ⟶ IsCofiltered.min i₀ (IsCofiltered.min a.source b.source))
      (h : SX.diagram.map hk ≫ SX.diagram.map ii₀ ≫ g₀ ≫ SY.diagram.map jc =
        SX.diagram.map hk ≫ SX.diagram.map ic ≫ c.hom)
      (q : IsCofiltered.min ka kb ⟶ k) (hq : q ≫ hk ≫ ii₀ = hka' ≫ hka ≫ ii₀) :
      SX.diagram.map (q ≫ hk ≫ ic) ≫ c.hom =
        (SX.diagram.map (hka' ≫ hka ≫ ii₀) ≫ g₀) ≫ SY.diagram.map jc := by
    rw [← hq]
    simp only [Functor.map_comp, Category.assoc]
    rw [← h]
  refine ⟨⟨IsCofiltered.min ka kb, IsCofiltered.min a.target b.target,
    SX.diagram.map (hka' ≫ hka ≫ ii₀) ≫ g₀, ?_⟩, ⟨hka' ≫ hka ≫ iia, ja, ?_⟩,
    ⟨hkb' ≫ hkb ≫ iib, jb, ?_⟩⟩
  · rw [reassoc_of% (SX.π_app_map (hka' ≫ hka ≫ ii₀)), hg₀]
  · exact refines a ja iia hka eqa hka' rfl
  · exact refines b jb iib hkb eqb hkb' (Subsingleton.elim _ _)

/-- The chosen transition morphism of the sources underlying a refinement. -/
private noncomputable def refinesSourceMap {SX : StageSystem B hZ X} {SY : StageSystem B hZ Y}
    {a b : CompatibleStage f SX SY} (h : b ≤ a) :
    a.source ⟶ b.source :=
  Classical.choose h

/-- The chosen transition morphism of the targets underlying a refinement. -/
private noncomputable def refinesTargetMap {SX : StageSystem B hZ X} {SY : StageSystem B hZ Y}
    {a b : CompatibleStage f SX SY} (h : b ≤ a) :
    a.target ⟶ b.target :=
  Classical.choose (Classical.choose_spec h)

/-- The commuting square of a refinement, for the two chosen transition morphisms. -/
private theorem refinesSquare {SX : StageSystem B hZ X} {SY : StageSystem B hZ Y}
    {a b : CompatibleStage f SX SY} (h : b ≤ a) :
    SX.diagram.map (refinesSourceMap h) ≫ b.hom =
      a.hom ≫ SY.diagram.map (refinesTargetMap h) :=
  Classical.choose_spec (Classical.choose_spec h)

/-! ### The relative system and its limit -/

/-- The inverse system of arrows indexed by the stages of the relative system. -/
private noncomputable def compatibleDiagram (f : X ⟶ Y)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y) :
    (CompatibleStage f SX SY)ᵒᵖ ⥤ Arrow ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) where
  obj i := Arrow.mk i.unop.hom
  map {i j} h := Arrow.homMk' (SX.diagram.map (refinesSourceMap (leOfHom h.unop)))
    (SY.diagram.map (refinesTargetMap (leOfHom h.unop))) (refinesSquare (leOfHom h.unop))
  map_id i := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · exact (congrArg SX.diagram.map (Subsingleton.elim _ (𝟙 _))).trans
        (SX.diagram.map_id _)
    · exact (congrArg SY.diagram.map (Subsingleton.elim _ (𝟙 _))).trans
        (SY.diagram.map_id _)
  map_comp {i j k} g h := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · exact (congrArg SX.diagram.map (Subsingleton.elim _
        (refinesSourceMap (leOfHom g.unop) ≫ refinesSourceMap (leOfHom h.unop)))).trans
        (SX.diagram.map_comp _ _)
    · exact (congrArg SY.diagram.map (Subsingleton.elim _
        (refinesTargetMap (leOfHom g.unop) ≫ refinesTargetMap (leOfHom h.unop)))).trans
        (SY.diagram.map_comp _ _)

/-- The projection from the stages of the relative system to the stages of the approximation of
the source. -/
private noncomputable def compatibleSourceProjection (f : X ⟶ Y)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y) :
    (CompatibleStage f SX SY)ᵒᵖ ⥤ (SX.I)ᵒᵖ where
  obj i := i.unop.source
  map h := refinesSourceMap (leOfHom h.unop)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The projection from the stages of the relative system to the stages of the approximation of
the target. -/
private noncomputable def compatibleTargetProjection (f : X ⟶ Y)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y) :
    (CompatibleStage f SX SY)ᵒᵖ ⥤ (SY.I)ᵒᵖ where
  obj i := i.unop.target
  map h := refinesTargetMap (leOfHom h.unop)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The projection to the stages of the approximation of the source is initial: every stage of
the source is refined by the source of some stage of the relative system, and the morphism
types of the index sets are subsingletons. -/
private theorem compatibleSourceProjection_initial (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y)
    [Nonempty (CompatibleStage f SX SY)] [IsDirected (CompatibleStage f SX SY) (· ≤ ·)] :
    (compatibleSourceProjection f SX SY).Initial := by
  classical
  have _ : IsCofiltered (SX.I)ᵒᵖ := inferInstance
  apply Functor.initial_of_exists_of_isCofiltered
  · intro d
    obtain ⟨i, g, hg⟩ := exists_compatible_hom f hX SX SY (op (Classical.arbitrary SY.I))
    have hgk : SX.π.app (IsCofiltered.min i d) ≫
        (SX.diagram.map (IsCofiltered.minToLeft i d) ≫ g) =
          f ≫ SY.π.app (op (Classical.arbitrary SY.I)) := by
      rw [reassoc_of% (SX.π_app_map (IsCofiltered.minToLeft i d)), hg]
    exact ⟨op ⟨IsCofiltered.min i d, _, _, hgk⟩, ⟨IsCofiltered.minToRight i d⟩⟩
  · intro d c s s'
    exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩

/-- The projection to the stages of the approximation of the target is initial: every stage of
the target carries a stage of the relative system, and the morphism types of the index sets are
subsingletons. -/
private theorem compatibleTargetProjection_initial (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y)
    [Nonempty (CompatibleStage f SX SY)] [IsDirected (CompatibleStage f SX SY) (· ≤ ·)] :
    (compatibleTargetProjection f SX SY).Initial := by
  classical
  have _ : IsCofiltered (SY.I)ᵒᵖ := inferInstance
  apply Functor.initial_of_exists_of_isCofiltered
  · intro d
    obtain ⟨i, g, hg⟩ := exists_compatible_hom f hX SX SY
      (IsCofiltered.min (op (Classical.arbitrary SY.I)) d)
    exact ⟨op ⟨i, _, g, hg⟩,
      ⟨IsCofiltered.minToRight (op (Classical.arbitrary SY.I)) d⟩⟩
  · intro d c s s'
    exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩

/-- **The relative system of two aligned approximations, with its limiting cone.** The stages of
the relative system form a nonempty directed set, the two projections to the index sets of the
approximations are initial, and the cone in the arrow category whose components are the two
families of projections is limiting because its images under the two projections of the arrow
category are the restrictions of the two limiting cones along initial functors. -/
private noncomputable def relativeApproximationOfStageSystems (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (SX : StageSystem B hZ X) (SY : StageSystem B hZ Y) :
    RelativeApproximation B hZ f := by
  classical
  letI hne : Nonempty (CompatibleStage f SX SY) := compatibleStage_nonempty f hX SX SY
  letI hdir : IsDirected (CompatibleStage f SX SY) (· ≤ ·) :=
    ⟨fun a b => compatibleStage_commonRefinement hX a b⟩
  letI : (compatibleSourceProjection f SX SY).Initial :=
    compatibleSourceProjection_initial f hX SX SY
  letI : (compatibleTargetProjection f SX SY).Initial :=
    compatibleTargetProjection_initial f hX SX SY
  refine
    { I := CompatibleStage f SX SY
      diagram := compatibleDiagram f SX SY
      isAlgebraicSpace_left := fun j =>
        SX.isAlgebraicSpace ((compatibleSourceProjection f SX SY).obj j)
      isAlgebraicSpace_right := fun j =>
        SY.isAlgebraicSpace ((compatibleTargetProjection f SX SY).obj j)
      isAffineHom_left := fun g =>
        SX.isAffineHom_map ((compatibleSourceProjection f SX SY).map g)
      isAffineHom_right := fun g =>
        SY.isAffineHom_map ((compatibleTargetProjection f SX SY).map g)
      isAbsolutelyQuasiSeparated_left := fun j =>
        SX.isAbsolutelyQuasiSeparated ((compatibleSourceProjection f SX SY).obj j)
      isAbsolutelyQuasiSeparated_right := fun j =>
        SY.isAbsolutelyQuasiSeparated ((compatibleTargetProjection f SX SY).obj j)
      isFiniteTypeOverIntegers_left := fun j =>
        SX.isFiniteTypeOverIntegers ((compatibleSourceProjection f SX SY).obj j)
      isFiniteTypeOverIntegers_right := fun j =>
        SY.isFiniteTypeOverIntegers ((compatibleTargetProjection f SX SY).obj j)
      π :=
        { app := fun i => Arrow.homMk'
            (SX.π.app ((compatibleSourceProjection f SX SY).obj i))
            (SY.π.app ((compatibleTargetProjection f SX SY).obj i)) i.unop.compatible
          naturality := fun i j g => by
            refine Arrow.hom_ext _ _ ?_ ?_
            · change SX.π.app ((compatibleSourceProjection f SX SY).obj j) =
                SX.π.app ((compatibleSourceProjection f SX SY).obj i) ≫
                  SX.diagram.map ((compatibleSourceProjection f SX SY).map g)
              exact (Category.id_comp _).symm.trans
                (SX.π.naturality ((compatibleSourceProjection f SX SY).map g))
            · change SY.π.app ((compatibleTargetProjection f SX SY).obj j) =
                SY.π.app ((compatibleTargetProjection f SX SY).obj i) ≫
                  SY.diagram.map ((compatibleTargetProjection f SX SY).map g)
              exact (Category.id_comp _).symm.trans
                (SY.π.naturality ((compatibleTargetProjection f SX SY).map g)) }
      isLimit := ?_ }
  exact Comma.fstSndJointlyReflectLimit
    ((Functor.Initial.isLimitWhiskerEquiv (compatibleSourceProjection f SX SY)
      (Cone.mk X SX.π)).symm SX.isLimit)
    ((Functor.Initial.isLimitWhiskerEquiv (compatibleTargetProjection f SX SY)
      (Cone.mk Y SY.π)).symm SY.isLimit)

end Compatible

end AlgebraicGeometry.Space

end
