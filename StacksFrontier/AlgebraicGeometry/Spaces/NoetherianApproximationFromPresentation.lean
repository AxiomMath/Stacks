module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation

/-!
# Absolute Noetherian approximation for algebraic spaces, from the constructed system

**Stacks 07SU** asserts that a quasi-compact and quasi-separated algebraic space `X` over
`Spec ℤ` is the limit of a directed inverse system of algebraic spaces with affine transition
morphisms whose stages are quasi-separated and of finite type over `Spec ℤ`.

The source's proof follows Theorem 1.2.2 of Conrad–Lieblich–Olsson: it stratifies `X` by open
subspaces with étale scheme neighbourhoods, approximates each stratum with absolute Noetherian
approximation for *schemes*, approximates the étale equivalence relations stagewise, and ends by
identifying the quotient of the constructed system's limit with `X`.  That last step is the only
part of the argument that mentions `X` at all, and it is what is proved here: the construction
produces a system together with a surjective étale atlas of `X` and one of the system's limit
whose kernel pairs are isomorphic as relations, and Stacks 0262 then makes the two spaces the
same.

## Main results

* `AlgebraicGeometry.Space.noetherianApproximationLimit` — the limit of a directed inverse
  system of algebraic spaces with affine transition morphisms whose stages are quasi-separated
  and of finite type over `Spec ℤ` is its own Noetherian approximation.  This is the assembly of
  the conclusion of Stacks 07SU out of a system, with no hypothesis on the limit.
* `AlgebraicGeometry.Space.hasNoetherianApproximation_of_isomorphicPresentation_limit` —
  **Stacks 07SU**, granted the Conrad–Lieblich–Olsson construction's output as the general
  hypothesis `hCLO`.

## Implementation notes

### What `hCLO` carries, and what is proved from it

`hCLO` is the output of the construction, quantified over its own algebraic space: for *every*
quasi-compact, absolutely quasi-separated algebraic space over `S` it produces a directed index
set, an inverse system over it with affine transition morphisms whose stages are algebraic
spaces, quasi-separated and of finite type over `Spec ℤ`, and — this is the construction's
closing datum — an object `U` of the site carrying a surjective étale atlas of the given space
*and* one of the system's limit, with the two kernel pairs isomorphic as relations on `U`.

It is not this theorem's conclusion pre-instantiated.  Its consequent asserts nothing about the
given space being a limit; the clauses about the system are clauses about the system, and the
only clause relating the given space to the system is the isomorphism of the two kernel pairs,
which is strictly weaker than an isomorphism of the two spaces.  Three things are proved from
it: that the limit of the system is an algebraic space, which is Stacks 07SF, existence, and is
needed before Stacks 0262 can be applied to it; that the limit is its own Noetherian
approximation, which is `AlgebraicGeometry.Space.noetherianApproximationLimit`; and that the
given space is isomorphic to that limit, which is the source's final step, Stacks 0262, proved
as `AlgebraicGeometry.Space.exists_iso_of_isomorphic_presentations`.

What is *not* proved is the construction itself: the stratification (Stacks 07ST), absolute
Noetherian approximation for schemes (Stacks 01ZA, proved for bare schemes as
`AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType` — see below), and the
stagewise approximation of the étale equivalence relations.

### The cardinality conditions, and the correction they record

Stacks 07SF, existence — `AlgebraicGeometry.Space.isAlgebraicSpace_limit` — carries two side
conditions on the index category of the system: fewer objects, and fewer morphisms in each
Hom-set, than the cofinality of the site's size cutoff `B.cutoff`.  They are what makes the
limit of the system an algebraic space at all, and they are the conditions Stacks
07SF and Stacks 0828 carry throughout this development.  A formalization of Stacks 07SU that
omits them is false as written, so `hCLO` supplies them and
`AlgebraicGeometry.Space.noetherianApproximationLimit` requires them.  This is the correction
recorded in the tag's attribute description.

### Stacks 01ZA, and why the scheme case does not discharge `hCLO`

Absolute Noetherian approximation for schemes is proved, as
`AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType` in
`StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeApproximation/Absolute.lean`.
It does not by itself give even the
representable case of Stacks 07SU in this framework: its stages are bare schemes, with no
morphism to the base `S` and no membership of the site, its limit is a limit in `Scheme` rather
than of presheaves on the site, and it records of its stages only that they are quasi-compact
and locally of finite type over the integers, not that they are quasi-separated — which is
clause (2) of Stacks 07SU and a field of `AlgebraicGeometry.Space.NoetherianApproximation`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The two cardinality conditions Stacks 07SF asks of the index category of an inverse system,
transported from the directed index set `I` to the index category `Iᵒᵖ` of the system. -/
private theorem mk_op_lt_of_mk_lt {I : Type u} [Preorder I]
    (hsize : #I < B.cutoff.ord.cof)
    (hhom : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) :
    #(Iᵒᵖ) < B.cutoff.ord.cof ∧ ∀ i j : Iᵒᵖ, #(i ⟶ j) < B.cutoff.ord.cof := by
  refine ⟨by rwa [← Cardinal.mk_congr (Opposite.equivToOpposite (α := I))], fun i j => ?_⟩
  have e : (i ⟶ j) ≃ (j.unop ⟶ i.unop) :=
    (Opposite.equivToOpposite (α := (j.unop ⟶ i.unop))).symm
  rw [Cardinal.mk_congr e]
  exact hhom _ _

/-- **The conclusion of Stacks 07SU, assembled from a system.**  Let `I` be a directed set and
`D` an inverse system over it of algebraic spaces over `S` whose transition morphisms are affine
and whose stages are quasi-separated and of finite type over `Spec ℤ`.  Then the limit of `D` is
its own Noetherian approximation, over `D` itself.

No hypothesis is placed on the limit: the cone is the canonical limit cone of `D`, which exists
because limits of presheaves do. -/
noncomputable def noetherianApproximationLimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j))
    (hAffine : ∀ {j j' : Iᵒᵖ} (g : j ⟶ j'), IsAffineHom B S hS (D.map g))
    (hqs : ∀ j, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj j))
    (hft : ∀ j, IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B S hS hZ (D.obj j)))) :
    NoetherianApproximation B S hS hZ (limit D) where
  I := I
  diagram := D
  isAlgebraicSpace := hD
  isAffineHom_map := hAffine
  isAbsolutelyQuasiSeparated := hqs
  isFiniteTypeOverIntegers := hft
  π := (limit.cone D).π
  isLimit := limit.isLimit D

/-- **Stacks 07SU.**  Let `X` be a quasi-compact and quasi-separated algebraic space over `S`.
Then there are a directed set `I` and an inverse system of algebraic spaces `(X_i, f_{ii'})`
over `I` whose transition morphisms are affine, whose stages are quasi-separated and of finite
type over `Spec ℤ`, and whose limit is `X`.

The tag's own hypotheses — `X` an algebraic space, quasi-compact and quasi-separated — are the
hypotheses here, and the conclusion is the full conclusion of the tag, in the interface
`AlgebraicGeometry.Space.HasNoetherianApproximation` of
`StacksFrontier/AlgebraicGeometry/Spaces/NoetherianApproximation.lean`.  What is granted is the
single general hypothesis `hCLO`, the output of the Conrad–Lieblich–Olsson construction, which
is quantified over its own algebraic space and does not mention `X`; see the module
documentation for what it carries and for why it is not this conclusion pre-instantiated.  It
supplies the two cardinality conditions on the index set that Stacks 07SF, existence needs, and
which a statement of Stacks 07SU that omits them does not have; that is the correction recorded
below.

Proved from it: the limit of the system is an algebraic space (Stacks 07SF, existence), it is
its own Noetherian approximation (`AlgebraicGeometry.Space.noetherianApproximationLimit`), and
`X` is isomorphic to it, which is the step the source's proof ends with (Stacks 0262, as
`AlgebraicGeometry.Space.exists_iso_of_isomorphic_presentations`). -/
@[stacks 07SU "granted the Conrad–Lieblich–Olsson construction's output as the general \
hypothesis hCLO, strengthened by the two cardinality conditions on the index set that make the \
limit an algebraic space and without which the statement is false"]
theorem hasNoetherianApproximation_of_isomorphicPresentation_limit
    (hCLO : ∀ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Z →
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
                (BigFppfOver.toScheme B S hS))) a')
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    HasNoetherianApproximation B S hS hZ X := by
  obtain ⟨I, inst, hne, hdir, D, hsize, hhom, hD, hAffine, hqsD, hftD,
    R, R', U, s, t, s', t', a, a', e, hR, hR', hs, ht, hsa, hea, hsa', hea'⟩ :=
    hCLO X hX hqc hqs
  let := inst
  let := hne
  let := hdir
  let : IsCofiltered (Iᵒᵖ) := inferInstance
  obtain ⟨hsizeop, hhomop⟩ := mk_op_lt_of_mk_lt B (I := I) hsize hhom
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit B S hS D hsizeop hhomop hD hAffine
  obtain ⟨φ, -⟩ := exists_iso_of_isomorphic_presentations B S hS hR hR' e hs ht hX hlim
    hsa hea hsa' hea'
  exact HasNoetherianApproximation.ofIso
    ⟨noetherianApproximationLimit B S hS hZ D hD hAffine hqsD hftD⟩ φ.symm

end AlgebraicGeometry.Space

end
