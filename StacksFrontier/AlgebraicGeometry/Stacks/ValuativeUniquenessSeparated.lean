module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionExistencePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionSecondDiagonal

/-!
# Valuative criterion for separatedness (Stacks 0CLT)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site `B`.
**Stacks 0CLT** says that a *quasi-separated* `f` satisfying the uniqueness part of the valuative
criterion is separated.

Separatedness of `f` (**Stacks 04YW**) is properness of the relative diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` in the relative sense of Stacks 04XB, that is: separatedness, finite type
and universal closedness of every algebraic space representing a base change of `Δ_f` along a
scheme-valued point. The three conjuncts come from three different places.

* *Separated.* This is **Stacks 0CLR**, whose setoid hypothesis is the first conjunct of the
  uniqueness criterion for `f`.
* *Finite type.* Quasi-compactness is the first conjunct of quasi-separatedness of `f`. Local
  finiteness of type of `Δ_f` is part (2) of **Stacks 04XS**, which holds for an arbitrary
  1-morphism of algebraic stacks.
* *Universally closed.* The uniqueness criterion for `f` gives the existence part of the
  valuative criterion for `Δ_f` — a formal consequence of **Stacks 0E8L**, below — and Stacks
  0CLN transports that to every algebraic space representing a base change of `Δ_f`, where it
  combines with quasi-compactness through **Stacks 03KA** to give universal closedness.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_valuativeCriterionUniqueness`:
  **Stacks 0CLT**.
* `AlgebraicGeometry.Stack.valuativeCriterionExistence_relativeDiagonal_of_uniqueness`: the
  existence part of the valuative criterion for `Δ_f`, from the uniqueness part for `f`.
* `AlgebraicGeometry.Stack.nonempty_dottedArrow_relativeDiagonal`: a valuative diagram for `Δ_f`
  admits a dotted arrow outright, with no extension of the valuation ring.
* `AlgebraicGeometry.Stack.ValuativeSquare.toValuativeDiagram` and
  `AlgebraicGeometry.Stack.ValuativeSquare.ofDominatingExtension`: a valuative square is a
  valuative diagram, and the square a dominating extension leaves behind.
* `AlgebraicGeometry.Stack.IsLocallyOfFiniteType`: local finiteness of type in the relative sense
  of Stacks 04XB.

## Implementation notes

`AlgebraicGeometry.Stack.ValuativeSquare` (**Stacks 0CLK**, carrying the existence criterion) has
its two points at the canonical spectra `Spec K` and `Spec R`, whereas
`AlgebraicGeometry.Stack.ValuativeDiagram` (**Stacks 0CLG**, carrying the uniqueness criterion)
allows any objects of the site whose underlying schemes are merely isomorphic to them.
`AlgebraicGeometry.Stack.ValuativeSquare.toValuativeDiagram` is the resulting inclusion of the
first family into the second: the identification of `Spec K` with `Spec` of the fraction field of
`R` is `IsFractionRing.fieldEquivOfRingEquiv`'s special case `FractionRing.algEquiv`, and the
identification of `Spec R` with itself is the identity, so the generic point, the special point,
the left edge and the filling 2-morphism are carried over unchanged. The existence criterion for
`Δ_f` is therefore proved with the *identity* dominating extension
(`AlgebraicGeometry.Stack.dominatingExtensionOfRingMaps` at the identity of `R`): the uniqueness
criterion for `f` already fills a `Δ_f`-square over `R` itself.

Local finiteness of type of `Δ_f` is part (2) of Stacks 04XS, taken from
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack`, which
places no hypothesis on `f`. It is spelled as the Stacks 04XB relative condition at
`AlgebraicGeometry.Space.IsLocallyOfFiniteType`, in the shape
`AlgebraicGeometry.Stack.IsFiniteType` and `AlgebraicGeometry.Stack.IsQuasiCompact` are written;
`AlgebraicGeometry.Stack.IsLocallyOfFiniteType` here is that spelling, and the two agree
definitionally with the longhand form the 04XS statement is written in. Both conjuncts of
quasi-separatedness do work: quasi-separatedness of `Δ_f` in Stacks 0CLR and quasi-compactness
of `Δ_f` in Stacks 03KA.

The passage between the site of `S` and the site of a scheme-valued point `U` is the one of
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` together with
`AlgebraicGeometry.Space.isQuasiCompact_relocalizeToYoneda_iff` and
`AlgebraicGeometry.Space.universallyClosed_relocalize_iff`; the two `RespectsIso` hypotheses are
supplied by hand from base-change stability, as in Stacks 0CLR, because the available instances
go through an fpqc precoverage whose universe the goal does not determine.

## References

* [Stacks Project, Tag 03KA](https://stacks.math.columbia.edu/tag/03KA)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLN](https://stacks.math.columbia.edu/tag/0CLN)
* [Stacks Project, Tag 0CLR](https://stacks.math.columbia.edu/tag/0CLR)
* [Stacks Project, Tag 0CLT](https://stacks.math.columbia.edu/tag/0CLT)
* [Stacks Project, Tag 0E8L](https://stacks.math.columbia.edu/tag/0E8L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.Stack.AlgebraicStacks

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Local finiteness of type in the relative sense of Stacks 04XB -/

section Relative

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces is *locally of finite type* when every algebraic space
representing its base change along a scheme-valued point of the target has structural morphism
locally of finite type, read as a morphism of algebraic spaces over `S`. This is the notion of
Stacks 04XB for `AlgebraicGeometry.Space.IsLocallyOfFiniteType`, the missing companion of
`AlgebraicGeometry.Stack.IsQuasiCompact` and `AlgebraicGeometry.Stack.IsFiniteType`. -/
abbrev IsLocallyOfFiniteType (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsLocallyOfFiniteType B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end Relative

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-! ### A valuative square is a valuative diagram -/

/-- **A valuative square is a valuative diagram.** The two notions differ only in that a square
places its two points at the canonical spectra of a valuation ring and of its chosen fraction
field, while a diagram allows any objects of the site whose underlying schemes are isomorphic to
them; the generic point, the special point, the left edge and the filling 2-morphism are the same
data. -/
noncomputable def ValuativeSquare.toValuativeDiagram {g : 𝒳 ⟶ 𝒴}
    (q : ValuativeSquare B S hS g) : ValuativeDiagram B S hS 𝒳 𝒴 g :=
  letI e := RingEquiv.toCommRingCatIso (FractionRing.algEquiv q.R q.K).toRingEquiv
  haveI hcomm : CommRingCat.ofHom (algebraMap q.R (FractionRing q.R)) ≫ e.hom =
      CommRingCat.ofHom (algebraMap q.R q.K) := by
    ext r
    exact (FractionRing.algEquiv q.R q.K).commutes r
  { R := q.R
    generic := siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
    whole := siteObject B S hS q.ring_mem q.base
    generic_iso :=
      { hom := Spec.map e.hom
        inv := Spec.map e.inv
        hom_inv_id := by
          rw [← Spec.map_comp, e.inv_hom_id, Spec.map_id]
          rfl
        inv_hom_id := by rw [← Spec.map_comp, e.hom_inv_id, Spec.map_id] }
    whole_iso := Iso.refl _
    inclusion := q.genericMap
    inclusion_spec := by
      change (BigFppfOver.toScheme B S hS).map q.genericMap =
        Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap q.R (FractionRing q.R))) ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp, hcomm]
      exact q.genericMap_left
    j := q.j
    j_canonical := q.j_canonical
    x := q.x
    y := q.y
    γ := q.γ }

/-! ### The existence part of the valuative criterion for the relative diagonal -/

/-- **A valuative diagram for the relative diagonal admits a dotted arrow as soon as `f` satisfies
the uniqueness part of the valuative criterion at the diagram's valuation ring**, with no
extension of that ring at all.

This is the formal argument of Stacks 0CLT. By part (1) of **Stacks 0E8L** the diagram produces
two dotted arrows `(a₁, α₁, id)` and `(a₂, α₂, φ)` for the `f`-square with the same generic point
and special point `f ∘ a₁`; uniqueness makes them isomorphic, and part (2) of Stacks 0E8L
identifies the morphisms between them with the isomorphism classes of dotted arrows of the
original diagram, so there is at least one.

The `f`-diagram the argument feeds to `hu` differs from `D` only in its special point and filler,
so its valuation ring is `D`'s with the same ring structure: a uniqueness criterion tested only on
a restricted class of valuation rings — discrete ones, for **Stacks 0E80** — suffices. The ring,
domain and valuation-ring structures are passed to `Pred` explicitly because
`AlgebraicGeometry.Stack.ValuativeDiagram` does not register its fields as instances. -/
theorem nonempty_dottedArrow_relativeDiagonal_of_pred (f : 𝒳 ⟶ 𝒴)
    (Pred : ∀ R : Type u, [CommRing R] → [IsDomain R] → [ValuationRing R] → Prop)
    (hu : ∀ D : ValuativeDiagram B S hS 𝒳 𝒴 f, @Pred D.R D.ring D.domain D.valuation →
      ∀ a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ, Nonempty (a ≅ b))
    (D : ValuativeDiagram B S hS 𝒳 (AlgebraicStacks.twoFibreProduct B S hS f f)
      (AlgebraicStacks.relativeDiagonal B S hS f))
    (hD : @Pred D.R D.ring D.domain D.valuation) :
    Nonempty (CategoryTheory.DottedArrow D.x D.j
      (AlgebraicStacks.relativeDiagonal B S hS f).hom D.y D.γ) := by
  obtain ⟨m⟩ := hu { D with
      y := (D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ≫ f.hom
      γ := diagonalWitness B S hS D } hD
    (diagonalDottedArrowFst B S hS D) (diagonalDottedArrowSnd B S hS D)
  obtain ⟨d, _⟩ := Quotient.exists_rep
    ((diagonalDottedArrowClassesEquiv B S hS D).symm m.hom)
  exact ⟨d⟩

/-- **A valuative diagram for the relative diagonal admits a dotted arrow as soon as `f`
satisfies the uniqueness part of the valuative criterion**, with no extension of the valuation
ring at all.

This is `AlgebraicGeometry.Stack.nonempty_dottedArrow_relativeDiagonal_of_pred` at the trivially
true predicate. -/
theorem nonempty_dottedArrow_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (hu : ValuativeCriterion.Uniqueness B S hS f)
    (D : ValuativeDiagram B S hS 𝒳 (AlgebraicStacks.twoFibreProduct B S hS f f)
      (AlgebraicStacks.relativeDiagonal B S hS f)) :
    Nonempty (CategoryTheory.DottedArrow D.x D.j
      (AlgebraicStacks.relativeDiagonal B S hS f).hom D.y D.γ) :=
  nonempty_dottedArrow_relativeDiagonal_of_pred B S hS f (fun _ => True)
    (fun D' _ => (hu D').2) D trivial

/-- **The valuative square a dominating extension leaves behind.** Its valuation ring is the
dominating one, its base morphism is the extended one, and its generic point, special point and
filling 2-morphism are those of the original square pulled back along the extension. A dotted
arrow for it is exactly a dotted arrow for the original square over the extension. -/
noncomputable def ValuativeSquare.ofDominatingExtension {g : 𝒳 ⟶ 𝒴}
    (q : ValuativeSquare B S hS g) (e : q.DominatingExtension) : ValuativeSquare B S hS g where
  R := e.R'
  K := e.K'
  ring_mem := e.ring_mem
  field_mem := e.field_mem
  base := Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base
  genericMap := e.genericMap
  genericMap_left := e.genericMap_left
  j := e.j
  j_canonical := e.j_canonical
  x := e.k ≫ q.x
  y := e.a ≫ q.y
  γ := e.inducedGamma

/-- **The relative diagonal satisfies the existence part of the valuative criterion as soon as
`f` satisfies the uniqueness part.** This is Definition 0CLK for `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`.

The dominating extension can be taken to be the identity of the valuation ring: reading the
square it leaves behind as a valuative diagram, the uniqueness criterion for `f` already fills
it through Stacks 0E8L. -/
theorem valuativeCriterionExistence_relativeDiagonal_of_uniqueness (f : 𝒳 ⟶ 𝒴)
    (hu : ValuativeCriterion.Uniqueness B S hS f) :
    ValuativeCriterion.Existence B S hS (AlgebraicStacks.relativeDiagonal B S hS f) := by
  intro q
  exact ⟨dominatingExtensionOfRingMaps B q q.R q.K (RingHom.id q.R) (RingHom.id q.K)
    (isLocalHom_id q.R) (by rw [RingHom.comp_id, RingHom.id_comp]) q.ring_mem q.field_mem,
    nonempty_dottedArrow_relativeDiagonal B S hS f hu
      (ValuativeSquare.toValuativeDiagram B S hS
        (ValuativeSquare.ofDominatingExtension B S hS q _))⟩

/-! ### Stacks 0CLT -/

namespace AlgebraicStacks

/-- **Stacks 0CLT.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Assume `f` is
quasi-separated. If `f` satisfies the uniqueness part of the valuative criterion, then `f` is
separated.

Separatedness of `f` is properness of `Δ_f` in the relative sense of Stacks 04XB. Its three
conjuncts are: separatedness of `Δ_f`, which is Stacks 0CLR fed with the setoid half of the
uniqueness criterion; finiteness of type, whose quasi-compactness half is the first conjunct of
quasi-separatedness and whose local half is part (2) of Stacks 04XS; and universal closedness,
which comes from the existence part of the valuative criterion for `Δ_f` through Stacks 0CLN and
Stacks 03KA. -/
@[stacks 0CLT]
theorem isSeparated_of_valuativeCriterionUniqueness (f : 𝒳 ⟶ 𝒴)
    (hqs : IsQuasiSeparated B S hS f)
    (hu : ValuativeCriterion.Uniqueness B S hS f) :
    IsSeparated B S hS f := by
  have hlft : Stack.IsLocallyOfFiniteType B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
    (Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS f).2
  have hriqc : MorphismProperty.RespectsIso (Space.quasiCompactProperty B S hS) :=
    (Space.isQuasiCompact_isStableUnderBaseChange B S hS).respectsIso
  have hriuc : MorphismProperty.RespectsIso (Space.universallyClosedProperty B S hS) :=
    (Space.universallyClosedProperty_isStableUnderBaseChange B S hS).respectsIso
  have hriuc' : MorphismProperty.RespectsIso (@Space.UniversallyClosed B S hS) :=
    Space.universallyClosed_respectsIso B S hS
  rintro U y hy F hF ⟨e⟩
  refine ⟨isSeparated_relativeDiagonal_of_isSetoidCategory_dottedArrow
      B S hS f hqs.2 (fun D => (hu D).1) U y hy F hF ⟨e⟩,
    ⟨hlft U y hy F hF ⟨e⟩, hqs.1 U y hy F hF ⟨e⟩⟩, ?_⟩
  -- quasi-compactness of the base change, over the site of `U`
  have hqcU : Space.IsQuasiCompact B U.left.1 U.left.2
      (Space.toYonedaId B U.left.1 U.left.2 F) :=
    (Space.isQuasiCompact_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom F).mp
      ((prop_algebraicSpaceMap_iff B S hS (Space.quasiCompactProperty B S hS) U F hF).mp
        (hqs.1 U y hy F hF ⟨e⟩))
  -- the existence part of the valuative criterion for the base change, by Stacks 0CLN
  have hexU : Space.ValuativeCriterion.Existence (Space.toYonedaId B U.left.1 U.left.2 F) :=
    valuativeCriterionExistence_baseChange_point B S hS
      (AlgebraicStacks.relativeDiagonal B S hS f)
      (valuativeCriterionExistence_relativeDiagonal_of_uniqueness B S hS f hu) U y hy F e _
  -- universal closedness of the base change, by Stacks 03KA
  have hucU : Space.UniversallyClosed B U.left.1 U.left.2
      (Space.toYonedaId B U.left.1 U.left.2 F) :=
    Space.universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence hF
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _) _ hqcU hexU
  refine (prop_algebraicSpaceMap_iff B S hS (Space.universallyClosedProperty B S hS)
    U F hF).mpr ?_
  show Space.UniversallyClosed B S hS (OverShriek.relocalizeToYoneda U.hom F)
  rw [← relocalizeToYoneda_eq_map_toYonedaId B U.left.1 S U.left.2 hS U.hom F]
  exact (MorphismProperty.cancel_right_of_respectsIso (@Space.UniversallyClosed B S hS) _ _).2
    ((Space.universallyClosed_relocalize_iff B U.left.1 U.left.2 S hS U.hom hF
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _) _).mpr hucU)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
