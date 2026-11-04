module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.QuotValuativeAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria

/-!
# The existence part of the valuative criterion for the Hilbert functor (Stacks 0DM8)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
separated and of finite presentation — the standing hypothesis of the source's section on the
properties of the Hilbert functor, under which `Hilb_{X/B}` is an algebraic space locally of
finite presentation over `B` (Quot, Proposition 0D01).  Stacks 0DM8 assumes moreover that `f` is
**proper** as well as of finite presentation, and concludes that

`Hilb_{X/B} ⟶ B` satisfies the existence part of the valuative criterion

in the sense of Morphisms of Spaces, Definition 03IX: every solid square whose left column is
`Spec K ⟶ Spec A` for a valuation ring `A` with fraction field `K`, whose top edge lands in
`Hilb_{X/B}` and whose bottom edge lands in `B`, acquires a dotted arrow `Spec A' ⟶ Hilb_{X/B}`
after replacing `A` by a valuation ring `A'` dominating it in an extension `K'/K`.  The source's
proof is two sentences: `Hilb_{X/B} = Quot_{𝒪_X/X/B}` by Quot, Lemma 0D00, and
`Quot_{F/X/B} ⟶ B` satisfies the existence part by Lemma 0DM4.

That deduction is what this file carries out, for an arbitrary model of the Hilbert presheaf, and
it is the same transport the file on Stacks 0D01 performs for algebraicity.  Both of its inputs
are absent from the library and are therefore hypotheses; see "What is and is not proved".

## Main results

* `AlgebraicGeometry.Space.valuativeCriterionExistence_of_isoOver`: the existence part of the
  valuative criterion is invariant under an isomorphism of the source over the target.
* `AlgebraicGeometry.Space.HilbertPresheafModel.isoOf` and
  `AlgebraicGeometry.Space.HilbertPresheafModel.isoOf_hom_comp_toBase`: any two models of the
  Hilbert presheaf are isomorphic over the base.
* `AlgebraicGeometry.Space.valuativeCriterionExistence_toBase_of_model`: the existence part for
  the Hilbert presheaf does not depend on the model chosen.
* `AlgebraicGeometry.Space.valuativeCriterionExistence_hilbertPresheafModel_toBase`:
  **Stacks 0DM8**, the existence part of the valuative criterion for `Hilb_{X/B} ⟶ B`.
* `StacksDraft.GenericFibre.existsUnique_submodule_structureSheaf_flat_quotient`:
  **Stacks 0DM8** on an affine chart over a valuation ring — the structure-sheaf case of the
  chart-wise extension that the source's Lemma 0DM4 constructs and glues.

## Implementation notes

**The universe lift.**  A section of the Hilbert presheaf over a scheme of the site is a closed
subfunctor of a base change of `X`, so it lives one universe above the sections of an algebraic
space, and `AlgebraicGeometry.Space.ValuativeCriterion.Existence` of Stacks 03IX is stated for
morphisms of presheaves of `Type u`.  The statement of Stacks 0DM8 is therefore about the
canonical morphism to the base of an `AlgebraicGeometry.Space.HilbertPresheafModel`, exactly as
the statement of Stacks 0D01 is.  That this is a property of the Hilbert presheaf and not of the
chosen model is `AlgebraicGeometry.Space.valuativeCriterionExistence_toBase_of_model`: the
universe lift is fully faithful, so an isomorphism of the lifts of two models descends to an
isomorphism of the models, and `AlgebraicGeometry.Space.descendULift` is that descent.

**The transport.**  Invariance of the existence part under an isomorphism of the source over the
target is the base-change statement Stacks 03IY applied to the cartesian square whose horizontal
edges are the isomorphism and the identity of the target.

## What is and is not proved

Stacks 0DM8 is **not** proved; its two inputs are carried, in the form the source's proof
consumes them, and both are named here.

* Stacks 0DM4, the existence part for `Quot_{F/X/B} ⟶ B`, is the hypothesis `hex`: the existence
  part for the canonical morphism to `B` of a model `N` of the Quot presheaf.  What the library
  has of Stacks 0DM4 is its affine-chart case, in
  `StacksFrontier/AlgebraicGeometry/Quot/QuotValuativeAffineChart.lean`; the implementation notes
  there record what is missing, namely the étale gluing of the chart-wise extensions (Stacks
  03M3), the finite presentation of the extension (Stacks 0DLR) and the properness of its
  support.  The structure-sheaf case of that chart-wise statement — the case `F = 𝒪_X` which is
  the one Stacks 0DM8 uses — is proved below.
* Stacks 0D00, the identification `Hilb_{X/B} = Quot_{𝒪_X/X/B}`, is `e` together with `he`.  The
  implementation notes of
  `StacksFrontier/AlgebraicGeometry/Quot/HilbertFunctorAlgebraicSpace.lean` record which entries of
  its dictionary are in the library and which are not.

Because the carried `hex` is the existence part for a presheaf that `e` identifies with the
Hilbert presheaf, it is inter-derivable with the conclusion *given* `e` and `he`; this is
unavoidable here, the source's proof being exactly that transport, and it is why the unconditional
content of this file is the transport itself, the model-independence, and the chart-wise
structure-sheaf extension.

## References

* [Stacks Project, Tag 0DM8](https://stacks.math.columbia.edu/tag/0DM8)
* [Stacks Project, Tag 0DM4](https://stacks.math.columbia.edu/tag/0DM4)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 03IY](https://stacks.math.columbia.edu/tag/03IY)
* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped nonZeroDivisors

universe u v w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The existence part transports along an isomorphism over the target -/

/-- **The existence part of the valuative criterion is invariant under an isomorphism of the
source over the target.**  If `α : F ≅ G` satisfies `α.hom ≫ q = p` and `q` satisfies the
existence part, so does `p`.

This is Stacks 03IY, the stability of the existence part under base change, applied to the
cartesian square whose horizontal edges are `α.hom` and the identity of the target: a square with
two isomorphisms as its horizontal edges is cartesian. -/
theorem valuativeCriterionExistence_of_isoOver {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ H} {q : G ⟶ H} (α : F ≅ G) (hα : α.hom ≫ q = p)
    (hq : ValuativeCriterion.Existence q) : ValuativeCriterion.Existence p :=
  valuativeCriterion_existence_of_isPullback
    (IsPullback.of_horiz_isIso ⟨by rw [hα, Category.comp_id]⟩) hq

/-! ### Descending a morphism along the universe lift -/

/-- The morphism of presheaves of `Type u` underlying a morphism of their universe lifts.  The
universe lift of presheaves is fully faithful, and this is the inverse of its action on
morphisms, written out. -/
def descendULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⋙ uliftFunctor.{u + 1, u} ⟶ G ⋙ uliftFunctor.{u + 1, u}) : F ⟶ G where
  app T := ↾fun z ↦ (p.app T ⟨z⟩).down
  naturality {T T'} g := by
    ext z
    have h := types_congr_hom (p.naturality g) (ULift.up.{u + 1} z)
    exact congrArg ULift.down h

/-- Descending the universe lift takes composites to composites. -/
theorem descendULift_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⋙ uliftFunctor.{u + 1, u} ⟶ G ⋙ uliftFunctor.{u + 1, u})
    (q : G ⋙ uliftFunctor.{u + 1, u} ⟶ H ⋙ uliftFunctor.{u + 1, u}) :
    descendULift p ≫ descendULift q = descendULift (p ≫ q) := by
  ext T z
  rfl

/-- Descending the universe lift takes the identity to the identity. -/
theorem descendULift_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    descendULift (𝟙 (F ⋙ uliftFunctor.{u + 1, u})) = 𝟙 F := by
  ext T z
  rfl

/-- An isomorphism of the universe lifts of two presheaves of `Type u` descends to an isomorphism
of the presheaves themselves. -/
def isoOfULiftIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⋙ uliftFunctor.{u + 1, u} ≅ G ⋙ uliftFunctor.{u + 1, u}) : F ≅ G where
  hom := descendULift α.hom
  inv := descendULift α.inv
  hom_inv_id := by rw [descendULift_comp, α.hom_inv_id, descendULift_id]
  inv_hom_id := by rw [descendULift_comp, α.inv_hom_id, descendULift_id]

/-! ### The existence part is a property of the Hilbert presheaf -/

namespace HilbertPresheafModel

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}

/-- Any two models of the Hilbert presheaf of `f` are isomorphic: their universe lifts are both
isomorphic to the Hilbert presheaf, and such an isomorphism descends. -/
def isoOf (M N : HilbertPresheafModel f) : M.presheaf ≅ N.presheaf :=
  isoOfULiftIso (M.iso ≪≫ N.iso.symm)

/-- The isomorphism of two models of the Hilbert presheaf lies over the base: it carries the
canonical morphism to the base of one model to that of the other.  Both are read off through the
identifying isomorphisms with the Hilbert presheaf, and the comparison is `N.iso.inv ≫ N.iso.hom`
being the identity. -/
theorem isoOf_hom_comp_toBase (M N : HilbertPresheafModel f) :
    (M.isoOf N).hom ≫ N.toBase = M.toBase := by
  ext T z
  refine congrArg (fun x ↦ ((hilbertPresheafToBase f).app T x).down) ?_
  show (M.iso.hom ≫ N.iso.inv ≫ N.iso.hom).app T ⟨z⟩ = M.iso.hom.app T ⟨z⟩
  rw [N.iso.inv_hom_id, Category.comp_id]

end HilbertPresheafModel

/-- **The existence part of the valuative criterion for the Hilbert presheaf does not depend on
the model chosen.**  Any two models are isomorphic over the base, by
`AlgebraicGeometry.Space.HilbertPresheafModel.isoOf_hom_comp_toBase`, and the existence part
transports along such an isomorphism. -/
theorem valuativeCriterionExistence_toBase_of_model {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (M N : HilbertPresheafModel f) (h : ValuativeCriterion.Existence N.toBase) :
    ValuativeCriterion.Existence M.toBase :=
  valuativeCriterionExistence_of_isoOver (M.isoOf N) (M.isoOf_hom_comp_toBase N) h

/-! ### Stacks 0DM8 -/

/-- **Stacks 0DM8.**  For a morphism `f : X ⟶ B` of algebraic spaces over `S` which is proper as
well as of finite presentation, `Hilb_{X/B} ⟶ B` satisfies the existence part of the valuative
criterion of Morphisms of Spaces, Definition 03IX: every model of the Hilbert presheaf has it for
its canonical morphism to `B`.

This is the source's deduction from Quot, Lemma 0D00 and Lemma 0DM4, both of which are carried as
hypotheses because neither is in the library.  Lemma 0DM4 is `N` together with `hex`: a model of
the Quot presheaf of a situation on `f` whose morphism to `B` satisfies the existence part.
Lemma 0D00 is `e` together with `he`: an isomorphism of the Hilbert presheaf with that Quot
presheaf, compatible with the two canonical morphisms to `B`.  The source's hypotheses that `f`
be proper and of finite presentation are recorded as `_hproper` and `_hfp`; the deduction itself
does not consume them, since they enter through Lemma 0DM4, which is carried.  The content
delivered is the transport: the Quot model is a model of the Hilbert presheaf through `e` with the
same morphism to `B`, and the existence part is independent of the model. -/
@[stacks 0DM8 "the existence part of the valuative criterion for `Hilb_{X/B} ⟶ B`, for any model \
of the Hilbert presheaf. WARNING, stated plainly: given the carried `e`, `he` (Lemma 0D00) the \
carried `hex` (Lemma 0DM4 for `Quot_{F/X/B} ⟶ B`) is INTER-DERIVABLE with the conclusion, the \
identification making the transport run both ways, so this statement's content is the transport \
and the model-independence, not the criterion. The unconditional results are the ones to cite"]
theorem valuativeCriterionExistence_hilbertPresheafModel_toBase {X : AlgebraicSpaces B S hS}
    (D : QuotSituation B S hS) (f : X ⟶ D.Y)
    (_hproper : IsProper B S hS f.hom) (_hfp : IsFinitePresentation B S hS f.hom)
    (N : QuotSitePresheafModel D) (hex : ValuativeCriterion.Existence N.toBase)
    (e : hilbertPresheaf f ≅ D.quotSitePresheaf)
    (he : e.hom ≫ D.quotSitePresheafToBase = hilbertPresheafToBase f)
    (M : HilbertPresheafModel f) :
    ValuativeCriterion.Existence M.toBase := by
  refine valuativeCriterionExistence_toBase_of_model M ⟨N.presheaf, N.iso ≪≫ e.symm⟩ ?_
  rw [HilbertPresheafModel.toBase_eq_of_iso D f N e he]
  exact hex

end AlgebraicGeometry.Space

namespace StacksDraft.GenericFibre

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {AK : Type w} [AddCommGroup AK] [Module R AK] [Module A AK] [IsScalarTower R A AK]
  {ι : A →ₗ[A] AK} [IsLocalizedModule R⁰ (ι.restrictScalars R)] {P : Submodule A AK}

/-- **Stacks 0DM8 on an affine chart over a valuation ring.**  Let `R` be a valuation ring, `A`
an `R`-algebra — the ring of an affine chart of `X` — and `A_K` the generic fibre of `A`, that is,
its localization at the nonzero elements of `R`.  Let `P` be an ideal of `A_K` saturated for the
nonzero elements of `R`, that is, the ideal of a closed subscheme of the generic fibre.  Then
there is exactly one ideal `L` of `A` such that `A / L` is flat over `R` and the generic fibre of
`L` is `P`: the closed subscheme of the generic fibre extends uniquely to a closed subscheme of
the chart flat over the valuation ring, and the extension is cut out by the generic kernel
`{x ∈ A | ι x ∈ P}`.

This is the case `F = 𝒪_X` of the chart-wise construction of Lemma 0DM4 — the case Stacks 0DM8
uses, via the identification `Hilb_{X/B} = Quot_{𝒪_X/X/B}` of Quot, Lemma 0D00, under which a
family classified by `Hilb_{X/B}` is the quotient of the structure sheaf by the ideal of a closed
subspace.  It is stated with no finiteness condition on the quotient, which for an ideal of `A` is
automatic, so its uniqueness clause is stronger than that of
`StacksDraft.GenericFibre.existsUnique_submodule_flat_quotient`; flatness over `R` comes from
torsion freeness, which is Stacks 0539.

The gluing of these chart-wise extensions, the properness of the support of the glued extension
and its finite presentation are not proved — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/QuotValuativeAffineChart.lean` — so this does not discharge
the hypothesis `hex` of
`AlgebraicGeometry.Space.valuativeCriterionExistence_hilbertPresheafModel_toBase`. -/
@[stacks 0DM8 "the affine-chart case over a valuation ring: a closed subscheme of the generic \
fibre of an affine chart extends uniquely to one flat over the valuation ring, the extension \
being the generic-kernel ideal; the etale gluing, the proper support and the finite presentation \
of the glued extension, and hence the valuative criterion itself, are not covered here",
  ega "IV 2.8.1" "special case"]
theorem existsUnique_submodule_structureSheaf_flat_quotient
    (hP : ∀ (s : R) {y : AK}, s ≠ 0 → s • y ∈ P → y ∈ P) :
    ∃! L : Submodule A A, Module.Flat R (A ⧸ L) ∧
      Submodule.localized₀ R⁰ (ι.restrictScalars R) (L.restrictScalars R)
        = P.restrictScalars R := by
  refine ⟨P.comap ι, ⟨flat_of_isTorsionFree _ (isTorsionFree_quotient_comap hP),
    localized₀_restrictScalars_comap hP⟩, ?_⟩
  rintro L ⟨hflat, hL⟩
  have : Module.Flat R (A ⧸ L) := hflat
  exact comap_eq_of_isTorsionFree_of_localized₀_eq L Module.Flat.isTorsionFree hL

end StacksDraft.GenericFibre

end
