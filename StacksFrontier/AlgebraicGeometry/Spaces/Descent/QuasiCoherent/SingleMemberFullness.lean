module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleComparisonRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite

/-!
# Descent of morphisms of modules along a covering with one member

The fullness half of Stacks 04W6,
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq`, consumes the
pairwise condition of Stacks 04W3 as
`AlgebraicGeometry.Space.QuasiCoherentDescent.IsPairwiseCompatible`, an equation on each
pairwise fibre product `Y i ×_X Y j`.  When the index type has at most one element — the
situation of Stacks 03M3, where the covering is the single surjective étale `φ : U ⟶ X` — the
two indices coincide, and the condition is the compatibility of *one* morphism of inverse images
with the canonical comparison of Stacks 04W5 at a pair of morphisms into the one member.  That
is the form supplied here.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.isPairwiseCompatible_of_subsingleton`: for a
  family indexed by a subsingleton, the pairwise condition of Stacks 04W3 follows from the
  compatibility of each member of the family of morphisms with the canonical comparison of
  Stacks 04W5 at an arbitrary pair of morphisms into the corresponding member with equal
  composites to `X`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_subsingleton`:
  **a family of morphisms of inverse images along a covering with at most one member which is
  compatible with the canonical comparison of Stacks 04W5 at every such pair is the family of
  the inverse images of a morphism of `𝒪_X`-modules.**  For a family of relatively representable
  members nothing is carried, by
  `AlgebraicGeometry.Space.QuasiCoherentDescent.pairEtaleRestrictionComp_of_representable`.

## Implementation notes

The hypothesis is stated **one index at a time**, and that is the point of the file.  The
pairwise condition relates the members of the family at two indices, so an equation between
composites of morphisms of modules whose two sides are typed at `f i` and at `f j`; a consumer
with a single morphism `φ` has to identify `f i` with `φ` inside such a composite, and that
single conversion is not affordable — the elaborator exhausts its budget inside one `isDefEq`
on `CategoryTheory.CategoryStruct.comp` at these types.  Identifying the two *indices* first,
by `Subsingleton.elim`, leaves a condition in which the member morphism occurs in one spelling
only, so a consumer matches it with no conversion inside a composite at all; the conversions
that remain for it are at a `CategoryTheory.Functor.map`, at an object of the category of
modules and at propositions, each of which is cheap.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-- **The pairwise condition of Stacks 04W3 for a family indexed by a subsingleton.**  The two
indices of a pairwise fibre product coincide, so the condition is the compatibility of the
member of the family at that one index with the canonical comparison of Stacks 04W5 at the two
projections — which is an instance of the compatibility at an arbitrary pair of morphisms into
the corresponding member of the family with equal composites to `X`. -/
theorem isPairwiseCompatible_of_subsingleton [Subsingleton I]
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hc : ∀ (i : I) (P : AlgebraicSpaces B S hS) (a b : P ⟶ Yi i)
        (hab : a ≫ f i = b ≫ f i),
      (modulePullback B S hS a).map (w i) ≫ (canonicalComparison a b (f i) (f i) hab N).hom =
        (canonicalComparison a b (f i) (f i) hab M).hom ≫
          (modulePullback B S hS b).map (w i)) :
    IsPairwiseCompatible B S hS Yi f w := by
  intro i j
  obtain rfl : j = i := Subsingleton.elim j i
  exact hc j (pair B S hS Yi f j j) (pairFst B S hS Yi f j j) (pairSnd B S hS Yi f j j)
    (pair_condition B S hS Yi f j j)

include hf in
/-- **Descent of morphisms of `𝒪_X`-modules along an étale covering with at most one member.**
A family of morphisms of the inverse images which is compatible with the canonical comparison of
Stacks 04W5 at every pair of morphisms into the corresponding member with equal composites to
`X` is the family of the inverse images of a morphism of `𝒪_X`-modules. -/
theorem exists_modulePullback_map_eq_of_subsingleton [Subsingleton I]
    (hcomp : PairEtaleRestrictionComp B S hS Yi f hf)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hc : ∀ (i : I) (P : AlgebraicSpaces B S hS) (a b : P ⟶ Yi i)
        (hab : a ≫ f i = b ≫ f i),
      (modulePullback B S hS a).map (w i) ≫ (canonicalComparison a b (f i) (f i) hab N).hom =
        (canonicalComparison a b (f i) (f i) hab M).hom ≫
          (modulePullback B S hS b).map (w i)) :
    ∃ χ : M ⟶ N, ∀ i, (modulePullback B S hS (f i)).map χ = w i :=
  exists_modulePullback_map_eq B S hS Yi f hf hcomp hcov w
    (isPairwiseCompatible_of_subsingleton B S hS Yi f w hc)

/-! ### A covering with one member -/

/-- **Descent of morphisms of `𝒪_X`-modules along a single surjective étale morphism.**  A
morphism `ψ` of the two inverse images along `g : Y ⟶ X` whose étale form — the reading of `ψ`
on sections over the charts of `Y`, by Stacks 03LW — is natural in *arbitrary* morphisms of the
induced charts of `X` is the inverse image along `g` of a morphism of `𝒪_X`-modules.

This is the fullness half of Stacks 04W6 for the one-member covering `{g}`, and **nothing is
carried**: the compatibility of the comparison of Stacks 03LU with étale restriction enters the
general statement only in turning the pairwise condition of Stacks 04W3 into that naturality,
which is here a hypothesis.

The naturality is stated on *sections*, and that is what makes the statement reachable.  The
pairwise condition is an equation between composites of morphisms of modules typed at the member
of a family, and a consumer holding a single morphism `g` cannot identify `(fun _ => g) i` with
`g` inside such a composite: the elaborator exhausts its budget inside one `isDefEq` on
`CategoryTheory.CategoryStruct.comp` at these types, and so does the kernel.  On sections the
same identification is a conversion of an application of
`CategoryTheory.Functor.map` and of a module of sections, which is cheap. -/
theorem exists_modulePullback_map_eq_single {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => Y.1) (fun _ => g.hom))
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (ψ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (hnat : ∀ (V V' : SmallEtale B S hS Y.1)
        (k : (smallEtalePostcomp B S hS g hg).obj V' ⟶
          (smallEtalePostcomp B S hS g hg).obj V)
        (t : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS g hg).obj V))),
      (etaleForm B S hS g hg ψ).val.app (.op V') (M.val.map k.op t) =
        N.val.map k.op ((etaleForm B S hS g hg ψ).val.app (.op V) t)) :
    ∃ χ : M ⟶ N, (modulePullback B S hS g).map χ = ψ := by
  have := isCoverDense_memberFunctor B S hS (fun _ : Unit => Y) (fun _ => g) (fun _ => hg) hcov
  have hform := memberChartForm_apply B S hS (fun _ : Unit => Y) (fun _ => g) (fun _ => hg)
    (fun _ => ψ)
  obtain ⟨χ, hχ⟩ := exists_modulePullback_map_eq_of_naturality B S hS (fun _ : Unit => Y)
    (fun _ => g) (fun _ => hg) hcov (fun _ => ψ)
    fun i j V V' k t =>
      (hform j V' (M.val.map k.op t)).trans
        ((hnat V V' k t).trans (congrArg (fun z => N.val.map k.op z) (hform i V t).symm))
  exact ⟨χ, hχ ()⟩

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
