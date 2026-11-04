module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf

/-!
# The universal property of the integral closure of the structure sheaf

Let `F` be an algebraic space over `S` and let `A` be a sheaf of commutative `𝒪_F`-algebras on
its small étale site.  `AlgebraicGeometry.Space.AlgebraSheaf.integralClosureSheaf` is the
subalgebra of locally integral sections of `A`.  This file proves that it absorbs every
algebra sheaf mapping into `A` whose own structure-algebra map is integral on affine charts, in
the sense of `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral`: such a morphism factors
through the integral closure, and through it in exactly one way.

This is the step "`χ(ℬ) ⊂ 𝒪'`" of the proof of Stacks 0823, where `ℬ` is the quasi-coherent
algebra of an integral morphism `Z ⟶ X` and `χ : ℬ ⟶ f_*𝒪_Y` is the algebra map of a
factorization of `f` through `Z`.  Nothing here carries a Stacks tag: Stacks 0820 asserts the
existence of the subalgebra and computes its sections on affine charts, and Stacks 0823 is the
universal property of the *relative normalization*, not of the subalgebra; what is proved here
is neither statement.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.mem_locallyIntegralSections_of_isIntegral`: the image
  of a section of an integral algebra sheaf under a morphism into `A` is a locally integral
  section of `A`.  The chart is arbitrary; integrality of the source is only assumed on affine
  charts, and the passage between the two is the cover-density of the affine étale charts.
* `AlgebraicGeometry.Space.AlgebraSheaf.existsUnique_hom_integralClosureSheaf`: a morphism of
  algebra sheaves out of an integral algebra sheaf factors through
  `AlgebraicGeometry.Space.AlgebraSheaf.integralClosureInclusion` in exactly one way.
* `AlgebraicGeometry.Space.AlgebraSheaf.locallyIntegralSections_eq_top_of_isIntegral`: an
  integral algebra sheaf is its own integral closure, every section over every chart being
  locally integral.
* `AlgebraicGeometry.Space.AlgebraSheaf.isIntegral_ofHom_id`: the structure sheaf, read as an
  algebra over itself, is an integral algebra sheaf.  This exhibits an inhabitant of the
  hypothesis of the results above, so that none of them is vacuous.

## Implementation notes

**Why the conclusion is about locally integral sections over an arbitrary chart.**
`AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral` quantifies over the *affine* étale charts
only — that is how Stacks 03ZP reads integrality of a morphism of algebraic spaces — while the
sections of the integral closure over an arbitrary chart are the locally integral ones.  The
bridge is `AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`, Stacks 04JS:
the affine étale charts are a dense subsite, so `CategoryTheory.Sieve.coverByImage` of their
inclusion is a covering sieve of every chart.  The extraction of
`CategoryTheory.Functor.IsCoverDense` from that tag is kept as a one-line `have` rather than a
declaration of its own, because
`AlgebraicGeometry.Space.SmallEtale.isCoverDense_affineEtaleInclusion` already states it in
`StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison`, with a body identical to the one
used here; that module is not imported only because its own import closure is much the larger
of the two.  An arrow in the covering sieve factors through an affine
chart, the image section restricts to an integral section there because the source algebra is
integral, and a further restriction of an integral section is integral
(`AlgebraicGeometry.Space.AlgebraSheaf.map_mem_integralSections`); so the covering sieve is
contained in the sieve of arrows along which the image section becomes integral, which is
exactly what being locally integral means.

The factorization is forced rather than chosen: the inclusion is injective on the sections over
every chart, so uniqueness is `Subtype.val_injective` and the factoring morphism is the
corestriction of the given one.  No universal property of a sheafification is used — the
sections of the integral closure over a chart are a subring of the sections of `A` over that
chart, by construction.

Integrality here is transported with `AlgebraicGeometry.Space.AlgebraSheaf.isIntegralElem_map`
along the *identity* of the structure sheaf's sections, the commuting square being
`AlgebraicGeometry.Space.AlgebraSheaf.comp_algebraMap`: a morphism of algebra sheaves carries
the structure-algebra map of its source to that of its target, so it carries elements integral
over the first to elements integral over the second.

## References

* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The image of a section of an integral algebra sheaf under a morphism of algebra sheaves is
an integral section of the target over every *affine* chart.

A morphism of algebra sheaves carries the structure-algebra map of its source to that of its
target, so it carries an element integral over the first to one integral over the second; the
elements of the source are all integral over its structure-algebra map because the chart is
affine. -/
theorem mem_integralSections_of_isIntegral {A C : AlgebraSheaf.{u, m} B S hS F hF}
    (φ : C ⟶ A) (hC : C.IsIntegral) (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (c : C.right.obj.obj (op U)) :
    (φ.right.hom.app (op U)).hom c ∈ A.integralSections (op U) :=
  mem_integralSections.2
    (isIntegralElem_map (RingHom.id _) ((φ.right.hom.app (op U)).hom)
      (((comp_algebraMap φ (op U)).trans (RingHom.comp_id _).symm))
      (hC U hU c))

/-- **The image of an integral algebra sheaf is locally integral.**  If `C` is an integral
algebra sheaf, then the image of any of its sections under a morphism `φ : C ⟶ A` is a locally
integral section of `A`, over an *arbitrary* chart.

The affine charts are cover-dense by Stacks 04JS, so the arrows factoring through an affine
chart cover.  Along such an arrow the image section restricts to an integral section — first
restricting to the affine chart, where `mem_integralSections_of_isIntegral` applies, and then
further, which preserves integrality. -/
theorem mem_locallyIntegralSections_of_isIntegral {A C : AlgebraSheaf.{u, m} B S hS F hF}
    (φ : C ⟶ A) (hC : C.IsIntegral) (U : (SmallEtale B S hS F)ᵒᵖ)
    (c : C.right.obj.obj U) :
    (φ.right.hom.app U).hom c ∈ A.locallyIntegralSections U := by
  have hdense : (AffineEtale.inclusion B S hS F).IsCoverDense (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2.isCoverDense'
  refine mem_locallyIntegralSections.2 ((SmallEtale.topology B S hS F).superset_covering ?_
    (hdense.is_cover (unop U)))
  rintro V f ⟨⟨W, lift, map, rfl⟩⟩
  rw [sieveOfSection_integralSubfunctor_apply, op_comp, A.right.obj.map_comp,
    CommRingCat.comp_apply]
  have hnat := ConcreteCategory.congr_hom (φ.right.hom.naturality map.op) c
  simp only [CommRingCat.comp_apply] at hnat
  rw [← hnat]
  exact A.map_mem_integralSections lift.op
    (mem_integralSections_of_isIntegral φ hC W.obj W.property _)

/-- **An integral algebra sheaf is its own integral closure.**  Every section of an integral
algebra sheaf over every chart is locally integral over the structure sheaf, so the subring of
locally integral sections is everything. -/
theorem locallyIntegralSections_eq_top_of_isIntegral {A : AlgebraSheaf.{u, m} B S hS F hF}
    (hA : A.IsIntegral) (U : (SmallEtale B S hS F)ᵒᵖ) :
    A.locallyIntegralSections U = ⊤ :=
  eq_top_iff.2 fun a _ => mem_locallyIntegralSections_of_isIntegral (𝟙 A) hA U a

/-- **The universal property of the integral closure.**  A morphism of algebra sheaves out of
an integral algebra sheaf factors through the integral closure of the structure sheaf in the
target, and through it in exactly one way.

This is the step of the proof of Stacks 0823 which places the algebra of an integral
factorization inside the integral closure. -/
theorem existsUnique_hom_integralClosureSheaf {A C : AlgebraSheaf.{u, m} B S hS F hF}
    (φ : C ⟶ A) (hC : C.IsIntegral) :
    ∃! ψ : C ⟶ integralClosureSheaf A, ψ ≫ integralClosureInclusion A = φ := by
  obtain ⟨ψ₀, hψ₀⟩ :
      ∃ ψ : C ⟶ integralClosureSheaf A, ψ ≫ integralClosureInclusion A = φ := by
    refine ⟨{ right :=
              { hom :=
                  { app := fun U => ConcreteCategory.ofHom
                      (((φ.right.hom.app U).hom).codRestrict
                        (A.locallyIntegralSections U)
                        (mem_locallyIntegralSections_of_isIntegral φ hC U))
                    naturality := fun U V i => by
                      ext c
                      exact Subtype.ext
                        (ConcreteCategory.congr_hom (φ.right.hom.naturality i) c) } }
              comm := fun U r => Subtype.ext (φ.comm U r) }, ?_⟩
    refine Hom.ext ?_
    ext U c
    rfl
  refine ⟨ψ₀, hψ₀, fun ψ hψ => ?_⟩
  refine Hom.ext ((cancel_mono (integralClosureInclusion A).right).1 ?_)
  rw [← comp_right, ← comp_right, hψ, hψ₀]

/-- **The structure sheaf is an integral algebra over itself.**  Its structure-algebra map is
the identity, and every element is integral over the identity: it is a root of `X - C x`.

This exhibits an inhabitant of `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral`, so the
hypothesis of the results above is satisfiable and none of them is vacuous. -/
theorem isIntegral_ofHom_id :
    (AlgebraSheaf.ofHom (hF := hF) (𝟙 (structureSheaf B S hS F hF))).IsIntegral :=
  fun _ _ x => isIntegralElem_apply _ x

end AlgebraSheaf

end AlgebraicGeometry.Space

end
