module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Descent of a morphism of sheaves of algebras along a surjective étale chart

Let `F` be an algebraic space over `S` and let `W` be a *surjective* étale chart of `F`.  The
étale charts of `F` admitting a morphism to `W` form a full subcategory of the small étale site
of `F` which is **cover dense**: an arbitrary chart `V` is covered by `V ×_F W`, and that fibre
product admits a morphism to `W`.  This file proves that observation and three consequences of
it, first for sheaves of commutative rings and then for sheaves of algebras over the structure
sheaf:

* a morphism is *determined* by its restriction to the charts over `W`;
* an arbitrary morphism of the restrictions *descends* to a morphism on the whole site; and
* a morphism whose restriction is invertible is invertible.

The cover-density is `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, which is the
geometric content, read through `CategoryTheory.Sieve.ofObjects`; the three consequences are
Mathlib's comparison lemma for a cover-dense functor,
`CategoryTheory.Functor.IsCoverDense.sheafHom` and its companions, which hold for sheaves valued
in an arbitrary category and therefore apply to `CommRingCat` with no extra input.

## Main definitions

* `AlgebraicGeometry.Space.IsChartOver` and `AlgebraicGeometry.Space.ChartOver`: the étale charts
  of `F` admitting a morphism to a fixed chart `W`, as a full subcategory of the small étale
  site, with `AlgebraicGeometry.Space.chartOverInclusion` the inclusion.
* `AlgebraicGeometry.Space.chartOverBaseHom`: a chosen morphism from a chart over `W` to `W`.
* `AlgebraicGeometry.Space.descChartRingHom`: **the descent of a morphism of sheaves of
  commutative rings** from the charts over a surjective étale chart to the whole small étale
  site.
* `AlgebraicGeometry.Space.descChartAlgebraHom` and
  `AlgebraicGeometry.Space.descChartAlgebraIso`: **the same for sheaves of algebras** over the
  structure sheaf — a morphism, respectively an isomorphism, of the restricted sheaves of rings
  that is compatible with the two structure maps over the charts over `W`.

## Main results

* `AlgebraicGeometry.Space.isCoverDense_chartOverInclusion`: **the charts over a surjective étale
  chart are cover dense in the small étale site.**
* `AlgebraicGeometry.Space.sheafHom_ext_chartOver` and
  `AlgebraicGeometry.Space.algebraHom_ext_chartOver`: a morphism of sheaves of commutative rings,
  respectively of algebra sheaves, is determined by its restriction to the charts over `W`.
* `AlgebraicGeometry.Space.descChartRingHom_restrict`: the descended morphism restricts to the
  one it was built from.
* `AlgebraicGeometry.Space.isIso_descChartRingHom`: it is invertible as soon as the morphism of
  restrictions is.

## Implementation notes

**Why the full subcategory of charts over `W`, and not the small étale site of `W` itself.**
A chart `W` of `F` is a scheme in the site, so it is an algebraic space and
`AlgebraicGeometry.Space.QuasiCoherentDescent.isCoverDense_singleFunctor` would give
cover-density of the charts of `W` in the small étale site of `F`.  That route carries the
induced-category plumbing of
`StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteModel` and reads a chart of
`F` over `W` as a chart of `W`, which is an extra identification at every use.  The full
subcategory used here is the same category up to equivalence and needs none of it: it is a
subcategory of the site the sheaves already live on, so "restriction" is literally
`CategoryTheory.Functor.whiskerLeft` along the inclusion, and local fullness — the second
hypothesis of the comparison lemma — is free, the inclusion of a full subcategory being full.

**The target category is `CommRingCat`, and that costs nothing.**  Mathlib's
`CategoryTheory.Functor.IsCoverDense.sheafHom` is stated for sheaves valued in an arbitrary
category: the gluing happens in the Yoneda image, so no limits in the target are needed.  This is
why no internal-hom sheaf has to be formed here, in contrast with the module-level gluing of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleHomDescent`, which goes through
`Stacks.PresheafOfModules.internalHom` because a morphism of modules is not determined by a
morphism of the underlying sheaves of sets.

**The algebra-level statements are at `AlgebraSheaf.{u, u}`.**  The compatibility of a morphism
with the two structure maps is phrased with
`AlgebraicGeometry.Space.AlgebraSheaf.hom`, the structure map read as a morphism of sheaves of
commutative rings, and that is available only when the algebra's sections lie in the universe of
the schemes.  The sectionwise `comm` field of a morphism of algebra sheaves is then recovered
definitionally, exactly as in `AlgebraicGeometry.Space.AlgebraSheaf.ofUnder`.

**Surjectivity of the chart is not removable.**  Without it the charts over `W` are cover dense
in the small étale site of the open subspace that is the image of `W`, and a morphism of sheaves
on that subspace says nothing about `F`.  Every algebraic space has a surjective étale chart, by
the atlas clause of `AlgebraicGeometry.IsAlgebraicSpace`.

**No `stacks` attribute is carried.**  The geometric input is registered where it is proved —
Stacks 03M0 on `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`'s file — and the
rest is Mathlib's comparison lemma.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (W : SmallEtale B S hS F)

/-! ### The charts over a fixed chart -/

/-- The property of an étale chart of `F` of admitting a morphism to the chart `W`.  Note that
the morphism is not part of the data: this is a property of the chart, so the charts with it form
a *full* subcategory. -/
def IsChartOver : ObjectProperty (SmallEtale B S hS F) := fun V => Nonempty (V ⟶ W)

/-- The étale charts of `F` admitting a morphism to the chart `W`, as a full subcategory of the
small étale site of `F`. -/
abbrev ChartOver := (IsChartOver B S hS F W).FullSubcategory

/-- The inclusion of the charts over `W` into the small étale site of `F`. -/
abbrev chartOverInclusion : ChartOver B S hS F W ⥤ SmallEtale B S hS F :=
  (IsChartOver B S hS F W).ι

/-- A chart over `W` admits a morphism to `W`: its defining property, read as a `Nonempty`. -/
theorem nonempty_hom_chartOver (V : ChartOver B S hS F W) : Nonempty (V.obj ⟶ W) :=
  V.property

/-- A chosen morphism from a chart over `W` to `W`.  Nothing below depends on which morphism it
is: the consumers of this choice are invariant under changing it, which is why the subcategory
can be full. -/
def chartOverBaseHom (V : ChartOver B S hS F W) : V.obj ⟶ W :=
  (nonempty_hom_chartOver B S hS F W V).some

include hF

/-- **The charts over a surjective étale chart are cover dense in the small étale site.**

The sieve of arrows factoring through a chart over `W` contains the sieve
`CategoryTheory.Sieve.ofObjects` of the one-element family `{W}`, which
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective` shows to be covering: a chart
admitting a morphism to `W` is a chart over `W`, and an arrow out of it factors through itself. -/
theorem isCoverDense_chartOverInclusion (hsurj : IsSurjective B S hS W.1.hom) :
    (chartOverInclusion B S hS F W).IsCoverDense (SmallEtale.topology B S hS F) where
  is_cover V := by
    refine (SmallEtale.topology B S hS F).superset_covering ?_
      (SmallEtale.coversTop_of_isSurjective B S hS F hF W hsurj V)
    intro T g hg
    obtain ⟨_i, hTW⟩ := hg
    exact ⟨⟨⟨T, hTW⟩, 𝟙 T, g, Category.id_comp g⟩⟩

/-! ### Sheaves of commutative rings -/

section RingSheaf

variable (hsurj : IsSurjective B S hS W.1.hom)
    {A C : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u}}

include hsurj

/-- **A morphism of sheaves of commutative rings on the small étale site is determined by its
restriction to the charts over a surjective étale chart.** -/
theorem sheafHom_ext_chartOver {φ ψ : A ⟶ C}
    (h : Functor.whiskerLeft (chartOverInclusion B S hS F W).op φ.hom =
      Functor.whiskerLeft (chartOverInclusion B S hS F W).op ψ.hom) :
    φ = ψ := by
  have := isCoverDense_chartOverInclusion B S hS F hF W hsurj
  refine Sheaf.hom_ext ?_
  have h' := congrArg (Functor.IsCoverDense.sheafHom (ℱ' := C)) h
  rwa [Functor.IsCoverDense.sheafHom_eq (chartOverInclusion B S hS F W) (ℱ' := C) φ.hom,
    Functor.IsCoverDense.sheafHom_eq (chartOverInclusion B S hS F W) (ℱ' := C) ψ.hom] at h'

/-- **The descent of a morphism of sheaves of commutative rings along a surjective étale chart.**
A morphism of the restrictions of `A` and `C` to the charts over `W` extends to a morphism
`A ⟶ C` of sheaves on the whole small étale site of `F`, uniquely by
`AlgebraicGeometry.Space.sheafHom_ext_chartOver`. -/
def descChartRingHom
    (α : (chartOverInclusion B S hS F W).op ⋙ A.obj ⟶
      (chartOverInclusion B S hS F W).op ⋙ C.obj) :
    A ⟶ C :=
  haveI := isCoverDense_chartOverInclusion B S hS F hF W hsurj
  ObjectProperty.homMk (Functor.IsCoverDense.sheafHom (ℱ' := C) α)

/-- **The descended morphism restricts to the morphism it was built from.** -/
theorem descChartRingHom_restrict
    (α : (chartOverInclusion B S hS F W).op ⋙ A.obj ⟶
      (chartOverInclusion B S hS F W).op ⋙ C.obj) :
    Functor.whiskerLeft (chartOverInclusion B S hS F W).op
        (descChartRingHom B S hS F hF W hsurj α).hom = α :=
  have := isCoverDense_chartOverInclusion B S hS F hF W hsurj
  Functor.IsCoverDense.sheafHom_restrict_eq (G := chartOverInclusion B S hS F W) (ℱ' := C) α

/-- **A morphism of sheaves of commutative rings whose restriction to the charts over a surjective
étale chart is invertible is invertible.** -/
theorem isIso_of_isIso_restrict_chartOver (φ : A ⟶ C)
    (h : IsIso (Functor.whiskerLeft (chartOverInclusion B S hS F W).op φ.hom)) :
    IsIso φ :=
  have := isCoverDense_chartOverInclusion B S hS F hF W hsurj
  Functor.IsCoverDense.iso_of_restrict_iso (G := chartOverInclusion B S hS F W) φ h

/-- The descent of an invertible morphism of restrictions is invertible. -/
theorem isIso_descChartRingHom
    (α : (chartOverInclusion B S hS F W).op ⋙ A.obj ⟶
      (chartOverInclusion B S hS F W).op ⋙ C.obj) [IsIso α] :
    IsIso (descChartRingHom B S hS F hF W hsurj α) := by
  refine isIso_of_isIso_restrict_chartOver B S hS F hF W hsurj _ ?_
  rw [descChartRingHom_restrict]
  infer_instance

end RingSheaf

/-! ### Sheaves of algebras -/

section AlgebraSheaf

variable (hsurj : IsSurjective B S hS W.1.hom)
    {A C : AlgebraSheaf.{u, u} B S hS F hF}

include hsurj

/-- **A morphism of sheaves of algebras is determined by the restriction of its underlying
morphism of sheaves of rings to the charts over a surjective étale chart.** -/
theorem algebraHom_ext_chartOver {φ ψ : A ⟶ C}
    (h : Functor.whiskerLeft (chartOverInclusion B S hS F W).op φ.right.hom =
      Functor.whiskerLeft (chartOverInclusion B S hS F W).op ψ.right.hom) :
    φ = ψ :=
  AlgebraSheaf.Hom.ext (sheafHom_ext_chartOver B S hS F hF W hsurj h)

/-- The structure map of `A` followed by the descent of a compatible morphism of restrictions is
the structure map of `C`. -/
theorem hom_comp_descChartRingHom
    (α : (chartOverInclusion B S hS F W).op ⋙ A.right.obj ⟶
      (chartOverInclusion B S hS F W).op ⋙ C.right.obj)
    (hα : Functor.whiskerLeft (chartOverInclusion B S hS F W).op A.hom.hom ≫ α =
      Functor.whiskerLeft (chartOverInclusion B S hS F W).op C.hom.hom) :
    A.hom ≫ descChartRingHom B S hS F hF W hsurj α = C.hom := by
  refine sheafHom_ext_chartOver B S hS F hF W hsurj ?_
  change Functor.whiskerLeft (chartOverInclusion B S hS F W).op
    (A.hom.hom ≫ (descChartRingHom B S hS F hF W hsurj α).hom) = _
  rw [Functor.whiskerLeft_comp, descChartRingHom_restrict, hα]

/-- **The descent of a morphism of sheaves of algebras along a surjective étale chart.**  A
morphism of the restricted sheaves of commutative rings that is compatible with the two structure
maps over the charts over `W` extends to a morphism `A ⟶ C` of algebra sheaves, uniquely by
`AlgebraicGeometry.Space.algebraHom_ext_chartOver`. -/
def descChartAlgebraHom
    (α : (chartOverInclusion B S hS F W).op ⋙ A.right.obj ⟶
      (chartOverInclusion B S hS F W).op ⋙ C.right.obj)
    (hα : Functor.whiskerLeft (chartOverInclusion B S hS F W).op A.hom.hom ≫ α =
      Functor.whiskerLeft (chartOverInclusion B S hS F W).op C.hom.hom) :
    A ⟶ C where
  right := descChartRingHom B S hS F hF W hsurj α
  comm U r :=
    congrArg (fun t : structureSheaf B S hS F hF ⟶ C.right => (t.hom.app U).hom r)
      (hom_comp_descChartRingHom B S hS F hF W hsurj α hα)

/-- The underlying morphism of sheaves of rings of `descChartAlgebraHom` is
`descChartRingHom`. -/
@[simp]
theorem descChartAlgebraHom_right
    (α : (chartOverInclusion B S hS F W).op ⋙ A.right.obj ⟶
      (chartOverInclusion B S hS F W).op ⋙ C.right.obj)
    (hα : Functor.whiskerLeft (chartOverInclusion B S hS F W).op A.hom.hom ≫ α =
      Functor.whiskerLeft (chartOverInclusion B S hS F W).op C.hom.hom) :
    (descChartAlgebraHom B S hS F hF W hsurj α hα).right =
      descChartRingHom B S hS F hF W hsurj α :=
  rfl

/-- **The descent of an isomorphism of sheaves of algebras along a surjective étale chart.**  An
isomorphism of the restricted sheaves of commutative rings compatible with the two structure maps
over the charts over `W` is the restriction of an isomorphism `A ≅ C` of algebra sheaves.

This is the shape in which a chartwise identification of two algebras becomes a global one. -/
def descChartAlgebraIso
    (θ : (chartOverInclusion B S hS F W).op ⋙ A.right.obj ≅
      (chartOverInclusion B S hS F W).op ⋙ C.right.obj)
    (hθ : Functor.whiskerLeft (chartOverInclusion B S hS F W).op A.hom.hom ≫ θ.hom =
      Functor.whiskerLeft (chartOverInclusion B S hS F W).op C.hom.hom) :
    A ≅ C where
  hom := descChartAlgebraHom B S hS F hF W hsurj θ.hom hθ
  inv := descChartAlgebraHom B S hS F hF W hsurj θ.inv (by
    rw [← hθ, Category.assoc, θ.hom_inv_id, Category.comp_id])
  hom_inv_id := by
    refine algebraHom_ext_chartOver B S hS F hF W hsurj ?_
    change Functor.whiskerLeft (chartOverInclusion B S hS F W).op
      ((descChartRingHom B S hS F hF W hsurj θ.hom).hom ≫
        (descChartRingHom B S hS F hF W hsurj θ.inv).hom) = _
    rw [Functor.whiskerLeft_comp, descChartRingHom_restrict, descChartRingHom_restrict,
      θ.hom_inv_id]
    rfl
  inv_hom_id := by
    refine algebraHom_ext_chartOver B S hS F hF W hsurj ?_
    change Functor.whiskerLeft (chartOverInclusion B S hS F W).op
      ((descChartRingHom B S hS F hF W hsurj θ.inv).hom ≫
        (descChartRingHom B S hS F hF W hsurj θ.hom).hom) = _
    rw [Functor.whiskerLeft_comp, descChartRingHom_restrict, descChartRingHom_restrict,
      θ.inv_hom_id]
    rfl

/-- The forward morphism of `descChartAlgebraIso` is `descChartAlgebraHom` of the forward
morphism of the given isomorphism. -/
@[simp]
theorem descChartAlgebraIso_hom
    (θ : (chartOverInclusion B S hS F W).op ⋙ A.right.obj ≅
      (chartOverInclusion B S hS F W).op ⋙ C.right.obj)
    (hθ : Functor.whiskerLeft (chartOverInclusion B S hS F W).op A.hom.hom ≫ θ.hom =
      Functor.whiskerLeft (chartOverInclusion B S hS F W).op C.hom.hom) :
    (descChartAlgebraIso B S hS F hF W hsurj θ hθ).hom =
      descChartAlgebraHom B S hS F hF W hsurj θ.hom hθ :=
  rfl

end AlgebraSheaf

end AlgebraicGeometry.Space

end
