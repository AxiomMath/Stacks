module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex of a ringed space, and well-definedness of the derived internal Hom

Let `(X, O_X)` be a ringed space. `StacksDraft.Ch20.Sec41.InternalHomComplex` says what it means
to *realize* the internal Hom complex `SheafHom^•(K, I)` of two complexes of `O_X`-modules and
what it means for a morphism of realizations to be the one induced by morphisms in the two
variables, but constructs nothing. This file supplies a realization for every pair of complexes,
together with its induced maps and their identity and composition laws, and proves that the
induced map is a quasi-isomorphism as soon as both inducing maps are and the complexes in the
covariant variable are K-injective, which is what makes the derived internal Hom well defined.

Nothing is built from scratch here. A topological space with a sheaf of commutative rings *is* a
ringed site,
namely the site of its opens with the open-cover topology, and for a ringed site the internal
Hom complex (`AlgebraicGeometry.RingedSite.sheafHomComplex`), its bifunctorial action
(`Stacks.Cohomology.InternalHom.sheafHomComplexMap`) and the quasi-isomorphism statement
(`Stacks.Cohomology.InternalHom.sheafHomComplexMap_quasiIso`, [Stacks, Tag 0A95]) are all
available. Everything below reads those off along `Stacks.SheafOfModules.ringedSite`.

## Main definitions

* `Stacks.SheafOfModules.ringedSite`: a sheaf of commutative rings on a space, read as a ringed
  site.
* `Stacks.SheafOfModules.ofSite`: site-level internal Hom data read as space-level data.
* `Stacks.SheafOfModules.sheafHomComplexConstruction`: the canonical bifunctorial internal Hom
  complex construction on a ringed space.
* `Stacks.SheafOfModules.sheafHomComplex` and `Stacks.SheafOfModules.sheafHomComplexMap`: the
  resulting internal Hom complex and the map it induces from a morphism in each variable.

## Main results

* `Stacks.SheafOfModules.sheafHomComplexMap_quasiIso` (Stacks 0A8S): a quasi-isomorphism of
  K-injective complexes in the covariant variable and a quasi-isomorphism in the contravariant
  variable induce a quasi-isomorphism of internal Hom complexes.
* `Stacks.SheafOfModules.sheafHomComplexMap_isInduced`,
  `Stacks.SheafOfModules.sheafHomComplexMap_id` and
  `Stacks.SheafOfModules.sheafHomComplexMap_comp`: the local formula for the canonical map and
  its identity and composition laws.

## Implementation notes

The site of opens of `X` with `Opens.grothendieckTopology X` and the sheaf `Rc` assemble into a
`AlgebraicGeometry.RingedSite` whose `ringSheaf` is definitionally `structureSheaf Rc`, whose
category of modules is definitionally `Stacks.SheafOfModules.StructureSheafModules Rc`, and
whose slice-site restriction and section complexes are definitionally those of
`StacksDraft.Ch20.Sec41.InternalHomComplex`. So the two `SheafHomComplex` structures differ in
one respect only: on the site an arrow `W ⟶ U` of the slice over `U` is arbitrary data, whereas
on a space it is `homOfLE` of an inclusion of opens, and two composed inclusions compose to the
transitive one. `ofSite` is where that is discharged, and `ringedSite` is an abbreviation so
that the identifications above remain visible to instance synthesis and to `rw` motive checks;
with those two in place no step below needs a transparency option.

## References

* [Stacks Project, Tag 0A8K](https://stacks.math.columbia.edu/tag/0A8K)
* [Stacks Project, Tag 0A8S](https://stacks.math.columbia.edu/tag/0A8S)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- A sheaf of commutative rings on a topological space, read as a ringed site: the site is the
site of opens of the space with the open-cover topology, and the structure sheaf is the given
sheaf. Its `ringSheaf` is `structureSheaf Rc`. -/
abbrev ringedSite : RingedSite.{u, u, u} where
  C := Opens X
  J := Opens.grothendieckTopology X
  O := Rc

/-- A realization of the internal Hom complex on the ringed site of `X`, read as a realization
on the ringed space `X`. The underlying complex, the section identifications and their
compatibility with scalars are the same data; the compatibility with restriction is the
site-level one along the inclusions, using that composing two inclusions of opens gives the
transitive inclusion. -/
def ofSite (K I : CochainComplex (StructureSheafModules Rc) ℤ)
    (H : RingedSite.SheafHomComplex (ringedSite Rc) K I) : SheafHomComplex Rc K I where
  obj := H.obj
  sectionsIso := H.sectionsIso
  restrict_natural := by
    intro U V hVU n p q hpq s W hWV x
    exact H.restrict_natural (homOfLE hVU) n p q hpq s (homOfLE hWV) x
  smul_natural := by
    intro U r n p q hpq s W hWU x
    exact H.smul_natural U r n p q hpq s (homOfLE hWU) x

/-- The canonical bifunctorial internal Hom complex construction for complexes of modules on a
ringed space: the site-level construction of [Stacks, Tag 0A8Z], with its bifunctorial action,
read on the ringed site of the space. -/
def sheafHomComplexConstruction : SheafHomComplexConstruction Rc where
  complex K I := ofSite Rc K I (RingedSite.sheafHomComplex (ringedSite Rc) K I)
  map {_ _ _ _} g f := Cohomology.InternalHom.sheafHomComplexMap (ringedSite Rc) g f
  map_isInduced g f :=
    (Cohomology.InternalHom.sheafHomComplexConstruction (ringedSite Rc)).map_isInduced g f
  map_id K I :=
    (Cohomology.InternalHom.sheafHomComplexConstruction (ringedSite Rc)).map_id K I
  map_comp g₁ g₂ f₁ f₂ :=
    (Cohomology.InternalHom.sheafHomComplexConstruction (ringedSite Rc)).map_comp g₁ g₂ f₁ f₂

/-- **Stacks 0A8K.** The internal Hom complex `SheafHom•(K, I)` of two complexes of
`O_X`-modules on a ringed space: in degree `n` its sections over an open `U` are the degree-`n`
cochains from `K|_U` to `I|_U`, that is the product over the pairs `p + n = q` of the sections
of `SheafHom(K^p, I^q)`, with the differential `d(f) = d_I ∘ f - (-1)^n f ∘ d_K`. -/
@[stacks 0A8K]
abbrev sheafHomComplex (K I : CochainComplex (StructureSheafModules Rc) ℤ) :
    SheafHomComplex Rc K I :=
  (sheafHomComplexConstruction Rc).complex K I

/-- The canonical map of internal Hom complexes induced contravariantly by `g` and covariantly
by `f`. -/
abbrev sheafHomComplexMap
    {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ} (g : K' ⟶ K) (f : I' ⟶ I) :
    (sheafHomComplex Rc K I').obj ⟶ (sheafHomComplex Rc K' I).obj :=
  (sheafHomComplexConstruction Rc).map g f

/-- On sections over any open, the canonical internal Hom map sends a cochain `z` to
`g ≫ z ≫ f`. -/
theorem sheafHomComplexMap_isInduced
    {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ} (g : K' ⟶ K) (f : I' ⟶ I) :
    SheafHomComplex.IsInducedMap Rc g f (sheafHomComplex Rc K I')
      (sheafHomComplex Rc K' I) (sheafHomComplexMap Rc g f) :=
  (sheafHomComplexConstruction Rc).map_isInduced g f

/-- The canonical internal Hom map induced by identity morphisms is the identity. -/
theorem sheafHomComplexMap_id (K I : CochainComplex (StructureSheafModules Rc) ℤ) :
    sheafHomComplexMap Rc (𝟙 K) (𝟙 I) = 𝟙 (sheafHomComplex Rc K I).obj :=
  (sheafHomComplexConstruction Rc).map_id K I

/-- Canonical internal Hom maps respect simultaneous composition in the two variables. -/
theorem sheafHomComplexMap_comp
    {K₀ K₁ K₂ I₀ I₁ I₂ : CochainComplex (StructureSheafModules Rc) ℤ}
    (g₁ : K₁ ⟶ K₀) (g₂ : K₂ ⟶ K₁) (f₁ : I₀ ⟶ I₁) (f₂ : I₁ ⟶ I₂) :
    sheafHomComplexMap Rc g₁ f₁ ≫ sheafHomComplexMap Rc g₂ f₂ =
      sheafHomComplexMap Rc (g₂ ≫ g₁) (f₁ ≫ f₂) :=
  (sheafHomComplexConstruction Rc).map_comp g₁ g₂ f₁ f₂

/-- **Stacks 0A8S.** A quasi-isomorphism between K-injective complexes, together with a
quasi-isomorphism in the contravariant variable, induces a quasi-isomorphism between the
corresponding canonical internal Hom complexes. This is what makes the derived internal Hom
of complexes of `O_X`-modules well defined. -/
@[stacks 0A8S]
theorem sheafHomComplexMap_quasiIso
    {I' I L' L : CochainComplex (StructureSheafModules Rc) ℤ}
    (i : I' ⟶ I) [QuasiIso i] [I'.IsKInjective] [I.IsKInjective]
    (l : L' ⟶ L) [QuasiIso l] :
    QuasiIso (sheafHomComplexMap Rc l i) :=
  @Cohomology.InternalHom.sheafHomComplexMap_quasiIso (ringedSite Rc) I' I L' L i ‹_› ‹_› ‹_› l ‹_›

end Stacks.SheafOfModules

end
