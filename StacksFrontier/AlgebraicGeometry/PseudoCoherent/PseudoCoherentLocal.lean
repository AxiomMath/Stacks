module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictRestrictComp

/-!
# Pseudo-coherence is local on the ringed space

Let `X` be a ringed space. An object of `D(𝒪_X)` whose restriction to each member of an open
covering of `X` is `m`-pseudo-coherent is `m`-pseudo-coherent, and likewise for complexes. This is
the statement that lets an argument shrink `X` freely, and it is what both halves of Stacks 09VA
need: the induction there runs on a neighbourhood of a point and has to conclude on `X`.

The content is the descent of a single approximation. Pseudo-coherence over `X|U` produces, near a
point, a strictly perfect complex over a *doubly* restricted space `(X|U)|V`, whereas the local
criterion `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derived_approximation`
(Stacks 08CC part (1)) consumes approximations over opens of `X`. The comparison
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare` moves the approximation to the open `W`
of `X` corresponding to `V`, its compatibility with restriction
(`AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleRestrictIso`) identifies the target, and
it preserves strict perfection
(`AlgebraicGeometry.RingedSpace.CorrespondingOpens.isStrictlyPerfect_compare`) and cohomology.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_local_strictlyPerfect_approximation_of_restrict`: an
  approximation of `𝒦|_U` near a point of `U`, read as an approximation of `𝒦|_W` for an open `W`
  of `X` contained in `U`.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_local`: a complex of
  `𝒪_X`-modules which is `m`-pseudo-coherent on a neighbourhood of every point is
  `m`-pseudo-coherent.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`: an object of `D(𝒪_X)`
  whose restriction to a neighbourhood of every point is `m`-pseudo-coherent is
  `m`-pseudo-coherent.

## Implementation notes

The pair of corresponding opens is `AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofSub`, which
takes `W` to be the image of `V` in `X`; that `x` lies in `W` is exactly that the point of `U`
over `x` lies in `V`.

`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict` uses Stacks 08CC part (2)
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_iso`), not part (1): part (2) takes
an object of the derived category together with an *arbitrary* complex representing it, which is
the situation here, the complex being the restriction to `U` of a chosen representative of `E` on
`X`.

`CategoryTheory.isIso_homologyMap_of_iso` and `CategoryTheory.epi_homologyMap_of_iso` are stated
for an abstract abelian category: in the local contexts occurring below, instance search does not
find `CategoryTheory.quasiIsoAt_of_isIso` for the comparison isomorphism, while applying those two
lemmas is immediate.

The derived categories of `X` and of its open subspaces are hypotheses with independent universes,
as everywhere in this development, and every binder is written at the `StrictlyPerfect.OXMod`
spelling of the category of `𝒪`-modules.

## References

* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.46.9 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u u₁ v₁

/-- Cohomology in a fixed degree carries an isomorphism of complexes to an isomorphism.

Stated separately, for an abstract abelian category, because in the large local contexts of the
proofs about sheaves of modules below the instance `CategoryTheory.quasiIsoAt_of_isIso` is not
found, while applying this lemma is immediate. -/
public theorem CategoryTheory.isIso_homologyMap_of_iso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (e : P ≅ Q) (j : ℤ) :
    IsIso (HomologicalComplex.homologyMap e.hom j) :=
  inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) j).map e.hom))

/-- Cohomology in a fixed degree carries an isomorphism of complexes to an epimorphism; see
`CategoryTheory.isIso_homologyMap_of_iso`. -/
public theorem CategoryTheory.epi_homologyMap_of_iso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (e : P ≅ Q) (j : ℤ) :
    Epi (HomologicalComplex.homologyMap e.hom j) :=
  have : IsIso (HomologicalComplex.homologyMap e.hom j) := isIso_homologyMap_of_iso e j
  IsIso.epi_of_iso _

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-! ### Moving an approximation from a doubly restricted space to an open of `X` -/

/-- The identification of the triple restriction of a complex with its restriction to the
corresponding open of `X`: applying `Φ` degreewise to the restriction to `V` of the restriction to
`U` of a complex `𝒦` of `𝒪_X`-modules gives the restriction of `𝒦` to `W`.

This is `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleRestrictIso` carried to complexes
by `CategoryTheory.Functor.mapHomologicalComplexCompIso`, the pattern of
`AlgebraicGeometry.RingedSpace.restrictComplexOfLEIso`. -/
public def CorrespondingOpens.restrictComplexCompareIso {U : Opens X.carrier}
    (D : CorrespondingOpens X U) (K : CochainComplex (OXMod.{u, u} X) ℤ) :
    (((D.compare).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (restrictComplex (restrictComplex K U) D.sub)) ≅ restrictComplex K D.base :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictModules (X.restrict U.isOpenEmbedding) D.sub ⋙ D.compare))
      (ComplexShape.up ℤ)).app (restrictComplex K U) ≪≫
    (Functor.mapHomologicalComplexCompIso (D.tripleRestrictIso) (ComplexShape.up ℤ)).app K

/-- **An approximation over a doubly restricted space, read over an open of `X`.** Let `𝒦` be a
complex of `𝒪_X`-modules whose restriction to an open `U` of `X` is `m`-pseudo-coherent, and let
`x` be a point of `U`. Then `x` has an open neighbourhood `W` in `X` carrying a strictly perfect
complex and a morphism to `𝒦|_W` which is an isomorphism on cohomology above `m` and an
epimorphism in degree `m`.

The approximation `𝒫 ⟶ (𝒦|_U)|_V` supplied by `m`-pseudo-coherence over `X|U` lives over the
doubly restricted space `(X|U)|V`; `W` is the open of `X` corresponding to `V`, and the
approximation is carried to it by the comparison `Φ`, which preserves strict perfection and
cohomology and matches the two restrictions. -/
public theorem exists_local_strictlyPerfect_approximation_of_restrict
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ) (U : Opens X.carrier)
    (hU : IsPseudoCoherentComplexFrom (restrictComplex K U) m) (x : X.carrier) (hxU : x ∈ U) :
    ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ P' : CochainComplex (OXMod.{u, u} (X.restrict W.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P' ∧
        ∃ β : P' ⟶ restrictComplex K W,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
          Epi (HomologicalComplex.homologyMap β m) := by
  obtain ⟨V, hxV, P, hP, α, hα, hα₀⟩ := hU ⟨x, hxU⟩
  set D := CorrespondingOpens.ofSub U V
  refine ⟨D.base, ⟨⟨x, hxU⟩, hxV, rfl⟩,
    ((D.compare).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    D.isStrictlyPerfect_compare hP,
    ((D.compare).mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫
      (D.restrictComplexCompareIso K).hom, fun j hj => ?_, ?_⟩
  · exact CategoryTheory.isIso_homologyMap_comp _ _ j
      (CategoryTheory.isIso_homologyMap_mapHomologicalComplex (D.compare) α j (hα j hj))
      (CategoryTheory.isIso_homologyMap_of_iso _ j)
  · exact CategoryTheory.epi_homologyMap_comp _ _ m
      (CategoryTheory.epi_homologyMap_mapHomologicalComplex (D.compare) α m hα₀)
      (CategoryTheory.epi_homologyMap_of_iso _ m)

/-! ### Locality -/

/-- **`m`-pseudo-coherence of a complex is local on `X`.** A complex of `𝒪_X`-modules whose
restriction to some open neighbourhood of every point is `m`-pseudo-coherent is itself
`m`-pseudo-coherent.

Each point is supplied with an approximation over an open of `X` by
`AlgebraicGeometry.RingedSpace.exists_local_strictlyPerfect_approximation_of_restrict`, which is
exactly the clause of Stacks 08CB part (1). -/
public theorem isPseudoCoherentComplexFrom_of_local (K : CochainComplex (OXMod.{u, u} X) ℤ)
    (m : ℤ) (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      IsPseudoCoherentComplexFrom (restrictComplex K U) m) :
    IsPseudoCoherentComplexFrom K m := by
  intro x
  obtain ⟨U, hxU, hU⟩ := h x
  exact exists_local_strictlyPerfect_approximation_of_restrict K m U hU x hxU

/-- **`m`-pseudo-coherence in the derived category is local on `X`.** An object `E` of `D(𝒪_X)`
whose derived restriction to some open neighbourhood of every point is `m`-pseudo-coherent is
itself `m`-pseudo-coherent.

Choose a complex `𝒦` representing `E`. Over an open `U` on which `E|_U` is `m`-pseudo-coherent,
the complex `𝒦|_U` represents `E|_U`, so Stacks 08CC part (2) makes `𝒦|_U` an `m`-pseudo-coherent
*complex*; `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_local` then makes `𝒦`
one.

This is the form in which both halves of Stacks 09VA reduce to a neighbourhood of a point: there
the conclusion is local on the target of the closed immersion, while the induction shrinks the
space. -/
public theorem isPseudoCoherentFrom_of_local_restrict [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      IsPseudoCoherentFrom ((derivedRestrictModules X U).obj E) m) :
    IsPseudoCoherentFrom E m := by
  set K := DerivedCategory.Q.objPreimage E
  have e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
  refine ⟨K, isPseudoCoherentComplexFrom_of_local K m fun x => ?_, ⟨e⟩⟩
  obtain ⟨U, hxU, hU⟩ := h x
  refine ⟨U, hxU, isPseudoCoherentComplexFrom_of_iso ((derivedRestrictModules X U).obj E) m hU
    (restrictComplex K U) ?_⟩
  exact (derivedRestrictModulesObjQIso X U K).symm ≪≫ (derivedRestrictModules X U).mapIso e

end AlgebraicGeometry.RingedSpace

end
