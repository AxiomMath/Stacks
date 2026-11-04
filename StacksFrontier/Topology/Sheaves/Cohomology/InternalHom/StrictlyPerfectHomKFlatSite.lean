module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeStrictlyPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomKFlat

/-!
# Stacks 0GM5 on a ringed site: `SheafHom(E, F)` is K-flat at a strictly perfect `E`

Let `X` be a ringed site and let `E` be a complex of `O`-modules with only finitely many nonzero
terms, each a direct summand of a finite free module — the termwise condition of a strictly
perfect complex. Then the internal Hom complex `SheafHom(E, F)` is K-flat as soon as `F` is.

This is the ringed-site form of **Stacks 0GM5**. The ringed-space form,
`Stacks.SheafOfModules.isKFlat_sheafHomComplex_of_isKFlat`, is already in the library, but a
*slice* of a ringed site is a ringed site and not a ringed space, so the space form does not
reach the localization where the perfect case of Stacks 08DQ needs it. The argument is unchanged
and in fact loses a step: the space form has to compare the Stacks 0BYR comparison on the space
with the Stacks 0BYT interchange morphism of its site of opens
(`Stacks.SheafOfModules.diagonalBetter_eq_tensorHomInterchange`) before it can use the dévissage,
whereas on a site the interchange morphism is the thing itself.

## Main results

* `AlgebraicGeometry.RingedSite.acyclic_sheafHomComplex_of_acyclic`: the internal Hom complex out
  of a complex satisfying the strictly perfect termwise condition, into an acyclic complex, is
  acyclic.
* `AlgebraicGeometry.RingedSite.isKFlat_sheafHomComplex_of_isKFlat`: **Stacks 0GM5 on a ringed
  site.**

## The argument

For an acyclic `G`: `F` is K-flat and `G` is acyclic, so `Tot(G ⊗_O F)` is acyclic; the internal
Hom complex out of a strictly perfect source into an acyclic complex is acyclic, so the target of
the interchange morphism of Stacks 0BYT

`Tot(G ⊗_O SheafHom(E, F)) ⟶ SheafHom(E, Tot(G ⊗_O F))`

is acyclic; that morphism is a quasi-isomorphism at a strictly perfect source of the internal Hom
(`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`); hence its
source is acyclic too, and that source is what K-flatness of `SheafHom(E, F)` asks about.

The two vanishing lemmas the first step needs are already stated for an arbitrary ringed site, in
the ringed-space file: `Stacks.SheafOfModules.internalHomSheaf_isZero_of_isZero_target` and
`Stacks.SheafOfModules.sheafHomComplex_isZero_of_isZero_target`. They are imported rather than
restated.

**Why `X.J.WEqualsLocallyBijective AddCommGrpCat.{u}` is named in the local context.** Nothing is
reproved: the seatings below hand the elaborator the instance that already exists, which on its
own is found in about 1500 heartbeats. The trouble is that `Stacks.SheafOfModules.IsKFlat` is read
through `Stacks.SheafOfModules.KFlat.KFlat`, which asks for
`∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive` and for the family of
`HomologicalComplex.HasMapBifunctor`s; each of those is a *single* synthesis goal inside whose
binder that same search is repeated for every candidate tried, so the 20000-heartbeat budget is
spent before any of them is settled. Named once in the local context, where synthesis finds it
without search, the goals stay inside the budget — the limit itself is untouched, and `letI`
inlines its value, so the statement is the one it would be without it.

## References

* [Stacks Project, Tag 0GM5](https://stacks.math.columbia.edu/tag/0GM5)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.11 (Tag 0BYT)](https://stacks.math.columbia.edu/tag/0BYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite ZeroObject

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u})

/-- The zero morphism from the zero complex to an acyclic complex is a quasi-isomorphism: in
every degree both homologies vanish. -/
private theorem quasiIso_zero_of_acyclic₉
    {T : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hT : T.Acyclic) :
    QuasiIso (0 : (0 : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) ⟶ T) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero _
    ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _) i).isZero_homology)
    (hT i).isZero_homology

/-- **The internal Hom complex out of a strictly perfect complex into an acyclic complex is
acyclic.** The internal Hom complex out of `E` carries a quasi-isomorphism of targets to a
quasi-isomorphism when `E` is bounded with every term a direct summand of a finite free
`O`-module; applying that to the quasi-isomorphism from the zero complex to `T` compares
`SheafHom(E, T)` with `SheafHom(E, 0)`, which vanishes. -/
theorem acyclic_sheafHomComplex_of_acyclic
    (E T : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, IsFiniteFreeSummand X (E.X i))
    (hT : T.Acyclic) :
    (sheafHomComplex X E T).obj.Acyclic := by
  have hq : QuasiIso (0 : (0 : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) ⟶ T) :=
    quasiIso_zero_of_acyclic₉ X hT
  have hmap := homMap_quasiIso_of_isFiniteFreeSummand X (0 : (0 : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) ⟶ T) E hE hterm
  refine (HomologicalComplex.acyclic_iff_of_quasiIso _ hmap).1 ?_
  exact HomologicalComplex.acyclic_of_isZero _
    (Stacks.SheafOfModules.sheafHomComplex_isZero_of_isZero_target X E (isZero_zero _))

/-- **Stacks 0GM5 on a ringed site.** In the situation of Stacks 08DM — `E` with finitely many
nonzero terms, each a direct summand of a finite free module, so that the internal Hom complex
`SheafHom(E, F)` represents `RSheafHom(E, F)` — that complex is K-flat as soon as `F` is.

This is what makes the dual `SheafHom(P, O[0])` of a strictly perfect complex `P` usable as the
K-flat tensor factor in the invertibility criterion for the composition morphism of derived
internal Homs, and so is the input the local step of the third assertion of Stacks 08DQ needs on
the slices of the site. -/
@[stacks 0GM5 "on a ringed site"]
theorem isKFlat_sheafHomComplex_of_isKFlat
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, IsFiniteFreeSummand X (E.X i))
    (hF : letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
      Stacks.SheafOfModules.IsKFlat X.O F) :
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    Stacks.SheafOfModules.IsKFlat X.O (sheafHomComplex X E F).obj := by
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  intro G hG
  have h1 : (tensorTotal X G F).Acyclic :=
    (HomologicalComplex.acyclic_iff_of_quasiIso
      (tensorTotalIsoTensorComplex X G F).hom inferInstance).2 (hF G hG)
  have h2 : (sheafHomComplex X E (tensorTotal X G F)).obj.Acyclic :=
    acyclic_sheafHomComplex_of_acyclic X E _ hE hterm h1
  have h3 : (tensorTotal X G (sheafHomComplex X E F).obj).Acyclic :=
    (HomologicalComplex.acyclic_iff_of_quasiIso _
      (tensorHomInterchange_quasiIso_of_isFiniteFreeSummand X G F E hE hterm)).2 h2
  exact (HomologicalComplex.acyclic_iff_of_quasiIso
    (tensorTotalIsoTensorComplex X G (sheafHomComplex X E F).obj).hom inferInstance).1 h3

end AlgebraicGeometry.RingedSite

end
