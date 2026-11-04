module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernSetup
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaComplexes
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology

/-!
# Local boundedness and finite local freeness on a coproduct of schemes

Let `W : I → Scheme` be a family of schemes and let `P` be a complex of sheaves of modules on
`∐ W`. If the degreewise restriction of `P` to each summand is a locally bounded complex of
finite locally free modules, so is `P`.

Both clauses of `Stacks.Chow.IsLocallyBoundedFiniteLocallyFree` are local conditions and the
summand charts cover `∐ W`, so neither direction of the argument needs a hypothesis on the
family. Finite local freeness of each term is local on the base in the pointwise formulation
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`, which the summand charts witness by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isOpenImmersion_cover`, and that
formulation is the local-generators one of [Stacks, Tag 01C6] (2) by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff`. Boundedness is a condition at each
point separately, so the summand containing the point supplies its own bounds, on the image in
`∐ W` of the open of that summand on which they hold.

## Main results

* `AlgebraicGeometry.isLocallyBoundedFiniteLocallyFree_of_pullback_sigmaι` — a complex on a
  coproduct of schemes whose degreewise restriction to each summand is locally bounded with
  finite locally free terms is itself locally bounded with finite locally free terms.

## Implementation notes

The predicate is phrased through `AlgebraicGeometry.RingedSpace.restrictModules`, restriction
to an open subspace of the coproduct, not through `AlgebraicGeometry.Scheme.Modules.pullback`
along a summand chart. The two are connected by three identifications, each already in the
library: restriction to an open subspace is Mathlib's restriction along the inclusion of that
open subscheme (`Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict`), that
restriction is the pullback (`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), and
restriction along a composite is the composite of restrictions
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`). The open of `∐ W` used at a point of
the summand `W i` is the image `Sigma.ι W i ''ᵁ V` of the open `V` of `W i` the summand
supplies; its inclusion and the composite `V.ι ≫ Sigma.ι W i` have the same range, so they
differ by an isomorphism of schemes, along which the vanishing is transported.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.PseudoCoherence
open AlgebraicGeometry.Scheme.Modules (restrictFunctor restrictFunctorComp restrictFunctorCongr)
open Stacks.AlgebraicGeometry.PerfectCohomology (restrictModulesIsoRestrict)

universe u

namespace AlgebraicGeometry

variable {I : Type u} (W : I → Scheme.{u})

/-- A term of a complex on a coproduct of schemes is finite locally free as soon as its
restriction to each summand is: finite local freeness is local on the base, and the summand
charts cover the coproduct. -/
theorem isFiniteLocallyFree_of_pullback_sigmaι (M : (∐ W : Scheme.{u}).Modules)
    (h : ∀ i, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (Sigma.ι W i)).obj M)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  rw [← Scheme.Modules.isFiniteLocallyFree_iff]
  refine Scheme.Modules.isFiniteLocallyFree_of_isOpenImmersion_cover (fun i => Sigma.ι W i)
    (sigmaOpenCover W).iSup_opensRange fun i => ?_
  exact Scheme.Modules.IsFiniteLocallyFree.of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback (Sigma.ι W i)).app M).symm
    ((Scheme.Modules.isFiniteLocallyFree_iff _).2 (h i))

/-- A sheaf of modules on a coproduct of schemes vanishes on the image of an open of a summand
as soon as its restriction to that summand vanishes on the open. -/
theorem isZero_restrictModules_image_of_isZero (M : (∐ W : Scheme.{u}).Modules) (i : I)
    (V : (W i).Opens)
    (hV : IsZero ((restrictModules (W i).toRingedSpace V).obj
      ((Scheme.Modules.pullback (Sigma.ι W i)).obj M))) :
    IsZero ((restrictModules (∐ W : Scheme.{u}).toRingedSpace (Sigma.ι W i ''ᵁ V)).obj M) := by
  have h0 : IsZero ((restrictFunctor V.ι).obj
      ((Scheme.Modules.pullback (Sigma.ι W i)).obj M)) :=
    hV.of_iso ((restrictModulesIsoRestrict (W i) V).app _).symm
  have h1 : IsZero ((restrictFunctor V.ι).obj ((restrictFunctor (Sigma.ι W i)).obj M)) :=
    h0.of_iso ((restrictFunctor V.ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (Sigma.ι W i)).app M))
  have h2 : IsZero ((restrictFunctor (V.ι ≫ Sigma.ι W i)).obj M) :=
    h1.of_iso ((restrictFunctorComp V.ι (Sigma.ι W i)).app M)
  have hrange : Set.range (Sigma.ι W i ''ᵁ V).ι.base =
      Set.range (V.ι ≫ Sigma.ι W i).base := by
    simp [Set.range_comp]
  let φ : (Sigma.ι W i ''ᵁ V).toScheme ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (Sigma.ι W i ''ᵁ V).ι (V.ι ≫ Sigma.ι W i) hrange
  have hfac : (Sigma.ι W i ''ᵁ V).ι = φ.hom ≫ (V.ι ≫ Sigma.ι W i) :=
    (IsOpenImmersion.isoOfRangeEq_hom_fac (Sigma.ι W i ''ᵁ V).ι (V.ι ≫ Sigma.ι W i)
      hrange).symm
  have h3 : IsZero ((restrictFunctor (Sigma.ι W i ''ᵁ V).ι).obj M) :=
    (Functor.map_isZero (restrictFunctor φ.hom) h2).of_iso
      ((restrictFunctorCongr hfac).app M ≪≫ (restrictFunctorComp φ.hom
        (V.ι ≫ Sigma.ι W i)).app M)
  exact h3.of_iso ((restrictModulesIsoRestrict (∐ W : Scheme.{u}) (Sigma.ι W i ''ᵁ V)).app M)

/-- **Local boundedness with finite locally free terms is detected on the summands of a
coproduct of schemes.** If the degreewise restriction of a complex `P` of sheaves of modules on
`∐ W` to each summand is a locally bounded complex of finite locally free modules, then so is
`P`.

Finite local freeness of each term is local on the base and the summand charts cover `∐ W`.
Local boundedness is a condition at each point separately: a point of `∐ W` lies on exactly one
summand, which supplies an open `V` of itself and bounds valid there, and the image of `V` in
`∐ W` is an open neighbourhood of the point on which the same bounds hold. -/
theorem isLocallyBoundedFiniteLocallyFree_of_pullback_sigmaι
    (P : CochainComplex (∐ W : Scheme.{u}).Modules ℤ)
    (h : ∀ i, Stacks.Chow.IsLocallyBoundedFiniteLocallyFree
      (((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) :
    Stacks.Chow.IsLocallyBoundedFiniteLocallyFree P := by
  refine ⟨fun n => isFiniteLocallyFree_of_pullback_sigmaι W (P.X n) fun i => (h i).1 n,
    fun x => ?_⟩
  obtain ⟨i, y, rfl⟩ := (sigmaOpenCover W).exists_eq x
  obtain ⟨V, hyV, lo, hi, hbd⟩ := (h i).2 y
  exact ⟨Sigma.ι W i ''ᵁ V, ⟨y, hyV, rfl⟩, lo, hi, fun n hn =>
    isZero_restrictModules_image_of_isZero W (P.X n) i V (hbd n hn)⟩

end AlgebraicGeometry

end
