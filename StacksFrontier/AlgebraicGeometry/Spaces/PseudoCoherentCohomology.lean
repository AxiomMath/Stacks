module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a pseudo-coherent complex on an algebraic space is quasi-coherent

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `E` be
an object of `D(𝒪_F)` which is `n`-pseudo-coherent in the sense of Stacks 08FT.  Then `Hⁱ(E)` is
quasi-coherent for every `i > n`.  In particular a pseudo-coherent object of `D(𝒪_F)` lies in
`D_QCoh(𝒪_F)`.  That is Stacks 08JL. The cohomology statement here carries closure hypotheses
beyond the source, so it is untagged. The unconditional assertions are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherentCohomologyUnconditional.lean`.

## Main results

* `SheafOfModules.IsQuasicoherentOnSite.free`: a finite free module is quasi-coherent.
* `SheafOfModules.IsQuasicoherentOnSite.of_isDirectSummandOfFiniteFree`: a direct summand of a
  finite free module is quasi-coherent.
* `SheafOfModules.IsQuasicoherentOnSite.homology`: the cohomology of a complex of quasi-coherent
  modules is quasi-coherent.
* `SheafOfModules.IsQuasicoherentOnSite.homology_isStrictlyPerfect`: the cohomology of a
  strictly perfect complex is quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom` gives
  quasi-coherent cohomology above the approximation degree under closure of quasi-coherence
  under kernels and cokernels on every slice. It is untagged because of these extra hypotheses.

## Closure hypotheses

The cohomology theorem below assumes closure under kernels and cokernels on the slices of the
small étale site. The corresponding unconditional theorem and the assertion that every
pseudo-coherent object lies in the quasi-coherent derived category are proved and registered
with Stacks 08JL in `PseudoCoherentCohomologyUnconditional.lean`.

The hypotheses are not an artefact of the formalization.  They are what turns "the terms of the
strictly perfect model `P` are quasi-coherent" into "`Hⁱ(P)` is quasi-coherent", the cocycles
being a kernel and the cohomology a cokernel, and they are also what makes a direct summand of a
finite free module quasi-coherent.  The source takes both for granted, citing 03M1 implicitly in
"the sheaves `ℰ ⁱ` are direct summands of finite free modules, hence quasi-coherent".  They are
asked for on every slice because the approximation lives on the members of a covering.

What Stacks 03M1 needs.  All four of its clauses reduce, for the small étale site, to
Stacks 03DX, and this development carries 03DX only as the hypothesis
`AlgebraicGeometry.Space.HasAffineChartPresentations` / `HasAffineSlicePresentations` of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentAffineChartPresentation.lean`, never
discharging either: the only theorem concluding one of them trades it for the other.  The kernel
and cokernel clauses are the two without a further mathematical obstruction — unlike closure
under arbitrary direct sums, which cannot be reached by refining coverings, a Grothendieck
topology having no infinite intersections, and unlike closure under extensions, for which
nothing is available at any non-trivial topology — so they are the two that the chart
presentations would settle.

## Implementation notes

Pseudo-coherence is `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` of Stacks 08FT on the
small étale ringed site `AlgebraicGeometry.Space.smallEtaleRingedSite` of `F`, and
quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite` of Stacks 03DL(6).

The argument is the source's, run on the slices of the small étale site rather than on the small
étale sites of the étale charts.  Pseudo-coherence of a representative complex `K` gives, over
each object `U`, a covering on whose members `K` is approximated above degree `n` by a strictly
perfect complex `P` of modules on the slice; `Hⁱ(P) ≅ Hⁱ(K)|_V` for `i > n`, because restriction
to a slice is exact; the terms of `P` are direct summands of finite free modules and hence
quasi-coherent; so `Hⁱ(P)` is quasi-coherent; and quasi-coherence is local, which upgrades the
conclusion from the covering to `Hⁱ(K)` itself.  Working on the slice rather than on the chart's
own small étale site is what makes the comparison of Stacks 04M1 unnecessary here.

What the source supplies beyond this, and what appears as a hypothesis — and so keeps the
Stacks 08JL tag off both theorems, see the section above — is the closure of quasi-coherence
under kernels and cokernels, two of the clauses of Stacks 03M1, needed on each slice of the
site.  They are what turns "the terms of `P` are quasi-coherent" into "the
cohomology of `P` is quasi-coherent", and they are also what makes a direct summand of a finite
free module quasi-coherent: such a summand is the cokernel of `1 - r ∘ i` on the finite free
module.  The finite free module itself is quasi-coherent with no hypothesis, being a finite
product of copies of the structure sheaf, which is `SheafOfModules.isQuasicoherentOnSite_unit`
and the unconditional `SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts`.

The locality step is the quasi-coherence clause of Stacks 03DN,
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`, which
consumes a family covering the final object;
the per-object coverings supplied by pseudo-coherence are collected into such a family by
indexing over all arrows of all the coverings.

The module universe is the universe `u` of the structure rings, as in Stacks 08FT itself: the
strictly perfect local models are built from the structure sheaf, so the sections of the models
and of the structure sheaf live in one universe, and the comparison with the restriction of `K`
puts `K` there too.

## References

* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

universe u v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A finite free module is quasi-coherent: it is a finite coproduct, hence a finite product, of
copies of the structure sheaf, and quasi-coherence contains the structure sheaf and is closed
under finite products. -/
theorem IsQuasicoherentOnSite.free (n : ℕ) :
    (SheafOfModules.free (R := R) (ULift.{u} (Fin n))).IsQuasicoherentOnSite := by
  have : HasFiniteBiproducts (SheafOfModules.{u} R) := Abelian.hasFiniteBiproducts
  have hprod : (isQuasicoherentOnSite.{u₁, v₁, u, u} R)
      (∏ᶜ fun _ : ULift.{u} (Fin n) ↦ SheafOfModules.unit R) :=
    (isQuasicoherentOnSite.{u₁, v₁, u, u} R).prop_product
      fun _ ↦ isQuasicoherentOnSite_unit R
  exact (isQuasicoherentOnSite.{u₁, v₁, u, u} R).prop_of_iso
    ((biproduct.isoProduct fun _ : ULift.{u} (Fin n) ↦ SheafOfModules.unit R).symm ≪≫
      biproduct.isoCoproduct _) hprod

/-- A direct summand of a finite free module is quasi-coherent, as soon as quasi-coherence is
closed under cokernels: a retract `i : M ⟶ O^{⊕n}`, `r : O^{⊕n} ⟶ M` with `i ≫ r = 𝟙` exhibits
`r` as a cokernel of `𝟙 - r ≫ i`, and `O^{⊕n}` is quasi-coherent. -/
theorem IsQuasicoherentOnSite.of_isDirectSummandOfFiniteFree
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [(isQuasicoherentOnSite.{u₁, v₁, u, u} R).IsClosedUnderCokernels]
    {M : SheafOfModules.{u} R} (hM : IsDirectSummandOfFiniteFree R M) :
    M.IsQuasicoherentOnSite := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R M).1 hM
  have hzero : (𝟙 (SheafOfModules.free (R := R) (ULift.{u} (Fin n))) - r ≫ i) ≫ r = 0 := by
    simp [Preadditive.sub_comp, hir]
  have : IsSplitEpi r := ⟨⟨i, hir⟩⟩
  have hcolim : IsColimit (CokernelCofork.ofπ r hzero) := by
    refine Cofork.IsColimit.mk _ (fun s ↦ i ≫ s.π) (fun s ↦ ?_) (fun s t ht ↦ ?_)
    · have hs : (𝟙 (SheafOfModules.free (R := R) (ULift.{u} (Fin n))) - r ≫ i) ≫ s.π = 0 := by
        simp only [CokernelCofork.condition]
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, sub_eq_zero] at hs
      exact hs.symm
    · have ht' : r ≫ t = s.π := ht
      calc t = (i ≫ r) ≫ t := by rw [hir, Category.id_comp]
        _ = i ≫ s.π := by rw [Category.assoc, ht']
  exact (isQuasicoherentOnSite.{u₁, v₁, u, u} R).prop_of_isColimit_cokernelCofork hcolim
    (IsQuasicoherentOnSite.free n) (IsQuasicoherentOnSite.free n)

/-- The cohomology of a complex of quasi-coherent modules is quasi-coherent, as soon as
quasi-coherence is closed under kernels and cokernels: the cocycles are a kernel of a
differential and the cohomology is a cokernel of a map into them. -/
theorem IsQuasicoherentOnSite.homology
    [(isQuasicoherentOnSite.{u₁, v₁, u, u} R).IsClosedUnderKernels]
    [(isQuasicoherentOnSite.{u₁, v₁, u, u} R).IsClosedUnderCokernels]
    (P : CochainComplex (SheafOfModules.{u} R) ℤ)
    (hP : ∀ j : ℤ, (P.X j).IsQuasicoherentOnSite) (i : ℤ) :
    (P.homology i).IsQuasicoherentOnSite := by
  set Q := isQuasicoherentOnSite.{u₁, v₁, u, u} R with hQ
  have hcycles : Q (P.cycles i) :=
    Q.prop_of_isLimit_kernelFork (P.cyclesIsKernel (i := i) (j := i + 1) (by simp))
      (hP i) (hP (i + 1))
  exact Q.prop_of_isColimit_cokernelCofork (P.homologyIsCokernel (i := i - 1) (j := i) (by simp))
    (hP (i - 1)) hcycles

/-- The cohomology of a strictly perfect complex of `R`-modules is quasi-coherent: its terms are
direct summands of finite free modules, hence quasi-coherent, and quasi-coherence is closed
under kernels and cokernels. -/
theorem IsQuasicoherentOnSite.homology_isStrictlyPerfect
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [(isQuasicoherentOnSite.{u₁, v₁, u, u} R).IsClosedUnderKernels]
    [(isQuasicoherentOnSite.{u₁, v₁, u, u} R).IsClosedUnderCokernels]
    (P : CochainComplex (SheafOfModules.{u} R) ℤ) (hP : IsStrictlyPerfect R P) (i : ℤ) :
    (P.homology i).IsQuasicoherentOnSite :=
  IsQuasicoherentOnSite.homology P
    (fun j ↦ IsQuasicoherentOnSite.of_isDirectSummandOfFiniteFree
      (hP.termDirectSummand j)) i

end SheafOfModules

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [∀ V : (smallEtaleRingedSite B S hS F hF).C,
      HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V) AddCommGrpCat.{u}]
    [∀ V : (smallEtaleRingedSite B S hS F hF).C,
      ((smallEtaleRingedSite B S hS F hF).J.over V).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [∀ V : (smallEtaleRingedSite B S hS F hF).C,
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V)).IsClosedUnderKernels]
    [∀ V : (smallEtaleRingedSite B S hS F hF).C,
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V)).IsClosedUnderCokernels]

/-- The cohomology sheaves of an `n`-pseudo-coherent object of `D(𝒪_F)` are quasi-coherent in
every degree strictly greater than `n`, given the closure of quasi-coherence under kernels and
cokernels on every slice of the small étale site.

Those two closure properties are two clauses of Stacks 03M1, which this development does not
have.  Stacks 08JL has no such hypothesis, so this statement is weaker than the source's and is
left untagged; see "Why the two statements of Stacks 08JL carry no tag" in the module
documentation. -/
-- No `@[stacks 08JL]` attribute, deliberately: the two `IsClosedUnder…` instance binders in the
-- section variables are hypotheses Stacks 08JL does not have, and a statement carrying a
-- hypothesis its source lacks must not carry the tag.  The attribute goes on the moment
-- Stacks 03M1 is proved — delete the two binders, and the proof body below is unchanged.
theorem isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (n i : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E n) (hi : n < i) :
    ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) i).obj E).IsQuasicoherentOnSite := by
  classical
  set Y := smallEtaleRingedSite B S hS F hF with hY
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  choose T hT happrox using hK
  -- The arrows of all the coverings, as a family of objects of the site.
  set A := Σ U : Y.C, Σ V : Y.C, {f : V ⟶ U // T U f} with hA
  set Z : A → Y.C := fun a ↦ a.2.1 with hZ
  have hcover : Y.J.CoversTop Z := by
    intro W
    refine Y.J.superset_covering ?_ (hT W)
    rintro P g ⟨V, h, f, hf, rfl⟩
    exact ⟨⟨W, V, f, hf⟩, ⟨h⟩⟩
  have hqc : (K.homology i).IsQuasicoherentOnSite := by
    rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite
      (K.homology i)]
    refine ⟨A, Z, hcover, fun a ↦ ?_⟩
    obtain ⟨P, hP, α, hα, _⟩ := happrox a.1 a.2.2.1 a.2.2.2
    have hiso := hα i hi
    have hhom : (SheafOfModules.overFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (Z a)).PreservesHomology := by
      have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (Z a)) :=
        SheafOfModules.preservesFiniteLimits_overFunctor _ _
      have : (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (Z a)).PreservesEpimorphisms :=
        Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesEpimorphisms (Z a)
      exact Functor.preservesHomology_of_preservesEpis_and_kernels _
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (asIso (HomologicalComplex.homologyMap α i) ≪≫
        (K.sc i).mapHomologyIso (SheafOfModules.overFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (Z a)))
      (SheafOfModules.IsQuasicoherentOnSite.homology_isStrictlyPerfect P hP i)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctorFactors _ i).symm.app K ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e) hqc

end AlgebraicGeometry.Space

end
