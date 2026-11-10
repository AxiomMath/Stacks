module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Completion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit

/-!
# The Čech completion as a derived limit of derived tensor products with duals

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `K ∈ D(𝒪)`.
The completion functor of [Stacks, Tag 099B] attached to `f_1, …, f_r` is
`K ↦ K^∧ = R𝑆heafHom_𝒪(Č(f), K)`, derived internal Hom out of the extended alternating Čech
complex. [Stacks, Tag 0A0E] asserts that this object is computed as

`K^∧ = R lim (K ⊗^𝐋_𝒪 K_n)`, `K_n = K(𝒪, f_1^n, …, f_r^n)`,

the derived limit of the tower of derived tensor products with the Koszul complexes on the
powers of the chosen sections.

This file records the two statements about that formula which do not need the Koszul complexes
of sheaves: that its right-hand side exists for an arbitrary inverse system, and that the
formula holds for the Čech completion as soon as the system presents `Č(f)` as a derived
colimit.

## Main results

* `AlgebraicGeometry.RingedSite.exists_isDerivedLimit_tensorDerivedDualSystem`: the right-hand
  side of the formula is defined — the inverse system `n ↦ K ⊗^𝐋_𝒪 K_n^∨` has a derived limit
  in `D(𝒪)` for every ringed site and every system `(K_n)`.
* `AlgebraicGeometry.RingedSite.completionFunctor_obj_eq_derivedSheafHom_flip`: the completion
  functor of Tag 099B evaluated at `K` is the object of `D(𝒪)` that the conclusion of
  [Stacks, Tag 0A0A] is about.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_completionFunctor`: the
  formula for the Čech completion, granted a derived-colimit presentation of `Č(f)` by the
  system and clause 3 of [Stacks, Tag 08JJ]. The direct-sum comparison that
  `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit` also
  assumes is discharged here, and nothing is assumed to exist.

## Implementation notes

`R lim` is not a functor here, and the formula is therefore not an equation between terms.
`CategoryTheory.Pretriangulated.IsDerivedLimit` is a predicate, as
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/DerivedLimits.lean`
records: the object completing the Milnor difference map to a distinguished triangle is
determined only up to non-unique isomorphism, so no canonical `R lim : (ℕᵒᵖ ⥤ D(𝒪)) ⥤ D(𝒪)`
exists to write an equation with. The formula is accordingly stated as *`K^∧` is a derived
limit of the tower*, which is how the source's equality is to be read.

The inverse system of the formula is `AlgebraicGeometry.RingedSite.tensorDerivedDualSystem`,
`n ↦ K ⊗^𝐋_𝒪 K_n^∨`, and not `n ↦ K ⊗^𝐋_𝒪 K_n`. The two agree for the Koszul complexes
of [Stacks, Tag 0913], which sit in degrees `0, …, r` there, because their derived duals are
the Koszul complexes in degrees `-r, …, 0`; that identification of `K_n^∨` as a complex is not
in the library, and the dual spelling is the one in which [Stacks, Tag 0A0A] is stated and so
the one Tag 0A0E is recorded in.

The derived limit of the tower exists unconditionally, with no exactness hypothesis on the
countable products of `Mod(𝒪)` — Grothendieck's AB4*, which fails for sheaves of modules —
because `AlgebraicGeometry.RingedSite.exists_isDerivedLimit_ringSheaf` obtains the countable
products of `D(𝒪)` from K-injective resolutions instead.

### What is not proved here, and where tag 0A0E lives

The Koszul complexes are absent from every statement below: the colimit presentation is a
hypothesis here rather than a construction, so the formula below is an instance of
[Stacks, Tag 0A0A] for the Čech complex and carries no 0A0E attribute.

Tag 0A0E itself is proved, for the canonical derived tensor product of [Stacks, Tag 06YU], by
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_canonical`
of `KoszulCechHomotopyColimit.lean` in this directory, which is where the attribute sits. It
does not prove `hdual` below: for the canonical datum that hypothesis is bypassed rather than
discharged, so `hdual` remains unproved as a general clause of [Stacks, Tag 08JJ], exactly as
described in this section.

* **The derived-colimit presentation.** `hcolim` below is [Stacks, Tag 0913] for sheaves on a
  site: that `Č(f)` is the colimit of the Koszul complexes on the powers of `f_1, …, f_r`.
  The Koszul complexes themselves are available —
  `AlgebraicGeometry.RingedSite.koszulPowerComplex` and the sequential diagram
  `AlgebraicGeometry.RingedSite.koszulPowerSystem` of
  `KoszulDerivedCompletion.lean` of this directory build them for an arbitrary ringed site out
  of a finite family of global sections — and so is the comparison with the Čech complex and
  its colimit property, by
  `AlgebraicGeometry.RingedSite.isColimitKoszulPowerFunctorCocone` of
  `KoszulCechComparison.lean`: the system `S ↦ 𝒪` with transition maps `f_{T ∖ S}^{n+1}` has
  the system `S ↦ 𝒪_{f_S}` of `AlgebraicGeometry.RingedSite.awayLocalizationFunctor` as its
  colimit. What is still missing between that and `hcolim` is the passage from a colimit in the
  system indexed by the subsets of `{1, …, r}` to a colimit of the alternating Čech complexes
  built from them — the interchange of the sequential colimit with the finite products
  `CategoryTheory.AlternatingCech.term` — and then
  `DerivedCategory.isHomotopyColimit_Q_obj_colimit` of [Stacks, Tag 0949].
* **The second input of Tag 0A0A.** Of the two inputs that tag's proof needs beyond `hcolim`,
  the direct-sum comparison `R𝑆heafHom_𝒪(⊕ K_n, K) ⟶ ∏ R𝑆heafHom_𝒪(K_n, K)` is **not**
  missing and is not assumed below: it is
  `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomCoproducts.lean`, which
  the statement below applies for itself. What is missing is `hdual`, clause 3 of
  [Stacks, Tag 08JJ], that `K ⊗^𝐋_𝒪 K_n^∨ ⟶ R𝑆heafHom_𝒪(K_n, K)` is invertible for a perfect
  `K_n`: what is proved is its base case and the closure properties of the class of objects at
  which it holds — `isIso_derivedTensorDualToSheafHom_structureSheaf` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedCompositionUnit.lean`,
  together with the dévissage steps of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedTensorDualDevissage.lean`,
  which reach every retract of a finite direct sum of copies of `𝒪` and not the Koszul complexes.
  But the proof of [Stacks, Tag 0A0A] uses that clause only to identify the tower
  `n ↦ K ⊗^𝐋_𝒪 K_n^∨` with the tower
  `n ↦ R𝑆heafHom_𝒪(K_n, K)`, and clause 3 itself — the isomorphism, with both naturalities — is
  in the library for a perfect object by the route of [Stacks, Tag 0ATN], as
  `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso`. So the identification of the two
  towers follows from perfectness of the Koszul complexes alone
  (`AlgebraicGeometry.RingedSite.isPerfect_koszulPowerComplex` of `KoszulPerfect.lean`), which
  is what `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isPerfect` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/DualTensorDerivedLimit.lean` records.

The hypothesis `hdual` is kept below because the statement below holds for an *arbitrary*
derived tensor product datum, which the perfectness route does not reach: the isomorphism of
[Stacks, Tag 0ATN] is stated for the canonical datum.

One statement in the neighbourhood of the tag is still absent, though it is **not** part of
what Tag 0A0E asserts: that `R lim (K ⊗^𝐋_𝒪 K_n)` is derived complete along the ideal sheaf
generated by `f_1, …, f_r`, which is
`Koszul.rlim_derivedTensor_koszulPowers_isDerivedComplete` for modules over a commutative ring.
For the completion `K^∧` that is [Stacks, Tag 099B]; proved directly for the tower it would
need the null-homotopy of multiplication by `f_i` on the Koszul complexes, available only for
modules (`Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator`), and the linearity of
the derived tensor product over `Stacks.SheafOfModules.globalSectionToEnd`, whose absence
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/AdicQuotientReduction.lean`
already records as the reason its own completeness statement is narrowed to nilpotent ideal
sheaves.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The right-hand side of the formula of [Stacks, Tag 0A0E] is defined.** For every inverse
system `(K_n)` of objects of `D(𝒪)` and every `K`, the tower `n ↦ K ⊗^𝐋_𝒪 K_n^∨` has a
derived limit in `D(𝒪)`.

No exactness of the countable products of `Mod(𝒪)` is used: the countable products of `D(𝒪)`
come from K-injective resolutions, through
`AlgebraicGeometry.RingedSite.exists_isDerivedLimit_ringSheaf`. -/
theorem exists_isDerivedLimit_tensorDerivedDualSystem
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ (_ : HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X T F K).obj (op n))
      (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      IsDerivedLimit (tensorDerivedDualSystem X T F K) L :=
  exists_isDerivedLimit_ringSheaf.{u, u, u} X _

variable {r : ℕ} [HasWeakSheafify X.J CommRingCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The completion functor of [Stacks, Tag 099B] is derived internal Hom out of the Čech
complex, read in its second variable.** This is the object that the conclusion of
[Stacks, Tag 0A0A] is about, so it is what lets that tag's formula be stated for `K^∧`. -/
theorem completionFunctor_obj_eq_derivedSheafHom_flip
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (completionFunctor X f).obj K =
      ((derivedSheafHomBifunctor X).flip.obj K).obj
        (op (DerivedCategory.Q.obj (extendedAlternatingCech X f))) :=
  rfl

/-- **The formula of [Stacks, Tag 0A0E] for the Čech completion, from a derived-colimit
presentation of the Čech complex.** Let `(K_n)` be a system of objects of `D(𝒪)` which has the
extended alternating Čech complex of `f_1, …, f_r` as its derived colimit. Then the completion
`K^∧ = R𝑆heafHom_𝒪(Č(f), K)` of [Stacks, Tag 099B] is a derived limit of the tower
`n ↦ K ⊗^𝐋_𝒪 K_n^∨`.

Two hypotheses carry what is not proved. `hcolim` is [Stacks, Tag 0913] for sheaves of
modules on a site, which is where the Koszul complexes would enter and which the library does
not have; `hdual` is clause 3 of [Stacks, Tag 08JJ], that
`K ⊗^𝐋_𝒪 K_n^∨ ⟶ R𝑆heafHom_𝒪(K_n, K)` is invertible. The third input of
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit`, the
invertibility of `R𝑆heafHom_𝒪(⊕ K_n, K) ⟶ ∏ R𝑆heafHom_𝒪(K_n, K)`, is not assumed: it is
discharged by `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison`, through the
primed form
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit'`. Nor is
the existence of the direct sum `⊕ K_n` or of either product assumed; those are supplied by
the instances of [Stacks, Tag 07D9] for the derived category of a Grothendieck abelian
category. With `hcolim` assumed the statement mentions no Koszul complex, which is why it
carries no 0A0E attribute. -/
theorem isDerivedLimit_tensorDerivedDualSystem_completionFunctor
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hdual : ∀ n : ℕ, IsIso (derivedTensorDualToSheafHom X T (F.obj n) K))
    (hcolim : IsHomotopyColimit F
      (DerivedCategory.Q.obj (extendedAlternatingCech X f))) :
    IsDerivedLimit (tensorDerivedDualSystem X T F K) ((completionFunctor X f).obj K) :=
  isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit' X T F K hdual hcolim

end AlgebraicGeometry.RingedSite

end
