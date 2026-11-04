module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDirectSums
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat resolutions of differential graded modules

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it and
let `M` be a right differential graded `A`-module. The source produces a homomorphism
`P → M` of right differential graded `A`-modules which is surjective, which is surjective on
the kernels of the differentials, and whose source is good. It does so by assembling `P` as a
direct sum of elementary pieces, one for each triple `(U, k, x)` with `x` a section of `M^k`
over `U`.

This file carries out the assembly, from a family of flat pieces which it takes as a hypothesis,
and proves all three conclusions for the direct sum. See the implementation notes for exactly
what is and is not proved.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.resolutionOfFamilyHom`: the map `P → M` out of the
  direct sum `P = SheafOfModules.DifferentialGradedModule.directSum` of a family, induced by a
  family of maps to `M`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_resolutionOfFamily`:
  **clause (3)**, in the form conditions (1) and (2) of goodness: the direct sum of flat K-flat
  pieces is flat as a graded module and K-flat.
* `SheafOfModules.DifferentialGradedModule.epi_resolutionOfFamilyHom`: **clause (1)**, `P → M`
  is surjective — an epimorphism of sheaves of modules in every degree.
* `SheafOfModules.DifferentialGradedModule.exists_closed_preimage_resolutionOfFamily`:
  **clause (2)**, every section of `M^n` killed by the differential is the image of a section of
  `P^n` killed by the differential.
* `SheafOfModules.DifferentialGradedModule.exists_resolution_of_generatingFamily` bundles the
  three for one `P`.

## Implementation notes

**What the hypotheses are.** The results below take a family `P : ι → DifferentialGradedModule A`
with maps `ψ i : P i ⟶ M` and three properties: each `P i` is flat as a graded module and
K-flat; every section of `M^n` over every object is the image of a section of some `P i^n` over
that object; and every section of `M^n` over every object which the differential kills is the
image of a section of some `P i^n` which the differential kills. These are exactly the
properties the source establishes for its two families — the `j_{U!}A_U[-k]`, whose generator
`1` is a closed section of degree `k` mapping to a closed `x`, and the `j_{U!}C_U` for `C_U` the
cone on the identity of `A_U`, whose generator maps to an arbitrary `x`. The sectionwise form,
rather than a local one, is what those generators give: the generator is an honest section over
`U` mapping to `x` on the nose.

**Why the family is a hypothesis and not a construction.** Three ingredients of the source's
two families are absent from this library, and each is needed to build them.

1. *Shifts.* The pieces are `j_{U!}A_U[-k]` for every `k ∈ Z`, and this library has no shift of
   a right differential graded module by an arbitrary integer in the present setting: only the
   degree-one shift `SheafOfModules.DifferentialGradedModule.shift`. The degree barrier is
   sharp, not incidental: by
   `SheafOfModules.DifferentialGradedModule.homRegularEquivClosedSections`, composed with the
   Tag 0FRW adjunction `SheafOfModules.dgExtendHomEquiv`, the homomorphisms `j_!A_U ⟶ M` are
   exactly the closed sections of `M` restricted to `U` in degree *zero*. That is forced — such
   a homomorphism is right multiplication by the image of the unit, and the unit of a sheaf of
   differential graded algebras sits in degree zero — so the unshifted piece of Tag 0FSB reaches
   no degree other than zero and no section the differential does not kill.
2. *Flatness of a shift.* Even granted the shift, Tag 0FSB is proved in this library only for the
   unshifted `j_!A_U`
   (`SheafOfModules.dgExtensionByZeroRegular_isGradedFlat` and `..._isKFlat`), and flatness of a
   shift is not available: it needs the degreewise identification of `P[k] ⊗_A N` with a degree
   shift of `P ⊗_A N`, natural in `N`, which is not in the library.
3. *K-flatness of `j_{U!}C_U`.* The source gets goodness of the cone piece from the admissible
   short exact sequence `0 → A_U → C_U → A_U[1] → 0` by Tag 0FSC. This library's Tag 0FSC,
   `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.isGradedFlat_middle` and its
   two siblings, proves condition (1) only; there is no two-out-of-three for K-flatness, so the
   cone piece cannot be shown K-flat.

What *is* available is the other half of the source's argument, and it is what is proved here:
the adjunction `Hom_A(j_{U!}K, N) ≅ Hom_{A_U}(K, N|_U)` of Tag 0FRW
(`SheafOfModules.dgExtendHomEquiv`), the identification of morphisms out of the regular module
with closed global sections
(`SheafOfModules.DifferentialGradedModule.homRegularEquivClosedSections`), and the direct sums
of Tag 0FRJ. So the elementary pieces exist in degree zero; it is their flatness in other
degrees that is missing, and stating the family as a hypothesis is what keeps this file from
special-casing degree zero.

**Clause (3) is conditions (1) and (2) of goodness, not goodness, and cannot be strengthened.**
"Good" is the three-condition notion of Tag 0FSA, formalized as
`SheafOfModules.DifferentialGradedModule.IsGood`: flatness of the underlying graded module,
K-flatness, and both after arbitrary base change. The conclusion here is the first two
conjuncts. Condition (3) is not concluded and no part of it is claimed, for three independent
reasons:

1. Condition (3) quantifies over an arbitrary
   `SheafOfModules.DifferentialGradedModule.PullbackData` on an arbitrary target site, and the
   library has no such family. Two pullback data are constructed —
   `SheafOfModules.DifferentialGradedModule.idPullbackData` along the identity functor and
   `Stacks.DifferentialGradedPullbackConstruction.pullbackData`, which is `f⁻¹M ⊗_{f⁻¹A'} A` at
   a representably flat final continuous functor of two small sites in one universe — and
   neither is a construction at an arbitrary datum, which is what condition (3) demands.
2. `SheafOfModules.DifferentialGradedModule.IsGood.baseChange` is therefore not a way in: its
   body is `hP.2.2 u σ A₁ φ PD`, a projection out of a goodness hypothesis. It consumes
   condition (3); it cannot produce it.
3. `SheafOfModules.DifferentialGradedModule.isGoodCocontinuousBaseChange_of_isColimitCofan` —
   the goodness half of Tag 0FSD — consumes goodness of the summands in the sense of
   `IsGoodCocontinuousBaseChange`, and nothing in the library supplies that for the elementary
   pieces: Tag 0FSB proves conditions (1) and (2) only, and says so itself.

So what is consumed here is
`SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_of_isColimit`, the conditions
(1) and (2) half of Tag 0FSD.

**Clause (1) is an epimorphism; clause (2) is sectionwise.** "Surjective" is rendered as: the
degree-`n` component of `P → M` is an epimorphism of sheaves of modules, for every `n`. That is
the source's notion, and `Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective` is what
turns the sectionwise hypothesis into it. For clause (2) the source asks that
`Ker(d_P) → Ker(d_M)` be surjective; this library has no subsheaf `Ker(d)` of a differential
graded module, so the conclusion is stated as literal surjectivity on sections killed by the
differential. Kernels of sheaves of modules are computed sectionwise, so this is stronger than
the surjectivity of `Ker(d_P) → Ker(d_M)` and implies it.

**Universes.** Site, topology, ring and module universes are independent, as they are in Tag
0FSD, which is what the flatness conclusion consumes. The index type of the family lies in the
module universe; direct sums of sheaves of modules exist only for shapes small relative to it.

## References

* [Stacks Project, Tag 0FSE](https://stacks.math.columbia.edu/tag/0FSE)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSB](https://stacks.math.columbia.edu/tag/0FSB)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

namespace DifferentialGradedModule

section Epi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A morphism of sheaves of modules which is surjective on sections over every object is an
epimorphism. This is the sectionwise half of
`Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`. -/
theorem epi_of_surjective_sections {X Y : SheafOfModules.{m} R} (f : X ⟶ Y)
    (hf : ∀ (U : Cᵒᵖ) (y : Y.val.obj U), ∃ x : X.val.obj U, homSections f U x = y) : Epi f :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective f
    (Presheaf.isLocallySurjective_of_surjective J _ fun U y ↦ hf U y)

/-- If `f ≫ g = h`, then applying `g` to the image of a section under `f` gives its image
under `h`. -/
private theorem homSections_homSections_of_comp_eq {X Y Z : SheafOfModules.{m} R}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (U : Cᵒᵖ) (x : X.val.obj U) :
    homSections g U (homSections f U x) = homSections h U x := by
  rw [← homSections_comp, e]

end Epi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  {M : DifferentialGradedModule.{t, m, m} A} {ι : Type m}
  {P : ι → DifferentialGradedModule.{t, m, m} A}

/-- The morphism `directSum P ⟶ M` out of the direct sum of the family `P` induced by a family
of morphisms `ψ i : P i ⟶ M`. -/
noncomputable def resolutionOfFamilyHom (ψ : ∀ i, P i ⟶ M) : directSum P ⟶ M :=
  Cofan.IsColimit.desc (directSumIsColimit P) ψ

/-- The inclusion of the `i`-th summand followed by `resolutionOfFamilyHom ψ` is `ψ i`. -/
@[simp]
theorem directSumι_comp_resolutionOfFamilyHom (ψ : ∀ i, P i ⟶ M) (i : ι) :
    directSumι P i ≫ resolutionOfFamilyHom ψ = ψ i :=
  Cofan.IsColimit.fac (directSumIsColimit P) ψ i

/-- The degree-`n` component of `directSumι` followed by that of
`resolutionOfFamilyHom`, on sections. -/
theorem homSections_resolutionOfFamilyHom_directSumι (ψ : ∀ i, P i ⟶ M) (i : ι) (n : ℤ)
    (U : Cᵒᵖ) (y : ((P i).complex.X n).val.obj U) :
    homSections ((resolutionOfFamilyHom ψ).toHomologicalComplex.f n) U
        (homSections ((directSumι P i).toHomologicalComplex.f n) U y) =
      homSections ((ψ i).toHomologicalComplex.f n) U y :=
  homSections_homSections_of_comp_eq
    (by rw [← comp_f, directSumι_comp_resolutionOfFamilyHom]) U y

/-! ### Clause (3): flatness of the direct sum -/

/-- An arbitrary direct sum of K-flat right differential graded modules is K-flat. -/
theorem isKFlat_directSum (hP : ∀ i, RelativeTensor.IsKFlat (P i)) :
    RelativeTensor.IsKFlat (directSum P) := by
  have h := RelativeTensor.isKFlat_of_isColimitCofan (directSumIsColimit P) hP
  exact h

/-- An arbitrary direct sum of right differential graded modules whose underlying graded modules
are flat has flat underlying graded module. -/
theorem isGradedFlat_directSum
    (hP : ∀ i, RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (P i))) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (directSum P)) := by
  have := ab4OfSize.{t, m} (toRingCat J Osharp)
  have h := RelativeTensor.isGradedFlat_of_isColimit
    (K := Discrete.functor P ⋙ forgetToGradedModule A)
    (c := (forgetToGradedModule A).mapCocone (Cofan.mk (directSum P) (directSumι P)))
    (isColimitOfPreserves (forgetToGradedModule A) (directSumIsColimit P)) fun d ↦ hP d.as
  exact h

/-- **Clause (3) of Tag 0FSE, as conditions (1) and (2) of goodness.** A direct sum of right
differential graded modules which are flat as graded modules and K-flat is itself flat as a
graded module and K-flat. -/
theorem isGradedFlat_and_isKFlat_resolutionOfFamily
    (hP : ∀ i, RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (P i)) ∧
      RelativeTensor.IsKFlat (P i)) :
    RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded (directSum P)) ∧
      RelativeTensor.IsKFlat (directSum P) :=
  ⟨isGradedFlat_directSum fun i ↦ (hP i).1, isKFlat_directSum fun i ↦ (hP i).2⟩

/-! ### Clause (1): surjectivity -/

/-- **Clause (1) of Tag 0FSE.** If every section of `M^n` over every object is the image of a
section of one of the pieces, then `P → M` is surjective: its degree-`n` component is an
epimorphism of sheaves of modules, for every `n`. -/
theorem epi_resolutionOfFamilyHom (ψ : ∀ i, P i ⟶ M)
    (hsurj : ∀ (n : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U), ∃ (i : ι)
      (y : ((P i).complex.X n).val.obj U),
        homSections ((ψ i).toHomologicalComplex.f n) U y = x)
    (n : ℤ) : Epi ((resolutionOfFamilyHom ψ).toHomologicalComplex.f n) := by
  refine epi_of_surjective_sections _ fun U x ↦ ?_
  obtain ⟨i, y, hy⟩ := hsurj n U x
  exact ⟨homSections ((directSumι P i).toHomologicalComplex.f n) U y,
    (homSections_resolutionOfFamilyHom_directSumι ψ i n U y).trans hy⟩

/-! ### Clause (2): surjectivity on the kernels of the differentials -/

/-- **Clause (2) of Tag 0FSE.** If every section of `M^n` killed by the differential is the
image of a section of one of the pieces killed by the differential, then the same holds for
`P → M`. Since kernels of sheaves of modules are computed sectionwise, this says in particular
that `Ker(d_P) → Ker(d_M)` is surjective. -/
theorem exists_closed_preimage_resolutionOfFamily (ψ : ∀ i, P i ⟶ M)
    (hclosed : ∀ (n : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U),
      homSections (M.complex.d n (n + 1)) U x = 0 → ∃ (i : ι)
        (y : ((P i).complex.X n).val.obj U),
          homSections ((P i).complex.d n (n + 1)) U y = 0 ∧
            homSections ((ψ i).toHomologicalComplex.f n) U y = x)
    (n : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U)
    (hx : homSections (M.complex.d n (n + 1)) U x = 0) :
    ∃ z : ((directSum P).complex.X n).val.obj U,
      homSections ((directSum P).complex.d n (n + 1)) U z = 0 ∧
        homSections ((resolutionOfFamilyHom ψ).toHomologicalComplex.f n) U z = x := by
  obtain ⟨i, y, hdy, hy⟩ := hclosed n U x hx
  refine ⟨homSections ((directSumι P i).toHomologicalComplex.f n) U y, ?_,
    (homSections_resolutionOfFamilyHom_directSumι ψ i n U y).trans hy⟩
  rw [homSections_homSections_of_comp_eq ((directSumι P i).toHomologicalComplex.comm n (n + 1)),
    homSections_comp, hdy, map_zero]

/-! ### The three clauses together -/

/-- **The three clauses of Tag 0FSE for the direct sum of a flat generating family.** Given a
right differential graded `A`-module `M` and a family of right differential graded `A`-modules
which are flat as graded modules and K-flat, with maps to `M` whose images contain every section
of `M` and every section of `M` killed by the differential, the direct sum of the family is a
right differential graded `A`-module `P` with a homomorphism `P → M` which is surjective, which
is surjective on the sections killed by the differentials, and which is flat as a graded module
and K-flat.

Clause (3) is concluded as conditions (1) and (2) of the definition of good (Tag 0FSA) only;
condition (3) of that definition, stability under arbitrary base change, is not concluded. -/
theorem exists_resolution_of_generatingFamily (M : DifferentialGradedModule.{t, m, m} A)
    {ι : Type m} (P : ι → DifferentialGradedModule.{t, m, m} A) (ψ : ∀ i, P i ⟶ M)
    (hflat : ∀ i, RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (P i)) ∧
      RelativeTensor.IsKFlat (P i))
    (hsurj : ∀ (n : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U), ∃ (i : ι)
      (y : ((P i).complex.X n).val.obj U),
        homSections ((ψ i).toHomologicalComplex.f n) U y = x)
    (hclosed : ∀ (n : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U),
      homSections (M.complex.d n (n + 1)) U x = 0 → ∃ (i : ι)
        (y : ((P i).complex.X n).val.obj U),
          homSections ((P i).complex.d n (n + 1)) U y = 0 ∧
            homSections ((ψ i).toHomologicalComplex.f n) U y = x) :
    ∃ (Q : DifferentialGradedModule.{t, m, m} A) (π : Q ⟶ M),
      (∀ n : ℤ, Epi (π.toHomologicalComplex.f n)) ∧
        (∀ (n : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U),
          homSections (M.complex.d n (n + 1)) U x = 0 →
            ∃ z : (Q.complex.X n).val.obj U,
              homSections (Q.complex.d n (n + 1)) U z = 0 ∧
                homSections (π.toHomologicalComplex.f n) U z = x) ∧
          RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
            RelativeTensor.IsKFlat Q :=
  ⟨directSum P, resolutionOfFamilyHom ψ, epi_resolutionOfFamilyHom ψ hsurj,
    exists_closed_preimage_resolutionOfFamily ψ hclosed,
    (isGradedFlat_and_isKFlat_resolutionOfFamily hflat).1,
    (isGradedFlat_and_isKFlat_resolutionOfFamily hflat).2⟩

end DifferentialGradedModule

end SheafOfModules

end
