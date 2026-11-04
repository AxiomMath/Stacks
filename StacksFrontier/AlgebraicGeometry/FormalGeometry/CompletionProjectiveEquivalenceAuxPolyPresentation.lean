module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedGradedPolynomialCover
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GradedFiniteTypeTotalSections
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.PolyAlgebraTotalNoetherian
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.SchemeFinitePieces
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.Basic

/-!
# The polynomial algebra as the auxiliary algebra of the dévissage of [Stacks, Tag 0897]

`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_presentation` reduces
`Stacks.Coherent.HasAssociatedGradedTwistVanishing` — part (2) of [Stacks, Tag 0897] for the
associated graded algebra of `ℐ = I · 𝒪_X`, and the one hypothesis of [Stacks, Tag 0884] — to the
existence, for every presentation `D` of that algebra, of a sheaf of graded algebras `𝓟` with

* `hφ` a unital homomorphism `φ : 𝓟 ⟶ D.algebra` surjective on the sections over affine opens,
* `hPfin` homogeneous pieces whose sections over affine opens are finite modules, and
* a presentation of every quasi-coherent graded `𝓟`-module of finite type by a degreewise
  epimorphism whose source has uniformly acyclic twists and whose graded kernel is again
  quasi-coherent of finite type.

This file takes `𝓟 = 𝒪_X[x_i : i ∈ ι] = Stacks.Coherent.polyAlgebra X ι` on a finite family of
generators of `I` and discharges everything in that list except the degreewise epimorphism
itself: `hφ` is `Stacks.Coherent.surjective_polyHom_app`, `hPfin` is
`Stacks.SymmetricFree.forall_moduleFinite_symmetricAlgebraPiece`, and the two conditions on the
graded kernel are supplied here from the corresponding conditions on the source. What remains is
exactly the construction of the epimorphism, and
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_epi_over_polyAlgebra` states it as the one
hypothesis.

## Main results

* `Stacks.Coherent.isQuasicoherent_kerObj` — **the sectionwise kernel of a morphism of
  quasi-coherent `𝒪_X`-modules is quasi-coherent.** The quasi-coherence of a kernel is known for
  the categorical kernel (`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`) and for
  the kernel subsheaf in the `X.Modules` spelling
  (`Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_kerMod`), while
  `SheafOfModules.GradedModule.ker` is built from `SheafOfModules.kerObj`; this is that statement
  at `SheafOfModules.kerObj`, which is what the degree-`n` piece of the graded kernel *is*, on
  the nose.
* `Stacks.Coherent.isNoetherianRing_total_polyAlgebra` — the homogeneous sections of
  `𝒪_X[x_i]` over an affine open of a locally Noetherian scheme form a Noetherian ring. This is
  the hypothesis of `Stacks.Coherent.isFiniteTypeOnAffine_ker`, so it is what makes the graded
  kernel of the presentation re-enter the induction.
* `Stacks.Coherent.exists_free_polyAlgebra_piece` — the
  homogeneous pieces of `𝒪_X[x_i]` are free of finite rank in every integer degree, the negative
  ones being zero objects. This is the hypothesis `hfree` of
  `Stacks.Coherent.isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule`, i.e. the input that
  makes the twists of the free graded `𝓟`-modules uniformly acyclic.
* `Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_epi_over_polyAlgebra` — **part (2) of
  [Stacks, Tag 0897] for the associated graded algebra, from a degreewise epimorphic presentation
  of graded `𝒪_X[x_i]`-modules alone.** Every other input of
  `Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_presentation` is discharged here.

## Where `hepi` comes from

The hypothesis `hepi` of the last two theorems is discharged in
`CompletionProjectiveEquivalenceAuxEpiAssembly.lean`, by
`Stacks.Coherent.exists_epi_degreePresentation_polyAlgebra`, and
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_isProper` there is the resulting
unconditional form of part (2) of [Stacks, Tag 0897].

The presenting module is the *tautological* one, `Stacks.Coherent.degreePresentation N J`, i.e.
`⨁_{j ∈ J} N_j ⊗ 𝓟(-j)` with the homogeneous pieces of `N` themselves as the summands. The
source's `⨁_{j ∈ J} (L ^⊗ (-k_j)) ^{⊕ I_j} ⊗ 𝓟(-j)` is **not** needed: what the dévissage asks
of the middle term is only that its twists be uniformly acyclic, and the pieces of `N` already
have that, being coherent in the finitely many degrees of `J`
(`Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_on_finset`), while the degree-`n`
piece of a summand is `N_j ⊗ 𝓟_{n-j}` with `𝓟_{n-j}` free of finite rank, so one bound serves
every homogeneous degree (`exists_free_polyAlgebra_piece` below together with
`Stacks.Coherent.isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule`).

The degreewise epimorphism itself is
`Stacks.Coherent.exists_finset_epi_degreePresentationHom`, resting on the global degree bound:
`Stacks.Coherent.IsFiniteTypeOnAffine` gives a finite generating family over *each* affine open
separately, with its own degrees, and a finite affine cover of the quasi-compact `X` bounds the
degrees over the members of that cover only;
`AlgebraicGeometry.epi_of_forall_exists_surjective_app_affineOpen` is the step from there to a
neighbourhood of an arbitrary point, through
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`.

The other three clauses are
`Stacks.Coherent.isQuasicoherent_directSum_piece` and
`Stacks.Coherent.isZero_Hgroup_directSum_piece_tensorModules` in
`CompletionProjectiveEquivalenceAuxDirectSumPiece.lean`, and
`Stacks.Coherent.isFiniteTypeOnAffine_directSum` over
`Stacks.Coherent.isFiniteTypeOnAffine_freeGradedModuleOn` in
`CompletionProjectiveEquivalenceAuxEpiPresentation.lean`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.Cohomology.FormalFunctions

universe u

namespace Stacks.Coherent

/-! ### Quasi-coherence of the sectionwise kernel -/

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory in
/-- **The sectionwise kernel of a morphism of quasi-coherent `𝒪_X`-modules is quasi-coherent.**

`SheafOfModules.kerObj` and
`Stacks.AlgebraicGeometry.IdealPowerColimit.kerMod` are the same subsheaf of the source — the
first through `SheafOfModules.kerSubmodule`, the second through
`SheafOfModules.Submodule.ker`, two definitions of the sectionwise kernel submodule whose `obj`
fields are both `LinearMap.ker` of the component — so this is
`Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_kerMod` read at the first spelling.
The local reducibility of `AlgebraicGeometry.Scheme.Modules` is what lets the two categories
agree; `X.Modules` carries its own `Category` instance, so a statement about the one does not
apply to the other without it.

The degree-`n` piece of `SheafOfModules.GradedModule.ker` is `SheafOfModules.kerObj` of the
degree-`n` component by `rfl`, so this is the quasi-coherence clause the presentation of
part (2) of [Stacks, Tag 0897] asks about its graded kernel. -/
public theorem isQuasicoherent_kerObj {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (SheafOfModules.kerObj φ).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_kerMod (X := X) φ

/-- **The graded kernel of a homomorphism of graded modules has quasi-coherent pieces** as soon
as the source and the target do. -/
public theorem isQuasicoherent_gradedKer_piece {X : Scheme.{u}}
    {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    {Q N : SheafOfModules.GradedModule P} (π : Q ⟶ N)
    (hQ : ∀ n : ℤ, (Q.piece n).IsQuasicoherent)
    (hN : ∀ n : ℤ, (N.piece n).IsQuasicoherent) (n : ℤ) :
    ((SheafOfModules.GradedModule.ker π).piece n).IsQuasicoherent :=
  have := hQ n
  have := hN n
  isQuasicoherent_kerObj (π.app n)

/-! ### The polynomial algebra as the auxiliary algebra -/

/-- **The homogeneous sections of `𝒪_X[x_i]` over an affine open of a locally Noetherian scheme
form a Noetherian ring.** This is
`Stacks.SymmetricFree.isNoetherianRing_total_symmetricAlgebraFree` with the Noetherianity of the
sections over the affine open read off from `IsLocallyNoetherian`, and it is the hypothesis
`hnoeth` of `Stacks.Coherent.isFiniteTypeOnAffine_ker`.

`Stacks.Coherent.polyAlgebra X ι` and `Stacks.SymmetricFree.symmetricAlgebraFree X ι` are the
same term: both are `SheafOfModules.sheafifiedSymmetricAlgebra` of the free sheaf of modules on
`ι`, the second through the abbreviation `Stacks.SymGraded.freeModule`. -/
public theorem isNoetherianRing_total_polyAlgebra {X : Scheme.{u}} [IsLocallyNoetherian X]
    (ι : Type u) [Finite ι] (U : X.affineOpens) :
    IsNoetherianRing ((polyAlgebra X ι).toPresheafGradedAlgebra.Total (op U.1)) := by
  have := IsLocallyNoetherian.component_noetherian (X := X) U
  exact Stacks.SymmetricFree.isNoetherianRing_total_symmetricAlgebraFree (ι := ι) U.2

/-- **Every homogeneous piece of `𝒪_X[x_i : i ∈ ι]` is free of finite rank**, for a finite family
of variables. In degree `n ≥ 0` the basis is the set of degree-`n` monomials, which is finite by
`Stacks.SymmetricFree.finite_setOf_degree_eq`, and the identification is
`Stacks.SymmetricFree.schemeSymmetricPieceFreeIso` — the sheaf-level [Stacks, Tag 00DN]. A
negative piece is a zero object, hence free on the empty type.

This is the hypothesis `hfree` of
`Stacks.Coherent.isZero_Hgroup_tensorLeft_piece_tensorPowModule` and of
`Stacks.Coherent.isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule`: it is the reason the
twists of a free graded `𝒪_X[x_i]`-module are acyclic uniformly in the homogeneous degree, which
is what the associated graded algebra itself cannot provide. -/
public theorem exists_free_polyAlgebra_piece (X : Scheme.{u}) (ι : Type u) [Finite ι] (m : ℤ) :
    ∃ κ : Type u, ∃ _ : Finite κ,
      Nonempty ((polyAlgebra X ι).piece m ≅ SheafOfModules.free κ) := by
  rcases lt_or_ge m 0 with hm | hm
  · exact ⟨PEmpty.{u + 1}, inferInstance,
      ⟨IsZero.iso
        (SheafOfModules.isZero_sheafifiedSymmetricAlgebra_piece_of_neg
          (Opens.grothendieckTopology ↥X) (SheafOfModules.free (R := X.ringCatSheaf) ι) m hm)
        (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_free_pempty)⟩⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact ⟨{d : ι →₀ ℕ | Finsupp.degree d = n}, inferInstance,
      ⟨Stacks.SymmetricFree.schemeSymmetricPieceFreeIso X ι n⟩⟩

/-! ### Part (2) of Tag 0897 from a presentation over the polynomial algebra -/

/-- **Part (2) of [Stacks, Tag 0897] for the associated graded algebra of `I · 𝒪_X`, from a
degreewise epimorphic presentation of graded `𝒪_X[x_i]`-modules.**

Let `A` be Noetherian, `f : X ⟶ Spec A` proper, `L` an invertible `𝒪_X`-module, and let
`a : ι → A` be a finite family spanning `I`. Assume that every quasi-coherent graded
`𝒪_X[x_i : i ∈ ι]`-module `N` of finite type on affine opens admits, in every positive
cohomological degree, a homomorphism `π : Q ⟶ N` of graded modules which is an epimorphism in
every degree, with `Q` quasi-coherent, of finite type on affine opens, and with the twists of
its pieces acyclic in all positive degrees for all large `d`, uniformly in the homogeneous
degree. Then `Stacks.Coherent.HasAssociatedGradedTwistVanishing` holds.

Everything else that
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_presentation` asks for is discharged:

* the auxiliary algebra is `Stacks.Coherent.polyAlgebra X ι` and the unital homomorphism onto
  the presentation is `Stacks.Coherent.polyHom`, surjective on affine sections by
  `Stacks.Coherent.surjective_polyHom_app`;
* its pieces have finite sections over affine opens by
  `Stacks.SymmetricFree.forall_moduleFinite_symmetricAlgebraPiece`;
* the graded kernel of `π` has quasi-coherent pieces by
  `Stacks.Coherent.isQuasicoherent_gradedKer_piece`, the pieces of `Q` and of `N` being
  quasi-coherent; and
* it is of finite type by `Stacks.Coherent.isFiniteTypeOnAffine_ker`, whose Noetherianity
  hypothesis is `Stacks.Coherent.isNoetherianRing_total_polyAlgebra` — the local Noetherianity of
  `X` coming from `LocallyOfFiniteType f`, which properness supplies.

So the hypothesis `hepi` is the whole of what part (2) of [Stacks, Tag 0897] still costs this
library; the "What is still missing" section of the module documentation says what the intended
`Q` is and which two facts about quasi-coherent modules its construction needs. -/
public theorem hasAssociatedGradedTwistVanishing_of_epi_over_polyAlgebra
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules)
    [IsInvertibleModule X L]
    {ι : Type u} [Finite ι] (a : ι → A) (ha : Ideal.span (Set.range a) = I)
    (hepi : IsAmple X L →
      ∀ N : SheafOfModules.GradedModule (polyAlgebra X ι),
        (∀ n : ℤ, (N.piece n).IsQuasicoherent) → IsFiniteTypeOnAffine N → ∀ p : ℕ, 0 < p →
        ∃ (Q : SheafOfModules.GradedModule (polyAlgebra X ι)) (π : Q ⟶ N),
          (∀ n : ℤ, Epi (gradedAppMod π n)) ∧
          (∀ n : ℤ, (Q.piece n).IsQuasicoherent) ∧
          IsFiniteTypeOnAffine Q ∧
          ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
            IsZero (Hgroup X.ringCatSheaf ⊤ m
              (tensorModules X (Q.piece n) (tensorPowModule X L d)))) :
    HasAssociatedGradedTwistVanishing A I f L := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine hasAssociatedGradedTwistVanishing_of_presentation A I f L fun hL D => ?_
  refine ⟨polyAlgebra X ι, polyHom A I f D a ha, surjective_polyHom_app A I f D a ha,
    Stacks.SymmetricFree.forall_moduleFinite_symmetricAlgebraPiece X ι,
    fun N hqc hft p hp => ?_⟩
  obtain ⟨Q, π, hπ, hQqc, hQft, d₁, hd₁⟩ := hepi hL N hqc hft p hp
  exact ⟨Q, π, hπ, isQuasicoherent_gradedKer_piece π hQqc hqc,
    isFiniteTypeOnAffine_ker π hQft (isNoetherianRing_total_polyAlgebra ι), d₁, hd₁⟩

/-- **`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_epi_over_polyAlgebra` with the family
of generators removed.** A Noetherian ring has every ideal finitely generated, so the family
`a : ι → A` spanning `I` need not be supplied: it is produced here from `Ideal.FG`, with `ι` the
elements of a finite spanning set. The hypothesis is therefore the construction of the
degreewise epimorphism alone, over the polynomial algebra on an arbitrary finite set of
variables.

This is the exact residue of part (2) of [Stacks, Tag 0897] for the associated graded algebra of
`I · 𝒪_X`, and hence of the hypothesis `h0897` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`. -/
public theorem hasAssociatedGradedTwistVanishing_of_forall_epi_over_polyAlgebra
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules)
    [IsInvertibleModule X L]
    (hepi : ∀ (ι : Type u) (_ : Finite ι), IsAmple X L →
      ∀ N : SheafOfModules.GradedModule (polyAlgebra X ι),
        (∀ n : ℤ, (N.piece n).IsQuasicoherent) → IsFiniteTypeOnAffine N → ∀ p : ℕ, 0 < p →
        ∃ (Q : SheafOfModules.GradedModule (polyAlgebra X ι)) (π : Q ⟶ N),
          (∀ n : ℤ, Epi (gradedAppMod π n)) ∧
          (∀ n : ℤ, (Q.piece n).IsQuasicoherent) ∧
          IsFiniteTypeOnAffine Q ∧
          ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
            IsZero (Hgroup X.ringCatSheaf ⊤ m
              (tensorModules X (Q.piece n) (tensorPowModule X L d)))) :
    HasAssociatedGradedTwistVanishing A I f L := by
  obtain ⟨S, hS⟩ : ∃ S : Finset A, Ideal.span (S : Set A) = I :=
    (IsNoetherian.noetherian I).imp fun _ h => h
  have : Finite {x : A // x ∈ S} := inferInstance
  refine hasAssociatedGradedTwistVanishing_of_epi_over_polyAlgebra A I f L
    (ι := {x : A // x ∈ S}) Subtype.val ?_ (hepi {x : A // x ∈ S} inferInstance)
  rw [Subtype.range_coe]
  exact hS

end Stacks.Coherent

end
