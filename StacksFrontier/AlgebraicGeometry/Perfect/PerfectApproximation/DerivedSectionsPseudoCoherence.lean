module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.AffineScheme
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Homology.PseudoCoherent.TriangulatedApproximation
import StacksCore.Tactic.StacksAttribute

/-!
# Testing pseudo-coherence of a derived image on perfect complexes

Let `A` be a ring, let `X` be a scheme and let `G : D(𝒪_X) ⥤ D(A)` be an exact functor of
triangulated categories. Suppose

* `G` has finite cohomological dimension on `D_QCoh(𝒪_X)`: there is an integer `d` such that an
  object with quasi-coherent cohomology sheaves vanishing in all degrees at least `c` has
  `G`-image with cohomology vanishing in all degrees at least `c + d`;
* `X` satisfies approximation by perfect complexes;
* `G(P)` is pseudo-coherent in `D(A)` for every perfect object `P` of `D(𝒪_X)`.

Then `G(E)` is pseudo-coherent in `D(A)` for every pseudo-coherent object `E` of `D(𝒪_X)`.

This is the dévissage of [Stacks, Tag 0CSH], carried out for the functor
`G = RΓ(X, - ⊗^𝐋_{𝒪_X} K)`. The source's hypothesis that `X` be quasi-compact and quasi-separated
and that `K` lie in `D^-_QCoh(𝒪_X)` is used there in exactly two ways, and both are isolated in
the hypotheses above: it makes `X` satisfy approximation by perfect complexes ([Stacks,
Tag 08ES]), and it bounds the cohomological dimension of `G` — the bound `d = b + N` where `b` is
an upper bound for the cohomology of `K`, `N` is the cohomological dimension of `RΓ(X, -)` on
`D_QCoh(𝒪_X)` ([Stacks, Tag 08D5] part (2)), and `- ⊗^𝐋 K` both raises an upper bound by `b` and
preserves quasi-coherence of cohomology ([Stacks, Tag 08DX] part (1)).

## Main results

* `AlgebraicGeometry.PerfectApproximation.isPseudoCoherent_obj_of_hasApproximationByPerfect`:
  the dévissage, with approximation by perfect complexes as a hypothesis.
* `AlgebraicGeometry.PerfectApproximation.isPseudoCoherent_obj_of_isAffine`: the same conclusion
  for an affine scheme, where approximation by perfect complexes is available.
* `CategoryTheory.Functor.exists_mem_distTriang_obj` and
  `CategoryTheory.Functor.exists_mem_distTriang_obj_comp`: the exactness hypothesis of the two
  results above, discharged for an exact functor and for a composite of two of them.

## Implementation notes

**Approximation as a hypothesis.** Approximation by perfect complexes enters the first result
below as the hypothesis `AlgebraicGeometry.HasApproximationByPerfectComplexes X`, so that the
dévissage stands for any scheme satisfying it. It is discharged in the second result for an affine
`X` ([Stacks, Tag 08EQ]), and for a quasi-compact quasi-separated `X` by [Stacks, Tag 08ES],
`AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes`; [Stacks, Tag 0CSH]
itself, with the functor `RΓ(X, - ⊗^𝐋 K)` made concrete, is
`AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent`
in the module `DerivedSectionsTensorPseudoCoherence` of
`StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation`.

The functor is abstract rather than spelled as `RΓ(X, - ⊗^𝐋_{𝒪_X} K)` for two reasons. The
derived tensor product of `D(𝒪_X)` and the perfectness predicate each occur in this library under
two incompatible spellings, one over the module category of a scheme and one over a ringed site,
and the cohomological-dimension bound for `A`-linear derived global sections — as opposed to the
`Γ(X, 𝒪_X)`-linear `AlgebraicGeometry.isLE_rightDerivedSections_obj_of_isQuasicoherent` — is not
available either. Abstracting the composite leaves one hypothesis where there would be three, and
it is the hypothesis a consumer can discharge in whichever spelling it is working in.

**Exactness is a hypothesis, not two instances, and the reason is specific.** Both results below
ask for `hGtri`: a distinguished triangle of `D(𝒪_X)` goes to a distinguished triangle on the
`G`-images of its vertices, with the three maps existentially quantified. They do *not* ask for
`G.CommShift ℤ` and `G.IsTriangulated`. Those two classes are strictly stronger than what the
proof reads off the image triangle — which is only its vertices — and, more to the point, they
are not synthesizable for the composite a consumer actually has.
`AlgebraicGeometry.globalSectionsOver`, and hence
`AlgebraicGeometry.derivedGlobalSectionsOver`, is declared under two
`HasDerivedCategory` binders which its body does not use, so an occurrence of it carries two
universe metavariables and two pending instance goals; a composite ending in it therefore does
not get `(F ⋙ G).CommShift ℤ` from instance search even when both factors' structures are in
scope. This is the same obstruction that
`Stacks.AlgebraicGeometry.ProperSupportCoherent.siteSections` exists to work around, recorded in
the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget`.

So the two structures are consumed one factor at a time instead, which needs no composite
instance: `CategoryTheory.Functor.exists_mem_distTriang_obj_comp` takes
`F.CommShift ℤ`, `F.IsTriangulated`, `H.CommShift ℤ` and `H.IsTriangulated` and produces `hGtri`
for `F ⋙ H`. For `G = RΓ(X, - ⊗^𝐋_{𝒪_X} K)` the two factors do carry them: tensoring with a
fixed object in the left variable by the `commShift_left` and `exact_left` fields of
`Stacks.SheafOfModules.DerivedTensorProduct`, and `A`-linear derived global sections by
`AlgebraicGeometry.derivedGlobalSectionsOver_commShift` and
`AlgebraicGeometry.derivedGlobalSectionsOver_isTriangulated`, for every model of the derived
category. `CategoryTheory.Functor.exists_mem_distTriang_obj` is the one-factor form, for a
consumer that does have the composite's own structures.

**The proof.** Pseudo-coherence in `D(A)` is `m`-pseudo-coherence in every degree `m`, so fix `m`
and approximate `E` in degree `m - d - 1`: approximation by perfect complexes applied to the
closed subset `X` itself — whose complement is empty, hence retrocompact — produces a perfect `P`
and a map `α : P ⟶ E` which is an isomorphism on cohomology above `m - d - 1` and an epimorphism
there. The cone `C` of `α` then has no cohomology from degree `m - d - 1` upwards
(`CategoryTheory.isZero_homology_obj₃_of_distinguished`), and it has quasi-coherent cohomology
because `E` and `P` do — both being pseudo-coherent, by [Stacks, Tag 08E5] — and because
`D_QCoh(𝒪_X)` is a triangulated subcategory. The cohomological-dimension hypothesis therefore
kills `G(C)` from degree `m - 1` upwards, and
`StacksDraft.PseudoCoherence.isPseudoCoherentFrom_obj₂_of_distTriang` applied to the image
triangle on `G(P)`, `G(E)`, `G(C)` supplied by `hGtri` gives `m`-pseudo-coherence of `G(E)`.

Quasi-coherence of the cone is read off the rotated triangle `E ⟶ C ⟶ P⟦1⟧`, whose outer
vertices are the two objects already known to lie in `D_QCoh(𝒪_X)`; the shift stays there by
`Stacks.DerivedCategoryB.derivedCategoryB_shift_mem`. The weak Serre property of quasi-coherent
modules that this uses, the lemma `isQuasicoherent_isWeakSerre` of
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre`, is a statement about `𝒪_X`-modules and not
about any model of `D(𝒪_X)`, so it is usable here even
though the triangulated-subcategory instance derived from it in that file is stated at the
locally small model. The derived categories here are the standard ones, as they must be: that is
the model in which `AlgebraicGeometry.HasApproximationByPerfectComplexes` and
`StacksDraft.PseudoCoherence.IsPseudoCoherent` are stated.

## References

* [Stacks Project, Tag 0CSH](https://stacks.math.columbia.edu/tag/0CSH)
* [Stacks Project, Tag 08ES](https://stacks.math.columbia.edu/tag/08ES)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

universe u

/-! ### Exactness, in the form the dévissage consumes -/

namespace CategoryTheory.Functor

section Exactness

variable {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]
  {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {ℰ : Type*} [Category ℰ] [Preadditive ℰ] [HasZeroObject ℰ] [HasShift ℰ ℤ]
  [∀ n : ℤ, (shiftFunctor ℰ n).Additive] [Pretriangulated ℰ]

/-- **An exact functor sends a distinguished triangle to one on the images of its vertices.**
The three maps are existentially quantified: only the vertices are named, which is all a
statement that reads a triangle through its vertices can use, and it is what makes the
conclusion satisfiable without a shift-commutation structure on the functor in hand. -/
theorem exists_mem_distTriang_obj (F : 𝒞 ⥤ ℰ) [F.CommShift ℤ] [F.IsTriangulated] {P E C : 𝒞}
    (a : P ⟶ E) (b : E ⟶ C) (c : C ⟶ P⟦(1 : ℤ)⟧)
    (h : Pretriangulated.Triangle.mk a b c ∈ distTriang 𝒞) :
    ∃ (a' : F.obj P ⟶ F.obj E) (b' : F.obj E ⟶ F.obj C)
      (c' : F.obj C ⟶ (F.obj P)⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk a' b' c' ∈ distTriang ℰ :=
  ⟨_, _, _, F.map_distinguished _ h⟩

/-- **The same for a composite, from the two factors separately.** The point of this form is
that it never mentions `(F ⋙ H).CommShift ℤ` or `(F ⋙ H).IsTriangulated`: a composite of two
functors each carrying those structures need not have them available to instance search, and
`AlgebraicGeometry.derivedGlobalSectionsOver` in particular is declared under two
`HasDerivedCategory` binders its body does not use, so a composite ending in it carries pending
instance goals. Here each factor is used at its own structure and only the resulting triangles
are composed. -/
theorem exists_mem_distTriang_obj_comp (F : 𝒞 ⥤ 𝒟) [F.CommShift ℤ] [F.IsTriangulated]
    (H : 𝒟 ⥤ ℰ) [H.CommShift ℤ] [H.IsTriangulated] {P E C : 𝒞}
    (a : P ⟶ E) (b : E ⟶ C) (c : C ⟶ P⟦(1 : ℤ)⟧)
    (h : Pretriangulated.Triangle.mk a b c ∈ distTriang 𝒞) :
    ∃ (a' : (F ⋙ H).obj P ⟶ (F ⋙ H).obj E) (b' : (F ⋙ H).obj E ⟶ (F ⋙ H).obj C)
      (c' : (F ⋙ H).obj C ⟶ ((F ⋙ H).obj P)⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk a' b' c' ∈ distTriang ℰ :=
  ⟨_, _, _, H.map_distinguished _ (F.map_distinguished _ h)⟩

end Exactness

end CategoryTheory.Functor

/-! ### The dévissage -/

namespace AlgebraicGeometry.PerfectApproximation

attribute [local instance 100000] HasDerivedCategory.standard

variable {A : Type u} [Ring A] (X : Scheme.{u})
  (G : DerivedCategory.{u + 1} X.Modules ⥤ DerivedCategory (ModuleCat.{u} A))

/-- **The dévissage of [Stacks, Tag 0CSH].** Let `G : D(𝒪_X) ⥤ D(A)` be a functor which carries
a distinguished triangle to a distinguished triangle on the images of its vertices (`hGtri`) and
whose cohomological dimension on `D_QCoh(𝒪_X)` is bounded by `d`: an object with quasi-coherent
cohomology sheaves vanishing in all degrees at least `c` has `G`-image with cohomology vanishing
in all degrees at least `c + d`. If `X` satisfies approximation by perfect complexes and `G`
carries perfect objects to pseudo-coherent objects of `D(A)`, then it carries pseudo-coherent
objects to pseudo-coherent objects.

For `G = RΓ(X, - ⊗^𝐋_{𝒪_X} K)` with `X` quasi-compact and quasi-separated over `A` and `K` in
`D^-_QCoh(𝒪_X)` this is the engine of [Stacks, Tag 0CSH]: both hypotheses on `G` and on `X` are
discharged there, approximation by perfect complexes by [Stacks, Tag 08ES], in
`AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent`.

Exactness enters as the hypothesis `hGtri` rather than as `G.CommShift ℤ` together with
`G.IsTriangulated`, and `CategoryTheory.Functor.exists_mem_distTriang_obj_comp` discharges it for
a composite from the two factors' structures; see the implementation notes for why a composite
ending in `AlgebraicGeometry.derivedGlobalSectionsOver` cannot be expected to carry those two
classes by instance search. -/
theorem isPseudoCoherent_obj_of_hasApproximationByPerfect (d : ℤ)
    (hGtri : ∀ (P E' C : DerivedCategory.{u + 1} X.Modules) (a : P ⟶ E') (b : E' ⟶ C)
      (c : C ⟶ P⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang (DerivedCategory.{u + 1} X.Modules) →
        ∃ (a' : G.obj P ⟶ G.obj E') (b' : G.obj E' ⟶ G.obj C)
          (c' : G.obj C ⟶ (G.obj P)⟦(1 : ℤ)⟧),
          Triangle.mk a' b' c' ∈ distTriang (DerivedCategory (ModuleCat.{u} A)))
    (hG : ∀ C : DerivedCategory.{u + 1} X.Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj C).IsQuasicoherent) →
      ∀ c : ℤ, (∀ i : ℤ, c ≤ i →
          IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj C)) →
        ∀ i : ℤ, c + d ≤ i →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (G.obj C)))
    (happrox : HasApproximationByPerfectComplexes X)
    (hperf : ∀ P : DerivedCategory.{u + 1} X.Modules,
      RingedSpace.IsPerfect (X := X.toRingedSpace) P →
        StacksDraft.PseudoCoherence.IsPseudoCoherent (G.obj P))
    (E : DerivedCategory.{u + 1} X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (G.obj E) := by
  obtain ⟨r, hr⟩ := happrox Set.univ isClosed_univ
    (by simp)
  have hEqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent.{u, u + 1} X E hE
  refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all (G.obj E)).2 fun m => ?_
  obtain ⟨P, hPperf, -, α, hiso, hepi⟩ := hr E (m - d - 1) hEqc
    (hE.isPseudoCoherentFrom (m - d - 1 - r)) (fun i x _ hx => absurd (Set.mem_univ x) hx)
  obtain ⟨C, β, γ, hT⟩ := distinguished_cocone_triangle α
  have hCvan : ∀ i : ℤ, m - d - 1 ≤ i →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj C) :=
    CategoryTheory.isZero_homology_obj₃_of_distinguished (m - d - 1)
      (Triangle.mk α β γ) hT hiso hepi
  have hPqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj P).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent.{u, u + 1} X P hPperf.isPseudoCoherent
  have hws := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X
  have hCqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj C).IsQuasicoherent :=
    @_root_.DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished X.Modules _ _
      (HasDerivedCategory.standard X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf) hws
      ((Triangle.mk α β γ).rotate) (rot_of_distTriang _ hT) hEqc
      (@_root_.DerivedCategoryB.derivedCategoryB_shift_mem X.Modules _ _
        (HasDerivedCategory.standard X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) hws 1 P hPqc)
  obtain ⟨a', b', c', hdist⟩ := hGtri P E C α β γ hT
  exact StacksDraft.PseudoCoherence.isPseudoCoherentFrom_obj₂_of_distTriang m
    (Triangle.mk a' b' c') hdist (hperf P hPperf)
    fun i hi => hG C hCqc (m - d - 1) hCvan i (by omega)

/-- **[Stacks, Tag 0CSH] for an affine scheme.** On an affine scheme approximation by perfect
complexes holds ([Stacks, Tag 08EQ]), so an exact functor `G : D(𝒪_X) ⥤ D(A)` of bounded
cohomological dimension on `D_QCoh(𝒪_X)` carries pseudo-coherent objects to pseudo-coherent
objects as soon as it carries perfect ones there. Exactness is the hypothesis `hGtri` of
`AlgebraicGeometry.PerfectApproximation.isPseudoCoherent_obj_of_hasApproximationByPerfect`. -/
theorem isPseudoCoherent_obj_of_isAffine [IsAffine X] (d : ℤ)
    (hGtri : ∀ (P E' C : DerivedCategory.{u + 1} X.Modules) (a : P ⟶ E') (b : E' ⟶ C)
      (c : C ⟶ P⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang (DerivedCategory.{u + 1} X.Modules) →
        ∃ (a' : G.obj P ⟶ G.obj E') (b' : G.obj E' ⟶ G.obj C)
          (c' : G.obj C ⟶ (G.obj P)⟦(1 : ℤ)⟧),
          Triangle.mk a' b' c' ∈ distTriang (DerivedCategory (ModuleCat.{u} A)))
    (hG : ∀ C : DerivedCategory.{u + 1} X.Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj C).IsQuasicoherent) →
      ∀ c : ℤ, (∀ i : ℤ, c ≤ i →
          IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj C)) →
        ∀ i : ℤ, c + d ≤ i →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (G.obj C)))
    (hperf : ∀ P : DerivedCategory.{u + 1} X.Modules,
      RingedSpace.IsPerfect (X := X.toRingedSpace) P →
        StacksDraft.PseudoCoherence.IsPseudoCoherent (G.obj P))
    (E : DerivedCategory.{u + 1} X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (G.obj E) :=
  isPseudoCoherent_obj_of_hasApproximationByPerfect X G d hGtri hG
    (hasApproximationByPerfectComplexes_of_isAffine X) hperf E hE

end AlgebraicGeometry.PerfectApproximation

end
