module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexOverFieldClauses
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDuality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafSmoothCurve

/-!
# The dualizing complex of a proper scheme of dimension at most one over a field

This file collects [Stacks, Tag 0BS2] into one statement. Let `X` be a proper scheme of dimension
at most one over a field `k`, with structure morphism `f : X ⟶ Spec k`. The dualizing complex of
the tag is

  `ω_X^• = f^×(𝒪_{Spec k}) = a(𝒪_{Spec k})`, `Stacks.Duality.dualizingComplexOverField f`,

the value at `𝒪_{Spec k}` of the right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec k})`
([Stacks, Tag 0A9E]), and `ω_X = H^{-1}(ω_X^•)` is `Stacks.Duality.dualizingSheafOverField f`.

## Main results

* `Stacks.Duality.dualizingComplexOverField_properties` — **[Stacks, Tag 0BS2]**: `ω_X^•` is a
  dualizing complex with properties (1)–(6) of the tag.

## Implementation notes

The tag asserts that *there exists* a dualizing complex with properties (1)–(6); as in the
source's proof, the statement here is about the specific complex `ω_X^• = f^×(𝒪_{Spec k})`, which
is a stronger form of the existence assertion. The pieces:

* the dualizing property, clauses (1)–(3), and the bijectivity in clause (4) are in
  `StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingComplexOverFieldClauses.lean`;
* the functoriality of clause (4) and its compatibility with shifts and distinguished triangles
  are `Stacks.Duality.dualityEquiv_comp`, `Stacks.Duality.dualityLinearMap_shift` and
  `Stacks.Duality.dualityLinearMap_triangle` ([Stacks, Tag 0FVV], part (5));
* clause (5) is `Stacks.Duality.clauseFiveLinearEquiv`, the `k`-linear form of
  `Stacks.Duality.clauseFiveAddEquiv`, with the naturality
  `Stacks.Duality.clauseFiveAddEquiv_naturality`;
* clause (6) is `Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials`
  (`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingSheafSmoothCurve.lean`), the
  proof of [Stacks, Tag 0BRT] at relative dimension one.

In clause (4) the isomorphism `Ext^i_X(K, ω_X^•) ≅ Hom_k(H^{-i}(X, K), k)` is the explicit
`k`-linear map `Stacks.Duality.dualityLinearMap`, `α ↦ t ∘ H^{-i}(X, α)` with `t` the trace; it is
defined on all of `D(𝒪_X)`, and it is bijective on `D_QCoh(𝒪_X)`. The hypercohomology
`H^n(X, K)` is `H^n(RΓ(X, K))`, written with `Stacks.Duality.derivedGlobalSectionsOver f`.

The `k`-vector space structure on the morphism groups `Hom(ℱ, ω_X)` of clause (5), and on the
groups `Ext^i_X(K, ω_X^•)` of clause (4), is the one `𝒪_X`-modules carry over the base,
`AlgebraicGeometry.Scheme.linearOver f`: a scalar acts through `k ⟶ Γ(X, 𝒪_X)`. For it the
global sections functor is `k`-linear (`AlgebraicGeometry.globalSectionsOver_linearOver`), which
is what makes the identifications of both clauses `k`-linear.

The stalk `H^0(ω_{X,x}^•)` of clause (3) is written as the stalk at `x` of the cohomology sheaf
`H^0(ω_X^•)`; the stalk functor is exact, so the two agree.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **[Stacks, Tag 0BS2].** Let `X` be a proper scheme of dimension at most one over a field `k`.
The complex `ω_X^• = f^×(𝒪_{Spec k})` is a dualizing complex on `X`, and, writing
`ω_X = H^{-1}(ω_X^•)`:
1. `H^i(ω_X^•)` is nonzero only for `i = -1, 0`;
2. `ω_X` is a coherent Cohen--Macaulay module whose support is the union of the irreducible
   components of dimension `1`;
3. for `x ∈ X` closed, `H^0(ω_{X,x}^•)` is nonzero if and only if `dim 𝒪_{X,x} = 0`, or
   `dim 𝒪_{X,x} = 1` and `𝒪_{X,x}` is not Cohen--Macaulay;
4. for `K` in `D_QCoh(𝒪_X)` the maps `Ext^i_X(K, ω_X^•) ⟶ Hom_k(H^{-i}(X, K), k)` are
   isomorphisms, functorial in `K` and compatible with shifts and distinguished triangles;
5. there are functorial isomorphisms of `k`-vector spaces `Hom(ℱ, ω_X) = Hom_k(H^1(X, ℱ), k)`
   for `ℱ` quasi-coherent;
6. if `X ⟶ Spec k` is smooth of relative dimension `1`, then `ω_X ≅ Ω_{X/k}`. -/
@[stacks 0BS2]
theorem dualizingComplexOverField_properties (hdim : topologicalKrullDim X ≤ 1) :
    letI := LocallyOfFiniteType.isLocallyNoetherian f
    letI := Scheme.linearOver f
    -- `ω_X^•` is a dualizing complex
    IsDualizingComplex (dualizingComplexOverField f).obj ∧
    -- (1)
    (∀ i : ℤ, ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      (dualizingComplexOverField f).obj) → i = -1 ∨ i = 0) ∧
    -- (2)
    (_root_.SheafOfModules.IsCoherent (dualizingSheafOverField f) ∧
      SheafIsCohenMacaulay X (dualizingSheafOverField f) ∧
      _root_.SheafOfModules.supp (dualizingSheafOverField f) =
        ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = 1}) ∧
    -- (3)
    (∀ x : X, IsClosed ({x} : Set X) →
      (Nontrivial (moduleStalkAtPoint ((DerivedCategory.homologyFunctor X.Modules 0).obj
          (dualizingComplexOverField f).obj) x) ↔
        ringKrullDim (X.presheaf.stalk x) = 0 ∨
          ringKrullDim (X.presheaf.stalk x) = 1 ∧
            ¬ IsCohenMacaulayLocalRing (X.presheaf.stalk x))) ∧
    -- (4): isomorphisms on `D_QCoh(𝒪_X)`
    (∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      Function.Bijective (dualityLinearMap f K.obj i)) ∧
    -- (4): functoriality
    (∀ (K L : DerivedCategory X.Modules) (i : ℤ) (g : K ⟶ L)
      (α : DerivedCategory.Ext L (dualizingComplexOverField f).obj i)
      (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
        ((derivedGlobalSectionsOver f).obj K)),
      dualityLinearMap f K i (g ≫ α) x =
        dualityLinearMap f L i α
          ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).map
            ((derivedGlobalSectionsOver f).map g) x)) ∧
    -- (4): compatibility with shifts
    (∀ (K : DerivedCategory X.Modules) (i n : ℤ)
      (α : DerivedCategory.Ext K (dualizingComplexOverField f).obj i)
      (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-(i + n))).obj
        ((derivedGlobalSectionsOver f).obj (K⟦n⟧))),
      dualityLinearMap f (K⟦n⟧) (i + n) (ShiftedHom.comp (𝟙 (K⟦n⟧)) α rfl) x =
        dualityLinearMap f K i α
          ((((derivedGlobalSectionsOver f ⋙
            DerivedCategory.homologyFunctor (ModuleCat k) 0).shiftIso n (-(i + n)) (-i)
              (by omega)).hom.app K) x)) ∧
    -- (4): compatibility with distinguished triangles
    (∀ (T : Pretriangulated.Triangle (DerivedCategory X.Modules)) (i : ℤ)
      (α : DerivedCategory.Ext T.obj₁ (dualizingComplexOverField f).obj i)
      (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-(i + 1))).obj
        ((derivedGlobalSectionsOver f).obj T.obj₃)),
      dualityLinearMap f T.obj₃ (i + 1)
          (ShiftedHom.comp (T.mor₃ : DerivedCategory.Ext T.obj₃ T.obj₁ 1) α rfl) x =
        dualityLinearMap f T.obj₁ i α
          ((derivedGlobalSectionsOver f ⋙
            DerivedCategory.homologyFunctor (ModuleCat k) 0).homologySequenceδ T (-(i + 1)) (-i)
              (by omega) x)) ∧
    -- (5)
    (∃ e : ∀ F : X.Modules, F.IsQuasicoherent →
        ((F ⟶ dualizingSheafOverField f) ≃ₗ[k] (cohomologyOverField k f F 1 →ₗ[k] k)),
      ∀ (F G : X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
        (φ : G ⟶ dualizingSheafOverField f),
        e F hF (u ≫ φ) = (e G hG φ).comp (cohomologyOverFieldMap k f u 1).hom) ∧
    -- (6)
    (SmoothOfRelativeDimension 1 f →
      Nonempty (dualizingSheafOverField f ≅ Scheme.Hom.relativeDifferentials f)) := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := Scheme.linearOver f
  let : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linearOver f
  refine ⟨isDualizingComplex_dualizingComplexOverField f, ?_,
    dualizingSheafOverField_clauseTwo f hdim,
    fun x hx => nontrivial_stalk_homology_zero_dualizingComplexOverField_iff f hdim hx,
    bijective_dualityLinearMap_dualizingComplexOverField f,
    fun K L i g α x => ?_, fun K i n α x => dualityLinearMap_shift f K i n α x,
    fun T i α x => dualityLinearMap_triangle f T i α x,
    ⟨fun F hF => clauseFiveLinearEquiv f hdim F hF,
      fun F G hF hG u φ => clauseFiveAddEquiv_naturality f hdim F G hF hG u φ⟩,
    fun _ => nonempty_dualizingSheafOverField_iso_relativeDifferentials f⟩
  · intro i hi
    by_contra h
    rw [not_or] at h
    exact hi (isZero_homology_dualizingComplexOverField_of_ne f hdim h.1 h.2)
  · exact congrArg (fun φ => φ.hom x) (dualityPairing_comp f g i α)

end Stacks.Duality

end
