module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward
public import StacksFrontier.Algebra.Homology.SpectralSequence.Grothendieck
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# The Leray spectral sequence of a morphism of ringed spaces, for sheaves of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `K` be an object of `D⁺(Mod(𝒪_X))`.
Taking sections on `X` is taking sections on `Y` of the direct image, with scalars restricted
along the map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` induced by `f`, and the direct image of an injective
`𝒪_X`-module has acyclic sections over every open of `Y` — [Stacks, Tag 01EX] part (2).  The
Grothendieck spectral sequence of [Stacks, Tag 015N] therefore applies to the composition
`Γ(Y, -) ∘ f_*` and produces a spectral sequence of `Γ(Y, 𝒪_Y)`-modules
```
E_2^{p,q} = H^p(Y, R^q f_* K)
```
which is bounded, converges to `H^*(X, K)` and induces a finite filtration on each
`H^n(X, K)`, the abutment being the hypercohomology of `X` with scalars restricted along `f`.

## Main results

* `abutmentIso`: the abutment of that spectral sequence is the hypercohomology of `X`, with
  scalars restricted along `Γ(Y, 𝒪_Y) ⟶ Γ(f^{-1}(⊤), 𝒪_X)`.
* `exists_spectralSequence_leray`: the Leray spectral sequence
  `H^p(Y, R^q f_* K) ⇒ H^{p+q}(X, K)` for sheaves of modules.

## Implementation notes

* As for [Stacks, Tag 015N] and [Stacks, Tag 0132], a spectral sequence "converging to
  `H^*(K)`" is a spectral sequence together with a filtered complex `K` whose spectral
  sequence it is: its pages are identified with the quotients `Z_r^{p,q}/D_r^{p,q}` of
  [Stacks, Tag 012M], and boundedness, finiteness of the filtration induced on cohomology and
  convergence are properties of that presentation.
* Everything is stated for `RingedSpace.{u, u}` and `SheafOfModules.{u}`, the universe
  constraint imposed by Mathlib's adjunction for the pushforward of presheaves of modules.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPushforwardSections

universe u

namespace Stacks.Cohomology.LerayModules

attribute [local instance] HasDerivedCategory.standard

-- The instance getting pointwise right derivability from `EnoughInjectives` is tried before the
-- one that would prove termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Sections over an open subset of a ringed space form an additive functor. -/
local instance evaluationAdditive (X : RingedSpace.{u, u}) (V : Opens X.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X) (op V)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The abutment of the Leray spectral sequence is the hypercohomology of `X`.**  The derived
functor of `Γ(Y, -) ∘ f_*` is the derived functor of sections over `f^{-1}(⊤)` followed by the
derived restriction of scalars along `Γ(Y, 𝒪_Y) ⟶ Γ(f^{-1}(⊤), 𝒪_X)`. -/
noncomputable def abutmentIso :
    (modulePushforward f ⋙ SheafOfModules.evaluation (structureSheafRing Y)
        (op (⊤ : Opens Y.carrier))).rightDerivedFunctorPlus ≅
      (SheafOfModules.evaluation (structureSheafRing X)
          (op ((opensMap f).obj (⊤ : Opens Y.carrier)))).rightDerivedFunctorPlus ⋙
        (ModuleCat.restrictScalars
          ((structureSheafHom f).hom.app
            (op (⊤ : Opens Y.carrier))).hom).rightDerivedFunctorPlus :=
  compIso _ _ (rightAcyclic_modulePushforward_obj f ⊤) ≪≫
    (rightDerivedSectionsRestrictionIso f ⊤).symm

/-- **The Leray spectral sequence for sheaves of modules.**  Let `f : X ⟶ Y` be a morphism of
ringed spaces and let `K` be an object of `D⁺(Mod(𝒪_X))`.  There is a filtered complex `L` of
`Γ(Y, 𝒪_Y)`-modules with `H^n(L) ≅ H^n(X, K)` for all `n`, the right-hand side being the
hypercohomology of `X` with scalars restricted along `f`, whose spectral sequence `E`,
presented as in [Stacks, Tag 012M] by its pages `Z_r^{p,q}/D_r^{p,q}`, has
`E_2^{p,q} ≅ H^p(Y, R^q f_* K)`, is bounded, induces a finite filtration on each `H^n(L)`, and
converges to `H^*(L)`. -/
@[stacks 01F2 "the whole statement: existence of the spectral sequence with second page
`H^p(Y, R^q f_* K)` converging to `H^{p+q}(X, K)`, for `K` in `D⁺(Mod(𝒪_X))`. Functoriality in
`K` is NOT asserted — the source does not state it"]
theorem exists_spectralSequence_leray
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    ∃ L : FilteredObject (CochainComplex
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier)))) ℤ) ℤᵒᵖ,
      (∀ n : ℤ, Nonempty (L.X.homology n ≅
        (DerivedCategory.Plus.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier)))) n).obj
          (((SheafOfModules.evaluation (structureSheafRing X)
                (op ((opensMap f).obj (⊤ : Opens Y.carrier)))).rightDerivedFunctorPlus ⋙
              (ModuleCat.restrictScalars
                ((structureSheafHom f).hom.app
                  (op (⊤ : Opens Y.carrier))).hom).rightDerivedFunctorPlus).obj K))) ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((L.filtration.ι.app (op p)).f n))
        (Z : ∀ (_r _p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ r p n : ℤ, Z r p n =
          Fil p n ⊓ (Subobject.pullback (L.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (D : ∀ (_r _p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (L.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
        (FH : ∀ (n _p : ℤ), Subobject (L.X.homology n))
        (_ : ∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (L.filtration.ι.app (op p)) n)),
      ∃ (E : CohomologicalSpectralSequence
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier)))) 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          ((SheafOfModules.evaluation (structureSheafRing Y)
              (op (⊤ : Opens Y.carrier))).rightDerivedPlus p).obj
            ((DerivedCategory.Plus.homologyFunctor
                (SheafOfModules.{u} (structureSheafRing Y)) q).obj
              ((modulePushforward f).rightDerivedFunctorPlus.obj K)))) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.pullback (L.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
                Fil (p + 1) n)
            (kernelSubobject (L.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.«exists» (L.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
                Fil (p + 1) n)
            (imageSubobject (L.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) := by
  obtain ⟨L, hL, -, hE⟩ :=
    CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp
      (modulePushforward f)
      (SheafOfModules.evaluation (structureSheafRing Y) (op (⊤ : Opens Y.carrier)))
      (rightAcyclic_modulePushforward_obj f ⊤) K
  exact ⟨L, fun n => ⟨(hL n).some ≪≫ (DerivedCategory.Plus.homologyFunctor
    (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier)))) n).mapIso
      ((abutmentIso f).app K)⟩, hE⟩

end Stacks.Cohomology.LerayModules

end
