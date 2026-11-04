module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleDerivedSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleReductions
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.StratificationNoetherian
import StacksCore.Tactic.StacksAttribute

/-!
# Adic constructible complexes on the pro-étale site

Let `Λ` be a ring, `I ⊆ Λ` an ideal and `X` a scheme. An object `K` of `D(X_proét, Λ)` is
*adic constructible* when every affine open `U` of `X` decomposes as a finite disjoint union
`U = ∐ U_i` of constructible locally closed subschemes such that each restriction `K|_{U_i}` is
adic lisse, that is, pro-étale locally isomorphic to the complex
`\underline{M^a}^∧ → ⋯ → \underline{M^b}^∧` of completed constant sheaves attached to a finite
complex of finite projective `Λ^∧`-modules
(`AlgebraicGeometry.ProEtale.IsAdicLisseDerivedSheaf`).

The restriction `K ↦ K|_Z` along a morphism of schemes `g : Z ⟶ X` is the derived functor of the
inverse image `g⁻¹` of pro-étale sheaves of `Λ`-modules, which is exact, transported to
`D(X_proét, Λ)` through the equivalence of sheaves of `Λ`-modules with sheaves of modules over
the constant coefficient ring sheaf.

## Main definitions

In the namespace `AlgebraicGeometry.ProEtale`:

* `derivedInverseImage`: the restriction `K ↦ K|_Z` along a morphism of schemes, on unbounded
  derived categories `D(X_proét, Λ) ⥤ D(Z_proét, Λ)`.
* `IsAdicConstructibleViaDerivedInverseImage`: part (2) of the adic condition.

## Main results

In the namespace `AlgebraicGeometry.ProEtale`:

* `exists_stratification_connectedSpace_isFiniteTypeLocallyConstant`: on a Noetherian scheme,
  finitely many constructible sheaves of `Λ`-modules are simultaneously locally constant of
  finite type on the connected strata of one constructible decomposition of any affine open.
* `exists_stratification_connectedSpace_isFiniteTypeLocallyConstant_homology`: for `K` in
  `D_cons(X, Λ)` with `X` Noetherian, every affine open has a constructible decomposition with
  connected strata on which all cohomology sheaves of `K ⊗_Λ^L Λ/I` are locally constant of
  finite type.

## Implementation notes

The inverse image is `AlgebraicGeometry.ProEtale.proetaleModuleInverseImage`, the left Kan
extension along pro-étale base change followed by sheafification; it is the restriction through
which constructibility of sheaves of `Λ`-modules is read (Stacks 09AJ), so restriction to a
stratum means the same thing for complexes as for their cohomology sheaves.

## References

* [Stacks Project, Tag 09C4](https://stacks.math.columbia.edu/tag/09C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

/-- The restriction `K ↦ K|_Z` of an object of `D(X_proét, Λ)` along a morphism of schemes
`g : Z ⟶ X`: the inverse image of pro-étale sheaves of `Λ`-modules, which is exact, applied to
complexes and read in `D(Z_proét, Λ)` through `AlgebraicGeometry.ProEtale.derivedModuleEquiv`. -/
def derivedInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) (Λ : Type r) [CommRing Λ] :
    DerivedSheaves.{u, r, w} X Λ ⥤ DerivedSheaves.{u, r, w} Z Λ :=
  (derivedModuleEquiv.{u, r, w} X Λ).inverse ⋙
    (proetaleModuleInverseImage.{u, r, w} g Λ).mapDerivedCategory ⋙
      (derivedModuleEquiv.{u, r, w} Z Λ).functor

variable (X : Scheme.{u}) (Λ : Type r) [CommRing Λ] (I : Ideal Λ)

/-- **Stacks 09C4, part (2).** An object `K` of `D(X_proét, Λ)` is *adic constructible* if every
affine open `U` of `X` admits a decomposition `U = ∐ U_i` into constructible locally closed
subschemes such that every restriction `K|_{U_i}` is adic lisse. -/
@[stacks 09C4 "part (2): adic constructible"]
abbrev IsAdicConstructibleViaDerivedInverseImage (K : DerivedSheaves.{u, r, w} X Λ) : Prop :=
  ∀ U : X.affineOpens, ∃ s : Scheme.ConstructibleStratification X U.1,
    ∀ i, IsAdicLisseDerivedSheaf.{u, r, w} (s.piece i) Λ I
      ((derivedInverseImage.{u, r, w} (s.inclusion i) Λ).obj K)

/-- **A common connected trivializing stratification.** Let `X` be a Noetherian scheme and
`F₀, …, F_{m-1}` finitely many constructible sheaves of `Λ`-modules on `X_proét` (Stacks 09AJ).
Every affine open `U` of `X` has a single decomposition into constructible locally closed
subschemes whose strata are connected and on each of which every `F_k` restricts to a locally
constant sheaf of finite type.

The decompositions attached to the `F_k` have a common refinement, which is refined in turn by
one with connected strata, each an open subscheme of a stratum; restriction along an immersion
into a stratum preserves local constancy of finite type. -/
theorem exists_stratification_connectedSpace_isFiniteTypeLocallyConstant.{v}
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ] {m : ℕ}
    (F : Fin m → Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : ∀ k, IsConstructibleModuleSheaf'.{u, v, w} X Λ (F k)) (U : X.affineOpens) :
    ∃ s : Scheme.ConstructibleStratification X U.1, (∀ j, ConnectedSpace (s.piece j)) ∧
      ∀ k j, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
        (Scheme.ProEt.topology (s.piece j)) Λ
        ((proetaleModuleInverseImage.{u, v, w} (s.inclusion j) Λ).obj (F k)) := by
  choose s hs using fun k => hF k U
  obtain ⟨r, hr⟩ := Scheme.ConstructibleStratification.exists_refines_forall s
  obtain ⟨t, htc, htr⟩ := r.exists_connectedSpace_refines
  refine ⟨t, htc, fun k j => ?_⟩
  obtain ⟨i, q, -, hq⟩ := htr j
  obtain ⟨i', a, -, ha⟩ := hr k i
  have h : (q ≫ a) ≫ (s k).inclusion i' = t.inclusion j := by
    rw [Category.assoc, ha, hq]
  rw [← h]
  exact ObjectProperty.prop_of_iso _
    ((proetaleModuleInverseImageCompIso.{u, v, w} Λ (q ≫ a) ((s k).inclusion i')).app (F k))
    (isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage (q ≫ a) _ (hs k i'))

/-- **The cohomology of the reduction of a constructible complex is lisse on a connected
stratification.** Let `X` be a Noetherian scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and
`K` an object of `D_cons(X, Λ)`. Every affine open `U` of `X` has a decomposition into
constructible locally closed subschemes with connected strata on each of which every cohomology
sheaf of `K ⊗_Λ^L Λ/I` restricts to a locally constant sheaf of finite type.

`K ⊗_Λ^L Λ/I` has Tor amplitude in some `[a, b]` because `X` is quasi-compact, so only its
cohomology sheaves in degrees `a, …, b` can be nonzero; these finitely many sheaves are
constructible, and the zero sheaves are trivially locally constant. -/
theorem exists_stratification_connectedSpace_isFiniteTypeLocallyConstant_homology
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (max (u + 1) w)} [CommRing Λ]
    [IsNoetherianRing Λ] {I : Ideal Λ} {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K) (U : X.affineOpens) :
    ∃ s : Scheme.ConstructibleStratification X U.1, (∀ j, ConnectedSpace (s.piece j)) ∧
      ∀ (i : ℤ) j, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
          max (u + 1) w, max (u + 1) w}
        (Scheme.ProEt.topology (s.piece j)) (Λ ⧸ I)
        ((proetaleModuleInverseImage.{u, max (u + 1) w, w} (s.inclusion j) (Λ ⧸ I)).obj
          ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K))) := by
  obtain ⟨a, b, h⟩ := Stacks.ModuleSheaf.exists_hasTorAmplitude_of_locallyHasFiniteTorDimension
    Scheme.ProEt.isTerminal_mk_id (fun S hS => Scheme.ProEt.exists_finite_coversTop_le S hS)
    _ hK.2.2
  obtain ⟨hGE, hLE⟩ := h.isGE_isLE
  let H : ℤ → Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I)) := fun i =>
    (DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K)
  obtain ⟨s, hsc, hs⟩ := exists_stratification_connectedSpace_isFiniteTypeLocallyConstant.{u, w}
    (fun k : Fin (b - a + 1).toNat => H (a + k)) (fun k => hK.2.1 (a + k)) U
  refine ⟨s, hsc, fun i j => ?_⟩
  by_cases hi : a ≤ i ∧ i ≤ b
  · have hk : (i - a).toNat < (b - a + 1).toNat := by omega
    have hik : a + (((⟨(i - a).toNat, hk⟩ : Fin (b - a + 1).toNat) : ℕ) : ℤ) = i := by
      simp only
      omega
    have := hs ⟨(i - a).toNat, hk⟩ j
    rwa [hik] at this
  · apply Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_isZero
    refine Functor.map_isZero _ ?_
    rcases not_and_or.mp hi with hi | hi
    · exact ((derivedReduction.{u, w} X Λ I).obj K).isZero_of_isGE a i (by omega)
    · exact ((derivedReduction.{u, w} X Λ I).obj K).isZero_of_isLE b i (by omega)

end AlgebraicGeometry.ProEtale

end
