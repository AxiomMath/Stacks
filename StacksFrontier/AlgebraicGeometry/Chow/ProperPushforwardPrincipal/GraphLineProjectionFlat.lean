module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import
  StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GraphLineProjectionFinite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local rings of the projective line are Bezout, and the graph projection is flat

The second projection `q : Y ⟶ ℙ¹_S` out of the graph closure of Stacks 02RQ is **flat** when it
is dominant. Together with finiteness
(`Stacks.Chow.isFinite_graphLineProjection`) this is what makes `q` finite locally free, which is
the shape in which the dominant branch of the proof of Stacks 02RU uses it.

The mechanism is torsion-freeness, not a dimension count. A dominant morphism of integral schemes
induces an **injective** map on local rings (Stacks 0CC1,
`AlgebraicGeometry.tfae_isDominant_of_isIntegral`), and the local rings of an integral scheme are
domains; so each local ring of `Y` is a torsion-free module over the corresponding local ring of
`ℙ¹_S`. Over a Bezout domain torsion-free modules are flat (Stacks 0539,
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`), so all that is needed is that the local rings
of `ℙ¹_S` are Bezout domains — and they are, being localizations of a polynomial ring in one
variable over a field, which is a principal ideal domain.

That last step is where the two affine charts of `ℙ¹_S` are used. A point of `ℙ¹_S` lies on one of
them (`Stacks.Chow.range_affineChart_union_range_affineYChart`), each is an open immersion from
`𝔸¹_S`, and an open immersion induces isomorphisms on local rings; `𝔸¹_{Spec k}` is the spectrum
of `k[T]` (`Stacks.Chow.affineLineOverIsoSpecPolynomial`), whose local rings are the
localizations `k[T]_𝔭`. No standard-open cover of the charts and no identification of the closed
points of `ℙ¹_k` is needed.

## Main definitions

* `Stacks.Chow.specPolynomialIsoSpecMvPolynomialOfBase` — `Spec R[T]` is the spectrum of the
  one-element-indexed multivariate polynomial ring over `R`.
* `Stacks.Chow.affineLineOverIsoSpecPolynomial` — `𝔸¹_{Spec R}` is `Spec R[T]`.

## Main results

* `isBezout_of_ringEquiv` — the Bezout property transports along a ring isomorphism.
* `Stacks.Chow.flat_of_injective_of_isBezout` — an injective ring map from a Bezout domain to a
  domain is flat.
* `Stacks.Chow.flat_of_isDominant_of_isBezout_stalk` — a dominant morphism of integral schemes
  whose target has Bezout local rings is flat.
* `Stacks.Chow.isBezout_stalk_affineLineOver` and
  `Stacks.Chow.isBezout_stalk_relativeProjectiveLine` — the local rings of `𝔸¹_k` and of `ℙ¹_k`
  are Bezout domains.
* `Stacks.Chow.flat_graphLineProjection` — **the second projection out of the graph closure is
  flat** when it is dominant.
* `Stacks.Chow.isFiniteLocallyFree_graphLineProjection` — **that projection is finite locally
  free**, which is Stacks 02KA for it without its rank.

## Implementation notes

### Why Bezout and not Dedekind

`Module.Flat` has three torsion-free criteria at this pin: over a Bezout domain, over a ring all
of whose localizations at maximal ideals are valuation rings, and over a Dedekind domain. The
Bezout one is the cheapest here, because the local rings in question are *presented* as
localizations of a principal ideal domain and `IsBezout` is then an instance; identifying them as
discrete valuation rings would additionally need their dimension.

### What this does not prove, and why no rank appears

Finiteness and flatness give `IsFiniteLocallyFree q`, but **not** the constant-rank form
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank q d` that Stacks 02KB and 02KA are stated for. The
rank is locally constant (Stacks 01C9) and `ℙ¹_S` is connected, so it is constant; the repository
has 01C9 only as an *existence* statement (`exists_locallyConstant_rank`), which does not produce
the integer. The integer itself is available with no appeal to 01C9: it is
`Scheme.Hom.residueDegree q (genericPoint Y)`, the degree of the function-field extension, since
the residue field at the generic point of an integral scheme is its function field. What is
missing is the identification of that integer with the rank at every point, which is the
local-constancy argument.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 0CC1](https://stacks.math.columbia.edu/tag/0CC1)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- The Bezout property transports along a ring isomorphism: an isomorphism carries finitely
generated ideals to finitely generated ideals and principal ideals to principal ideals. -/
theorem isBezout_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    [IsBezout R] : IsBezout S where
  isPrincipal_of_FG J hJ := by
    have h1 : J.map (e.symm : S →+* R) = J.comap (e : R →+* S) := Ideal.map_symm e
    have hfg : (J.comap (e : R →+* S)).FG := h1 ▸ hJ.map (e.symm : S →+* R)
    obtain ⟨a, ha⟩ := IsBezout.isPrincipal_of_FG _ hfg
    refine ⟨e a, ?_⟩
    rw [← Ideal.map_comap_of_surjective (e : R →+* S) e.surjective J, ha, Ideal.map_span]
    simp

namespace Stacks.Chow

/-! ### Flatness from torsion-freeness -/

/-- An injective ring map from a Bezout domain to a domain is flat: the target is torsion-free as
a module over the source, and over a Bezout domain that is flatness (Stacks 0539). -/
@[ega "0 6.3.4" "last assertion, A Bézout", sga "1 IV 1.3" "(ii)"]
theorem flat_of_injective_of_isBezout {R S : Type u} [CommRing R] [CommRing S] [IsBezout R]
    [IsDomain R] [IsDomain S] {f : R →+* S} (hf : Function.Injective f) : f.Flat := by
  rw [RingHom.Flat]
  let _ : Algebra R S := f.toAlgebra
  have _ : NoZeroSMulDivisors R S := by
    refine ⟨fun {r m} h ↦ ?_⟩
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hf (by simpa using h))
    · exact Or.inr h
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- **A dominant morphism of integral schemes whose target has Bezout local rings is flat.** By
Stacks 0CC1 a dominant morphism of integral schemes is injective on local rings, and the local
rings of an integral scheme are domains. -/
theorem flat_of_isDominant_of_isBezout_stalk {P Y : Scheme.{u}} [IsIntegral P] [IsIntegral Y]
    (q : Y ⟶ P) [IsDominant q]
    (hbez : ∀ y : P, IsBezout (P.presheaf.stalk y)) : Flat q := by
  refine Flat.of_stalkMap q fun x ↦ ?_
  have _ := hbez (q.base x)
  have hall : ∀ z : Y, Function.Injective (q.stalkMap z) :=
    ((tfae_isDominant_of_isIntegral q).out 1 6).mp ‹IsDominant q›
  have hinj : Function.Injective (q.stalkMap x) := hall x
  exact flat_of_injective_of_isBezout (f := (q.stalkMap x).hom) hinj

/-! ### The affine line is the spectrum of a polynomial ring -/

/-- The spectra of the one-variable and of the one-element-indexed multivariate polynomial ring
over a ring `R` are isomorphic. This is
`Stacks.Chow.specPolynomialIsoSpecMvPolynomial` with an arbitrary base in place of the
integers. -/
def specPolynomialIsoSpecMvPolynomialOfBase (R : CommRingCat.{u}) :
    Spec (CommRingCat.of (Polynomial ↑R)) ≅
      Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} ↑R)) :=
  Scheme.Spec.mapIso
    ((MvPolynomial.uniqueAlgEquiv ↑R PUnit.{u + 1}).toRingEquiv.toCommRingCatIso).op

/-- **The affine line over `Spec R` is the spectrum of the polynomial ring `R[T]`.** It is
Mathlib's affine space on a one-element index type (`Stacks.Chow.affineLineOverIsoAffineSpace`),
which over an affine base is the spectrum of a multivariate polynomial ring
(`AlgebraicGeometry.AffineSpace.SpecIso`), and a one-element index type gives the one-variable
polynomial ring. -/
def affineLineOverIsoSpecPolynomial (R : CommRingCat.{u}) :
    affineLineOver (Spec R) ≅ Spec (CommRingCat.of (Polynomial ↑R)) :=
  affineLineOverIsoAffineSpace (Spec R) ≪≫ AffineSpace.SpecIso PUnit.{u + 1} R ≪≫
    (specPolynomialIsoSpecMvPolynomialOfBase R).symm

/-! ### The local rings of the affine and projective line over a field are Bezout -/

/-- The local rings of `𝔸¹_k` are Bezout domains: `𝔸¹_{Spec k}` is `Spec k[T]`, whose local rings
are the localizations of the principal ideal domain `k[T]`. -/
theorem isBezout_stalk_affineLineOver (k : Type u) [Field k]
    (z : affineLineOver (Spec (CommRingCat.of k))) :
    IsBezout ((affineLineOver (Spec (CommRingCat.of k))).presheaf.stalk z) := by
  have hiso : IsIso ((affineLineOverIsoSpecPolynomial (CommRingCat.of k)).hom.stalkMap z) :=
    inferInstance
  exact isBezout_of_ringEquiv
    (((Spec.stalkIso (CommRingCat.of (Polynomial ↑(CommRingCat.of k)))
          ((affineLineOverIsoSpecPolynomial (CommRingCat.of k)).hom.base z)).symm ≪≫
        asIso ((affineLineOverIsoSpecPolynomial (CommRingCat.of k)).hom.stalkMap
          z)).commRingCatIsoToRingEquiv)

/-- **The local rings of `ℙ¹_k` are Bezout domains.** Every point lies on one of the two affine
charts, each an open immersion from `𝔸¹_k`, and an open immersion induces isomorphisms on local
rings. -/
theorem isBezout_stalk_relativeProjectiveLine (k : Type u) [Field k]
    (y : relativeProjectiveLine (Spec (CommRingCat.of k))) :
    IsBezout ((relativeProjectiveLine (Spec (CommRingCat.of k))).presheaf.stalk y) := by
  rcases Set.eq_univ_iff_forall.mp
      (range_affineChart_union_range_affineYChart (Spec (CommRingCat.of k))) y with
    ⟨z, rfl⟩ | ⟨z, rfl⟩ <;>
  · have _ := isBezout_stalk_affineLineOver k z
    exact isBezout_of_ringEquiv (asIso (Scheme.Hom.stalkMap _ z)).commRingCatIsoToRingEquiv.symm

/-! ### The graph projection is flat -/

/-- **The second projection out of the graph closure of Stacks 02RQ is flat**, when it is dominant
and the curve lies over the spectrum of a field.

With `Stacks.Chow.isFinite_graphLineProjection` this makes `q` finite flat; what is still missing
before Stacks 02KB and 02KA apply is the constancy of its rank. See the implementation notes. -/
theorem flat_graphLineProjection (k : Type u) [Field k] (C : ChowSituation.{u}) [IsIntegral C.S]
    (hS : C.S = AlgebraicGeometry.Spec (.of k))
    {X : Scheme.{u}} (sX : X ⟶ C.S) (U : X.Opens) (g : (Γ(X, U))ˣ)
    (hYint : IsIntegral (graphClosure sX U ↑g))
    (hdom : IsDominant (graphLineProjection sX U ↑g)) :
    Flat (graphLineProjection sX U ↑g) := by
  have := hYint
  have := hdom
  have hbez : ∀ y : relativeProjectiveLine C.S,
      IsBezout ((relativeProjectiveLine C.S).presheaf.stalk y) := by
    rw [hS]
    exact isBezout_stalk_relativeProjectiveLine k
  exact flat_of_isDominant_of_isBezout_stalk (graphLineProjection sX U ↑g) hbez

/-- **The second projection out of the graph closure of Stacks 02RQ is finite locally free**, when
it is dominant and the curve lies over the spectrum of a field.

This is Stacks 02KA for `q` without its rank: `q` is finite
(`Stacks.Chow.isFinite_graphLineProjection`), flat (`Stacks.Chow.flat_graphLineProjection`) and
locally of finite presentation, being locally of finite type over the locally Noetherian `ℙ¹_S`.
The rank is not supplied; see the implementation notes of this file for what is missing between
here and `Stacks.Morphisms.IsFiniteLocallyFreeOfRank`. -/
theorem isFiniteLocallyFree_graphLineProjection (k : Type u) [Field k] (C : ChowSituation.{u})
    [IsIntegral C.S] (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [IsProper sX] [IsIntegral X]
    (U : X.Opens) (g : (Γ(X, U))ˣ)
    (hYint : IsIntegral (graphClosure sX U ↑g))
    (hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g))
    (hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (1 : EInt))
    (hdom : IsDominant (graphLineProjection sX U ↑g)) :
    Stacks.Morphisms.IsFiniteLocallyFree (graphLineProjection sX U ↑g) := by
  rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
  refine ⟨isFinite_graphLineProjection k C hS hδ sX U g hYint hYft hYdim hdom,
    flat_graphLineProjection k C hS sX U g hYint hdom, inferInstance⟩

end Stacks.Chow

end
