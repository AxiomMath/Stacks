module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedCriterion
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs

/-!
# Global functions on a geometrically connected proper scheme

The ring of global functions on a geometrically connected proper scheme over a field is
geometrically irreducible over that field.

## Main definitions

No new definitions are introduced.

## Main results

All of these live in the namespace `Stacks.AlgebraicGeometry.ProperSectionsGeom`.

* `isGeometricallyIrreducible_globalSections_of_isProper`: clause (5) of [Stacks, Tag 0BUG]. The
  global sections of a geometrically connected proper scheme over a field are geometrically
  irreducible.
* `isGeometricallyIrreducible_globalSections_of_geometricallyIrreducible`: clause (6) of
  [Stacks, Tag 0BUG]. The same conclusion for a geometrically *irreducible* proper scheme.
* `isIdempotentElem_eq_zero_or_one_of_preconnectedSpace`: a ring whose spectrum is preconnected
  has no idempotents other than `0` and `1`.
* `irreducibleSpace_primeSpectrum_of_isIntegral`: an algebra integral over a field whose spectrum
  is connected has irreducible spectrum.

## Implementation notes

The algebra structure on the global sections is the canonical one induced by the structure
morphism to the spectrum of the base field.

The proof does **not** go through degree-zero flat base change for cohomology (Stacks Tag 02KH),
which the Stacks proof uses in order to identify `Γ(X, ⊤) ⊗[k] k'` with `Γ(X_{k'}, ⊤)`.  That
input is available at the present pin — it is Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, instantiated at the top
open by `Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.isPushout_appTop` — and an earlier
version of this docstring wrongly called it absent;  it is simply not needed here.  The proof is
organized instead so that only *connectedness* of each base change `Spec (Γ(X, ⊤) ⊗[k] k')` is
needed, and that is obtained by pushing connectedness forward along a surjection rather than by
computing the ring:

* `X ⟶ Spec Γ(X, ⊤)` is surjective for `X` proper over a field
  (`ProperGeomConnected.surjective_toSpecΓ`), so `Spec Γ(X, ⊤)` is connected, being the image of
  the connected space `X`;
* Tag 056R (`geometricallyConnected_of_comp_of_connectedSpace`) upgrades this to geometric
  connectedness of `Spec Γ(X, ⊤) ⟶ Spec k`, because the composite with `X ⟶ Spec Γ(X, ⊤)` is the
  geometrically connected structure morphism of `X`;
* Tag 0386 (`geometricallyConnected_spec_iff`) turns that into connectedness of every
  `Spec (k' ⊗[k] Γ(X, ⊤))`.

Irreducibility is then a ring-theoretic consequence of connectedness, and this is where
properness enters a second time:  Mathlib's `isIntegral_appTop_of_universallyClosed` makes
`Γ(X, ⊤)` integral over `k`, hence `k' ⊗[k] Γ(X, ⊤)` integral over `k'`, hence of Krull dimension
zero; a connected spectrum has no nontrivial idempotents, and an algebra integral over a field
with no nontrivial idempotents is local of dimension zero, so its spectrum is a single point
(`Stacks.RingTheory.IntegralOverField.subsingleton_primeSpectrum`).  A nonempty subsingleton space
is irreducible.  Finiteness of `Γ(X, ⊤)` over `k` — part (1) of the tag, i.e. finiteness of
coherent cohomology — is therefore *not* needed.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0386](https://stacks.math.columbia.edu/tag/0386)
* [Stacks Project, Tag 056R](https://stacks.math.columbia.edu/tag/056R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ProperSectionsGeom

/-- A commutative ring whose prime spectrum is preconnected has no idempotents other than `0`
and `1`:  the basic open of an idempotent is clopen, hence empty or everything, and an idempotent
is determined by its basic open. -/
theorem isIdempotentElem_eq_zero_or_one_of_preconnectedSpace {R : Type u} [CommRing R]
    [PreconnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases _root_.isClopen_iff.mp (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩) with h | h
  · exact Or.inl (PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.zero
      (SetLike.ext' (h.trans (by simp))))
  · exact Or.inr (PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.one
      (SetLike.ext' (h.trans (by simp))))

/-- An algebra integral over a field whose spectrum is connected has irreducible spectrum:  the
spectrum is in fact a single point. -/
theorem irreducibleSpace_primeSpectrum_of_isIntegral (K R : Type u) [Field K] [CommRing R]
    [Algebra K R] [Algebra.IsIntegral K R] [ConnectedSpace (PrimeSpectrum R)] :
    IrreducibleSpace (PrimeSpectrum R) := by
  have hne : Nonempty (PrimeSpectrum R) := inferInstance
  have hnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exact absurd hne (not_nonempty_iff.mpr inferInstance)
    · exact h
  have hsub : Subsingleton (PrimeSpectrum R) :=
    Stacks.RingTheory.IntegralOverField.subsingleton_primeSpectrum (K := K)
      (fun _ he => isIdempotentElem_eq_zero_or_one_of_preconnectedSpace he)
  exact ⟨hne⟩

/-- **[Stacks, Tag 0BUG] (5).** Let `X` be a geometrically connected proper scheme over a field
`k`. Then the ring of global sections of `X`, with its canonical `k`-algebra structure, is
geometrically irreducible over `k`. -/
@[stacks 0BUG "clause (5): for a GEOMETRICALLY CONNECTED proper scheme over a field k, the global \
sections are geometrically irreducible over k: every base change to a field extension of k has \
irreducible spectrum."]
theorem isGeometricallyIrreducible_globalSections_of_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [GeometricallyConnected f] [IsProper f] :
    letI : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Algebra.IsGeometricallyIrreducible k Γ(X, ⊤) := by
  let alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hint : Algebra.IsIntegral k Γ(X, ⊤) := ⟨fun x => by
    rw [_root_.IsIntegral, RingHom.algebraMap_toAlgebra]
    exact ProperGeomConnected.isIntegral_toSpecΓ_algebraMap f x⟩
  have hXconn : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton f
  have hconnSpec : ConnectedSpace (Spec Γ(X, ⊤)) := by
    rw [connectedSpace_iff_univ,
      ← Set.range_eq_univ.mpr (ProperGeomConnected.surjective_toSpecΓ f)]
    exact isConnected_range X.toSpecΓ.continuous
  have hfac : X.toSpecΓ ≫ Spec.map (ofHom (algebraMap k Γ(X, ⊤))) = f := by
    show X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hgc : GeometricallyConnected
      (X.toSpecΓ ≫ Spec.map (ofHom (algebraMap k Γ(X, ⊤)))) := by
    rw [hfac]
    infer_instance
  have hGC : GeometricallyConnected (Spec.map (ofHom (algebraMap k Γ(X, ⊤)))) :=
    geometricallyConnected_of_comp_of_connectedSpace k X.toSpecΓ _
  have hgcAlg : Algebra.IsGeometricallyConnected k Γ(X, ⊤) :=
    (geometricallyConnected_spec_iff k Γ(X, ⊤)).mp hGC
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro k' _ _
  have := hgcAlg.connectedSpace_primeSpectrum_tensorProduct k'
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm k k' Γ(X, ⊤)).toRingEquiv).irreducibleSpace_iff.mp
      (irreducibleSpace_primeSpectrum_of_isIntegral k' (k' ⊗[k] Γ(X, ⊤)))

/-- **[Stacks, Tag 0BUG] (6).** Let `X` be a geometrically *irreducible* proper scheme over a
field `k`. Then the ring of global sections of `X`, with its canonical `k`-algebra structure, is
geometrically irreducible over `k`.

A geometrically irreducible morphism is geometrically connected, every base change of it having
an irreducible and hence connected underlying space, so this is clause (5) applied to the same
`X`. -/
@[stacks 0BUG "clause (6): for a GEOMETRICALLY IRREDUCIBLE proper scheme over a field k, the \
global sections are geometrically irreducible over k. The source deduces this clause from clause \
(5) by the remark that a geometrically irreducible scheme is geometrically connected, and that \
is what is done here: every base change has an irreducible, hence connected, underlying space."]
theorem isGeometricallyIrreducible_globalSections_of_geometricallyIrreducible
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [GeometricallyIrreducible f] [IsProper f] :
    letI : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Algebra.IsGeometricallyIrreducible k Γ(X, ⊤) :=
  have : GeometricallyConnected f := ⟨fun _ _ y Z fst snd h => by
    have := ‹GeometricallyIrreducible f›.geometrically_irreducibleSpace y fst snd h
    infer_instance⟩
  isGeometricallyIrreducible_globalSections_of_isProper k f

end Stacks.AlgebraicGeometry.ProperSectionsGeom

end
