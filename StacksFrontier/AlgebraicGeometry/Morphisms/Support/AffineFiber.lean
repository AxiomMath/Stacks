module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.RingTheory.Support.Fiber

/-!
# The support of the fibre module of a module on an affine scheme

Let `f : X ⟶ S` be a morphism of affine schemes, let `ℱ` be a quasi-coherent `𝒪_X`-module of
finite type, let `s` be a point of `S` and let `r` be the prime of `Γ(S, ⊤)` corresponding to
`s`. This file identifies the stalkwise support of the pullback of `ℱ` to the scheme-theoretic
fibre of `f` over `s` with the part of `Supp_{Γ(X, ⊤)}(Γ(ℱ, ⊤))` lying over `r`, which is
`Module.fiberSupport`.

Both are subspaces of `Spec Γ(X, ⊤)`, through the embedding
`AlgebraicGeometry.Scheme.Hom.fiberToSpecΓ` of the fibre: a point of the fibre of `f` over `s`
is a point of `X`, hence a prime of `Γ(X, ⊤)`, and the primes so obtained are exactly those
lying over `r`. The support condition is then the affine dictionary for supports,
`AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp` (Stacks 056I), together
with the computation `Stacks.Modules.supp_pullback` (Stacks 056J) of the support of a pullback.

The same embedding identifies the whole fibre with the fibre of `Spec Γ(X, ⊤) → Spec Γ(S, ⊤)`,
which computes the dimension of a fibre of a morphism of affine schemes ring-theoretically.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.fiberToSpecΓ`: a point of the fibre of a morphism of affine
  schemes, read as a prime of the ring of functions on the source.
* `AlgebraicGeometry.suppFiberHomeomorph`: **the support of the fibre module is the part of the
  support of the module of sections lying over the prime of the base point.**

## Main results

* `AlgebraicGeometry.Scheme.Hom.isEmbedding_fiberToSpecΓ` and
  `AlgebraicGeometry.Scheme.Hom.range_fiberToSpecΓ`: the fibre embeds in `Spec Γ(X, ⊤)` with
  image the fibre of `Spec Γ(X, ⊤) → Spec Γ(S, ⊤)`.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_fiber_eq`: the dimension of a fibre of a
  morphism of affine schemes is the dimension of the corresponding fibre of spectra.
* `AlgebraicGeometry.topologicalKrullDim_supp_fiber` and
  `AlgebraicGeometry.topologicalKrullDimAt_supp_fiber`: the dimension, and the local dimension
  at a point, of the support of the fibre module, read on rings.

## Implementation notes

The algebra structure on `Γ(X, ⊤)` over `Γ(S, ⊤)` is a hypothesis together with the equation
identifying its structure map with `f.appTop`, rather than `f.appTop.hom.toAlgebra`: a consumer
has a structure fixed in advance by the object it is translating, and the equation is `rfl` for
the structure induced by `f`.

Primes are likewise passed as variables with an equation identifying them with
`(X.isoSpec.hom x).asIdeal`, as in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraDictionaryAt.lean`: the
`Ideal.IsPrime` instance of a prime read off a point is not found by instance synthesis.

`AlgebraicGeometry.Scheme.Hom.fiberToSpecΓ` is declared with target `PrimeSpectrum Γ(X, ⊤)`
rather than the carrier of the scheme `Spec Γ(X, ⊤)`. The two agree by `rfl`, but a set of
points of the scheme and a set of primes are not interchangeable under the transparency the
`Set` lemmas are applied at, and everything here is stated about sets of primes.

## References

* [Stacks Project, Tag 056I](https://stacks.math.columbia.edu/tag/056I)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} [IsAffine X] [IsAffine S]

/-! ### Points of an affine scheme as primes -/

/-- The prime of `Γ(X, ⊤)` attached to a point of an affine scheme by the affine dictionary is
the prime read off the canonical isomorphism `X ≅ Spec Γ(X, ⊤)`. -/
public theorem primeIdealOf_top (x : X) :
    (isAffineOpen_top X).primeIdealOf ⟨x, by simp⟩ = X.isoSpec.hom x := by
  change (⊤ : X.Opens).toSpecΓ ⟨x, by simp⟩ = X.isoSpec.hom x
  rw [Scheme.Opens.toSpecΓ_top, Scheme.isoSpec_hom]
  rfl

/-- The prime attached to a point of the source of a morphism of affine schemes contracts to
the prime attached to its image. -/
public theorem comap_algebraMap_isoSpec_hom (f : X ⟶ S) [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) = f.appTop.hom) (x : X) :
    PrimeSpectrum.comap (algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)))
        (X.isoSpec.hom x) = S.isoSpec.hom (f x) := by
  rw [halg]
  change Spec.map f.appTop (X.isoSpec.hom x) = _
  rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality f, Scheme.Hom.comp_apply]

/-! ### The fibre of a morphism of affine schemes as a set of primes -/

/-- A point of the fibre of a morphism of affine schemes over `s`, read as a prime of the ring
of functions on the source. -/
public def Scheme.Hom.fiberToSpecΓ (f : X ⟶ S) (s : S) (w : f.fiber s) :
    PrimeSpectrum Γ(X, (⊤ : X.Opens)) :=
  X.isoSpec.hom (f.fiberι s w)

omit [IsAffine S] in
/-- Reading a point of a fibre as a prime of the functions on the source is a topological
embedding: it is the fibre inclusion followed by a homeomorphism. -/
public theorem Scheme.Hom.isEmbedding_fiberToSpecΓ (f : X ⟶ S) (s : S) :
    Topology.IsEmbedding (f.fiberToSpecΓ s) :=
  (Scheme.homeoOfIso X.isoSpec).isEmbedding.comp (f.fiberι s).isEmbedding

/-- **The primes of `Γ(X, ⊤)` coming from the fibre of `f` over `s` are exactly those lying
over the prime of `s`.** -/
public theorem Scheme.Hom.range_fiberToSpecΓ (f : X ⟶ S) [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) = f.appTop.hom) (s : S)
    (r : Ideal Γ(S, (⊤ : S.Opens))) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r) :
    Set.range (f.fiberToSpecΓ s) =
      PrimeSpectrum.comap (algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens))) ⁻¹'
        {(⟨r, ‹_›⟩ : PrimeSpectrum Γ(S, (⊤ : S.Opens)))} := by
  have hs : S.isoSpec.hom s = (⟨r, ‹_›⟩ : PrimeSpectrum Γ(S, (⊤ : S.Opens))) :=
    PrimeSpectrum.ext hr
  ext p
  have hinv : X.isoSpec.hom (X.isoSpec.inv p) = p :=
    (Scheme.homeoOfIso X.isoSpec).apply_symm_apply p
  have hrange (y : X) : y ∈ Set.range (f.fiberι s) ↔ f y = s := by
    rw [f.range_fiberι s]
    rfl
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, rfl⟩
    have hfw := (hrange _).1 (Set.mem_range_self w)
    change PrimeSpectrum.comap _ (X.isoSpec.hom (f.fiberι s w)) = _
    rw [comap_algebraMap_isoSpec_hom f halg, hfw, hs]
  · intro hp
    have hy : f (X.isoSpec.inv p) = s := by
      refine (Scheme.homeoOfIso S.isoSpec).injective ?_
      change S.isoSpec.hom _ = S.isoSpec.hom s
      rw [← comap_algebraMap_isoSpec_hom f halg, hinv, hs]
      exact hp
    obtain ⟨w, hw⟩ := (hrange _).2 hy
    refine ⟨w, ?_⟩
    change X.isoSpec.hom (f.fiberι s w) = p
    rw [hw, hinv]

/-- **The dimension of a fibre of a morphism of affine schemes is the dimension of the
corresponding fibre of prime spectra.** -/
public theorem Scheme.Hom.topologicalKrullDim_fiber_eq (g : X ⟶ S) [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) = g.appTop.hom) (s : S)
    (r : Ideal Γ(S, (⊤ : S.Opens))) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r) :
    topologicalKrullDim (g.fiber s) =
      topologicalKrullDim ↥(PrimeSpectrum.comap
        (algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens))) ⁻¹'
          {(⟨r, ‹_›⟩ : PrimeSpectrum Γ(S, (⊤ : S.Opens)))}) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (((g.isEmbedding_fiberToSpecΓ s).toHomeomorph).trans
      (Homeomorph.setCongr (g.range_fiberToSpecΓ halg s r hr))).isHomeomorph

/-! ### The support of the fibre module -/

variable (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

omit [SheafOfModules.IsFiniteType F] in
/-- **Stacks 056I over the whole of an affine scheme.** A point of an affine scheme lies in the
support of a quasi-coherent module exactly when the corresponding prime lies in the support of
the module of global sections. -/
public theorem mem_support_sections_iff_mem_supp_top (x : X) :
    X.isoSpec.hom x ∈ Module.support Γ(X, (⊤ : X.Opens)) Γ(F, (⊤ : X.Opens)) ↔
      x ∈ SheafOfModules.supp F := by
  rw [← primeIdealOf_top x]
  exact Scheme.Modules.mem_support_sections_iff_mem_supp F ⟨⊤, isAffineOpen_top X⟩ x (by simp)

omit [IsAffine S] in
/-- The support of the fibre module is the inverse image of the support of the module of
sections under the reading of the fibre as a set of primes. -/
public theorem supp_pullback_fiberι_eq_preimage (s : S) :
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) =
      f.fiberToSpecΓ s ⁻¹' Module.support Γ(X, (⊤ : X.Opens)) Γ(F, (⊤ : X.Opens)) := by
  rw [Stacks.Modules.supp_pullback (f.fiberι s) F]
  ext w
  exact (mem_support_sections_iff_mem_supp_top F (f.fiberι s w)).symm

/-- **The support of the fibre module, read as a set of primes of `Γ(X, ⊤)`, is the part of the
support of the module of sections lying over the prime of the base point.** -/
public theorem image_supp_pullback_fiberι [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) = f.appTop.hom) (s : S)
    (r : Ideal Γ(S, (⊤ : S.Opens))) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r) :
    f.fiberToSpecΓ s '' SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) =
      Module.fiberSupport Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens))
        Γ(F, (⊤ : X.Opens)) r := by
  rw [supp_pullback_fiberι_eq_preimage f F s, Set.image_preimage_eq_inter_range,
    f.range_fiberToSpecΓ halg s r hr]
  rfl

/-- **The support of the fibre module of a quasi-coherent module on an affine scheme is the part
of the support of its module of sections lying over the prime of the base point.** -/
public def suppFiberHomeomorph [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) = f.appTop.hom) (s : S)
    (r : Ideal Γ(S, (⊤ : S.Opens))) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r) :
    ↥(SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≃ₜ
      ↥(Module.fiberSupport Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) Γ(F, (⊤ : X.Opens)) r) :=
  ((f.isEmbedding_fiberToSpecΓ s).homeomorphImage
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F))).trans
    (Homeomorph.setCongr (image_supp_pullback_fiberι f F halg s r hr))

/-- The dimension of the support of the fibre module, read on rings. -/
public theorem topologicalKrullDim_supp_fiber [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) = f.appTop.hom) (s : S)
    (r : Ideal Γ(S, (⊤ : S.Opens))) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r) :
    topologicalKrullDim ↥(SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι s)).obj F)) =
      topologicalKrullDim ↥(Module.fiberSupport Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens))
        Γ(F, (⊤ : X.Opens)) r) :=
  IsHomeomorph.topologicalKrullDim_eq _ (suppFiberHomeomorph f F halg s r hr).isHomeomorph

/-- The local dimension of the support of the fibre module at a point of the source, read on
rings. -/
public theorem topologicalKrullDimAt_supp_fiber [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) = f.appTop.hom) (x : X)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (r : Ideal Γ(S, (⊤ : S.Opens))) [r.IsPrime] (hr : (S.isoSpec.hom (f x)).asIdeal = r)
    (p : Ideal Γ(X, (⊤ : X.Opens))) [p.IsPrime] (hp : (X.isoSpec.hom x).asIdeal = p)
    (hmem : (⟨p, ‹_›⟩ : PrimeSpectrum Γ(X, (⊤ : X.Opens))) ∈
      Module.fiberSupport Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) Γ(F, (⊤ : X.Opens)) r) :
    topologicalKrullDimAt ↥(SheafOfModules.supp
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) ⟨f.asFiber x, hx⟩ =
      topologicalKrullDimAt ↥(Module.fiberSupport Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens))
        Γ(F, (⊤ : X.Opens)) r) ⟨⟨p, ‹_›⟩, hmem⟩ := by
  refine (topologicalKrullDimAt_eq_of_homeomorph
    (suppFiberHomeomorph f F halg (f x) r hr) ⟨f.asFiber x, hx⟩).trans ?_
  refine congrArg _ (Subtype.ext ?_)
  change X.isoSpec.hom (f.fiberι (f x) (f.asFiber x)) =
    (⟨p, ‹_›⟩ : PrimeSpectrum Γ(X, (⊤ : X.Opens)))
  rw [Scheme.Hom.fiberι_asFiber]
  exact PrimeSpectrum.ext hp

end AlgebraicGeometry

end
