module

public import StacksFrontier.Homology.Tor.DerivedTensorProductIsLE
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIso
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
public import StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormulaNatural
public import StacksFrontier.RingTheory.Dualizing.RelativeUniqueness

/-!
# The Tor-amplitude bound of [stacks 0ATK] (3) descends from the diagonal to `A`

Let `R → A` be a flat ring map, put `B = A ⊗[R] A`, write `p₁ : A → B` for the left coprojection
and `Δ : B → A` for the multiplication map.  The proof of [stacks 0E2D] in the source cites
[stacks 0ATK] (3) at the two tensor--Hom diagonals of the base changes, and part (3) of that tag
asks for the *tensor factor* to have Tor amplitude bounded below **over `B`**.  In this library
that hypothesis is carried by
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude`, whose docstring reads it
as a weakening of perfectness of the base change.

This file proves that it is not a weakening of anything: **a lower Tor-amplitude bound on
`p₁^*K` over `B` is a lower Tor-amplitude bound on `K` over `A`**.

## The one-line reason

Every `A`-module is the restriction along `p₁` of a `B`-module, namely of its own restriction
along `Δ`, because `Δ ∘ p₁ = id`.  Testing the bound over `B` against those `B`-modules therefore
tests it over `A`, and the identification of the two tensor products is the projection formula at
the diagonal

`Δ_*(M ⊗ᴸ_A Z) ≅ Δ_*M ⊗ᴸ_B p₁^*Z`

of `Dualizing.diagonalProjectionNatIso`, read at `M` a module placed in degree zero and `Z = K`.
Nothing is carried: that projection formula needs only flatness of `A` over `R`, and restriction
of scalars along `Δ` is exact and faithful, so it reflects vanishing of homology.

## Main results

* `Dualizing.isZero_of_isZero_restrictScalars` — restriction of scalars reflects zero modules.
* `Dualizing.isZero_homology_of_isZero_homology_mapDerivedCategory_restrictScalars` — hence
  derived restriction of scalars reflects vanishing of a homology object.  This is the converse
  of `Dualizing.isGE_mapDerivedCategory_restrictScalars`.
* `Dualizing.nonempty_restrictScalars_canonicalTensor_single_iso` — the projection formula at the
  diagonal in the spelling the Tor-amplitude hypothesis uses:
  `Δ_*(K ⊗ᴸ_A N) ≅ p₁^*K ⊗ᴸ_B Δ_*N` for a module `N` placed in degree zero.
* `Dualizing.torAmplitude_of_diagonalDerivedExtension` — **the descent**: the lower Tor-amplitude
  bound on `p₁^*K` over `B` gives the same bound on `K` over `A`.

## What this says about the route through [stacks 0ATK] (3)

`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude` carries exactly the bound
descended here, for `K` and for `L`.  Its docstring records the bound as strictly weaker than
perfectness of the base change, which is formally true — a perfect object has Tor amplitude
bounded below — but is not a weakening in substance: with the bound descended to `A` by the
theorem below, and a relative dualizing complex being pseudo-coherent and bounded, the two
hypotheses single out the same objects, so the source's own route to [stacks 0E2D] reaches no
further than
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange` does.  The last
step of that reading, pseudo-coherence together with a Tor-amplitude window giving perfectness,
is `StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension` together with
`StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative`; it is *not* carried out
below, and the theorem proved here is only the descent of the bound itself.

The witness of the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation` — `R = k` a field,
`A = k[x, y]/(x, y)²`, `K = L = Hom_k(A, k)` — is a relative dualizing complex that is not
perfect over `A`, its `Tor_i` against the residue field being nonzero in every degree.  So the
bound fails there, which is the same thing the refutation observes about the base change over
`B`, and this theorem explains why the two observations are one.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

section Reflect

/-- **Restriction of scalars reflects zero modules.**  Restriction along `f : S →+* T` is
faithful and additive, so a module whose restriction has a zero identity has a zero identity. -/
theorem isZero_of_isZero_restrictScalars {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) {M : ModuleCat.{u} T}
    (h : IsZero ((ModuleCat.restrictScalars.{u} f).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  refine (ModuleCat.restrictScalars.{u} f).map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h

/-- **Derived restriction of scalars reflects vanishing of homology.**  Restriction of scalars is
exact, so it commutes with the homology of the derived category by
`CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`, and it reflects zero modules
by `Dualizing.isZero_of_isZero_restrictScalars`.

This is the converse of `Dualizing.isGE_mapDerivedCategory_restrictScalars`, which only needs
that an additive functor carries a zero object to a zero object. -/
theorem isZero_homology_of_isZero_homology_mapDerivedCategory_restrictScalars
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (K : DerivedCategory (ModuleCat.{u} T)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) i).obj K) :=
  isZero_of_isZero_restrictScalars f
    ((((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryCompHomologyFunctorIso
      i).app K).isZero_iff.mp h)

end Reflect

section Descent

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]

/-- **The projection formula at the diagonal, in the spelling the Tor-amplitude hypothesis of
[stacks 0ATK] (3) uses.**  For an object `K` of `D(A)` and an `A`-module `N`,

`Δ_*(K ⊗ᴸ_A N[0]) ≅ p₁^*K ⊗ᴸ_B (Δ_*N)[0]`   in `D(B)`,   `B = A ⊗[R] A`,

with both derived tensor products the canonical one of [stacks 068I].

The content is `Dualizing.diagonalProjectionNatIso` at the tensor factor `K` and the first
argument `N[0]`; what is added is the passage between the two spellings of the derived tensor
product, by `Dualizing.derivedHomAdjunctionTensorNatIso` over each of the two rings, the symmetry
of the derived tensor product on either side, and the commutation of derived restriction of
scalars with the degree-zero single functor. -/
theorem nonempty_restrictScalars_canonicalTensor_single_iso
    (K : DerivedCategory (ModuleCat.{u} A)) (N : ModuleCat.{u} A) :
    Nonempty
      ((ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.lmul' R :
              A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) ≅
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj K)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
            ((ModuleCat.restrictScalars.{u}
              (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj N))) := by
  let Δ : A ⊗[R] A →+* A := (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  let MN : DerivedCategory (ModuleCat.{u} A) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
  let eA : (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).obj
        MN) ≅ (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor A).obj (MN, K) :=
    (derivedHomAdjunctionTensorNatIso A).app (K, MN) ≪≫
      (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction A).tensorSwap K MN
  let eB : (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
        ((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj MN,
          (diagonalDerivedExtension R A).obj K) ≅
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj K)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
          ((ModuleCat.restrictScalars.{u} Δ).obj N)) :=
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).mapIso
        (Iso.prod (((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategorySingleFunctor 0).app N)
          (Iso.refl ((diagonalDerivedExtension R A).obj K))) ≪≫
      (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction (A ⊗[R] A)).tensorSwap _ _ ≪≫
        ((derivedHomAdjunctionTensorNatIso (A ⊗[R] A)).app
          ((diagonalDerivedExtension R A).obj K, _)).symm
  exact ⟨(ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.mapIso eA ≪≫
    (diagonalProjectionNatIso R A MN).app K ≪≫ eB⟩

/-- **The Tor-amplitude bound of [stacks 0ATK] (3) descends from the diagonal to `A`.**  Let
`R → A` be flat, put `B = A ⊗[R] A` and let `p₁ : A → B` be the left coprojection.  If the
derived base change `p₁^*K` has Tor amplitude bounded below by `a` over `B` — that is, tensoring
it with a `B`-module placed in degree zero gives nothing in degrees below `a` — then `K` itself
has Tor amplitude bounded below by `a` over `A`.

The bound over `B` is tested only against the `B`-modules obtained from `A`-modules by
restriction along the multiplication map `Δ`, which is where the hypothesis is strongest:
`Δ ∘ p₁ = id`, so such a `B`-module restricts along `p₁` to the `A`-module it came from, and
`Dualizing.nonempty_restrictScalars_canonicalTensor_single_iso` identifies the two tensor
products.  Nothing is carried.

This is the hypothesis of
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude`, whose docstring reads it
over `A ⊗[R] A` "which is precisely what fails for a general relative dualizing complex"; the
theorem here says that what fails is the same bound over `A`, so the hypothesis asks of `K`
exactly finite Tor dimension over `A`. -/
theorem torAmplitude_of_diagonalDerivedExtension
    (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ)
    (hKtor : ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj K)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N)))) :
    ∀ (N : ModuleCat.{u} A) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) := by
  intro N i hi
  refine isZero_homology_of_isZero_homology_mapDerivedCategory_restrictScalars
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom _ i ?_
  exact IsZero.of_iso (hKtor _ i hi)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).mapIso
      (nonempty_restrictScalars_canonicalTensor_single_iso R A K N).some)

/-- **At a relative dualizing complex the Tor-amplitude hypothesis of [stacks 0ATK] (3) is
perfectness.**  If `K` is a relative dualizing complex for `R → A` whose derived base change
along the left coprojection has Tor amplitude bounded below over `A ⊗[R] A`, then `K` is a
perfect object of `D(A)`.

Three inputs, beyond the descent of the bound proved above.  Relative perfectness gives `K` a
bounded representative, hence an upper cohomological bound, and the derived tensor product is
right t-exact (`CochainComplex.DerivedTensor.isLE_canonicalDerivedTensorProduct`), so the
Tor-amplitude window closes above for free; relative perfectness also contains pseudo-coherence
of `K` over `A` outright; and a pseudo-coherent object with a Tor-amplitude window is perfect, by
[stacks 0654] (`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative`)
and [stacks 0658]
(`StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension`).

Consequently `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude` is a
corollary of `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange`
rather than a strengthening of it: the base change of a perfect object is perfect, [stacks 066W].
The route the source's proof of [stacks 0E2D] takes through [stacks 0ATK] (3) therefore reaches
the perfect case and no further. -/
theorem isPerfect_of_isRelativeDualizingComplex_of_torAmplitude
    [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K) (a : ℤ)
    (hKtor : ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj K)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N)))) :
    StacksDraft.Perfect.IsPerfect K := by
  obtain ⟨P, a', b, hGE, hLE, hflat, hfp, ⟨e⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ K).1 hK.relativelyPerfect
  have _ := hLE
  have hKLE : K.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  have htor : StacksDraft.TorAmplitude.HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) K a b := by
    intro M i hi
    have hi' : i < a ∨ b < i := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hi
    rcases hi' with h | h
    · exact torAmplitude_of_diagonalDerivedExtension R A K a hKtor M i h
    · have hle := CochainComplex.DerivedTensor.isLE_canonicalDerivedTensorProduct K
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) b 0
      exact (DerivedCategory.isLE_iff _ (b + 0)).1 hle i (by omega)
  exact (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u} K).1.mpr
    ⟨hK.relativelyPerfect.1, a, b,
      (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
        (StacksDraft.TorAmplitude.canonicalTensorComparison A)
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) K a b).1 htor⟩

end Descent

end

end Dualizing

end
