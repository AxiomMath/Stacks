module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Fibres.GenericFibreDensity
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticClosure
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothLocusAffine
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.RingTheory.GeometricallyIntegral.GoodReduced
public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromDenseFamily
public import StacksFrontier.RingTheory.GeometricallyIntegral.SmoothGenericFibre
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.RingTheory.Smooth.Reduced

/-!
# A geometrically reduced generic fibre spreads out

Let `D` be a Noetherian domain and `T` a finite type `D`-algebra whose generic fibre is
geometrically reduced. This file produces a nonempty standard open of `Spec D` over which every
fibre is geometrically reduced, and deduces that the locus of geometrically reduced fibres of a
finite type algebra over a Noetherian ring is constructible.

The route is the source's. Over the fraction field `K` of `D` the generic fibre `K ⊗[D] T` is
reduced and geometrically reduced, so its smooth locus over `K` is dense (Stacks 056V); the smooth
locus of `K ⊗[D] T` over `K` is the inverse image of the smooth locus of `T` over `D`, because
`D → K` is flat (Stacks 00TG, the commutative algebra behind Stacks 02V4); the generic fibre is
Noetherian, so finitely many standard opens `D(g₁), …, D(gₙ)` of `Spec T` contained in the smooth
locus of `T` already cover that inverse image. Their traces on the generic fibre are then
topologically dense, hence scheme-theoretically dense since the generic fibre is reduced
(Stacks 056D), and each `T_{gⱼ}` is smooth over `D`, so has geometrically reduced fibres
(Stacks 033B). That is exactly the input of
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily'`, which
spreads the density to the nearby fibres by Stacks 0573 and concludes by Stacks 056E.

With that, the dichotomy of the generic fibre is complete — its other half,
`Algebra.exists_ne_zero_disjoint_geometricallyReducedFibreLocus`, is already unconditional — and
the constructibility criterion of Stacks 053Z applies. That last step is not taken here: the
affine case of Stacks 0579 it yields is
`Algebra.isConstructible_geometricallyReducedFibreLocus'`, proved in
`StacksFrontier.RingTheory.GeometricallyIntegral.SmoothGenericFibre` from the purely ring-theoretic
form of the good half. The good half proved here is therefore a second, independent route to the
same conclusion, by way of the scheme-theoretic density of the smooth locus.

## Main results

* `AlgebraicGeometry.geometricallyReduced_specMap_of_forall_isReduced_tensorProduct`: an affine
  scheme over a field is geometrically reduced as soon as every field-valued base change of its
  ring of functions is reduced.
* `Algebra.dense_smoothLocus_of_forall_isReduced_tensorProduct`: the affine case of Stacks 056V as
  a statement about rings — the smooth locus of a reduced, geometrically reduced finite type
  algebra over a field is dense in its spectrum.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus`: the affine case of
  Stacks 0578 at the generic point. A geometrically reduced generic fibre forces a nonempty
  standard open of the base inside `Algebra.geometricallyReducedFibreLocus`.

## Implementation notes

The generic point is taken to be `FractionRing D`; no shrinking of `D` by generic flatness is
needed, because the flatness side-condition of Stacks 00TG is wanted for the morphism along which
one base changes, and `D → FractionRing D` is a localization.

`AlgebraicGeometry.Scheme.Hom.smoothLocus` and `Algebra.smoothLocus` are compared once, by
`AlgebraicGeometry.formallySmooth_stalkMap_specMap_iff`, and everything after that is a statement
about `PrimeSpectrum`; the two carriers `PrimeSpectrum A` and the points of
`Spec (CommRingCat.of A)` agree definitionally, so sets of one are transported to the other by
`Dense.mono` and `exact` rather than by rewriting.

The family is extracted from a `Finset` of standard opens by `Finset.equivFin`, because
`Algebra.bigPhi` and hence
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily'` index
their families by `Fin n`.

Nothing here is tagged: the statement proved of Stacks 0578 is the affine case at the generic
point, which is one of the four steps of that lemma rather than the lemma; and the affine case of
Stacks 0579 proved here is restated on schemes, in the shape of the source, in
`StacksFrontier.AlgebraicGeometry.Fibres.ReducedFibreLocus`, which is where the tag 0579 sits.

## References

* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 00TG](https://stacks.math.columbia.edu/tag/00TG)
* [Stacks Project, Tag 056D](https://stacks.math.columbia.edu/tag/056D)
* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 0573](https://stacks.math.columbia.edu/tag/0573)
* [Stacks Project, Tag 053Z](https://stacks.math.columbia.edu/tag/053Z)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Geometric reducedness of an affine scheme over a field, read on its ring of functions.** If
`B ⊗[K] L` is reduced for every field extension `L` of `K`, then `Spec B → Spec K` is
geometrically reduced.

Mathlib's `AlgebraicGeometry.GeometricallyReduced` asks that `Spec B ×_{Spec K} Spec L` be reduced
for every field `L` over `K`; that fibre product is `Spec (B ⊗[K] L)` by
`AlgebraicGeometry.pullbackSpecIso`, and the spectrum of a reduced ring is a reduced scheme. This
is the affine case of Stacks 020I, part (2). -/
theorem geometricallyReduced_specMap_of_forall_isReduced_tensorProduct
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    (h : ∀ (L : Type u) [Field L] [Algebra K L], _root_.IsReduced (B ⊗[K] L)) :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun L _ _ => ?_⟩
  have : _root_.IsReduced (B ⊗[K] L) := h L
  have : _root_.IsReduced (CommRingCat.of (B ⊗[K] L)) := this
  exact ObjectProperty.prop_of_iso (P := (IsReduced ·)) (pullbackSpecIso K B L).symm inferInstance

end AlgebraicGeometry

namespace Algebra

/-- **The affine case of Stacks 056V.** Let `B` be a reduced finite type algebra over a field `K`
which stays reduced after every field-valued base change. Then the primes of `B` at which `B` is
smooth over `K` are dense in `Spec B`.

Stacks 056V produces a dense open subscheme of `Spec B` smooth over `K`; such an open is contained
in the smooth locus of `Spec B → Spec K`, which is therefore dense, and that locus is
`Algebra.smoothLocus K B` by
`AlgebraicGeometry.formallySmooth_stalkMap_specMap_iff`. -/
theorem dense_smoothLocus_of_forall_isReduced_tensorProduct {K B : Type u} [Field K] [CommRing B]
    [Algebra K B] [Algebra.FiniteType K B] [IsReduced B]
    (h : ∀ (L : Type u) [Field L] [Algebra K L], IsReduced (B ⊗[K] L)) :
    Dense (Algebra.smoothLocus K B) := by
  have : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hred : _root_.IsReduced (CommRingCat.of B) := ‹IsReduced B›
  have : AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec (CommRingCat.of B)) := inferInstance
  have hgr := AlgebraicGeometry.geometricallyReduced_specMap_of_forall_isReduced_tensorProduct h
  obtain ⟨U, hUdense, hUsmooth⟩ :=
    (AlgebraicGeometry.geometricallyReduced_iff_exists_dense_open_smooth
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K B)))).mp hgr
  have hUsub : (U : Set ↥(AlgebraicGeometry.Spec (CommRingCat.of B))) ⊆
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K B))).smoothLocus :
        Set ↥(AlgebraicGeometry.Spec (CommRingCat.of B))) := by
    intro x hx
    have hx' : (⟨x, hx⟩ : U) ∈
        (U.ι ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K B))).smoothLocus := by
      rw [AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff.2 hUsmooth]
      trivial
    rwa [← AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_eq] at hx'
  exact (hUdense.mono hUsub).mono fun x hx =>
    (AlgebraicGeometry.formallySmooth_stalkMap_specMap_iff x).mp hx

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open PrimeSpectrum Topology

/-- **The good half of the generic-fibre dichotomy for geometric reducedness: the affine case of
Stacks 0578 at the generic point.** Let `D` be a Noetherian domain and `T` a finite type
`D`-algebra whose generic fibre is geometrically reduced, that is, the generic point `(0)` of
`Spec D` lies in `Algebra.geometricallyReducedFibreLocus D T`. Then some nonempty standard open
`D(f)` of `Spec D` is contained in that locus: every fibre over `D(f)` is geometrically reduced.

The proof takes `K = FractionRing D`. The generic fibre `K ⊗[D] T` is reduced and stays reduced
after every field extension of `K`, so its smooth locus over `K` is dense
(`Algebra.dense_smoothLocus_of_forall_isReduced_tensorProduct`, the affine case of Stacks 056V).
Flatness of `D → K` identifies that locus with the inverse image of `Algebra.smoothLocus D T`
(`Algebra.smoothLocus_comap_of_isPushout`, Stacks 00TG), which is covered by the standard opens of
`Spec T` lying inside `Algebra.smoothLocus D T`; the generic fibre is Noetherian, so finitely many
of them, say `D(g₁), …, D(gₙ)`, suffice. The union `⋃ⱼ D(1 ⊗ gⱼ)` is then dense in the generic
fibre, hence scheme-theoretically dense by Stacks 056D, while each `T_{gⱼ}` is smooth over `D` and
so has reduced fibres by Stacks 033B. That is the hypothesis of
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily'`. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus
    (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
    [Algebra.FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyReducedFibreLocus D T := by
  classical
  have : Algebra.FinitePresentation D T := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hDK : Function.Injective (algebraMap D (FractionRing D)) :=
    FaithfulSMul.algebraMap_injective D (FractionRing D)
  -- every field-valued base change of the generic fibre is reduced
  have hfib : ∀ (L : Type u) [Field L] [Algebra (FractionRing D) L],
      IsReduced ((FractionRing D ⊗[D] T) ⊗[FractionRing D] L) := by
    intro L _ _
    let _ : Algebra D L :=
      ((algebraMap (FractionRing D) L).comp (algebraMap D (FractionRing D))).toAlgebra
    have _ : IsScalarTower D (FractionRing D) L := IsScalarTower.of_algebraMap_eq' rfl
    have hDL : Function.Injective (algebraMap D L) :=
      (algebraMap (FractionRing D) L).injective.comp hDK
    have hTL : IsReduced (T ⊗[D] L) := hgen L ((RingHom.injective_iff_ker_eq_bot _).mp hDL)
    exact isReduced_of_ringEquiv
      (((Algebra.TensorProduct.comm (FractionRing D) (FractionRing D ⊗[D] T) L).trans
        (Algebra.TensorProduct.cancelBaseChange D (FractionRing D) (FractionRing D) L
          T)).toRingEquiv.trans (Algebra.TensorProduct.comm D L T).toRingEquiv) hTL
  have hTK : IsReduced (T ⊗[D] FractionRing D) :=
    hgen (FractionRing D) ((RingHom.injective_iff_ker_eq_bot _).mp hDK)
  have hBred : IsReduced (FractionRing D ⊗[D] T) :=
    isReduced_of_ringEquiv (Algebra.TensorProduct.comm D (FractionRing D) T).toRingEquiv hTK
  -- the smooth locus of the generic fibre is dense, and is the preimage of that of `T`
  have hdense : Dense (smoothLocus (FractionRing D) (FractionRing D ⊗[D] T)) :=
    dense_smoothLocus_of_forall_isReduced_tensorProduct hfib
  have h00TG : comap (algebraMap T (FractionRing D ⊗[D] T)) ⁻¹' smoothLocus D T =
      smoothLocus (FractionRing D) (FractionRing D ⊗[D] T) :=
    smoothLocus_comap_of_isPushout D T (FractionRing D) (FractionRing D ⊗[D] T)
  -- cover the smooth locus of `T` by the standard opens it contains
  set S : Set T := {b | (basicOpen b : Set (PrimeSpectrum T)) ⊆ smoothLocus D T} with hSdef
  have hcover : smoothLocus D T ⊆ ⋃ b : S, (basicOpen (b : T) : Set (PrimeSpectrum T)) := by
    intro x hx
    obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hxb, hb⟩ :=
      isBasis_basic_opens.exists_subset_of_mem_open hx isOpen_smoothLocus
    exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hxb⟩
  -- the smooth locus of the generic fibre is quasi-compact, so finitely many of them suffice
  have hNB : IsNoetherianRing (FractionRing D ⊗[D] T) :=
    Algebra.FiniteType.isNoetherianRing (FractionRing D) (FractionRing D ⊗[D] T)
  have hcompact : IsCompact (smoothLocus (FractionRing D) (FractionRing D ⊗[D] T)) :=
    TopologicalSpace.NoetherianSpace.isCompact _
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun b : S => (basicOpen (algebraMap T (FractionRing D ⊗[D] T) (b : T)) :
      Set (PrimeSpectrum (FractionRing D ⊗[D] T))))
    (fun b => (basicOpen _).2) (by
      rw [← h00TG]
      intro x hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hcover hx)
      refine Set.mem_iUnion.mpr ⟨b, ?_⟩
      simpa [PrimeSpectrum.mem_basicOpen, Ideal.mem_comap] using hb)
  let g : Fin s.card → T := fun j => ((s.equivFin.symm j : S) : T)
  have hgmem : ∀ j, (basicOpen (g j) : Set (PrimeSpectrum T)) ⊆ smoothLocus D T :=
    fun j => (s.equivFin.symm j : S).2
  have hgcover : smoothLocus (FractionRing D) (FractionRing D ⊗[D] T) ⊆
      ⋃ j, (basicOpen ((1 : FractionRing D) ⊗ₜ[D] g j) :
        Set (PrimeSpectrum (FractionRing D ⊗[D] T))) := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine Set.mem_iUnion.mpr ⟨s.equivFin ⟨b, hb⟩, ?_⟩
    have hgb : g (s.equivFin ⟨b, hb⟩) = (b : T) := by simp [g]
    rw [hgb]
    simpa [Algebra.TensorProduct.right_algebraMap_apply] using hxb
  -- density of the union of standard opens, read as injectivity of the multiplication map
  have hredB' : _root_.IsReduced (CommRingCat.of (FractionRing D ⊗[D] T)) := hBred
  have hSTD : AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense
      (Stacks.Morphisms.standardOpenUnion fun j => (1 : FractionRing D) ⊗ₜ[D] g j) :=
    ((AlgebraicGeometry.dense_open_tfae
      (Stacks.Morphisms.standardOpenUnion fun j => (1 : FractionRing D) ⊗ₜ[D] g j)).out 1 3).mp
      (hdense.mono fun x hx => TopologicalSpace.Opens.mem_iSup.mpr
        (Set.mem_iUnion.mp (hgcover hx)))
  rw [Stacks.Morphisms.isSchemeTheoreticallyDense_standardOpenUnion_iff_injective_bigPhi] at hSTD
  -- the members of the family have geometrically reduced fibres, being smooth over `D`
  have hredloc : ∀ (L : Type u) [Field L] [Algebra D L] (j : Fin s.card),
      IsReduced (L ⊗[D] Localization.Away (g j)) := by
    intro L _ _ j
    have : Algebra.Smooth D (Localization.Away (g j)) :=
      basicOpen_subset_smoothLocus_iff_smooth.mp (hgmem j)
    have : Algebra.Smooth L (L ⊗[D] Localization.Away (g j)) :=
      Algebra.Smooth.baseChange D (Localization.Away (g j)) L
    exact Algebra.isReduced_of_smooth L (L ⊗[D] Localization.Away (g j))
  exact exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily' g
    (FractionRing D) hDK hSTD hredloc

end Algebra

end
