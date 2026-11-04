module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilySheaf
public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineBasicOpenCurve
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# A basic open of the `t`-line and its preimage in the plane, as objects of the big étale site

Let `k'` be a finite field and `P ∈ k'[t]` nonzero. For the families of Laumon's argument on the
plane `Spec k'[x][t]` over the `t`-line `Spec k'[t]` (the projection
`Stacks.EtaleCohomology.laumonFamilyProjection`), the open `V' = D(P) = Spec k'[t]_P` of the line
and its preimage `U' = pr₂⁻¹(V')` carry all the data consumed by the purity arguments on `V'`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): `V'` and `U'` are Noetherian objects of
the big étale site, `V'` is affine, irreducible and connected, the open immersion `V' → 𝔸¹` has
image exactly `D(P)`, `U'` is the fibre product with the restriction `g' : U' → V'` of `pr₂`
separated of finite type with a compactification (Nagata, Tag 0F41), and the structure morphism
`fV : V' → Spec k'` is smooth of relative dimension one with a compactification and geometrically
connected (`Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_away`).

The statement is in continuation-passing form, so that the data can be consumed by the
propositions that quantify over such opens.

## Main results

* `Stacks.EtaleCohomology.laumonLineBasicOpen_elim`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace Stacks.EtaleCohomology

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))

omit [Fintype k'] in
/-- **The open `V' = D(P)` of the `t`-line and `U' = pr₂⁻¹(V')`, with all their structure**: for
`P ≠ 0` in `k'[t]` there are Noetherian objects `V'`, `U'` of the big étale site, `V'` affine,
irreducible and connected, an open immersion `jV' : V' → Spec k'[t]` with image `D(P)`, a
cartesian square `jU, g'` over `pr₂` and `jV'` with `g'` separated of finite type and a
compactification of `g'`, and `fV = jV' ≫ (Spec k'[t] → Spec k')` smooth of relative dimension one,
with a compactification, and geometrically connected over every field extension of `k'`. -/
public theorem laumonLineBasicOpen_elim {P : Polynomial k'} (hP : P ≠ 0) (C : Prop)
    (H : ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] [ConnectedSpace V'.1]
      [IrreducibleSpace V'.1] [IsAffine V'.1]
      (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
      (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
      [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
      [IsSeparated (B.inclusion.map g')] (_ : CompactificationOf (Over.mk (B.inclusion.map g')))
      (fV : V'.1 ⟶ Spec (.of k')) [LocallyOfFiniteType fV] [QuasiCompact fV] [IsSeparated fV]
      [SmoothOfRelativeDimension 1 fV] (_ : CompactificationOf (Over.mk fV)),
      IsOpenImmersion (B.inclusion.map jV') →
      Set.range (B.inclusion.map jV') =
        (PrimeSpectrum.basicOpen P : Set (PrimeSpectrum (Polynomial k'))) →
      B.inclusion.map jV' ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) = fV →
      IsPullback (B.inclusion.map jU) (B.inclusion.map g')
        (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
      (∀ (Ω : Type u) [Field Ω] [Algebra k' Ω],
        ConnectedSpace ↥(Limits.pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k' Ω))))) →
      C) : C := by
  let R := Localization.Away P
  have : IsDomain R := Stacks.GenericFiniteEtale.isDomain_away k' hP
  let ι : Spec (.of R) ⟶ Spec (.of (Polynomial k')) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k') R))
  have hV : schemeSizeBelow B.cutoff (Spec (.of R)) := Scheme.size_lt_of_isOpenImmersion ι hL
  let V' : B.Scheme := Stacks.ArtinSchreier.specObject R B hV
  let jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL := ObjectProperty.homMk ι
  let π : Spec (.of (Polynomial (Polynomial k'))) ⟶ Spec (.of (Polynomial k')) :=
    B.inclusion.map (laumonFamilyProjection k' B hS hL)
  have : LocallyOfFiniteType π := locallyOfFiniteType_laumonFamilyProjection k' B hS hL
  have : QuasiCompact π := quasiCompact_laumonFamilyProjection k' B hS hL
  have : IsSeparated π := isSeparated_laumonFamilyProjection k' B hS hL
  have hU : schemeSizeBelow B.cutoff (pullback π ι) := Scheme.size_pullback_lt _ _ hS hV
  let U' : B.Scheme := ⟨pullback π ι, hU⟩
  let jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS :=
    ObjectProperty.homMk (pullback.fst π ι)
  let g' : U' ⟶ V' := ObjectProperty.homMk (pullback.snd π ι)
  have : IsNoetherian V'.1 := inferInstanceAs (IsNoetherian (Spec (.of R)))
  have : IsAffine V'.1 := inferInstanceAs (IsAffine (Spec (.of R)))
  have : IrreducibleSpace V'.1 := inferInstanceAs (IrreducibleSpace (PrimeSpectrum R))
  have : ConnectedSpace V'.1 := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : CompactSpace ↥(pullback π ι : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd π ι)
  have : IsLocallyNoetherian (pullback π ι : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π ι)
  have : IsNoetherian U'.1 := (⟨⟩ : IsNoetherian (pullback π ι : Scheme.{u}))
  have : LocallyOfFiniteType (B.inclusion.map g') :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd π ι))
  have : QuasiCompact (B.inclusion.map g') := inferInstanceAs (QuasiCompact (pullback.snd π ι))
  have : IsSeparated (B.inclusion.map g') := inferInstanceAs (IsSeparated (pullback.snd π ι))
  have : CompactSpace ↥(B.inclusion.obj V') := inferInstanceAs (CompactSpace (PrimeSpectrum R))
  have : QuasiSeparatedSpace ↥(B.inclusion.obj V') :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of R)))
  obtain ⟨jg', -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace
    (B.inclusion.map g')
  let fV : V'.1 ⟶ Spec (.of k') := Spec.map (CommRingCat.ofHom (algebraMap k' R))
  have : SmoothOfRelativeDimension 1 fV :=
    Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_away k' P
  have : LocallyOfFiniteType fV := inferInstanceAs
    (LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k' R))))
  have : QuasiCompact fV := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k' R))))
  have : IsSeparated fV := inferInstanceAs
    (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k' R))))
  obtain ⟨jfV, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace fV
  refine H V' U' jV' jU g' jg' fV jfV (inferInstanceAs (IsOpenImmersion ι)) ?_ ?_
    (IsPullback.of_hasPullback π ι) (fun Ω _ _ =>
      Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_away k' hP Ω)
  · exact PrimeSpectrum.localization_away_comap_range R P
  · change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end Stacks.EtaleCohomology

end
