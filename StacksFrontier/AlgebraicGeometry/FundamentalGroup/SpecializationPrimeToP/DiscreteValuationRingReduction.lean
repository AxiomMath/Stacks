module

public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationPrimeToP.GaloisDescentPrimeToP
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.BaseChangeSquare
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.NoetherianReduction
public import
  StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothGeometricallyConnectedModel
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapValuationRing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapStrictlyHenselianDiscreteValuationRing

/-!
# Reducing the prime-to-`p` descent of finite quotients to a strictly henselian discrete
valuation ring

Let `f : X ⟶ S` be a smooth proper morphism with geometrically connected fibres and let
`sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` be a specialization map. The property of `sp` which the second
conclusion of [Stacks, Tag 0C0R] needs — every open normal subgroup of index prime to `p` is the
preimage along `sp` of an open normal subgroup, the hypothesis `hlift` of
`AlgebraicGeometry.exists_continuousMulEquiv_primeToP_of_forall_lift` — is invariant under
replacing `sp` by a conjugate: an isomorphism of topological groups carries open normal subgroups
to open normal subgroups and preserves the index.

That is all the three reductions with which the proof of [Stacks, Tag 0C0Q] begins need in order
to apply verbatim to this property instead of to injectivity, since each of them produces a
specialization map over a smaller base together with isomorphisms of topological groups conjugating
the given one into it:

* the base is made affine, by [Stacks, Tag 0C0M];
* the base is made Noetherian, by absolute Noetherian approximation together with
  [Stacks, Tag 0C0K] — here the conjugating isomorphisms are the maps of fundamental groups induced
  by the isomorphisms of geometric fibres which a cartesian square provides
  (`AlgebraicGeometry.isIso_fiberOverGeometricPointSquareMap`), promoted to homeomorphisms because
  the étale fundamental group is compact Hausdorff;
* the base is made the spectrum of a strictly henselian discrete valuation ring, by
  [Stacks, Tag 0C0N].

So the prime-to-`p` descent of the finite quotients of a specialization map over an arbitrary base
follows from the same statement over a strictly henselian discrete valuation ring with
algebraically closed residue field, from its generic to its closed point. Combined with
`AlgebraicGeometry.forall_lift_primeToP_of_isSpecializationMap_of_essImage_isGalois` this leaves
[Stacks, Tag 0C0R] standing on one geometric statement, in the same shape as the input `Hgal` of
[Stacks, Tag 0C0Q] with "residue characteristic zero" replaced by "Galois group of order prime to
`p`".

**No `@[stacks 0C0R]` attribute is attached to anything here**: the remaining input is not proved.

## Main results

* `Stacks.FundamentalGroup.forall_lift_of_comm_continuousMulEquiv` — the descent of the
  prime-to-`p` finite quotients is invariant under conjugation by isomorphisms of topological
  groups.
* `AlgebraicGeometry.continuousMulEquivOfBijective` — a bijective continuous homomorphism from a
  compact group to a Hausdorff group is an isomorphism of topological groups.
* `AlgebraicGeometry.forall_lift_primeToP_isSpecializationMap_of_isPullback` — the descent
  descends along a cartesian square, the form of [Stacks, Tag 0C0K] the reduction uses.
* `AlgebraicGeometry.forall_lift_primeToP_isSpecializationMap_of_forall_isDiscreteValuationRing` —
  the three reductions composed.
* `surjective_and_exists_continuousMulEquiv_primeToP_of_forall_isDiscreteValuationRing` — both
  conclusions of [Stacks, Tag 0C0R] granted the descent of the prime-to-`p` Galois covers of the
  geometric generic fibre over a strictly henselian discrete valuation ring.

## References

* [Stacks Project, Tag 0C0K](https://stacks.math.columbia.edu/tag/0C0K)
* [Stacks Project, Tag 0C0M](https://stacks.math.columbia.edu/tag/0C0M)
* [Stacks Project, Tag 0C0N](https://stacks.math.columbia.edu/tag/0C0N)
* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
* [Stacks Project, Tag 0C0R](https://stacks.math.columbia.edu/tag/0C0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory IsLocalRing
open Stacks.FundamentalGroup

universe u

namespace Stacks.FundamentalGroup

/-- **The descent of the prime-to-`p` finite quotients is invariant under conjugation.** Let
`φ : G →ₜ* H` and `ψ : G' →ₜ* H'` be continuous homomorphisms and let `eG : G ≃ₜ* G'` and
`eH : H ≃ₜ* H'` be isomorphisms of topological groups with `eH ∘ φ = ψ ∘ eG`. If every open normal
subgroup of `G'` of index prime to `p` is the preimage along `ψ` of an open normal subgroup, the
same holds for `φ`.

An isomorphism of topological groups carries an open normal subgroup to an open normal subgroup of
the same index, and preimages compose; so the subgroup of `H'` produced for the image of `N`
pulls back along `eH` to one which pulls back along `φ` to `N`. -/
theorem forall_lift_of_comm_continuousMulEquiv {p : ℕ} {G H G' H' : Type*}
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [Group G'] [TopologicalSpace G'] [Group H'] [TopologicalSpace H']
    (φ : G →ₜ* H) (ψ : G' →ₜ* H') (eG : G ≃ₜ* G') (eH : H ≃ₜ* H')
    (hcomm : ∀ g, eH (φ g) = ψ (eG g))
    (hψ : ∀ N : Subgroup G', N.Normal → IsOpen (N : Set G') → ¬ p ∣ N.index →
      ∃ M : Subgroup H', M.Normal ∧ IsOpen (M : Set H') ∧ M.comap ψ.toMonoidHom = N) :
    ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ¬ p ∣ N.index →
      ∃ M : Subgroup H, M.Normal ∧ IsOpen (M : Set H) ∧ M.comap φ.toMonoidHom = N := by
  intro N hnorm hopen hindex
  set u : G →* G' := eG.toMulEquiv.toMonoidHom with hu
  set u' : G' →* G := eG.symm.toMulEquiv.toMonoidHom with hu'
  set v : H →* H' := eH.toMulEquiv.toMonoidHom with hv
  have hu'surj : Function.Surjective u' := eG.symm.surjective
  obtain ⟨M', hM'norm, hM'open, hM'comap⟩ :=
    hψ (N.comap u') (hnorm.comap u') (by
        rw [Subgroup.coe_comap]
        exact hopen.preimage eG.symm.continuous)
      (by rwa [Subgroup.index_comap_of_surjective N hu'surj])
  refine ⟨M'.comap v, hM'norm.comap v, ?_, ?_⟩
  · rw [Subgroup.coe_comap]
    exact hM'open.preimage eH.continuous
  · rw [Subgroup.comap_comap,
      show v.comp φ.toMonoidHom = ψ.toMonoidHom.comp u from MonoidHom.ext hcomm,
      ← Subgroup.comap_comap, hM'comap, Subgroup.comap_comap,
      show u'.comp u = MonoidHom.id G from MonoidHom.ext (fun g ↦ eG.symm_apply_apply g),
      Subgroup.comap_id]

end Stacks.FundamentalGroup

namespace AlgebraicGeometry

/-- **A bijective continuous homomorphism from a compact group to a Hausdorff group is an
isomorphism of topological groups.** The inverse is continuous because a continuous bijection from
a compact space to a Hausdorff space is a homeomorphism. -/
def continuousMulEquivOfBijective {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] [CompactSpace G] [T2Space H] (φ : G →ₜ* H)
    (hbij : Function.Bijective φ) : G ≃ₜ* H :=
  ContinuousMulEquiv.mk'
    (φ.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ hbij)) (map_mul φ)

/-- The isomorphism `continuousMulEquivOfBijective φ hbij` agrees with `φ` pointwise. -/
@[simp]
theorem continuousMulEquivOfBijective_apply {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] [CompactSpace G] [T2Space H] (φ : G →ₜ* H)
    (hbij : Function.Bijective φ) (g : G) : continuousMulEquivOfBijective φ hbij g = φ g :=
  rfl

/-! ### Descending along a cartesian square -/

/-- **The descent of the prime-to-`p` finite quotients descends along a base change.** Let
```
Y ⟶ X
↓     ↓
T ⟶ S
```
be a cartesian square whose vertical morphisms are proper with geometrically connected fibres, and
let `sp : π₁(Y_{t̄'}) ⟶ π₁(Y_{t̄})` be a specialization map. If every specialization map of the
bottom row at the base points induced by the square has the property that its open normal
subgroups of index prime to `p` are preimages, then so does `sp`.

[Stacks, Tag 0C0K] produces such a specialization map `sp'` of the bottom row together with a
commuting square whose vertical maps are the ones induced by the morphisms of geometric fibres
determined by the square; those morphisms are isomorphisms because the square is cartesian
(`AlgebraicGeometry.isIso_fiberOverGeometricPointSquareMap`), so the vertical maps are bijective,
hence isomorphisms of topological groups, the fundamental groups being compact Hausdorff. Now
`Stacks.FundamentalGroup.forall_lift_of_comm_continuousMulEquiv` applies. -/
theorem forall_lift_primeToP_isSpecializationMap_of_isPullback {Y X T S : Scheme.{u}} (a : Y ⟶ X)
    (g : Y ⟶ T) (f : X ⟶ S) (b : T ⟶ S) (hsq : IsPullback a g f b) (p : ℕ) [IsProper f]
    [GeometricallyConnected f] [IsProper g] [GeometricallyConnected g] (t' t : GeometricPoint T)
    (y' : GeometricPoint (fiberOverGeometricPoint g t'))
    (y : GeometricPoint (fiberOverGeometricPoint g t))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint g t') y' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint g t) y)
    (hsp : IsSpecializationMap g t' t y' y sp)
    (H : ∀ sp' : EtaleFundamentalGroup (fiberOverGeometricPoint f (t'.map b))
            (y'.map (fiberOverGeometricPointSquareMap a g f b hsq.w t')) →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint f (t.map b))
            (y.map (fiberOverGeometricPointSquareMap a g f b hsq.w t)),
        IsSpecializationMap f (t'.map b) (t.map b)
            (y'.map (fiberOverGeometricPointSquareMap a g f b hsq.w t'))
            (y.map (fiberOverGeometricPointSquareMap a g f b hsq.w t)) sp' →
          ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f (t'.map b))
              (y'.map (fiberOverGeometricPointSquareMap a g f b hsq.w t'))),
            N.Normal →
            IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f (t'.map b))
              (y'.map (fiberOverGeometricPointSquareMap a g f b hsq.w t')))) →
            ¬ p ∣ N.index →
            ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f (t.map b))
                (y.map (fiberOverGeometricPointSquareMap a g f b hsq.w t))),
              M.Normal ∧
              IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f (t.map b))
                (y.map (fiberOverGeometricPointSquareMap a g f b hsq.w t)))) ∧
                M.comap sp'.toMonoidHom = N) :
    ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint g t') y'),
      N.Normal → IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint g t') y')) →
      ¬ p ∣ N.index →
      ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint g t) y),
        M.Normal ∧ IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint g t) y)) ∧
          M.comap sp.toMonoidHom = N := by
  obtain ⟨sp', hsp', hcomm⟩ :=
    exists_isSpecializationMap_comm_square a g f b hsq.w t' t y' y sp hsp
  have := isIso_fiberOverGeometricPointSquareMap a g f b hsq t'
  have := isIso_fiberOverGeometricPointSquareMap a g f b hsq t
  let : CompactSpace (EtaleFundamentalGroup (fiberOverGeometricPoint g t') y') :=
    compactSpace_etaleFundamentalGroup _ y'
  let : T2Space (EtaleFundamentalGroup (fiberOverGeometricPoint f (t'.map b))
      (y'.map (fiberOverGeometricPointSquareMap a g f b hsq.w t'))) :=
    t2Space_etaleFundamentalGroup _ _
  let : CompactSpace (EtaleFundamentalGroup (fiberOverGeometricPoint g t) y) :=
    compactSpace_etaleFundamentalGroup _ y
  let : T2Space (EtaleFundamentalGroup (fiberOverGeometricPoint f (t.map b))
      (y.map (fiberOverGeometricPointSquareMap a g f b hsq.w t))) :=
    t2Space_etaleFundamentalGroup _ _
  exact forall_lift_of_comm_continuousMulEquiv sp sp'
    (continuousMulEquivOfBijective
      (etaleFundamentalGroupMap (fiberOverGeometricPointSquareMap a g f b hsq.w t') y')
      ⟨injective_etaleFundamentalGroupMap_of_isIso _ y',
        surjective_etaleFundamentalGroupMap_of_isIso _ y'⟩)
    (continuousMulEquivOfBijective
      (etaleFundamentalGroupMap (fiberOverGeometricPointSquareMap a g f b hsq.w t) y)
      ⟨injective_etaleFundamentalGroupMap_of_isIso _ y,
        surjective_etaleFundamentalGroupMap_of_isIso _ y⟩)
    hcomm (H sp' hsp')

/-! ### Reducing to a strictly henselian discrete valuation ring -/

/-- **The descent of the prime-to-`p` finite quotients over a Noetherian base reduces to a
strictly henselian discrete valuation ring.** This is [Stacks, Tag 0C0N]: a specialization map of
a smooth proper morphism with geometrically connected fibres over a Noetherian base is conjugate,
by isomorphisms of topological groups, to the specialization map from the generic to the closed
point of such a morphism over a strictly henselian discrete valuation ring with algebraically
closed residue field. -/
theorem forall_lift_primeToP_isSpecializationMap_of_isNoetherian_of_forall_isDiscreteValuationRing
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsProper f] [Smooth f]
    [GeometricallyConnected f] (s' s : GeometricPoint S) (p : ℕ)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = p)
    (H : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [StrictlyHenselianLocalRing R] [IsAlgClosed (ResidueField R)]
        (Z : Scheme.{u}) (h : Z ⟶ Spec (.of R)) [IsProper h] [Smooth h]
        [GeometricallyConnected h] (η o : GeometricPoint (Spec (.of R)))
        (zη : GeometricPoint (fiberOverGeometricPoint h η))
        (zo : GeometricPoint (fiberOverGeometricPoint h o))
        (spR : EtaleFundamentalGroup (fiberOverGeometricPoint h η) zη →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h o) zo),
        η.hom default = genericPoint (Spec (.of R)) →
          o.hom default = closedPoint R →
            ringChar ((Spec (.of R)).residueField (o.hom default)) = p →
            IsSpecializationMap h η o zη zo spR →
              ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint h η) zη),
                N.Normal →
                IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint h η) zη)) →
                ¬ p ∣ N.index →
                ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint h o) zo),
                  M.Normal ∧
                  IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint h o) zo)) ∧
                    M.comap spR.toMonoidHom = N) :
    ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x'),
      N.Normal → IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x')) →
      ¬ p ∣ N.index →
      ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        M.Normal ∧ IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)) ∧
          M.comap sp.toMonoidHom = N := by
  obtain ⟨R, hR, hdom, hdvr, hsh, halg, r, η, o, zη, zo, spR, hηgen, hoclosed, -, hro, hspR,
    eη, eo, hcomm⟩ :=
    exists_isSpecializationMap_isomorphic_over_strictlyHenselianDVR f s' s x' x sp hsp
  let := hR
  let := hdom
  let := hdvr
  let := hsh
  let := halg
  have hcharR : ringChar ((Spec (.of R)).residueField (o.hom default)) = p := by
    rw [← ringChar_residueField_eq r (o.hom default), hro, hchar]
  exact forall_lift_of_comm_continuousMulEquiv sp spR eη eo hcomm
    (H R (pullback f r) (pullback.snd f r) η o zη zo spR hηgen hoclosed hcharR hspR)

/-- **The descent of the prime-to-`p` finite quotients over an affine base reduces to a Noetherian
base.** A smooth proper morphism with geometrically connected fibres over an affine base is the
base change of one over a Noetherian affine base by absolute Noetherian approximation, and the
property descends along the resulting cartesian square by
`AlgebraicGeometry.forall_lift_primeToP_isSpecializationMap_of_isPullback`. -/
theorem forall_lift_primeToP_isSpecializationMap_of_isAffine_of_forall_isNoetherian
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] [Smooth f]
    [GeometricallyConnected f] (s' s : GeometricPoint S) (p : ℕ)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = p)
    (H : ∀ (T Z : Scheme.{u}) (h : Z ⟶ T) [IsNoetherian T] [IsProper h] [Smooth h]
        [GeometricallyConnected h] (t' t : GeometricPoint T)
        (zt' : GeometricPoint (fiberOverGeometricPoint h t'))
        (zt : GeometricPoint (fiberOverGeometricPoint h t))
        (spT : EtaleFundamentalGroup (fiberOverGeometricPoint h t') zt' →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h t) zt),
        ringChar (T.residueField (t.hom default)) = p →
        IsSpecializationMap h t' t zt' zt spT →
          ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint h t') zt'),
            N.Normal →
            IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint h t') zt')) →
            ¬ p ∣ N.index →
            ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint h t) zt),
              M.Normal ∧
              IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint h t) zt)) ∧
                M.comap spT.toMonoidHom = N) :
    ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x'),
      N.Normal → IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x')) →
      ¬ p ∣ N.index →
      ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        M.Normal ∧ IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)) ∧
          M.comap sp.toMonoidHom = N := by
  obtain ⟨T, Z, h, q, q', hnoeth, hproper, hsmooth, hgconn, hpb⟩ :=
    exists_isPullback_isNoetherian_properSmoothGeometricallyConnected f
  have := hnoeth
  have := hproper
  have := hsmooth
  have := hgconn
  have hcharT : ringChar (T.residueField ((s.map q).hom default)) = p := by
    have hpt : (s.map q).hom default = q (s.hom default) := rfl
    rw [hpt, ringChar_residueField_eq q (s.hom default), hchar]
  exact forall_lift_primeToP_isSpecializationMap_of_isPullback q' f h q hpb p s' s x' x sp hsp
    fun sp' hsp' ↦ H T Z h (s'.map q) (s.map q) _ _ sp' hcharT hsp'

/-- **The descent of the prime-to-`p` finite quotients reduces to a Noetherian base.** By
[Stacks, Tag 0C0M] a specialization map is conjugate to one of the base change of `f` to the
spectrum of a strictly henselian valuation ring over `S`, which is affine; then
`AlgebraicGeometry.forall_lift_primeToP_isSpecializationMap_of_isAffine_of_forall_isNoetherian`
applies. -/
theorem forall_lift_primeToP_isSpecializationMap_of_forall_isNoetherian {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (p : ℕ) (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = p)
    (H : ∀ (T Z : Scheme.{u}) (h : Z ⟶ T) [IsNoetherian T] [IsProper h] [Smooth h]
        [GeometricallyConnected h] (t' t : GeometricPoint T)
        (zt' : GeometricPoint (fiberOverGeometricPoint h t'))
        (zt : GeometricPoint (fiberOverGeometricPoint h t))
        (spT : EtaleFundamentalGroup (fiberOverGeometricPoint h t') zt' →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h t) zt),
        ringChar (T.residueField (t.hom default)) = p →
        IsSpecializationMap h t' t zt' zt spT →
          ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint h t') zt'),
            N.Normal →
            IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint h t') zt')) →
            ¬ p ∣ N.index →
            ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint h t) zt),
              M.Normal ∧
              IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint h t) zt)) ∧
                M.comap spT.toMonoidHom = N) :
    ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x'),
      N.Normal → IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x')) →
      ¬ p ∣ N.index →
      ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        M.Normal ∧ IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)) ∧
          M.comap sp.toMonoidHom = N := by
  obtain ⟨R, hR, hdom, hval, hsh, -, -, r, η, o, zη, zo, spR, -, -, -, -, -, hro, hspR,
    eη, eo, hcomm⟩ :=
    exists_isSpecializationMap_isomorphic_over_strictlyHenselianValuationRing f s' s x' x sp hsp
  let := hR
  let := hdom
  let := hval
  let := hsh
  have hcharR : ringChar ((Spec (.of R)).residueField (o.hom default)) = p := by
    rw [← ringChar_residueField_eq r (o.hom default), hro, hchar]
  exact forall_lift_of_comm_continuousMulEquiv sp spR eη eo hcomm
    (forall_lift_primeToP_isSpecializationMap_of_isAffine_of_forall_isNoetherian
      (pullback.snd f r) η o p zη zo spR hspR hcharR H)

/-- **The descent of the prime-to-`p` finite quotients reduces to a strictly henselian discrete
valuation ring.** The three reductions of the first two paragraphs of the proof of
[Stacks, Tag 0C0Q], carried out for the hypothesis `hlift` of
`AlgebraicGeometry.exists_continuousMulEquiv_primeToP_of_forall_lift` in place of injectivity: the
base is made affine by [Stacks, Tag 0C0M], then Noetherian by absolute Noetherian approximation
together with [Stacks, Tag 0C0K], then the spectrum of a strictly henselian discrete valuation ring
with algebraically closed residue field by [Stacks, Tag 0C0N].

Unlike the injectivity version, no condition on the residue characteristic is carried: the
prime-to-`p` condition lives on the subgroups, and `p` is just a natural number as far as these
reductions are concerned. -/
theorem forall_lift_primeToP_isSpecializationMap_of_forall_isDiscreteValuationRing
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (s' s : GeometricPoint S) (p : ℕ)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = p)
    (H : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [StrictlyHenselianLocalRing R] [IsAlgClosed (ResidueField R)]
        (Z : Scheme.{u}) (h : Z ⟶ Spec (.of R)) [IsProper h] [Smooth h]
        [GeometricallyConnected h] (η o : GeometricPoint (Spec (.of R)))
        (zη : GeometricPoint (fiberOverGeometricPoint h η))
        (zo : GeometricPoint (fiberOverGeometricPoint h o))
        (spR : EtaleFundamentalGroup (fiberOverGeometricPoint h η) zη →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h o) zo),
        η.hom default = genericPoint (Spec (.of R)) →
          o.hom default = closedPoint R →
            ringChar ((Spec (.of R)).residueField (o.hom default)) = p →
            IsSpecializationMap h η o zη zo spR →
              ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint h η) zη),
                N.Normal →
                IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint h η) zη)) →
                ¬ p ∣ N.index →
                ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint h o) zo),
                  M.Normal ∧
                  IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint h o) zo)) ∧
                    M.comap spR.toMonoidHom = N) :
    ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x'),
      N.Normal → IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x')) →
      ¬ p ∣ N.index →
      ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        M.Normal ∧ IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)) ∧
          M.comap sp.toMonoidHom = N := by
  refine forall_lift_primeToP_isSpecializationMap_of_forall_isNoetherian f s' s p x' x sp hsp
    hchar ?_
  intro T Z h hN hP hS hG t' t zt' zt spT hcharT hspT
  have := hN
  have := hP
  have := hS
  have := hG
  exact forall_lift_primeToP_isSpecializationMap_of_isNoetherian_of_forall_isDiscreteValuationRing
    h t' t p zt' zt spT hspT hcharT H

/-! ### Tag 0C0R granted the descent over a strictly henselian discrete valuation ring -/

/-- **Stacks Project, Tag 0C0R, granted the descent of the prime-to-`p` Galois covers of the
geometric generic fibre over a strictly henselian discrete valuation ring (`Hgal`).** Let
`f : X ⟶ S` be a smooth proper morphism with geometrically connected fibres, let `s' ⇝ s` be a
specialization of points of `S` realized by a specialization map
`sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})`, and let `p` be the characteristic of `κ(s)`. If, for every
strictly henselian discrete valuation ring `R` whose residue field is algebraically closed of
characteristic `p` and every smooth proper
`h : Z ⟶ Spec R` with geometrically connected fibres, every Galois finite étale cover of the
geometric generic fibre `Z_{η̄}` **whose Galois group has order prime to `p`** is the base change
along `Z_{η̄} ⟶ Z` of a finite étale cover of `Z`, then `sp` is surjective and induces an
isomorphism `π'₁(X_{s̄'}) ≅ π'₁(X_{s̄})` of the maximal prime-to-`p` quotients, commuting with the
projections.

This is the exact analogue of
`AlgebraicGeometry.bijective_isSpecializationMap_of_ringChar_zero_of_forall_essImage_isGalois`
([Stacks, Tag 0C0Q] granted `Hgal`), with two differences, which are the two differences between
the tags: the descent is asked only of the Galois covers of order prime to `p`, and the residue
characteristic of `R` is `p` rather than zero. The conclusion is correspondingly weakened from
bijectivity of `sp` to surjectivity plus an isomorphism of the maximal prime-to-`p` quotients.

The residue characteristic of `R` is part of `Hgal` and must be: asked of a strictly henselian
discrete valuation ring of residue characteristic `ℓ ∉ {0, p}`, the descent of the covers of order
prime to `p` would be *false*, since a cover of order divisible by `ℓ` may be prime to `p`. The
reduction forces the residue characteristic of the ring it produces to be `p` and hands that
equation on, so `Hgal` is asked only of the rings for which it can hold.

**No `@[stacks 0C0R]` attribute is attached**: `Hgal` is an input, not a theorem. -/
theorem surjective_and_exists_continuousMulEquiv_primeToP_of_forall_isDiscreteValuationRing
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] [GeometricallyConnected f]
    (s' s : GeometricPoint S) (p : ℕ)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = p)
    (Hgal : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [StrictlyHenselianLocalRing R] [IsAlgClosed (ResidueField R)]
        (Z : Scheme.{u}) (h : Z ⟶ Spec (.of R)) [IsProper h] [Smooth h]
        [GeometricallyConnected h] (η : GeometricPoint (Spec (.of R)))
        (A : FiniteEtaleOver (fiberOverGeometricPoint h η)),
        ringChar ((Spec (.of R)).residueField (closedPoint R)) = p →
          η.hom default = genericPoint (Spec (.of R)) →
            IsGalois A → ¬ p ∣ Nat.card (Aut A) →
              ∃ B : FiniteEtaleOver Z,
                Nonempty ((finiteEtaleBaseChange (pullback.fst h η.hom)).obj B ≅ A)) :
    Function.Surjective sp ∧
      ∃ e : PrimeToP p (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x') ≃ₜ*
          PrimeToP p (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        ∀ g, e (primeToPMk p _ g) = primeToPMk p _ (sp g) := by
  refine exists_continuousMulEquiv_primeToP_of_forall_lift f s' s p x' x sp hsp ?_
  refine forall_lift_primeToP_isSpecializationMap_of_forall_isDiscreteValuationRing f s' s p
    x' x sp hsp hchar ?_
  intro R _ _ _ _ _ Z h _ _ _ η o zη zo spR hη ho hcharR hspR
  exact forall_lift_primeToP_of_isSpecializationMap_of_essImage_isGalois h η o p zη zo spR hspR
    (surjective_specializationMap_of_smooth h η o zη zo spR hspR)
    fun A hA hcard ↦ Hgal R Z h η A (ho ▸ hcharR) hη hA hcard

end AlgebraicGeometry

end
