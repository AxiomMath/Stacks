module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelStalk
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoNonvanishingBridge
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleStalkKernel
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer

/-!
# Associated points across the punctured closed immersion

Let `A` be a Noetherian local ring and `f ∈ 𝔪`. For a coherent triple `T`, the associated points
of the closed-fibre member of the quotient triple `T.quotientTriple hf` lying in the punctured
closed fibre map to associated points of `T.F / f T.F` on the punctured spectrum. For an
invertible triple `L` there is a section pair of `L` for which multiplication by it on the
quotient triple is a monomorphism on both members and has `f`-torsion-free cokernel on the
punctured spectrum.

## Main results

* `Stacks.Algebraization.isAssociatedPoint_pullback_open_iff`: a point is an associated point of
  the pullback of a module along an open immersion if and only if its image is an associated
  point of the module.
* `Stacks.Algebraization.isAssociatedPoint_pullback_puncturedClosedImmersion_iff`: a point of
  the punctured closed fibre is an associated point of the inverse image of `F` if and only if its
  image is an associated point of `F / f F`.
* `Stacks.Algebraization.isAssociatedPoint_cokernel_of_isAssociatedPoint_F₀_quotientTriple`: an
  associated point of the closed-fibre member of the quotient triple lying in the punctured
  closed fibre maps to an associated point of `T.F / f T.F`.
* `Stacks.Algebraization.forall_mem_associatedPoints_quotientTriple_mem_nonvanishingLocus`: a
  global section of `L.F` that does not vanish at the associated points of `T.F` and of
  `T.F / f T.F` does not vanish at the image of any associated point of the closed-fibre member
  of the quotient triple lying in the punctured closed fibre.
* `Stacks.Algebraization.CoherentTriple.mono_onClosedFibre_quotientTriple_of_nonvanishing`: for
  such a section, multiplication by the section pair on the quotient triple is a monomorphism on
  the closed-fibre member.
* `Stacks.Algebraization.exists_sectionPair_mono_quotientTriple`: there is a section pair of `L`
  for which multiplication by it on the quotient triple is a monomorphism on both members and has
  `f`-torsion-free cokernel on the punctured spectrum.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Limits IsLocalRing
open Stacks.AlgebraicGeometry.PrincipalIdealExtension (smulPowHom)

universe u

namespace Stacks.Algebraization

/-- For an open immersion `j : X ⟶ Y`, a point `x` of `X` is an associated point of the pullback
of `G` along `j` if and only if `j x` is an associated point of `G`. -/
theorem isAssociatedPoint_pullback_open_iff {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (G : Y.Modules) (x : X) :
    Stacks.Divisors.IsAssociatedPoint ((Scheme.Modules.pullback j).obj G) x ↔
      Stacks.Divisors.IsAssociatedPoint G (j.base x) :=
  (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr
      ((Scheme.Modules.restrictFunctorIsoPullback j).app G) x).symm.trans
    (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff j G x)

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}

omit [IsNoetherianRing A] in
/-- A point `p'` of the punctured closed fibre is an associated point of the inverse image of `F`
along the punctured closed immersion if and only if its image in the punctured spectrum is an
associated point of `F / f F`. -/
theorem isAssociatedPoint_pullback_puncturedClosedImmersion_iff
    (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    (p' : (puncturedClosedFibre A f).toScheme) :
    Stacks.Divisors.IsAssociatedPoint
        ((Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).obj F) p' ↔
      Stacks.Divisors.IsAssociatedPoint (cokernel (smulPowHom F (scalarGlobal A f) 1))
        ((puncturedClosedFibreRestriction A f).base p') := by
  rw [Stacks.Divisors.isAssociatedPoint_pullback_iff_quotient
      (puncturedClosedFibreRestriction A f) F p',
    ker_stalkMap_puncturedClosedImmersion,
    isAssociatedPoint_cokernel_smulPowHom_one_iff]
  exact Iff.rfl

/-- If the image in the closed fibre of a point `p'` of the punctured closed fibre is an
associated point of the closed-fibre member of the quotient triple `T.quotientTriple hf`, then the
image of `p'` in the punctured spectrum is an associated point of `T.F / f T.F`. -/
theorem isAssociatedPoint_cokernel_of_isAssociatedPoint_F₀_quotientTriple
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    (p' : (puncturedClosedFibre A f).toScheme)
    (hp : Stacks.Divisors.IsAssociatedPoint (T.quotientTriple hf).F₀
      ((puncturedClosedFibre A f).ι.base p')) :
    Stacks.Divisors.IsAssociatedPoint
      (cokernel (smulPowHom T.F (scalarGlobal A f) 1))
      ((puncturedClosedFibreRestriction A f).base p') :=
  (isAssociatedPoint_pullback_puncturedClosedImmersion_iff T.F p').mp
    ((Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr
        (T.quotientTriple hf).alpha p').mpr
      ((isAssociatedPoint_pullback_open_iff (puncturedClosedFibre A f).ι
        (T.quotientTriple hf).F₀ p').mpr hp))

/-- If a global section `x` of `L.F` does not vanish at the associated points of `T.F` and of
`T.F / f T.F`, then for every associated point `p` of the closed-fibre member of the quotient
triple `T.quotientTriple hf` lying in the punctured closed fibre, `x` does not vanish at the image
of `p` in the punctured spectrum. -/
theorem forall_mem_associatedPoints_quotientTriple_mem_nonvanishingLocus
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A)
    {L : CoherentTriple A f} (hL : IsInvertibleTriple L)
    (T : CoherentTriple A f) (x : Γ(L.F, ⊤))
    (hnv : letI := hL.invertible_F
      (Stacks.Divisors.associatedPoints T.F ∪
          Stacks.Divisors.associatedPoints
            (cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1))) ⊆
        (Stacks.NonvanishingOpen.nonvanishingOpen
          (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x : Set _)) :
    letI := hL.invertible_F
    ∀ p ∈ Stacks.Divisors.associatedPoints (T.quotientTriple hf).F₀,
      ∀ hp : p ∈ puncturedClosedFibre A f,
        (puncturedClosedFibreRestriction A f).base ⟨p, hp⟩ ∈
          Stacks.Ample.nonvanishingLocus L.F x := by
  let := hL.invertible_F
  intro p hp hpmem
  exact hnv (Or.inr (isAssociatedPoint_cokernel_of_isAssociatedPoint_F₀_quotientTriple hf T
    (⟨p, hpmem⟩ : (puncturedClosedFibre A f).toScheme) hp))

/-! ### Monicity on the closed fibre -/

/-- If a global section `x` of `L.F` does not vanish at the associated points of `T.F` and of
`T.F / f T.F`, then multiplication by the section pair `(x, x₀)` on the `n`-th twist of the
quotient triple `T.quotientTriple hf` is a monomorphism on the closed-fibre member. -/
public theorem CoherentTriple.mono_onClosedFibre_quotientTriple_of_nonvanishing
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) (T L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀)
    (n : ℤ) {N₀ : (closedFibre A f).Modules}
    (hq : (((T.quotientTriple hf).twistZ L hL n).F₀).IsQuasicoherent)
    (hq' : (Stacks.RelativeVeryAmple.tensorModules (closedFibre A f)
      (((T.quotientTriple hf).twistZ L hL n).F₀) L.F₀).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((closedFibre A f).toRingedSpace)).presheaf,
          (((closedFibre A f).toRingedSpace)).IsSheaf⟩).obj (L.F₀)).obj (N₀)) ≅
      _root_.SheafOfModules.unit _)
    (hnv : letI := hL.invertible_F
      (Stacks.Divisors.associatedPoints T.F ∪
          Stacks.Divisors.associatedPoints
            (cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1))) ⊆
        (Stacks.NonvanishingOpen.nonvanishingOpen
          (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x : Set _)) :
    Mono ((T.quotientTriple hf).mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onClosedFibre :=
  T.mono_onClosedFibre_mulSectionTwistZOfGlobalSections_quotientTriple hf L hL x x₀ hx n hq hq' ψ
    (forall_mem_associatedPoints_quotientTriple_mem_nonvanishingLocus hf hL T x hnv)

/-- For a Noetherian local ring `A`, an `f ∈ 𝔪`, an invertible triple `L` and any triple `T`,
there is a section pair `(x, x₀)` of `L` for which multiplication by it on the `n`-th twist of the
quotient triple `T.quotientTriple hf` is a monomorphism on both members and has `f`-torsion-free
cokernel on the punctured spectrum. -/
public theorem exists_sectionPair_mono_quotientTriple
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (T : CoherentTriple A f) (n : ℤ)
    {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
          (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
        (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    {N₀ : (closedFibre A f).Modules}
    (ψ₀ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((closedFibre A f).toRingedSpace)).presheaf,
          (((closedFibre A f).toRingedSpace)).IsSheaf⟩).obj (L.F₀)).obj (N₀)) ≅
      _root_.SheafOfModules.unit _)
    (hq : (((T.quotientTriple hf).twistZ L hL n).F).IsQuasicoherent)
    (hq' : (Stacks.RelativeVeryAmple.tensorModules
      (Stacks.Divisors.puncturedSpectrum A).toScheme
      (((T.quotientTriple hf).twistZ L hL n).F) L.F).IsQuasicoherent)
    (hqc : letI := hL.invertible_F
      (Stacks.RelativeVeryAmple.tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (cokernel (smulPowHom (T.quotientTriple hf).F (scalarGlobal A f) 1))
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).IsQuasicoherent)
    (hqc' : letI := hL.invertible_F
      (Stacks.RelativeVeryAmple.tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (Stacks.RelativeVeryAmple.tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
          (cokernel (smulPowHom (T.quotientTriple hf).F (scalarGlobal A f) 1))
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
        L.F).IsQuasicoherent)
    (hq₀ : (((T.quotientTriple hf).twistZ L hL n).F₀).IsQuasicoherent)
    (hq₀' : (Stacks.RelativeVeryAmple.tensorModules (closedFibre A f)
      (((T.quotientTriple hf).twistZ L hL n).F₀) L.F₀).IsQuasicoherent) :
    ∃ (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
      (hx : globalSectionsMap A f L x =
        pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀),
      Mono ((T.quotientTriple hf).mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onPunctured ∧
        IsFTorsionFree A f
          (cokernel
            ((T.quotientTriple hf).mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onPunctured) ∧
        Mono
          ((T.quotientTriple hf).mulSectionTwistZOfGlobalSections
            L hL x x₀ hx n).onClosedFibre := by
  let := hL.invertible_F
  obtain ⟨x, x₀, hx, hnv⟩ :=
    exists_sectionPair_nonvanishing_on_associatedPoints_depthFree hf hL T
  obtain ⟨hnvF, hnvQ⟩ := Set.union_subset_iff.mp hnv
  have hmono := (T.quotientTriple hf).mono_onPunctured_mulSectionTwistZOfGlobalSections L hL
    x x₀ hx n hq hq' ψ hnvF
  exact ⟨x, x₀, hx, hmono,
    (T.quotientTriple hf).isFTorsionFree_cokernel_onPunctured_mulSectionTwistZOfGlobalSections
      L hL x x₀ hx n hmono hqc hqc' ψ hnvQ,
    T.mono_onClosedFibre_quotientTriple_of_nonvanishing hf L hL x x₀ hx n hq₀ hq₀' ψ₀ hnv⟩

end Stacks.Algebraization

end
