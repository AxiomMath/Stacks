module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Meromorphic.IdealTimesModule
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact

/-!
# The two denominator quotients and their delta-dimension

Let `X` be locally of finite type over the base scheme of a Chow situation, let `L` be an
invertible `𝒪_X`-module, let `F` be coherent with full support and no embedded associated
points, and let `s` be a regular meromorphic section of `L` with ideal of denominators `I`.
The two canonical injections `1 : I F ⟶ F` and `s : I F ⟶ F ⊗ L` of
[Stacks, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2) are a monomorphism followed by
its cokernel, so each sits in a short exact sequence

  `0 ⟶ I F ⟶ F ⟶ Q₁ ⟶ 0`,   `0 ⟶ I F ⟶ F ⊗ L ⟶ Q₂ ⟶ 0`,

and both quotients are coherent. If moreover `dim_δ(X) ≤ k + 1`, both are supported in
delta-dimension at most `k`.

## Main definitions

* `Stacks.Chow.denominatorQuotient` — the quotient `Q₁ = F / I F`.
* `Stacks.Chow.denominatorSectionQuotient` — the quotient `Q₂ = (F ⊗ L) / s(I F)`.
* `Stacks.Chow.denominatorQuotientShortComplex`,
  `Stacks.Chow.denominatorSectionQuotientShortComplex` — the two short complexes above.

## Main results

* `Stacks.Chow.denominatorQuotientShortComplex_shortExact`,
  `Stacks.Chow.denominatorSectionQuotientShortComplex_shortExact` — both are short exact.
* `Stacks.Chow.isCoherent_denominatorQuotient`,
  `Stacks.Chow.isCoherent_denominatorSectionQuotient` — both quotients are coherent.
* `Stacks.Chow.schemeDeltaDimension_denominatorQuotient_le`,
  `Stacks.Chow.schemeDeltaDimension_denominatorSectionQuotient_le` — both are supported in
  delta-dimension at most `k`.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open Stacks.SheafOfModules.Invertible (tensorProduct)

universe u

namespace Stacks.Chow

/-- `Stacks.SheafOfModules.Invertible.tensorProduct` with its type ascribed as
`SheafOfModules X.ringCatSheaf`. -/
private noncomputable abbrev tensorModulesDecl (X : Scheme.{u})
    (F L : _root_.SheafOfModules.{u} X.ringCatSheaf) :
    _root_.SheafOfModules.{u} X.ringCatSheaf :=
  tensorProduct X.sheaf.obj X.ringCatSheaf.property F L

/-! ### A generic point avoids a closed nowhere dense subset -/

/-- The generic point of an irreducible component of a locally Noetherian scheme does not lie in a
closed nowhere dense subset. -/
private alias genericPoint_notMem_of_isNowhereDense :=
  AlgebraicGeometry.genericPoint_not_mem_closed_nowhereDense

/-- A point of the exceptional subset of [Stacks, Tag 02P2] has relative dimension at most `k` when
`dim_δ(X) ≤ k + 1`. -/
theorem relativeDimension_le_of_mem_denominatorBadLocus (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    {x : X} (hx : x ∈ denominatorBadLocus X L s) :
    relativeDimension C.dimensionFunction f x ≤ k := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction f
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set X)) isIrreducible_singleton.closure
  have hxW : x ∈ W := hsub (subset_closure rfl)
  have hgen : IsGenericPoint hW.1.genericPoint W :=
    hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  have hne : hW.1.genericPoint ≠ x := fun h =>
    genericPoint_notMem_of_isNowhereDense X hW hgen (denominatorBadLocus_isClosed X L s hL hs)
      (denominatorBadLocus_isNowhereDense X L s hL hs) (h ▸ hx)
  rw [schemeDeltaDimension_eq_iSup] at hdim
  have hWle : relativeDimension C.dimensionFunction f hW.1.genericPoint ≤ k + 1 := by
    have hle := WithBotTop.coe_le_coe.mp ((le_iSup
      (fun V : irreducibleComponents X => (deltaDimension C f ⟨(V : Set X), V.2.1,
        isClosed_of_mem_irreducibleComponents (V : Set X) V.2⟩ : EInt))
      (⟨W, hW⟩ : irreducibleComponents X)).trans hdim)
    rwa [deltaDimension_eq_of_isGenericPoint C f _ _ hgen] at hle
  have hlt := d.strictAnti_specializes (hgen.specializes hxW) hne
  rw [hd x, hd hW.1.genericPoint] at hlt
  omega

/-! ### The two quotients -/

/-- The quotient of a coherent `𝒪_X`-module `F` by its product with the ideal of denominators of
a meromorphic section `s` of an invertible `𝒪_X`-module `L`. -/
noncomputable def denominatorQuotient (X : Scheme.{u})
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L) :
    _root_.SheafOfModules.{u} X.ringCatSheaf :=
  cokernel (denominatorIdealTimesModuleι X L F s)

/-- The quotient of `F ⊗ L` by the image of the product of `F` with the ideal of denominators of
a regular meromorphic section `s` of `L` under multiplication by `s`. -/
noncomputable def denominatorSectionQuotient (X : Scheme.{u})
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) [F.IsCoherent]
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ) :
    _root_.SheafOfModules.{u} X.ringCatSheaf :=
  cokernel (denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).val

/-! ### The two short exact sequences -/

/-- The short complex `0 ⟶ I F ⟶ F ⟶ F / I F ⟶ 0` built from the first canonical map of
[Stacks, Tag 02P2] and its cokernel. -/
noncomputable def denominatorQuotientShortComplex (X : Scheme.{u})
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L) :
    ShortComplex (_root_.SheafOfModules.{u} X.ringCatSheaf) :=
  ShortComplex.mk (denominatorIdealTimesModuleι X L F s)
    (cokernel.π (denominatorIdealTimesModuleι X L F s)) (cokernel.condition _)

/-- The short complex `0 ⟶ I F ⟶ F ⊗ L ⟶ (F ⊗ L) / s(I F) ⟶ 0` built from the second canonical
map of [Stacks, Tag 02P2] and its cokernel. -/
noncomputable def denominatorSectionQuotientShortComplex (X : Scheme.{u})
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) [F.IsCoherent]
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ) :
    ShortComplex (_root_.SheafOfModules.{u} X.ringCatSheaf) :=
  ShortComplex.mk (denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).val
    (cokernel.π (denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).val)
    (cokernel.condition _)

/-- For `X` locally of finite type over the base of a Chow situation with `dim_δ(X) ≤ k + 1` and no
embedded points, `F` coherent of full support with no embedded associated points, and `s` a regular
meromorphic section of the invertible module `L`, the first canonical map of the ideal of
denominators sits in a short exact sequence `0 ⟶ I F ⟶ F ⟶ Q₁ ⟶ 0`. -/
theorem denominatorQuotientShortComplex_shortExact (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (_hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (_hX : HasNoEmbeddedPoints X)
    (_hF : HasNoEmbeddedAssociatedPoints F)
    (_hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (_hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (_hs : IsRegularMeromorphicSection X.sheaf L s) :
    (denominatorQuotientShortComplex X L F s).ShortExact :=
  have := denominatorIdealTimesModuleι_mono X L F s
  ShortComplex.shortExact_mk_cokernel_π _

/-- In the situation of `Stacks.Chow.denominatorQuotientShortComplex_shortExact`, multiplication by
`s` on the product of `F` with the ideal of denominators sits in a short exact sequence
`0 ⟶ I F ⟶ F ⊗ L ⟶ Q₂ ⟶ 0`. -/
theorem denominatorSectionQuotientShortComplex_shortExact (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (_hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (_hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    (@denominatorSectionQuotientShortComplex X L F s
      (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp).ShortExact :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := denominatorIdealTimesModuleMul_mono X L F s hL hs hF hSupp
  ShortComplex.shortExact_mk_cokernel_π _

/-! ### Coherence of the two quotients -/

/-- The product of the ideal of denominators with a coherent module is coherent. -/
public theorem isCoherent_denominatorIdealTimesModule {X : Scheme.{u}}
    [IsLocallyNoetherian X] (L F : _root_.SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    [hFc : F.IsCoherent] : (denominatorIdealTimesModule X L F s).IsCoherent := by
  have hFq : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have hIq : (denominatorIdeal X L s).IsQuasicoherent :=
    denominatorIdeal_isQuasicoherent X L s hL
  have htq : (tensorModulesDecl X (denominatorIdeal X L s) F).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ _ hIq hFq
  have hPq : (denominatorIdealTimesModule X L F s).IsQuasicoherent := by
    have hcoker : (cokernel (denominatorIdealAction X L F s)).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
        (M := tensorModulesDecl X (denominatorIdeal X L s) F) (N := F)
        (denominatorIdealAction X L F s)
    show (kernel (cokernel.π (denominatorIdealAction X L F s))).IsQuasicoherent
    exact @Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel X F _
      (cokernel.π (denominatorIdealAction X L F s)) inferInstance hcoker
  exact @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono X _ F
    (denominatorIdealTimesModule X L F s) hFc hPq (denominatorIdealTimesModuleι X L F s)
    (denominatorIdealTimesModuleι_mono X L F s)

/-- The quotient of `F` by its product with the ideal of denominators of `s` is coherent. -/
theorem isCoherent_denominatorQuotient (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    [hFc : F.IsCoherent] {k : ℤ}
    (_hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (_hX : HasNoEmbeddedPoints X)
    (_hF : HasNoEmbeddedAssociatedPoints F)
    (_hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (_hs : IsRegularMeromorphicSection X.sheaf L s) :
    (denominatorQuotient X L F s).IsCoherent :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := isCoherent_denominatorIdealTimesModule L F s hL
  have hQq : (denominatorQuotient X L F s).IsQuasicoherent :=
    have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
    have : (denominatorIdealTimesModule X L F s).IsQuasicoherent :=
      _root_.isQuasicoherent_of_isCoherent _
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
      (M := denominatorIdealTimesModule X L F s) (N := F)
      (denominatorIdealTimesModuleι X L F s)
  @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi X _ F
    (denominatorQuotient X L F s) hFc hQq
    (cokernel.π (denominatorIdealTimesModuleι X L F s)) coequalizer.π_epi

/-- The quotient of `F ⊗ L` by the image of the product of `F` with the ideal of denominators of
`s` is coherent. -/
theorem isCoherent_denominatorSectionQuotient (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (_hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (_hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    (@denominatorSectionQuotient X L F s (LocallyOfFiniteType.isLocallyNoetherian f) hL hs
      inferInstance hF hSupp).IsCoherent := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := isCoherent_denominatorIdealTimesModule L F s hL
  have hFq : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  have hLc : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
  have hLq : L.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent L
  have hFLq : (tensorModulesDecl X F L).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ _ hFq hLq
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have hFLc : (tensorModulesDecl X F L).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F L
  have hPq : (denominatorIdealTimesModule X L F s).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent _
  have hQq : (denominatorSectionQuotient X L F s hL hs hF hSupp).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
      (M := denominatorIdealTimesModule X L F s) (N := tensorModulesDecl X F L)
      (denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).val
  exact @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi X _
    (tensorModulesDecl X F L) (denominatorSectionQuotient X L F s hL hs hF hSupp) hFLc hQq
    (cokernel.π (denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).val)
    coequalizer.π_epi

/-! ### The delta-dimension of the two quotients -/

/-- If `dim_δ(X) ≤ k + 1`, the quotient of `F` by its product with the ideal of denominators of `s`
is supported in delta-dimension at most `k`. -/
theorem schemeDeltaDimension_denominatorQuotient_le (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    schemeDeltaDimension C ((@reducedSupport X (denominatorQuotient X L F s)
        (isCoherent_denominatorQuotient C f L F s hdim hX hF hSupp hL hs)).subschemeι ≫ f)
      ≤ (k : EInt) := by
  have := isCoherent_denominatorQuotient C f L F s hdim hX hF hSupp hL hs
  refine schemeDeltaDimension_reducedSupport_le C f _ fun x hx => ?_
  refine relativeDimension_le_of_mem_denominatorBadLocus C f L s hL hs hdim ?_
  refine denominatorIdealTimesModuleι_cokernel_support X L F s ?_
  rw [SheafOfModules.supp_eq_moduleSheaf_supp]
  exact hx

/-- If `dim_δ(X) ≤ k + 1`, the quotient of `F ⊗ L` by the image of the product of `F` with the
ideal of denominators of `s` is supported in delta-dimension at most `k`. -/
theorem schemeDeltaDimension_denominatorSectionQuotient_le (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : _root_.SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    schemeDeltaDimension C
        ((@reducedSupport X
            (@denominatorSectionQuotient X L F s (LocallyOfFiniteType.isLocallyNoetherian f) hL hs
              inferInstance hF hSupp)
            (isCoherent_denominatorSectionQuotient C f L F s hdim hX hF hSupp hL hs)).subschemeι
          ≫ f)
      ≤ (k : EInt) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := isCoherent_denominatorSectionQuotient C f L F s hdim hX hF hSupp hL hs
  refine schemeDeltaDimension_reducedSupport_le C f _ fun x hx => ?_
  refine relativeDimension_le_of_mem_denominatorBadLocus C f L s hL hs hdim ?_
  refine denominatorIdealTimesModuleMul_cokernel_supp X L F s hL hs hF hSupp ?_
  rw [SheafOfModules.supp_eq_moduleSheaf_supp]
  exact hx

end Stacks.Chow

end
