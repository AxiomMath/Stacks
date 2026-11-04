module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingAboveTheDimensionInduction

/-!
# Surjectivity of restriction in the top degree

Let `X` be a quasi-compact quasi-separated algebraic space over a scheme `S` with `dim X ≤ d`
and let `F` be a quasi-coherent `𝒪_X`-module.  Clause (2) of Stacks 0A4R says that the
restriction map `H^d(X, F) ⟶ H^d(U, F)` is onto for every quasi-compact open subspace `U`.
This file proves it along elementary distinguished squares.

For `d ≥ 1` the statement is proved for every open immersion `j : Z ⟶ X` from a quasi-compact
algebraic space, by the induction principle of Stacks 08GP.  On an affine `X`, `H^d(Z, F) = 0`
by Stacks 0A3G.  Across an elementary distinguished square `(U₀ ⊆ W, f : V ⟶ W)` with `V`
affine, put `U'' = Z ∪ U₀`:

* `(U'' ⊆ W, f)` is again an elementary distinguished square, its intersection is a
  quasi-compact open of the affine `V`, where `H^d` vanishes, so the Mayer–Vietoris sequence
  makes `H^d(W, F) ⟶ H^d(U'', F)` onto;
* inside `U''`, the open subspace `Z` and the open immersion `U₀ ⟶ U''` form an elementary
  distinguished square, whose Mayer–Vietoris map `H^d(U₀, F) ⟶ H^d(Z ∩ U₀, F)` is a restriction
  map, onto by induction; so `H^d(U'', F) ⟶ H^d(Z, F)` is onto;
* restriction maps compose.

This is the source's argument, with the excision of Stacks 0A4P replaced by the Mayer–Vietoris
sequence of Stacks 08GW.  For `d = 0` a quasi-compact open `U` of `X` is closed, and the
Mayer–Vietoris sequence of `U` and its complement, whose intersection is empty, makes
`H⁰(X, F) ⟶ H⁰(U, F)` onto.

## Main results

* `AlgebraicGeometry.Space.epi_rightDerived_globalSectionsAbRestriction_of_dimension_le_of_pos`:
  for `d ≥ 1`, restriction along an open immersion from a quasi-compact algebraic space is onto on
  `H^d`.
* `AlgebraicGeometry.Space.epi_rightDerived_globalSectionsAbRestriction_zero_of_dimension_le_zero`:
  the case `d = 0`.
* `AlgebraicGeometry.Space.epi_rightDerived_globalSectionsAbRestriction_of_dimension_le`: both
  together.

## Implementation notes

The statements are for an open immersion `j : Z ⟶ X` from a quasi-compact algebraic space,
which up to isomorphism is the inclusion of a quasi-compact open subspace; the induction needs
this generality, since the intersections of elementary distinguished squares are fibre products
rather than subspaces.

## References

* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The affine case.**  On an affine algebraic space `V` with `dim V ≤ d`, `d ≥ 1`,
restriction along an open immersion `Z ⟶ V` from a quasi-compact space is onto on `H^d`, because
`H^d(Z, F|_Z) = 0` by Stacks 0A3G
(`isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace`). -/
theorem epi_rightDerived_globalSectionsAbRestriction_of_isAffineSpace
    {V Z : AlgebraicSpaces B S hS} (hV : IsAffineSpace B S hS V.1) (d : ℕ) (hd : 0 < d)
    (hdim : dimension B S hS V.1 V.2 ≤ d) (j : Z ⟶ V) (hj : IsOpenImmersion B S hS j.hom)
    (hje : IsEtale B S hS j.hom) (hZ : IsQuasiCompactSpace B S hS Z.1)
    (F : Modules.{u, u} B S hS V.1 V.2) (hF : F.IsQuasicoherentOnSite) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hje) d).app F) :=
  epi_rightDerived_globalSectionsAbRestriction_of_isZero B S hS j hje F d
    (isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace B S hS j hj hV d d
      hdim le_rfl hd hZ _ (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ F hF))

/-- **Restriction to the open part of a square, up to isomorphism.**  Let
`(U ⊆ W, g₀ : V ⟶ W)` be an elementary distinguished square and let `j : Z ⟶ W` be identified
with the inclusion of `U` by an isomorphism `Z ≅ U`.  If restriction to `U` is onto on `H^d` at
`F`, then so is restriction along `j`. -/
theorem epi_rightDerived_globalSectionsAbRestriction_of_epi_edsOpenHom_of_iso (d : ℕ)
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y' : Subfunctor W.1}
    {g₀ : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 Y' g₀)
    (F : Modules.{u, u} B S hS W.1 W.2)
    (hC : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)) d).app F))
    {Z : AlgebraicSpaces B S hS} (j : Z ⟶ W) (hj : IsEtale B S hS j.hom)
    (e : Z.1 ≅ Y'.toFunctor) (he : e.hom ≫ Y'.ι = j.hom) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hj) d).app F) := by
  let e' : Z ⟶ edsOpen B S hS hsq := ObjectProperty.homMk e.hom
  have : IsIso e' := (ObjectProperty.isIso_hom_iff e').1 (inferInstanceAs (IsIso e.hom))
  have he' : IsEtale B S hS e'.hom := isEtale_of_isIso B S hS e.hom
  have := isIso_rightDerived_globalSectionsAbRestriction_of_isIso B S hS e' he'
    ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj F) d
  exact epi_rightDerived_globalSectionsAbRestriction_comp B S hS e' (edsOpenHom B S hS hsq) he'
    (isEtale_edsOpenHom B S hS hsq) (ObjectProperty.hom_ext _ he) hj F d hC inferInstance

/-- **Restriction to the open part of a square with open étale part.**  Let
`(U ⊆ W, g₀ : V ⟶ W)` be an elementary distinguished square whose étale part is an open
immersion, with intersection `P` and projection `s : P ⟶ V`, and let `j : Z ⟶ W` be identified
with the inclusion of `U` by an isomorphism `Z ≅ U`.  If restriction along `s` is onto on `H^d`
at `F|_V`, then restriction along `j` is onto on `H^d` at `F`: the Mayer–Vietoris map out of
`V` is restriction along `s`
(`AlgebraicGeometry.Space.epi_rightDerived_whiskerRight_edsEtaleComparison_of_epi`), so
restriction to `U` is onto by Mayer–Vietoris, and restriction along the isomorphism is
invertible. -/
theorem epi_rightDerived_globalSectionsAbRestriction_of_eds_of_iso (d : ℕ)
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y' : Subfunctor W.1}
    {g₀ : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 Y' g₀)
    (hg₀ : IsOpenImmersion B S hS g₀) (F : Modules.{u, u} B S hS W.1 W.2)
    (hIH : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)) d).app ((etaleModulePullback.{u, u} B S hS
        (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj F)))
    {Z : AlgebraicSpaces B S hS} (j : Z ⟶ W) (hj : IsEtale B S hS j.hom)
    (e : Z.1 ≅ Y'.toFunctor) (he : e.hom ≫ Y'.ι = j.hom) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hj) d).app F) :=
  epi_rightDerived_globalSectionsAbRestriction_of_epi_edsOpenHom_of_iso B S hS d hsq F
    (epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_epi B S hS hsq F d
      (epi_rightDerived_whiskerRight_edsEtaleComparison_of_epi B S hS hsq hg₀ F d hIH))
    j hj e he

/-- **Restriction to the open part of a square with affine étale part.**  Let `(U ⊆ W, f : V ⟶ W)`
be an elementary distinguished square with `W` quasi-separated, `U` quasi-compact and `V` affine
of dimension at most `d`, `d ≥ 1`.  Then restriction `H^d(W, F) ⟶ H^d(U, F)` is onto for every
quasi-coherent `F`, since `H^d` vanishes on the intersection, a quasi-compact open of `V`. -/
theorem epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_isAffineSpace (d : ℕ)
    (hd : 0 < d) {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : Subfunctor W.1} {f : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 U f)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) (hVaff : IsAffineSpace B S hS V)
    (hdimV : dimension B S hS V hsq.isAlgebraicSpace ≤ d)
    (F : Modules.{u, u} B S hS W.1 W.2) (hF : F.IsQuasicoherentOnSite) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)) d).app F) := by
  refine epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_isZero B S hS hsq F d ?_
  have hsnd : IsOpenImmersion B S hS (edsSnd B S hS hsq).hom :=
    isOpenImmersion_of_isPullback B S hS (isPullback_edsInter B S hS hsq) hsq.isOpenSubspace.2
  have hPqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1 :=
    isQuasiCompactSpace_pullback B S hS B.contains_terminal _ _ (edsOpen B S hS hsq).2 W.2
      hUqc (IsAffineSpace.isQuasiCompactSpace hVaff) hWqs
  exact isZero_rightDerived_globalSectionsAb_of_isOpenImmersion_of_isAffineSpace B S hS
    (edsSnd B S hS hsq) hsnd hVaff d d hdimV le_rfl hd hPqc _
    (isQuasicoherentOnSite_etaleModulePullback B S hS _ (isEtale_edsInterHom B S hS hsq) F hF)

/-- **The step across an elementary distinguished square.**  Let `(U₀ ⊆ W, f : V ⟶ W)` be an
elementary distinguished square with `W` quasi-separated, `U₀` quasi-compact and `V` affine of
dimension at most `d`, `d ≥ 1`, and suppose that on `U₀` restriction along every open immersion
from a quasi-compact space is onto on `H^d` for quasi-coherent modules.  Then the same holds on
`W`.  See the module docstring for the argument. -/
theorem epi_rightDerived_globalSectionsAbRestriction_of_eds (d : ℕ) (hd : 0 < d)
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : Subfunctor W.1}
    {f : V ⟶ W.1} (hsq : IsElementaryDistinguishedSquare B S hS W.2 U₀ f)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (hU₀qc : IsQuasiCompactSpace B S hS U₀.toFunctor) (hVaff : IsAffineSpace B S hS V)
    (hdimV : dimension B S hS V hsq.isAlgebraicSpace ≤ d)
    (hU : ∀ U₀' : AlgebraicSpaces B S hS, U₀'.1 = U₀.toFunctor →
      ∀ {Z : AlgebraicSpaces B S hS} (j : Z ⟶ U₀') (_ : IsOpenImmersion B S hS j.hom)
        (hje : IsEtale B S hS j.hom), IsQuasiCompactSpace B S hS Z.1 →
        ∀ F : Modules.{u, u} B S hS U₀'.1 U₀'.2, F.IsQuasicoherentOnSite →
          Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hje) d).app F))
    {Z : AlgebraicSpaces B S hS} (j : Z ⟶ W) (hj : IsOpenImmersion B S hS j.hom)
    (hje : IsEtale B S hS j.hom) (hZqc : IsQuasiCompactSpace B S hS Z.1)
    (F : Modules.{u, u} B S hS W.1 W.2) (hF : F.IsQuasicoherentOnSite) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hje) d).app F) := by
  have hU₀o := hsq.isOpenSubspace
  -- The open subspace `U''` with point set `|Z| ∪ |U₀|`.
  have hO : IsOpen (Set.range (pointsMap B S hS Z.1 j.hom) ∪
      Set.range (pointsMap B S hS U₀.toFunctor U₀.ι)) :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS j.hom hj).union
      (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS W.2 U₀ hU₀o)
  obtain ⟨U'', hU'', hU''range⟩ : ∃ U'' : Subfunctor W.1, IsOpenSubspace B S hS U'' ∧
      Set.range (pointsMap B S hS U''.toFunctor U''.ι) =
        Set.range (pointsMap B S hS Z.1 j.hom) ∪
          Set.range (pointsMap B S hS U₀.toFunctor U₀.ι) :=
    ⟨_, isOpenSubspace_openSubspaceOfPoints B S hS W.2 _ hO,
      range_pointsMap_ι_openSubspaceOfPoints B S hS _⟩
  have : CompactSpace (points B S hS Z.1) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS Z.2 hZqc
  have : CompactSpace (points B S hS U₀.toFunctor) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS hU₀o.1 hU₀qc
  have hU''qc : IsQuasiCompactSpace B S hS U''.toFunctor :=
    isQuasiCompactSpace_of_isCompact_range B S hS W.2 hU'' (by
      rw [hU''range]
      exact (isCompact_range (continuous_pointsMap B S hS j.hom)).union
        (isCompact_range (continuous_pointsMap B S hS U₀.ι)))
  have hU''qs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U''.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hU''.1 hWqs
      (isQuasiSeparated_of_mono B S hS U''.ι inferInstance)
  -- Step A: `H^d(W, F) ⟶ H^d(U'', F)` is onto.
  have hsq1 : IsElementaryDistinguishedSquare B S hS W.2 U'' f :=
    isElementaryDistinguishedSquare_of_range_subset B S hS hsq U'' hU'' (by
      rw [hU''range]
      exact Set.subset_union_right)
  have hA := epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_isAffineSpace B S hS d hd
    hsq1 hWqs hU''qc hVaff hdimV F hF
  -- `Z` and `U₀` inside `U''`.
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS W.2 Z.2 U'' hU''
    j.hom).2 (by rw [hU''range]; exact Set.subset_union_left)
  have hgo : IsOpenImmersion B S hS g :=
    isOpenImmersion_of_comp_mono B S hS g U''.ι (by rw [hg]; exact hj)
  obtain ⟨g0, hg0⟩ := (factorsThrough_openSubspace_iff_points B S hS W.2 hU₀o.1 U'' hU''
    U₀.ι).2 (by rw [hU''range]; exact Set.subset_union_right)
  have hg0o : IsOpenImmersion B S hS g0 :=
    isOpenImmersion_of_comp_mono B S hS g0 U''.ι (by rw [hg0]; exact hU₀o.2)
  have : Mono g := mono_of_presheaf_isOpenImmersion hgo
  obtain ⟨Y', hY', eY, heY⟩ : ∃ Y' : Subfunctor U''.toFunctor, IsOpenSubspace B S hS Y' ∧
      ∃ eY : Z.1 ≅ Y'.toFunctor, eY.hom ≫ Y'.ι = g :=
    ⟨_, isOpenSubspace_range_of_isAlgebraicSpace B S hS Z.2 g hgo,
      asIso (Subfunctor.toRange g), Subfunctor.toRange_ι g⟩
  have hinj : Function.Injective (pointsMap B S hS U''.toFunctor U''.ι) :=
    pointsMap_injective_of_mono B S hS U''.ι
  -- Step C: `H^d(U'', F) ⟶ H^d(Z, F)` is onto.
  have hsq2 : IsElementaryDistinguishedSquare B S hS (edsOpen B S hS hsq1).2 Y' g0 := by
    refine isElementaryDistinguishedSquare_of_compl_subset B S hS (edsOpen B S hS hsq1).2 Y' hY'
      hU₀o.1 g0 hg0o fun x hx => ?_
    have hxmem : pointsMap B S hS U''.toFunctor U''.ι x ∈
        Set.range (pointsMap B S hS U''.toFunctor U''.ι) := ⟨x, rfl⟩
    rw [hU''range] at hxmem
    rcases hxmem with ⟨z, hz⟩ | ⟨y, hy⟩
    · refine absurd ⟨pointsMap B S hS _ eY.hom z, hinj ?_⟩ hx
      rw [← hz, ← hg, ← heY]
      simp only [pointsMap_comp_apply]
      rfl
    · exact ⟨y, hinj (by rw [← hy, ← hg0, pointsMap_comp_apply]; rfl)⟩
  have hsnd2 : IsOpenImmersion B S hS (edsSnd B S hS (W := edsOpen B S hS hsq1) hsq2).hom :=
    isOpenImmersion_of_isPullback B S hS
      (isPullback_edsInter B S hS (W := edsOpen B S hS hsq1) hsq2) hY'.2
  have hP2qc : IsQuasiCompactSpace B S hS (edsInter B S hS (W := edsOpen B S hS hsq1) hsq2).1 :=
    isQuasiCompactSpace_pullback B S hS B.contains_terminal _ _
      (edsOpen B S hS (W := edsOpen B S hS hsq1) hsq2).2
      (edsOpen B S hS hsq1).2 (IsQuasiCompactSpace.of_iso B S hS hZqc eY) hU₀qc hU''qs
  have hj₁ := epi_rightDerived_globalSectionsAbRestriction_of_eds_of_iso B S hS d
    (W := edsOpen B S hS hsq1) hsq2 hg0o _
    (hU (edsEtale B S hS (W := edsOpen B S hS hsq1) hsq2) rfl
      (edsSnd B S hS (W := edsOpen B S hS hsq1) hsq2) hsnd2
      (isEtale_edsSnd B S hS (W := edsOpen B S hS hsq1) hsq2) hP2qc _
      (isQuasicoherentOnSite_etaleModulePullback B S hS _
        (isEtale_edsEtaleHom B S hS (W := edsOpen B S hS hsq1) hsq2) _
        (isQuasicoherentOnSite_etaleModulePullback B S hS _
          (isEtale_edsOpenHom B S hS hsq1) F hF)))
    (ObjectProperty.homMk g : Z ⟶ edsOpen B S hS hsq1)
    (isEtale_of_isOpenImmersion B S hS hgo) eY heY
  exact epi_rightDerived_globalSectionsAbRestriction_comp B S hS
    (ObjectProperty.homMk g : Z ⟶ edsOpen B S hS hsq1) (edsOpenHom B S hS hsq1)
    (isEtale_of_isOpenImmersion B S hS hgo) (isEtale_edsOpenHom B S hS hsq1)
    (ObjectProperty.hom_ext _ hg) hje F d hA hj₁

/-- **Surjectivity of restriction in the top degree, `d ≥ 1`.**  Let `X` be a quasi-compact
quasi-separated algebraic space with `dim X ≤ d`, `d ≥ 1`, let `j : Z ⟶ X` be an open immersion
from a quasi-compact algebraic space and `F` a quasi-coherent `𝒪_X`-module.  Then restriction
`H^d(X, F) ⟶ H^d(Z, F|_Z)` is onto.  This is the induction principle of Stacks 08GP, with
`epi_rightDerived_globalSectionsAbRestriction_of_isAffineSpace` and
`epi_rightDerived_globalSectionsAbRestriction_of_eds`. -/
theorem epi_rightDerived_globalSectionsAbRestriction_of_dimension_le_of_pos (d : ℕ) (hd : 0 < d)
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hdim : dimension B S hS X.1 X.2 ≤ d) {Z : AlgebraicSpaces B S hS} (j : Z ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (hje : IsEtale B S hS j.hom)
    (hZqc : IsQuasiCompactSpace B S hS Z.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hje) d).app F) := by
  refine qcqs_induction_on_self B S hS B.contains_terminal X hXqc hXqs
    (fun Y _ => ∀ W : AlgebraicSpaces B S hS, W.1 = Y → ∀ {Z : AlgebraicSpaces B S hS}
      (j : Z ⟶ W) (_ : IsOpenImmersion B S hS j.hom) (hje : IsEtale B S hS j.hom),
        IsQuasiCompactSpace B S hS Z.1 → ∀ F : Modules.{u, u} B S hS W.1 W.2,
          F.IsQuasicoherentOnSite →
            Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hje) d).app F))
    ?_ ?_ X rfl j hj hje hZqc F hF
  · intro V hVaff W hW Z j hj hje hZ F hF
    obtain rfl : W = V.1.left := ObjectProperty.FullSubcategory.ext hW
    exact epi_rightDerived_globalSectionsAbRestriction_of_isAffineSpace B S hS hVaff d hd
      ((dimension_le_of_isEtale B S hS V.1.left.2 X.2 V.1.hom.hom V.2).trans hdim) j hj hje hZ F
      hF
  · intro W V U f _ hsq _ hWqs hUqc hVaff hPU _ _ W' hW' Z j hj hje hZ F hF
    obtain rfl : W' = W.1.left := ObjectProperty.FullSubcategory.ext hW'
    exact epi_rightDerived_globalSectionsAbRestriction_of_eds B S hS d hd hsq hWqs hUqc hVaff
      ((dimension_le_of_isEtale B S hS V.1.left.2 X.2 V.1.hom.hom V.2).trans hdim) hPU j hj hje hZ
      F hF

/-- **Surjectivity of restriction in degree zero, in dimension zero.**  Let `X` be a
quasi-compact quasi-separated algebraic space with `dim X ≤ 0` and `j : Z ⟶ X` an open immersion
from a quasi-compact algebraic space.  Then `H⁰(X, F) ⟶ H⁰(Z, F|_Z)` is onto for every
`𝒪_X`-module `F`: the image `U` of `j` is closed
(`AlgebraicGeometry.Space.isClosed_range_pointsMap_ι_of_dimension_le_zero`), so `U` and its
complement form an elementary distinguished square with empty intersection, and the
Mayer–Vietoris sequence applies; restriction along the isomorphism `Z ≅ U` is invertible. -/
theorem epi_rightDerived_globalSectionsAbRestriction_zero_of_dimension_le_zero
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hdim : dimension B S hS X.1 X.2 ≤ 0) {Z : AlgebraicSpaces B S hS} (j : Z ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (hje : IsEtale B S hS j.hom)
    (hZqc : IsQuasiCompactSpace B S hS Z.1) (F : Modules.{u, u} B S hS X.1 X.2) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hje) 0).app F) := by
  have : Mono j.hom := mono_of_presheaf_isOpenImmersion hj
  let U : Subfunctor X.1 := Subfunctor.range j.hom
  have hU : IsOpenSubspace B S hS U := isOpenSubspace_range_of_isAlgebraicSpace B S hS Z.2 _ hj
  let eiso : Z.1 ≅ U.toFunctor := asIso (Subfunctor.toRange j.hom)
  have hUqc : IsQuasiCompactSpace B S hS U.toFunctor := IsQuasiCompactSpace.of_iso B S hS hZqc eiso
  have hcl := isClosed_range_pointsMap_ι_of_dimension_le_zero B S hS X.2 hXqc hXqs hdim U hU hUqc
  let U' : Subfunctor X.1 := openSubspaceOfPoints B S hS X.1
    (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
  have hU' : IsOpenSubspace B S hS U' :=
    isOpenSubspace_openSubspaceOfPoints B S hS X.2 _ hcl.isOpen_compl
  have hU'range : Set.range (pointsMap B S hS U'.toFunctor U'.ι) =
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hsq1 := isElementaryDistinguishedSquare_of_compl_subset B S hS X.2 U hU hU'.1 U'.ι hU'.2
    hU'range.ge
  have hdisj : Disjoint (Set.range (pointsMap B S hS U.toFunctor U.ι))
      (Set.range (pointsMap B S hS U'.toFunctor U'.ι)) := by
    rw [hU'range]
    exact disjoint_compl_right
  exact epi_rightDerived_globalSectionsAbRestriction_of_epi_edsOpenHom_of_iso B S hS 0 hsq1 F
    (epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_isZero B S hS hsq1 F 0
      (isZero_rightDerived_globalSectionsAb_of_isEmpty_points B S hS _
        (isEmpty_points_pullback_of_disjoint B S hS U.ι U'.ι hdisj) _ 0))
    j hje eiso (Subfunctor.toRange_ι j.hom)

/-- **Surjectivity of restriction in the top degree.**  Let `X` be a quasi-compact
quasi-separated algebraic space with `dim X ≤ d`, `j : Z ⟶ X` an open immersion from a
quasi-compact algebraic space and `F` a quasi-coherent `𝒪_X`-module.  Then
`H^d(X, F) ⟶ H^d(Z, F|_Z)` is onto. -/
theorem epi_rightDerived_globalSectionsAbRestriction_of_dimension_le (d : ℕ)
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hdim : dimension B S hS X.1 X.2 ≤ d) {Z : AlgebraicSpaces B S hS} (j : Z ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (hje : IsEtale B S hS j.hom)
    (hZqc : IsQuasiCompactSpace B S hS Z.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hje) d).app F) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact epi_rightDerived_globalSectionsAbRestriction_zero_of_dimension_le_zero B S hS X hXqc
      hXqs (by exact_mod_cast hdim) j hj hje hZqc F
  · exact epi_rightDerived_globalSectionsAbRestriction_of_dimension_le_of_pos B S hS d hd X hXqc
      hXqs hdim j hj hje hZqc F hF

end AlgebraicGeometry.Space

end
